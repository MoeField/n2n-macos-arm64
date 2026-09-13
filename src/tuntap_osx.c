/**
 * (C) 2007-22 - ntop.org and contributors
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not see see <http://www.gnu.org/licenses/>
 *
 */


#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>              // for arc4random_buf
#include <string.h>
#include <unistd.h>
#include <time.h>
#include "n2n.h"


#ifdef __APPLE__

#include <arpa/inet.h>           // for inet_addr
#include <ifaddrs.h>             // for getifaddrs
#include <net/if.h>              // for IFNAMSIZ
#include <net/if_dl.h>           // for sockaddr_dl, LLADDR
#include <net/if_utun.h>         // for UTUN_CONTROL_NAME, UTUN_OPT_IFNAME
#include <sys/ioctl.h>           // for ioctl
#include <sys/kern_control.h>    // for ctl_info, CTLIOCGINFO
#include <sys/socket.h>          // for connect
#include <sys/sys_domain.h>      // for AF_SYSTEM, AF_SYS_CONTROL


#define N2N_OSX_TAPDEVICE_SIZE  32

/* The utun device is a layer-3 device: it carries bare IP packets, whereas
 * n2n's edge expects a layer-2 tap device carrying ethernet frames. Therefore
 * the ethernet framing including ARP is emulated here: outbound IP packets
 * get an ethernet header (with the peer's MAC address resolved through ARP
 * on the overlay), inbound ethernet frames are stripped of their header and
 * ARP requests are answered.
 *
 * ARP requests caused by a failed address resolution are handed over to the
 * edge right away by returning them from tuntap_read(), which is where the
 * edge picks up packets to send. ARP replies (which are triggered from within
 * tuntap_write() and cannot be returned) are sent through the n2n_eth_tx_hook
 * the edge provides.
 */

#define N2N_UTUN_HEADER_SIZE    4    /* address family prefix of every utun packet */
#define N2N_UTUN_NEIGH_MAX      64   /* ARP cache size */
#define N2N_UTUN_PEND_MAX       8    /* packets waiting for ARP resolution */

#define N2N_UTUN_NEIGH_TIMEOUT  600  /* seconds, after which an ARP entry is stale */
#define N2N_UTUN_PEND_TIMEOUT   5    /* seconds, after which a pending packet is dropped */
#define N2N_UTUN_ARP_RETRY      1    /* seconds between ARP retries for the same packet */

#define N2N_UTUN_ETHERTYPE_IP   0x0800
#define N2N_UTUN_ETHERTYPE_ARP  0x0806

/* offsets within an ARP ethernet frame, see RFC 826 */
#define N2N_ARP_OPCODE_OFF      20
#define N2N_ARP_SENDER_MAC_OFF  22
#define N2N_ARP_SENDER_IP_OFF   28
#define N2N_ARP_TARGET_MAC_OFF  32
#define N2N_ARP_TARGET_IP_OFF   38
#define N2N_UTUN_ARP_FRAME_SIZE 42

/* offsets within an IPv4 header */
#define N2N_IP4_SRC_OFF         12
#define N2N_IP4_DST_OFF         16
#define N2N_IP4_MIN_SIZE        20


typedef struct utun_neigh {
    uint32_t  ip;             /* overlay IP address, network byte order, 0 if unused */
    n2n_mac_t mac;
    time_t    last_seen;
} utun_neigh_t;

typedef struct utun_pend {
    uint32_t  ip;             /* overlay IP address of the packet's destination */
    uint16_t  len;            /* 0 if unused */
    uint8_t   data[N2N_PKT_BUF_SIZE];  /* the IP packet itself */
    time_t    queued;
    time_t    last_arp;
} utun_pend_t;

typedef struct utun_ctx {
    int          fd;          /* -1 while not (yet) using utun */
    char         ifname[IFNAMSIZ];
    n2n_mac_t    mac;
    uint32_t     ip;
    uint32_t     mask;
    utun_neigh_t neigh[N2N_UTUN_NEIGH_MAX];
    utun_pend_t  pend[N2N_UTUN_PEND_MAX];
    time_t       last_unhandled_warning;
} utun_ctx_t;

static utun_ctx_t utun_ctx = { .fd = -1 };


/* ************************************** */

/* pick a stable, locally administered MAC address for the emulated ethernet
 * layer, based on the MAC address of the first real interface found. */
static void utun_pick_mac (n2n_mac_t mac) {

    struct ifaddrs *ifa = NULL, *cur;

    memset(mac, 0, sizeof(n2n_mac_t));

    if(getifaddrs(&ifa) == 0) {
        for(cur = ifa; cur; cur = cur->ifa_next) {
            if(cur->ifa_addr && (cur->ifa_addr->sa_family == AF_LINK) &&
               !(cur->ifa_flags & IFF_LOOPBACK)) {
                struct sockaddr_dl *sdl = (struct sockaddr_dl*)(cur->ifa_addr);

                if((sdl->sdl_alen == ETH_ADDR_LEN) && !is_null_mac((uint8_t*)LLADDR(sdl))) {
                    memcpy(mac, LLADDR(sdl), ETH_ADDR_LEN);
                    break;
                }
            }
        }
        freeifaddrs(ifa);
    }

    if(is_null_mac(mac))
        arc4random_buf(mac, ETH_ADDR_LEN);

    /* make sure it is neither a multicast nor the very interface's own address */
    mac[0] = (mac[0] & 0xFC) | 0x02;
}


static int utun_neigh_lookup (uint32_t ip, uint8_t *mac) {

    int i;

    for(i = 0; i < N2N_UTUN_NEIGH_MAX; i++) {
        if(utun_ctx.neigh[i].ip == ip) {
            memcpy(mac, utun_ctx.neigh[i].mac, ETH_ADDR_LEN);
            return 0;
        }
    }

    return -1;
}


static void utun_neigh_update (uint32_t ip, const uint8_t *mac, time_t now) {

    int i;
    int slot = -1;
    time_t oldest = now;

    if((ip == 0) || (ip == 0xFFFFFFFF) || (ip == utun_ctx.ip) || is_null_mac(mac))
        return;

    for(i = 0; i < N2N_UTUN_NEIGH_MAX; i++) {
        if(utun_ctx.neigh[i].ip == ip) {
            memcpy(utun_ctx.neigh[i].mac, mac, ETH_ADDR_LEN);
            utun_ctx.neigh[i].last_seen = now;
            return;
        }
        /* a MAC address that shows up on another IP address invalidates the old entry */
        if(memcmp(utun_ctx.neigh[i].mac, mac, ETH_ADDR_LEN) == 0)
            utun_ctx.neigh[i].ip = 0;
        if((utun_ctx.neigh[i].ip == 0) || (utun_ctx.neigh[i].last_seen < oldest)) {
            oldest = utun_ctx.neigh[i].last_seen;
            slot = i;
        }
    }

    if(slot < 0)
        slot = 0;

    utun_ctx.neigh[slot].ip = ip;
    memcpy(utun_ctx.neigh[slot].mac, mac, ETH_ADDR_LEN);
    utun_ctx.neigh[slot].last_seen = now;
}


static void utun_neigh_expire (time_t now) {

    int i;

    for(i = 0; i < N2N_UTUN_NEIGH_MAX; i++)
        if((utun_ctx.neigh[i].ip != 0) && (now - utun_ctx.neigh[i].last_seen > N2N_UTUN_NEIGH_TIMEOUT))
            utun_ctx.neigh[i].ip = 0;
}


static int utun_build_arp (uint16_t opcode,
                           const uint8_t *dst_mac, uint32_t dst_ip,
                           const uint8_t *src_mac, uint32_t src_ip,
                           uint8_t *out) {

    ether_hdr_t *eh = (ether_hdr_t*)out;

    /* hw type ethernet, protocol IPv4, 6 and 4 byte addresses */
    memcpy(out + ETH_FRAMESIZE, "\x00\x01\x08\x00\x06\x04", 6);
    out[N2N_ARP_OPCODE_OFF] = (opcode >> 8) & 0xff;
    out[N2N_ARP_OPCODE_OFF + 1] = opcode & 0xff;
    memcpy(out + N2N_ARP_SENDER_MAC_OFF, src_mac, ETH_ADDR_LEN);
    memcpy(out + N2N_ARP_SENDER_IP_OFF, &src_ip, 4);
    memcpy(out + N2N_ARP_TARGET_MAC_OFF, dst_mac, ETH_ADDR_LEN);
    memcpy(out + N2N_ARP_TARGET_IP_OFF, &dst_ip, 4);
    memcpy(eh->dhost, dst_mac, ETH_ADDR_LEN);
    memcpy(eh->shost, src_mac, ETH_ADDR_LEN);
    eh->type = htons(N2N_UTUN_ETHERTYPE_ARP);

    return N2N_UTUN_ARP_FRAME_SIZE;
}


static int utun_pend_add (uint32_t ip, const uint8_t *pkt, uint16_t len, time_t now) {

    int i;
    int slot = -1;
    time_t oldest = now + 1;

    if((len == 0) || (len > N2N_PKT_BUF_SIZE))
        return -1;

    /* a packet to the same destination that is already waiting is dropped */
    for(i = 0; i < N2N_UTUN_PEND_MAX; i++) {
        if(utun_ctx.pend[i].len == 0) {
            slot = i;
            break;
        }
        if(utun_ctx.pend[i].queued < oldest) {
            oldest = utun_ctx.pend[i].queued;
            slot = i;
        }
    }

    if(slot < 0)
        return -1;

    memset(&(utun_ctx.pend[slot]), 0, sizeof(utun_pend_t));
    utun_ctx.pend[slot].ip = ip;
    utun_ctx.pend[slot].len = len;
    memcpy(utun_ctx.pend[slot].data, pkt, len);
    utun_ctx.pend[slot].queued = now;
    utun_ctx.pend[slot].last_arp = now;

    return 0;
}


/* map an IPv4 address to the ethernet address used for it on a local network */
static void utun_map_ip_to_mac (uint32_t ip, uint8_t *mac) {

    memset(mac, 0, ETH_ADDR_LEN);

    if(ip == 0xFFFFFFFF) {
        /* limited broadcast */
        memset(mac, 0xFF, ETH_ADDR_LEN);
    } else if((ntohl(ip) >> 28) == 0x0E) {
        /* multicast, 01:00:5e plus the lower 23 bits of the address */
        uint32_t addr = ntohl(ip) & 0x007FFFFF;

        mac[0] = 0x01;
        mac[1] = 0x00;
        mac[2] = 0x5E;
        mac[3] = (addr >> 16) & 0x7F;
        mac[4] = (addr >> 8) & 0xFF;
        mac[5] = addr & 0xFF;
    }
}


/* find the ethernet address to send an IP packet to: broadcast and multicast
 * addresses are mapped, everything else is looked up in the ARP cache */
static int utun_resolve (uint32_t ip, uint8_t *mac) {

    utun_map_ip_to_mac(ip, mac);

    if(!is_null_mac(mac))
        return 0;

    return utun_neigh_lookup(ip, mac);
}


static int utun_create (void) {

    struct ctl_info ctl_info;
    struct sockaddr_ctl sc;
    socklen_t len;
    int fd;

    fd = socket(PF_SYSTEM, SOCK_DGRAM, SYSPROTO_CONTROL);
    if(fd < 0) {
        traceEvent(TRACE_ERROR, "unable to create utun control socket: %s", strerror(errno));
        return -1;
    }

    memset(&ctl_info, 0, sizeof(ctl_info));
    strncpy(ctl_info.ctl_name, UTUN_CONTROL_NAME, sizeof(ctl_info.ctl_name) - 1);
    if(ioctl(fd, CTLIOCGINFO, &ctl_info) < 0) {
        traceEvent(TRACE_ERROR, "unable to look up %s: %s", UTUN_CONTROL_NAME, strerror(errno));
        close(fd);
        return -1;
    }

    memset(&sc, 0, sizeof(sc));
    sc.sc_id = ctl_info.ctl_id;
    sc.sc_len = sizeof(sc);
    sc.sc_family = AF_SYSTEM;
    sc.ss_sysaddr = AF_SYS_CONTROL;
    sc.sc_unit = 0; /* have the kernel pick the next free unit */
    if(connect(fd, (struct sockaddr*)&sc, sizeof(sc)) < 0) {
        traceEvent(TRACE_ERROR, "unable to connect to %s: %s", UTUN_CONTROL_NAME, strerror(errno));
        close(fd);
        return -1;
    }

    len = sizeof(utun_ctx.ifname);
    if(getsockopt(fd, SYSPROTO_CONTROL, UTUN_OPT_IFNAME, utun_ctx.ifname, &len) < 0) {
        traceEvent(TRACE_ERROR, "unable to read utun interface name: %s", strerror(errno));
        close(fd);
        return -1;
    }

    return fd;
}


int tuntap_open (tuntap_dev *device,
                 char *dev,
                 const char *address_mode, /* static or dhcp */
                 char *device_ip,
                 char *device_mask,
                 const char *device_mac,
                 int mtu,
                 int metric) {

    int i;
    char tap_device[N2N_OSX_TAPDEVICE_SIZE];

    /* first call: try to get hold of a utun device */
    if(utun_ctx.fd < 0) {
        utun_pick_mac(utun_ctx.mac);
        utun_ctx.fd = utun_create();
        if(utun_ctx.fd < 0)
            traceEvent(TRACE_WARNING, "no utun device available, falling back to /dev/tap");
    }

    if(utun_ctx.fd >= 0) {
        char buf[256];
        char net_buf[N2N_NETMASK_STR_SIZE];
        char *net_str;
        macstr_t mac_str;
        uint32_t mask, net, prefix;
        n2n_mac_t mac;

        if(device_mac && (device_mac[0] != '\0')) {
            if(str2mac(mac, device_mac) >= 0)
                memcpy(utun_ctx.mac, mac, ETH_ADDR_LEN);
            else
                traceEvent(TRACE_WARNING, "invalid MAC address %s, keeping %s",
                           device_mac, macaddr_str(mac_str, utun_ctx.mac));
        }

        device->fd = utun_ctx.fd;
        device->ip_addr = inet_addr(device_ip);
        memcpy(device->mac_addr, utun_ctx.mac, ETH_ADDR_LEN);
        utun_ctx.ip = device->ip_addr;

        mask = inet_addr(device_mask);
        utun_ctx.mask = mask;
        net = utun_ctx.ip & mask;
        prefix = mask2bitlen(ntohl(mask));

        /* a utun device is a point-to-point interface and thus needs a peer
         * address. the network address is used, it can never be a host's
         * address and the actual routing is done through the route below. */
        net_str = intoa(ntohl(net), net_buf, sizeof(net_buf));
        snprintf(buf, sizeof(buf), "ifconfig %s inet %s %s netmask %s mtu %u up",
                 utun_ctx.ifname, device_ip, net_str, device_mask, mtu);
        system(buf);

        /* all community members are reached through this interface */
        snprintf(buf, sizeof(buf), "route -n add -net %s -netmask %s -interface %s",
                 net_str, device_mask, utun_ctx.ifname);
        system(buf);

        traceEvent(TRACE_NORMAL, "Interface %s up and running (%s/%u, mtu %u)",
                   utun_ctx.ifname, device_ip, prefix, mtu);
        traceEvent(TRACE_NORMAL, "Interface %s [MTU %u] mac %s",
                   utun_ctx.ifname, mtu, macaddr_str(mac_str, device->mac_addr));

        /* remember: overlay IP traffic only, the MAC addresses are emulated */
        traceEvent(TRACE_INFO, "%s is a layer-3 device, emulating a layer-2 (tap) interface",
                   utun_ctx.ifname);

        return device->fd;
    }

    /* fall back to the tuntaposx kernel extension, if the utun device could
     * not be created. requires /dev/tap0 - /dev/tap254 to be present and
     * root privileges */
    for(i = 0; i < 255; i++) {
        snprintf(tap_device, sizeof(tap_device), "/dev/tap%d", i);

        device->fd = open(tap_device, O_RDWR);
        if(device->fd > 0) {
            traceEvent(TRACE_NORMAL, "Succesfully open %s", tap_device);
            break;
        }
    }

    if(device->fd < 0) {
        traceEvent(TRACE_ERROR, "Unable to open any tap devices /dev/tap0 through /dev/tap254. Is this user properly authorized to access those descriptors?");
        traceEvent(TRACE_ERROR, "Please read https://github.com/ntop/n2n/blob/dev/doc/Building.md");
        return -1;
    } else {
        char buf[256];
        FILE *fd;

        device->ip_addr = inet_addr(device_ip);

        if(device_mac && device_mac[0] != '\0') {
            // FIXME - this is not tested. might be wrong syntax for OS X
            // set the hw address before bringing the if up
            snprintf(buf, sizeof(buf), "ifconfig tap%d ether %s", i, device_mac);
            system(buf);
        }

        snprintf(buf, sizeof(buf), "ifconfig tap%d %s netmask %s mtu %d up", i, device_ip, device_mask, mtu);
        system(buf);

        traceEvent(TRACE_NORMAL, "Interface tap%d up and running (%s/%s)", i, device_ip, device_mask);

        // read MAC address
        snprintf(buf, sizeof(buf), "ifconfig tap%d |grep ether|cut -c 8-24", i);
        // traceEvent(TRACE_INFO, "%s", buf);

        fd = popen(buf, "r");
        if(fd < 0) {
            tuntap_close(device);
            return -1;
        } else {
            int a, b, c, d, e, f;

            buf[0] = 0;
            fgets(buf, sizeof(buf), fd);
            pclose(fd);

            if(buf[0] == '\0') {
                traceEvent(TRACE_ERROR, "Unable to read tap%d interface MAC address");
                exit(0);
            }

            traceEvent(TRACE_NORMAL, "Interface tap%d [MTU %d] mac %s", i, mtu, buf);
            if(sscanf(buf, "%02x:%02x:%02x:%02x:%02x:%02x", &a, &b, &c, &d, &e, &f) == 6) {
                device->mac_addr[0] = a, device->mac_addr[1] = b;
                device->mac_addr[2] = c, device->mac_addr[3] = d;
                device->mac_addr[4] = e, device->mac_addr[5] = f;
            }
        }
    }

    // read_mac(dev, device->mac_addr);

    return(device->fd);
}


int tuntap_read (struct tuntap_dev *tuntap, unsigned char *buf, int len) {

    uint8_t tmp[N2N_PKT_BUF_SIZE + N2N_UTUN_HEADER_SIZE];
    uint8_t dst_mac[ETH_ADDR_LEN];
    uint32_t dst_ip;
    ipstr_t ip_str;
    ssize_t n;
    size_t pkt_len;
    uint8_t *pkt;
    int proto;
    int i, attempt;
    time_t now;

    if(utun_ctx.fd < 0)
        return(read(tuntap->fd, buf, len));

    now = time(NULL);
    utun_neigh_expire(now);

    /* packets waiting for address resolution ... */
    for(i = 0; i < N2N_UTUN_PEND_MAX; i++) {
        if(utun_ctx.pend[i].len == 0)
            continue;

        if(now - utun_ctx.pend[i].queued > N2N_UTUN_PEND_TIMEOUT) {
            traceEvent(TRACE_INFO, "no ARP answer from %s, dropping packet",
                       intoa(ntohl(utun_ctx.pend[i].ip), ip_str, sizeof(ip_str)));
            utun_ctx.pend[i].len = 0;
            continue;
        }
        if(utun_resolve(utun_ctx.pend[i].ip, dst_mac) == 0) {
            ether_hdr_t *eh = (ether_hdr_t*)buf;

            memcpy(eh->dhost, dst_mac, ETH_ADDR_LEN);
            memcpy(eh->shost, utun_ctx.mac, ETH_ADDR_LEN);
            eh->type = htons(N2N_UTUN_ETHERTYPE_IP);
            memcpy(buf + ETH_FRAMESIZE, utun_ctx.pend[i].data, utun_ctx.pend[i].len);
            n = ETH_FRAMESIZE + utun_ctx.pend[i].len;
            utun_ctx.pend[i].len = 0;

            return(n);
        }

        /* ... are retried from time to time */
        if(now - utun_ctx.pend[i].last_arp >= N2N_UTUN_ARP_RETRY) {
            utun_ctx.pend[i].last_arp = now;
            return(utun_build_arp(0x0001, broadcast_mac, utun_ctx.pend[i].ip,
                                  utun_ctx.mac, utun_ctx.ip, buf));
        }
    }

    /* ... or read a new packet from the utun device */
    for(attempt = 0; attempt < 8; attempt++) {

        n = read(utun_ctx.fd, tmp, sizeof(tmp));
        if(n <= 0)
            return(n);

        pkt = tmp;
        pkt_len = n;
        proto = 0;

        /* every utun packet starts with the address family in network byte order */
        if((tmp[0] == 0) && (tmp[1] == 0) && (tmp[2] == 0) && (tmp[3] != 0)) {
            proto = tmp[3];
            pkt = tmp + N2N_UTUN_HEADER_SIZE;
            pkt_len = n - N2N_UTUN_HEADER_SIZE;
        }

        if((proto != AF_INET) || (pkt_len < N2N_IP4_MIN_SIZE) ||
           (pkt_len > N2N_PKT_BUF_SIZE - ETH_FRAMESIZE) || ((pkt[0] >> 4) != 4)) {
            /* the emulated ethernet layer cannot carry anything but IPv4,
             * and the ethernet header has to fit into the caller's buffer */
            if(now - utun_ctx.last_unhandled_warning > 60) {
                utun_ctx.last_unhandled_warning = now;
                traceEvent(TRACE_WARNING, "dropping non-IPv4 packet (%s), "
                           "the utun device only supports IPv4 overlays",
                           (proto == AF_INET6) ? "IPv6" : "unknown");
            }
            continue;
        }

        memcpy(&dst_ip, pkt + N2N_IP4_DST_OFF, 4);

        if(utun_resolve(dst_ip, dst_mac) == 0) {
            ether_hdr_t *eh = (ether_hdr_t*)buf;

            memcpy(eh->dhost, dst_mac, ETH_ADDR_LEN);
            memcpy(eh->shost, utun_ctx.mac, ETH_ADDR_LEN);
            eh->type = htons(N2N_UTUN_ETHERTYPE_IP);
            memcpy(buf + ETH_FRAMESIZE, pkt, pkt_len);

            return(ETH_FRAMESIZE + pkt_len);
        }

        /* no idea yet which MAC address belongs to that IP address: ask
         * everyone and retry the packet once the answer has arrived */
        utun_pend_add(dst_ip, pkt, pkt_len, now);

        return(utun_build_arp(0x0001, broadcast_mac, dst_ip,
                              utun_ctx.mac, utun_ctx.ip, buf));
    }

    traceEvent(TRACE_WARNING, "unable to read a usable packet from %s", utun_ctx.ifname);

    return(-1);
}


int tuntap_write (struct tuntap_dev *tuntap, unsigned char *buf, int len) {

    ether_hdr_t *eh;
    uint16_t type;
    time_t now;

    if(utun_ctx.fd < 0)
        return(write(tuntap->fd, buf, len));

    if(len < ETH_FRAMESIZE)
        return(len);

    eh = (ether_hdr_t*)buf;
    type = ntohs(eh->type);
    now = time(NULL);

    if((type == N2N_UTUN_ETHERTYPE_ARP) && (len >= N2N_UTUN_ARP_FRAME_SIZE)) {
        uint32_t sender_ip, target_ip;
        uint16_t opcode = (buf[N2N_ARP_OPCODE_OFF] << 8) | buf[N2N_ARP_OPCODE_OFF + 1];

        memcpy(&sender_ip, buf + N2N_ARP_SENDER_IP_OFF, 4);
        memcpy(&target_ip, buf + N2N_ARP_TARGET_IP_OFF, 4);

        /* traffic from any community member tells us where it lives */
        utun_neigh_update(sender_ip, buf + N2N_ARP_SENDER_MAC_OFF, now);
        if(opcode == 0x0002)
            utun_neigh_update(target_ip, buf + N2N_ARP_TARGET_MAC_OFF, now);

        /* answer requests for our own address */
        if((opcode == 0x0001) && (target_ip == utun_ctx.ip)) {
            uint8_t reply[N2N_UTUN_ARP_FRAME_SIZE];

            utun_build_arp(0x0002, buf + N2N_ARP_SENDER_MAC_OFF, sender_ip,
                           utun_ctx.mac, utun_ctx.ip, reply);

            if(n2n_eth_tx_hook)
                n2n_eth_tx_hook(reply, sizeof(reply));
            else
                traceEvent(TRACE_DEBUG, "unable to answer ARP request, no way to send it");
        }

        return(len);
    }

    if((type == N2N_UTUN_ETHERTYPE_IP) && (len > ETH_FRAMESIZE) &&
       (len - ETH_FRAMESIZE <= N2N_PKT_BUF_SIZE)) {
        uint32_t src_ip;

        if(is_multi_broadcast(eh->dhost) || (memcmp(eh->dhost, utun_ctx.mac, ETH_ADDR_LEN) == 0)) {
            uint8_t out[N2N_PKT_BUF_SIZE + N2N_UTUN_HEADER_SIZE];
            uint32_t family = htonl(AF_INET);

            memcpy(out, &family, N2N_UTUN_HEADER_SIZE);
            memcpy(out + N2N_UTUN_HEADER_SIZE, buf + ETH_FRAMESIZE, len - ETH_FRAMESIZE);

            if(write(utun_ctx.fd, out, len - ETH_FRAMESIZE + N2N_UTUN_HEADER_SIZE) < 0) {
                traceEvent(TRACE_DEBUG, "unable to write to %s: %s", utun_ctx.ifname, strerror(errno));
                return(-1);
            }

            memcpy(&src_ip, buf + ETH_FRAMESIZE + N2N_IP4_SRC_OFF, 4);
            utun_neigh_update(src_ip, eh->shost, now);
        }
    }

    /* everything else, IPv6 in particular, cannot be carried by a layer-3 device */

    return(len);
}


void tuntap_close (struct tuntap_dev *tuntap) {

    close(tuntap->fd);

    if(utun_ctx.fd >= 0) {
        utun_ctx.fd = -1;
        memset(utun_ctx.neigh, 0, sizeof(utun_ctx.neigh));
        memset(utun_ctx.pend, 0, sizeof(utun_ctx.pend));
    }
}

// fill out the ip_addr value from the interface, called to pick up dynamic address changes
void tuntap_get_address (struct tuntap_dev *tuntap) {

    // no action
}


#endif /* __APPLE__ */
