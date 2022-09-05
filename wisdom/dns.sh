#!/bin/bash

# DNS stuff

# Various ways to query DNS
dig example.com               # Best --- bypasses cache
dig @192.168.0.1 example.com  # Query a specific server
host example.com
nslookup example.com

# Clear OS DNS cache on MacOS (10.15 and later)
sudo dscacheutil -flushcache && sudo killall -HUP mDNSResponder
