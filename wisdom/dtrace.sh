#!/bin/bash

# "DTrace" is BSD's souped-up equivalent of the Linux utility "STrace".  DTrace
# and STrace can track system calls and resource usage for any running process.
#
# DTrace has its own little programming language for specifying what to track.
# Since that's pretty hard to learn, I usually use "dtruss" instead, which is a
# simple wrapper around the most common DTrace functionality.
#
# Because it is so powerful, DTrace requires admin privileges (sudo).

# List all files opened by the C++ compiler as it runs:
sudo dtruss -f -t open -- c++ test.cpp

# NOTE 2020/7/22: MacOS El Capitan (10.11) has "System Integrity Protection"
# which disables almost all functionality of DTrace.  Example errors:
#
# > dtrace: failed to execute c++: dtrace cannot control executables signed with restricted entitlements
#
# > dtrace: failed to execute ./c++: (os/kern) failure
#
# To fix it, you need to copy the executable you want to trace and remove its
# code signature:
cp /usr/bin/c++ .
codesign --remove-signature ./c++
sudo dtruss ... -- ./c++ ... # works normally, but can't follow calls to other executables (dtruss -f flag)
