#!/usr/bin/env bash

# doesn't work the way you expect!
# when a bunch of commands appear under a boolean operator, -e flag ignored :(
set -ex
{
    echo 1
    false
    echo 2
} || echo foo

# this doesn't work either, with or without set -ex inside the subshell
(
    # set -ex
    echo 1
    false
    echo 2
) || echo foo
