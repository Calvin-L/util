#!/bin/bash

# Arrays
arr=('x' 'y')

echo "${arr[0]}" # 'x'
echo "${arr[2]}" # ''
echo "${arr[@]}" # equivalent to `echo 'x' 'y'`
