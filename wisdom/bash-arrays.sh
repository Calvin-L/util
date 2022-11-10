#!/bin/bash

# Arrays
arr=('x' 'y')

echo "${arr[0]}" # 'x'
echo "${arr[2]}" # ''
echo "${arr[@]}" # equivalent to `echo 'x' 'y'`

# Append an element / concatenate another array
arr+=('z')
echo "${arr[@]}" # 'x y z'

# Loop over an array
for i in "${arr[@]}"
do
   echo "$i"
done
