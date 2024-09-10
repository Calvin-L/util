#!/bin/bash

# Cut a section out of a video based on timestamps.
#  -ss TIMESTAMP        start at TIMESTAMP, either HH:MM:SS.MS or total number of seconds
#  -t  DURATION         take DURATION seconds
# Note the order of arguments: -ss and -t have to appear BEFORE -i!
ffmpeg \
    -ss 7.9 \
    -t 60 \
    -i twohourshow.avi \
    out.avi

# Cut a section out of a video based on timestamps (alternative method).
# This method is generally slower since ffmpeg has to read the ENTIRE file.
# It may have some advantages I don't know about.
# Source: https://twitter.com/climagic/status/1257341873854840834
ffmpeg \
    -i twohourshow.avi \
    -vf "select='between(t,7.9,7207.9)',setpts=N/FRAME_RATE/TB" \
    -af "aselect='between(t,7.9,7207.9)',asetpts=N/SR/TB" \
    out.avi

# Extract audio.
#  -vn              no video
#  -acodec copy     copy audio track as-is
# Inspect the file with `ffprobe FILE` to determine correct audio extension.
# Source: https://stackoverflow.com/questions/9913032/how-can-i-extract-audio-from-video-with-ffmpeg
ffmpeg \
    -i file.avi \
    -vn \
    -acodec copy \
    out.aac

# Cut out WAV in time range (given in seconds).
# (Should this use -ss/-t instead? See above.)
ffmpeg \
    -i file.mp4 \
    -vn \
    -af "aselect='between(t,67.5,76)'" \
    out.wav

# Cut out specific streams (e.g. Engish audio only).
#   -map INPUT:STREAM        include the given stream in the output
# Lots of things to know:
#   If no -map arguments are given, all streams are included.
#   If any -map arguments are given, only those streams are included.
#   Inputs are 0-indexed starting from the first -i INPUT.
#   Streams are 0-indexed; use `ffprobe FILE` to list them.
ffmpeg \
    -i file.mp4 \
    -map 0:0 \
    -map 0:1 \
    out.wav
