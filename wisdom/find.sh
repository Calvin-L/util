#!/bin/bash

# "find" is enormously useful, but even worse than "tar" when it comes to
# memorable command-line flags...

# Note quoting: *.java in bash will expand to something based on what's in
# your current directory.  If there are no .java files then it expands to
# literally '*.java'.  (In zsh if there are no java files the shell will throw
# an error instead.)  On the other hand, '*.java' means "the literal string
# '*.java'", which is more often what you want with find.  In short, you should
# understand why this happens:
#
#     ~ $ cd /tmp
#     /tmp $ touch x.txt
#     /tmp $ touch y.txt
#     /tmp $ find . -iname *.txt
#     find: y.txt: unknown primary or operator
#     /tmp $ find . -iname '*.txt'
#     ./x.txt
#     ./y.txt
#
# Double-quotes are probably fine too, but I don't trust them because they will
# expand $variables and maybe other things.

# find .java files containing the string 'foo'
# Notes:
#  - The \; to send a literal semicolon---';' would work also.
#  - The '-exec' overrides the default -print behavior, so we need to specify
#    '-print' manually.
#  - The '{}' stands in for the argument to fgrep; if omitted, fgrep will
#    hang trying to read from stdin and our command will not terminate.
find . -iname '*.java' -exec fgrep -q foo {} \; -print

# find files (not directories) modified in the last 7 days
# Notes:
#  - The '-' in '-7d' indicates the comparison direction, and is not a
#    negative sign; "-mtime -X" means "modtime >= now-X" to find files modified
#    more recently than X time ago, while "-mtime +X" means "modtime <= now-X"
#    to find files modified more than X time ago.
#  - Specifying the unit 'd' is a good idea; if omitted, find does some
#    rounding and other shenanigans and it's harder to tell what you're really
#    going to find.
find . -type f -mtime -7d

# Excluding subtrees, the quick-and-dirty way:
find . -not -path '*/.git/*'

# Find does not promise to be terribly smart about the "-path" test.  In the
# line above, it will actually descend into the ".git" subtree and explore
# everything there.  For big find jobs you can use "-prune" to prevent this
# behavior.
# Notes:
#  - "-prune" is a test that always evaluates to true and silences the default
#    "-print" behavior.
#  - If "-prune" is applied to a directory, find will not explore the subtree
#    below the directory.
#  - To use "-prune" effectively, use it with "-o" for "OR" along with the test
#    you actually want to perform.
find . \( -type d -name '.git' -prune \) -o -print

# To see what was pruned:
find . -type d -name '.git' -prune -print
