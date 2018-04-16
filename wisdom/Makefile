# Useful patterns for writing Makefiles.

# -----------------------------------------------------------------------------

# (0.) Misc. things to know

# https://www.gnu.org/software/make/manual/make.html#Makefile-Basics, 2018-04-13:
#  > Every Makefile should contain this line:
#  >     SHELL = /bin/sh
#  > to avoid trouble on systems where the SHELL variable might be inherited
#  > from the environment. (This is never a problem with GNU make.)
# I would modify that to be `SHELL = /bin/bash`, since `sh` is often an alias
# for Bash (i.e. on MacOS), and Bash has many more useful features.
SHELL = /bin/bash

# https://www.gnu.org/software/make/manual/make.html#Suffix-Rules, 2018-04-13
#  > Suffix rules are obsolete because pattern rules are more general and
#  > clearer. They are supported in GNU make for compatibility with old
#  > makefiles.
# I believe eliminating the default suffixes is generally good practice, unless
# you really plan to use them.
.SUFFIXES:

# https://www.gnu.org/software/make/manual/make.html#Phony-Targets, 2018-04-13:
#  > A phony target should not be a prerequisite of a real target file; if it
#  > is, its recipe will be run every time make goes to update that file. As
#  > long as a phony target is never a prerequisite of a real target, the phony
#  > target recipe will be executed only when the phony target is a specified
#  > goal
# This behavior is actually exploitable, see (1.) below

# https://www.gnu.org/software/make/manual/make.html#Multiple-Targets, 2018-04-13:
#  > A rule with multiple targets is equivalent to writing many rules, each
#  > with one target, and all identical aside from that.
# So, Make does not support recipes that generate multiple files.  This rule,
# for instance, declares two rules using a more succinct syntax.
target-a target-b:
	touch '$@'

# However, pattern rules behave differently:
# https://www.gnu.org/software/make/manual/make.html#Pattern-Intro, 2018-04-13:
#  >    %.tab.c %.tab.h: %.y
#  >        bison -d $<
#  > This tells make that the recipe ‘bison -d x.y’ will make both x.tab.c and
#  > x.tab.h.
# For these sorts of things, the special target variable $@ refers to ONE of
# the targets (the one that cause the recipe to be invoked).  In parallel
# builds I assume this could be arbitrary.

# https://www.gnu.org/software/make/manual/make.html#Shell-Function, 2018-04-13:
#  > The commands run by calls to the shell function are run when the function
#  > calls are expanded (see How make Reads a Makefile). Because this function
#  > involves spawning a new shell, you should carefully consider the
#  > performance implications of using the shell function within recursively
#  > expanded variables vs. simply expanded variables

# https://www.gnu.org/software/make/manual/make.html#Flavors, 2018-04-13:
#  > The first flavor of variable is a recursively expanded variable. Variables
#  > of this sort are defined by lines using ‘=’ (see Setting Variables) or by
#  > the define directive (see Defining Multi-Line Variables). The value you
#  > specify is installed verbatim; if it contains references to other
#  > variables, these references are expanded whenever this variable is
#  > substituted (in the course of expanding some other string). When this
#  > happens, it is called recursive expansion.
#  > [...] This flavor of variable is the only sort supported by most other
#  > versions of make.

#  > [...] Simply expanded variables are defined by lines using ‘:=’ or ‘::=’
#  > (see Setting Variables). Both forms are equivalent in GNU make; however
#  > only the ‘::=’ form is described by the POSIX standard (support for ‘::=’
#  > was added to the POSIX standard in 2012, so older versions of make won’t
#  > accept this form either).
#  > The value of a simply expanded variable is scanned once and for all,
#  > expanding any references to other variables and functions, when the
#  > variable is defined. The actual value of the simply expanded variable is
#  > the result of expanding the text that you write. It does not contain any
#  > references to other variables; it contains their values as of the time
#  > this variable was defined.

# So, this is bad (prints lots of 1s)

# V_BAD=$(shell cat /tmp/x | tee -a /tmp/x)
# .PHONY: badvar
# badvar:
# 	@echo 1 > /tmp/x
# 	@echo '$(V_BAD)'
# 	@echo '$(V_BAD)'
# 	@echo '$(V_BAD)'

# This is better (prints nothing)
# NOTE: this behaves differently with := and ::=, but the manual suggests they
# are the same. Wtf?
# Seems that MacOS make (3.81) was released in 2006, but ::= came up in 2012.
# So ::= has no effect? It is like not defining the var at all.
# From https://stackoverflow.com/questions/32061694/makefile-difference-between-and-assignment-operators
#  > [Regarding ::=,] Seems like the text in the GNU Make manual was hopeful
#  > that it would appear within the year when that text was written
# There is no "right" solution.  I guess := is the least-bad...

# V_GOOD := $(shell cat /tmp/x | tee -a /tmp/x)
# .PHONY: goodvar
# goodvar:
# 	@echo 1 > /tmp/x
# 	@echo '$(V_GOOD)'
# 	@echo '$(V_GOOD)'
# 	@echo '$(V_GOOD)'

# -----------------------------------------------------------------------------

# (1.) Depend on a resource whose "out-of-dateness" must be determined by a
#    script.  For instance, download the latest version of a remote repo
#    every time `make` is invoked, but only rebuild downstream targets if
#    there was a new version.

# There is no fantastic way to achieve both goals:
#  (1) only run the script if the target is in the dependency tree for the
#      requested targets and
#  (2) only rebuild downstream targets if things changed

# However, it can be done.  The way this works is:
#  (a) dummy.ok depends on a phony target, so it must always be rebuilt if it
#      is in the dependency tree
#  (b) the recipe for dummy.ok only runs `touch dummy.ok` if the repo must be
#      cloned for the first time or an update took place
#  (c) when building my-target, Make actually re-checks the modification times
#      of its dependents and skips rebuilding if possible; see
#      https://www.gnu.org/software/make/manual/make.html#How-Make-Works,
#      2018-04-13:
#       > After recompiling [prerequisites], make decides whether to [rebuild
#       > the target]. This must be done if the [target] does not exist, or if
#       > any of the [prerequisites] are newer
# Invariant: the modification time of dummy.ok is the most recent time its
# recipe was invoked and a change needed to be pulled.

# See also:
# https://stackoverflow.com/questions/11550997/in-a-makefile-is-it-possible-to-have-a-target-be-out-of-date-iff-another-target

.PHONY: always-rebuild

# Note: I am not certain that this is necessary in conjunction with .PHONY, but
# it doesn't hurt.
always-rebuild:
	@true

dummy.ok: always-rebuild
	if [[ -e repo ]]; then \
		V="$$(cd repo && git pull)" && \
		if [[ "Already up to date." == "$$V" ]]; then \
			echo '(no change)'; \
		else \
			echo 'Updated!' && \
			echo "$$V" && \
			touch '$@'; \
		fi; \
	else \
		git clone git@github.com:CozySynthesizer/cozy.git repo && touch '$@'; \
	fi

my-target: dummy.ok
	echo 'Building $@...'
	sleep 3
	touch '$@'

other:
	touch '$@'

# -----------------------------------------------------------------------------

.PHONY: clean
clean:
	$(RM) dummy.ok my-target other target-a target-b
	$(RM) -r repo
