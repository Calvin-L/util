function __gitinfo() {
	if [ -d .git ] || git rev-parse --git-dir >/dev/null 2>&1
	then
		echo -n " [$(git rev-parse --abbrev-ref HEAD 2>/dev/null)]"
	fi
}

function __prompt() {
	local EXIT="$?" # return code of last process
    local GREEN='01;32m'
    local RED='01;31m'
    if [[ "$EXIT" == "0" ]]; then
        __EXIT_STATUS_COLOR="${GREEN}"
    else
        __EXIT_STATUS_COLOR="${RED}"
    fi
}

export CLICOLOR=yes # colors for ls
export LS_COLORS='rs=0:di=01;34:ln=01;36:mh=00:pi=40;33:so=01;35:do=01;35:bd=40;33;01:cd=40;33;01:or=40;31;01:su=37;41:sg=30;43:ca=30;41:tw=30;42:ow=34;42:st=37;44:ex=01;32'; # colors for tree, generated using dircolors on linux
export PROMPT_COMMAND="__prompt;$PROMPT_COMMAND"
export PS1='\[\e[00;36m\]\w\[\e[00;33m\]$(__gitinfo) \[\e[${__EXIT_STATUS_COLOR}\]\$ \[\e[00m\]'
export PATH="/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/opt/X11/bin"
export PATH="$HOME/.cabal/bin:$PATH"
# export PATH="$HOME/Library/Python/3.6/bin:$PATH"
export PATH="$PATH:/usr/local/sbin"
export PATH="$HOME/bin:$PATH"
# source "$HOME/.git-completion.bash"
export EDITOR="subl -nw"
export HOMEBREW_EDITOR="$EDITOR"
export MAKEFLAGS="-j4"

# Python setup
# export PYTHONPATH="/usr/local/lib/python2.7/site-packages:$PYTHONPATH"
export PYTHONUNBUFFERED=unbuffered

# Ignore duplicate history items (e.g. if you issue "make && ./run.sh" over and over it is coalesced into one entry)
export HISTCONTROL=ignoredups

# Android
# export ANDROID_HOME="/usr/local/opt/android-sdk"

# LLVM
# export PATH="$PATH:/usr/local/opt/llvm/bin"

# LaTeX
# export PATH="$PATH:/usr/local/texlive/2017/bin/x86_64-darwin"

# Java setup
if false; then

    # A LOT of java tools need this, and for some dumb reason the JDK people refuse
    # to release a tool that will tell you what it is on your system.
    export JAVA_HOME="/Library/Java/JavaVirtualMachines/jdk1.7.0_40.jdk/Contents/Home"

    # Checker framework nonsense
    export JSR308="$HOME/sources/jsr308"
    export CHECKERS="$JSR308/checker-framework/checkers"
    export PATH="$CHECKERS/binary:$JSR308/jsr308-langtools/dist/bin:$PATH"

else
    # Java 1.8 FTW
    export JAVA_HOME="$(/usr/libexec/java_home)"
fi

for F in $(ls /usr/local/etc/bash_completion.d | fgrep -v ctest); do
    source "/usr/local/etc/bash_completion.d/$F"
done

# OPAM configuration
# . /Users/loncaric/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true

# Nix
if [ -e /Users/loncaric/.nix-profile/etc/profile.d/nix.sh ]; then . /Users/loncaric/.nix-profile/etc/profile.d/nix.sh; fi # added by Nix installer
