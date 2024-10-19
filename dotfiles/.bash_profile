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

# Make __prompt and __gitinfo available to subshells
export -f __gitinfo
export -f __prompt

export CLICOLOR=yes # colors for ls
export LS_COLORS='rs=0:di=01;34:ln=01;36:mh=00:pi=40;33:so=01;35:do=01;35:bd=40;33;01:cd=40;33;01:or=40;31;01:su=37;41:sg=30;43:ca=30;41:tw=30;42:ow=34;42:st=37;44:ex=01;32'; # colors for tree, generated using dircolors on linux
export PROMPT_COMMAND="__prompt;$PROMPT_COMMAND"
export PS1='\[\e[00;36m\]\w\[\e[00;33m\]$(__gitinfo) \[\e[${__EXIT_STATUS_COLOR}\]\$ \[\e[00m\]'
export PATH="$HOME/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/sbin"
export EDITOR="subl -nw"
export HOMEBREW_EDITOR="$EDITOR"
export MAKEFLAGS="-j4"
export GPG_TTY="$(tty)"

# Python setup
export PYTHONUNBUFFERED=unbuffered

# Ignore duplicate history items (e.g. if you issue "make && ./run.sh" over and over it is coalesced into one entry)
export HISTCONTROL=ignoredups

# Java setup
export JAVA_HOME="$(/usr/libexec/java_home)"

if [[ -d /usr/local/etc/bash_completion.d ]]; then
    for F in $(ls /usr/local/etc/bash_completion.d | fgrep -v ctest); do
        source "/usr/local/etc/bash_completion.d/$F"
    done
fi

# Nix
if [ -e '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh' ]; then
  . '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh'

  # Declarative channel management; see https://checkoway.net/musings/nix/
  export NIX_PATH="$HOME/.nix-channels"
fi
# End Nix
