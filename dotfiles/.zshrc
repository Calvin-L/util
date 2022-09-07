export PATH="$HOME/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/sbin"

export CLICOLOR=yes # colors for ls

export EDITOR="subl -nw"
export GPG_TTY="$(tty)"

export JAVA_HOME="$(/usr/libexec/java_home)"

# Ignore duplicate history items (e.g. if you issue "make && ./run.sh" over and over it is coalesced into one entry)
# See also: https://www.bartbusschots.ie/s/2019/06/17/moving-my-bashrc-to-zshrc/
setopt HIST_IGNORE_DUPS

function __gitinfo() {
    if [ -d .git ] || git rev-parse --git-dir >/dev/null 2>&1
    then
        echo -n " [$(git rev-parse --abbrev-ref HEAD 2>/dev/null)]"
    fi
}

function __prompt() {
    local EXIT="$?" # return code of last process
    if [[ "$EXIT" == "0" ]]; then
        echo -n "%F{green}"
    else
        echo -n "%F{red}"
    fi
}

function precmd() {
    local EXIT_STATUS_COLOR="$(__prompt)"
    export PS1="%F{cyan}%~%F{yellow}$(__gitinfo) %B${EXIT_STATUS_COLOR}\$%b%f "
}


# fix (nonstandard?) alt-backspace behavior
# https://unix.stackexchange.com/a/319854
function backward-kill-dir() {
    local WORDCHARS=${WORDCHARS/\/}
    zle backward-kill-word
}
zle -N backward-kill-dir
bindkey '^[^?' backward-kill-dir
