
export PATH='/Users/loncaric/.opam/default/bin:/Users/loncaric/bin:/Users/loncaric/.cabal/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/opt/X11/bin:/usr/local/sbin'

export CLICOLOR=yes # colors for ls

export EDITOR="subl -nw"

export JAVA_HOME="$(/usr/libexec/java_home)"

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
