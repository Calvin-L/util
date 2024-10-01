export PATH="$HOME/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/sbin"

export CLICOLOR=yes # colors for ls

# Set $EDITOR to a wrapper script.
#   - the wrapper script can make decisions about which editor to use based on
#     the environment
#   - the wrapper script can pass flags to the editor (some tools don't like
#     when $EDITOR contains spaces---and in truth, it's ambiguous whether the
#     spaces are part of the name of the executable or if they separate flags)
#   - you can change your editor by modifying the wrapper script without
#     restarting your shell
if [[ -x "$HOME/bin/editor" ]]; then
    export EDITOR="$HOME/bin/editor"
fi

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

# brew setup
eval "$(/opt/homebrew/bin/brew shellenv)"

# Nix
if [ -e '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh' ]; then
  . '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh'

  # Declarative channel management; see https://checkoway.net/musings/nix/
  export NIX_PATH="$HOME/.nix-channels"
fi
# End Nix
