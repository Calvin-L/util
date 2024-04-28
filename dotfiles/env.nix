# Packages for Nix.
#
# Usage (subject to change):
#  - copy/symlink this to ~/env.nix
#  - run `nix-sync` to install the packages defined here
#  - optionally, create a local.nix file next to this one with machine-specific
#    packages, like
#
#       $ cat local.nix
#       { nixpkgs, pin, ... }:
#       with nixpkgs;
#       [
#         cvs
#         subversion
#         (pin "coq_8.17" coq_8_17)
#       ]

let nixpkgs = import <nixpkgs> {}; in
let nixjars = (import (builtins.fetchTarball {
  url = "https://github.com/Calvin-L/nixjars/archive/65e363fefa471d7dac0f8523f132ae0c56203936.tar.gz";
  sha256 = "00mi29a1r8jk1w3l03m11xifii0bb3vkvbjcs65vii2k6bxjnlsz";
}) { nixpkgs=nixpkgs; }); in
with nixpkgs;

let

pin = (name: p:
  runCommandLocal ("pinned-" + name) {} (
    ''
      mkdir -p $out/pins
      ln -sv '${p}' $out/'pins/${name}'
    ''
  )
);

in

[
  # ---- On multi-user Nix installs, these come from the root profile
  # nix
  # cacert

  # ---- Core packages
  # nix-tree
  (python3.withPackages (p: [p.mypy p.virtualenv p.z3]))
  # z3 # apparently bin included in Python package???
  jq.bin
  # jdk17
  htop
  tree
  rlwrap
  pv
  cmake
  watch
  nixjars.tlatools

  # ---- Things I do not want GC'd (but also do not want in my env)
  # `bashInteractive` is a good choice because `nix-shell` always wants it
  (pin "bashInteractive" bashInteractive)
]

++ lib.optionals (builtins.pathExists ./local.nix) (import ./local.nix { nixpkgs=nixpkgs; nixjars=nixjars; pin=pin; })
