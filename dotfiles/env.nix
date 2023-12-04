# Packages for Nix.
#
# Usage (subject to change):
#  - copy/symlink this to ~/env.nix
#  - run `nix-sync` to install the packages defined here
#  - optionally, create a local.nix file next to this one with machine-specific
#    packages, like
#
#       $ cat local.nix
#       { nixpkgs, ... }:
#       with nixpkgs;
#       [
#         cvs
#         subversion
#       ]

let nixpkgs = import <nixpkgs> {}; in
with nixpkgs;

let

pin = (pkgs:
  runCommandLocal "pins" {} (
    ''
      mkdir -p $out/pins
      cd $out/pins
    '' + lib.concatStringsSep "\n" (builtins.map (a: "ln -sv '${pkgs.${a}}' '${a}'") (builtins.attrNames pkgs))
  )
);

in

[
  # ---- On multi-user Nix installs, these come from the root profile
  # nix
  # cacert

  # ---- Core packages
  # (python3.withPackages (p: [p.pyyaml]))
  # nix-tree

  # ---- Things I do not want GC'd (but also do not want in my env)
  # `bashInteractive` is a good choice because `nix-shell` always wants it
  (pin {
    bashInteractive = bashInteractive;
  })
]

++ lib.optionals (builtins.pathExists ./local.nix) (import ./local.nix { nixpkgs=nixpkgs; })
