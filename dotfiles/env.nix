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
let nixjars = (import <nixjars> { inherit nixpkgs; }); in
let calvin = (import <calvin> { inherit nixpkgs nixjars; }); in
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

# need this so COQPATH works...
coq-with-packages = p:
  runCommandLocal
  "${coq.name}-env"
  {
    buildInputs = [bash coq coq.ocamlPackages.findlib] ++ p;
  }
  ''
    echo "Env vars:"
    echo "  PATH=$PATH"
    echo "  OCAMLPATH=$OCAMLPATH"
    echo "  COQPATH=$COQPATH"
    mkdir -p "$out/bin"
    for f in ${coq}/bin/*; do
      n="$(basename "$f")"
      echo "Wrapping $f as $out/bin/$n"
      echo '#!/usr/bin/env bash' >"$out/bin/$n"
      echo "export PATH='$PATH'" >>"$out/bin/$n"
      echo "export OCAMLPATH='$OCAMLPATH'" >>"$out/bin/$n"
      echo "export COQPATH='$COQPATH'" >>"$out/bin/$n"
      echo "exec '$f' \"\$@\"" >>"$out/bin/$n"
      chmod +x "$out/bin/$n"
    done
    patchShebangs --host "$out/bin"
  '';

in

[
  # ---- On multi-user Nix installs, these come from the root profile
  # nix
  # cacert

  # ---- Core packages
  # nix-tree
  (python3.withPackages (p: [p.mypy p.virtualenv p.z3 p.requests]))
  # z3 # apparently bin included in Python package???
  jq.bin
  # jdk17
  htop
  tree
  rlwrap
  pv
  cmake
  watch
  calvin.tlatools-complete
  calvin.tlaps
  calvin.many-smt
  calvin.ezpsl
  (coq-with-packages [calvin.caltac])

  # ---- Things I do not want GC'd (but also do not want in my env)
  # `bashInteractive` is a good choice because `nix-shell` always wants it
  (pin "bashInteractive" bashInteractive)
]

++ lib.optionals (builtins.pathExists ./local.nix) (import ./local.nix { nixpkgs=nixpkgs; nixjars=nixjars; calvin=calvin; pin=pin; })
