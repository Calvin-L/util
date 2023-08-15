# Common stuff
#
# List all Nix packages
#   nix-env -qaP
#
# Neat nix-build flags
#   -K                            keep the build folder on failure
#   --option substitute false     don't use the remote binary cache (for offline builds)
#
# See:
#   https://musteresel.github.io/posts/2018/05/nix-disable-binary-cache.html

# -----------------------------------------------------------------------------
# Nix shebangs:
#
#   #!/usr/bin/env nix-shell
#   #! nix-shell -i <interpreter> -p <pkg1> <pkg2> ...
#
#   e.g.
#
#   ... -p "haskellPackages.ghcWithPackages (pkgs: [pkgs.data-ordlist])"
#
#   (single quotes don't work for some reason)
#
#   http://chriswarbo.net/projects/nixos/nix_shell_shebangs.html

# -----------------------------------------------------------------------------
# Build file for the Nix package manager.
# (Save this as default.nix in your project's directory.)
# You can put yourself in a shell with everything necessary to build the
# project by running
#
#     nix-shell --pure [path-to-this-file.nix]
#
# or you can build the project directly using
#
#     nix-build [path-to-this-file.nix]
#
# You do not need to specify the path to this file if your shell is in the
# directory containing this file.

with import <nixpkgs> {};

stdenv.mkDerivation rec {
  name = "vrepl";
  buildInputs = [
    sqlite
    openssl
  ];
  src = ./.;
  enableParallelBuilding = true;
  doCheck = false;
  installPhase = ''
    make install DESTDIR="$out"
  '';
}

# -----------------------------------------------------------------------------
# Sometimes you will need to create build scripts for other projects so that
# your project will compile.  I like to put these in a "./nix/" folder in my
# project.  Each file in the ./nix/ folder should look like:

{stdenv, fetchurl, gnumake}:

stdenv.mkDerivation rec {
  # ...
}

# And your parent project should have lines like

with import <nixpkgs> {};

let smake = callPackage ./nix/smake.nix {}; in
let cdrtools = callPackage ./nix/cdrtools.nix {
  smake=smake;
  Carbon=darwin.apple_sdk.frameworks.Carbon;
  IOKit=darwin.apple_sdk.frameworks.IOKit;
  CoreFoundation=darwin.apple_sdk.frameworks.CoreFoundation;
}; in

stdenv.mkDerivation rec {
  # ...
}

# -----------------------------------------------------------------------------
# ~/.config/nixpkgs/config.nix
# This file gives you an enormous amount of power over the nixpkgs repository.
# In this example I disabled the libuv tests.  The change replaces libuv in the
# entire build tree, so everything that depends on libuv gets the updated
# version!

{

  # allowUnsupportedSystem = true;

  packageOverrides = pkgs: rec {
    # Disable libuv tests because they make actual network calls and can fail
    # spuriously if your network is different from the developers' setups.
    libuv = pkgs.libuv.overrideAttrs (oldAttrs: { doCheck=false; });
  };

}

# -----------------------------------------------------------------------------
# Get the list of attributes of a set

lib.attrNames python3Packages
