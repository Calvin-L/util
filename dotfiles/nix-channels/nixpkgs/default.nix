let src = builtins.fetchTarball {
  # nixpkgs-25.11-darwin, 2025/12/11
  url = "https://github.com/NixOS/nixpkgs/archive/62cac6c5d5b70601ff3da3e6573cb2d461f86953.tar.gz";
  sha256 = "1w4j7f9hf0ks10066996ccpan9hla09caq313in5k3mwld0wk70z";
}; in

# NOTE 2024/11/19: Under normal circumstances, the Nix expressions
#
#     x: 1
#     {...}@x: 1
#
# are essentially equivalent, except that the second will fail when given a
# non-set argument.  So it looks a little silly that we need to use {...}@args
# here.  Couldn't it be simplified?
#
# However, there are cases where Nix tries to be a little too smart.  In
# particular, it will sometimes "auto-call" functions, such as when an
# argument to nix-build happens to evaluate to a function.  See
#  - https://github.com/NixOS/nix/blob/32becc87fef7340600df75ffed6e7c6bc56aa827/src/nix-build/nix-build.cc#L400
#  - https://github.com/NixOS/nix/blob/32becc87fef7340600df75ffed6e7c6bc56aa827/src/libexpr/attr-path.cc#L58
#  - https://github.com/NixOS/nix/blob/32becc87fef7340600df75ffed6e7c6bc56aa827/src/libexpr/eval.cc#L1761
#
# For auto-call to work propertly with `--arg name value` command-line
# arguments, Nix inspects whether the first argument is a set pattern with an
# ellipsis.  So to summarize,
#
# If we just write `args: ...`, then `nix-build '<nixpkgs>' -A tree` will fail
# because it won't supply an argument for `args`.
#
# But if we write `{...}@args: ...`, then the same command will supply `{}` for
# the argument, and we get what we expect.  Wild!

{...}@args: (import src args).appendOverlays [
  # NOTE 2025/6/4: This is once again relevant; coq is becoming rocq and CoqHammer isn't compatible
  # NOTE 2025/1/1: This is now an example overlay
  # NOTE 2024/10/17: need coq_8_19 because CoqHamer isn't 8.20 compatible, see
  #   https://github.com/lukaszcz/coqhammer/issues/184
  (self: super: {
    coq = super.coq_8_20;
    coqPackages = super.coqPackages_8_20;
  })

  # fix an issue where emscripten can't find babel
  #  > emcc: error: babel was not found! Please run "npm install" in Emscripten root directory to set up npm dependencies
  # https://github.com/emscripten-core/emscripten/blob/58f77a5235dbb91894de4149cd8971b992923c7c/tools/shared.py#L271
  (self: super: {
    emscripten = super.emscripten.overrideAttrs (prev: {
      prePatch = ''
        substituteInPlace tools/shared.py --replace-fail \
          '{name} was not found!' \
          '{cmd} was not found!'
      '';
      postInstall = ''
        mkdir -p $out/share/emscripten/node_modules/.bin
        ln -s "$out/share/emscripten/node_modules/@babel/cli/bin/babel.js" "$out/share/emscripten/node_modules/.bin/babel"
      '';
    });
  })

  # https://github.com/NixOS/nixpkgs/pull/469976
  (self: super: {
    cvs = super.cvs.overrideAttrs (prev: {
      patches = [
        "${src}/pkgs/by-name/cv/cvs/getcwd-chroot.patch"
        (self.fetchurl {
          url = "http://deb.debian.org/debian/pool/main/c/cvs/cvs_1.12.13+real-30.diff.gz";
          sha256 = "085124619dfdcd3e53c726e049235791b67dcb9f71619f1e27c5f1cbdef0063e";
        })
      ];
    });
  })

]
