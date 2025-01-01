let src = builtins.fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/4989a246d7a390a859852baddb1013f825435cee.tar.gz";
  sha256 = "0mdyxfmhgqnyvfv104f6gjvqva7inizv1d6jjshbc532ykj51h4h";
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
  # NOTE 2025/1/1: This is now an example overlay
  # # NOTE 2024/10/17: need coq_8_19 because CoqHamer isn't 8.20 compatible, see
  # #   https://github.com/lukaszcz/coqhammer/issues/184
  # (self: super: {
  #   coq = super.coq_8_19;
  #   coqPackages = super.coqPackages_8_19;
  # })
]
