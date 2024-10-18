let src = builtins.fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/0aeab749216e4c073cece5d34bc01b79e717c3e0.tar.gz";
  sha256 = "0fnw58pxb9l2iskrcr7d03vkbzf19qqb23r7w0ds2a62wclzxc6h";
}; in
args: (import src args).appendOverlays [
  # NOTE 2024/10/17: need coq_8_19 because CoqHamer isn't 8.20 compatible, see
  #   https://github.com/lukaszcz/coqhammer/issues/184
  (self: super: {
    coq = super.coq_8_19;
    coqPackages = super.coqPackages_8_19;
  })
]
