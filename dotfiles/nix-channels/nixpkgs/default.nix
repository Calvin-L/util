let src = builtins.fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/7881fbfd2e3ed1dfa315fca889b2cfd94be39337.tar.gz";
  sha256 = "0na5zykmva0a6valzrrcigp6g0rzq28mi7dqxqr0s3jbn6fm24hq";
}; in
args: (import src args).appendOverlays [
  # NOTE 2024/10/17: need coq_8_19 because CoqHamer isn't 8.20 compatible, see
  #   https://github.com/lukaszcz/coqhammer/issues/184
  (self: super: {
    coq = super.coq_8_19;
    coqPackages = super.coqPackages_8_19;
  })
]
