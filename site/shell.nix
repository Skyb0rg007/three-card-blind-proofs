# Tools for building and testing the play site:
#   nix-shell site/shell.nix --run 'site/build.sh'
{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = [
    pkgs.cargo
    pkgs.rustc   # nixpkgs' rustc ships the wasm32-unknown-unknown std
    pkgs.lld     # the wasm linker
    pkgs.nodejs  # test/walk-check.mjs
  ];
}
