{ pkgs ? import <nixpkgs> {} }:
let
  # Use the OCaml that Rocq was built with, so extracted code and the Rocq
  # plugins agree on the compiler version.
  ocamlPackages = pkgs.rocq-core.ocamlPackages;
in
pkgs.mkShell {
  nativeBuildInputs = [
    pkgs.rocq-core
    pkgs.rocqPackages.stdlib
    ocamlPackages.ocaml
    ocamlPackages.dune_3
    ocamlPackages.findlib
    pkgs.curl
  ];
}
