{ }:
let
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchurl = pkgs.fetchurl;
    ocaml = pkgs.ocaml_4_02;
    findlib = pkgs.ocamlPackages_4_02.findlib;
    ppx_tools =  import ../ppx_tools {};
in stdenv.mkDerivation {
    name = "ocaml_bisect_ppx";

    builder = builtins.toFile "builder.sh" "
            source $stdenv/setup

            tar xvfz $src
            cd ./bisect_ppx*
            chmod +x ./configure
            ./configure
            make all
            make install
    ";


    src = fetchurl {
      url = https://github.com/rleonid/bisect_ppx/archive/0.2.3.tar.gz;
      sha256 = "a69639041317f82e23e4f1def396bdfe7b99cc8afb93d5e45c4ea8189d5f03b5";
    };

    buildInputs = [ ocaml findlib pkgs.which ppx_tools];

    configFlags = "-ocaml-prefix $(ocaml) -ocamlfind $(findlib)";
    dontAddPrefix = true;
    createFindlibDestdir = true;

}