{ }:
let 
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchurl = pkgs.fetchurl;
    ocaml = pkgs.ocaml_4_02;
    findlib = pkgs.ocamlPackages_4_02.findlib;
in stdenv.mkDerivation {
    name = "ocaml_ppx_tools";
  
    src = fetchurl {
      url = https://github.com/alainfrisch/ppx_tools/archive/ppx_tools_0.99.2.tar.gz;
      sha256 = "98128022ea0574d769a263eb9b73be06200eec4bac9adb8dc44df289a77c4dec";
    };
  
    buildInputs = [ ocaml findlib pkgs.which];

    configPhase = true;
    buildPhase = "
      make all
    ";
    createFindlibDestdir = true;
 

}
