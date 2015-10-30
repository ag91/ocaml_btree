{ }:
let
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchgit = pkgs.fetchgit;
    perl = pkgs.perl;
    isabelle = import ./isabelle { };
    ocaml = pkgs.ocaml_4_02;
    findlib = pkgs.ocamlPackages_4_02.findlib;
    bisect = import ./bisect { };
    lem = import ./lem { };
in stdenv.mkDerivation {
    name = "lemenv";

    lem = lem;
    isabelle = isabelle;

    gmpLibPath = stdenv.lib.makeLibraryPath [ pkgs.gmp5 ];
    src = lem;
    buildInputs = [ perl isabelle lem ocaml findlib bisect];

    configurePhase = "true"; 	# Skip configure

    buildPhase = ''
      echo lemenv execute the following using eval ... from nix-shell
      cd ${lem}/lem
      isabelle build -d isabelle-lib -b LEM

#      export ISABELLE_PATH=$isabelle/Isabelle2014/heaps
#      export USER_HOME=$out
#      echo USER_HOME: $USER_HOME

      '';

# eval "${!curPhase:-$curPhase}" from nix-shell

    installPhase = "true"; # don't want to install


shellHook = ''
    export LD_LIBRARY_PATH=$gmpLibPath #this permits the dynamic binding of libgmp.so.10.so
    export LEMPATH=${lem}/lem
    export PATH=$PATH:${lem}/lem
    export LEMLIB=${lem}/lem/library
    curPhase=buildPhase

    # export out=/tmp/isa
    #export ISABELLE_LOGIC=LEM
  '';

}
