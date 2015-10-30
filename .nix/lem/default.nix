{ }:
let 
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    fetchgit = pkgs.fetchgit;
    ocaml = pkgs.ocaml_4_02;
    git = pkgs.git;
    findlib = pkgs.ocamlPackages_4_02.findlib;
    java = pkgs.jre; # from isabelle 
    zarith= pkgs.ocamlPackages_4_02.zarith;
    isabelle = import ./../isabelle { };
in stdenv.mkDerivation {
    name = "lem";
  
    src = fetchgit {
      url = https://bitbucket.org/Peter_Sewell/lem.git;
      rev = "2739f6a"; # good according to andrea
      sha256 = "9f3669122d45f2afdc1bc0bb46cb7b168f4f139a4d3f5a9511f1df82e8e6d788";
    };
  
    buildInputs = [ ocaml findlib git pkgs.pkgconfig pkgs.perl zarith pkgs.gmp isabelle ]; # note that lem tries to build zarith as well; java
  
    configurePhase = "true"; 	# Skip configure
    
    buildPhase = ''
      # export ISABELLE_JDK_HOME=${java}
      export LD_LIBRARY_PATH=`pwd`/ocaml-lib/dependencies/zarith:$LD_LIBRARY_PATH  # complete hack - need to find dllzarith.so
      # export ZARITH=
      echo 'let v="2739f6a"' >src/version.ml  # complete hack - the source code isn't a git repo after fetchgit
      echo "!!!"
      make

      echo "!!!"
      make ocaml-libs

      #mkdir -p $out/lem/.isabelle  # after build, need to copy these images to local .isabelle
      #export USER_HOME=$out/lem
      # make isa-libs
      #isabelle build -d isabelle-lib -b LEM # do this in the lem source dir

      # sudo chmod u+w ~/.isabelle/Isabelle2014/heaps/polyml-5.5.2_x86-linux/*
      # cp .isabelle/Isabelle2014/heaps/polyml-5.5.2_x86-linux/* ~/.isabelle/Isabelle2014/heaps/polyml-5.5.2_x86-linux/
      '';
  
    installPhase = ''
mkdir -p $out/lem && cp -R -L * $out/lem

# mkdir $out/bin
# cat > $out/bin/lem <<EOF
# #!/bin/bash
# export LEMLIB=$out/lem/library
# echo export LEMLIB=$out/lem/library
# $out/lem/lem "\$@"
# EOF
# chmod u+x $out/bin/lem

#ln -s $out/lem/lem $out/bin/lem 
''; # so we can inspect the result
    # note that we need to export LEM_LIBRARY_PATH=<absolute path to lem directory>/library before invoking lem

#    createFindlibDestdir = true;

}
