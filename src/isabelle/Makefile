LEM:=$(shell command -v ../../src_ext/lem/lem || command -v lem)
ISA_GEN_DIR:=gen_isabelle
all: ../abstract_btree.lem
	mkdir -p $(ISA_GEN_DIR)
	$(LEM) -isa -add_full_isa_lib_path -suppress_renaming -outdir $(ISA_GEN_DIR) ../abstract_btree.lem
	chmod ugo-w $(ISA_GEN_DIR)/*.thy
