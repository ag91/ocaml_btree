theory "TerminationLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"

begin


  termination from_to_h by lexicographic_order

  termination replace_helper by lexicographic_order

  termination ins_helper by lexicographic_order

  termination take2 by lexicographic_order

  termination del by lexicographic_order

  termination norm_entries_list_h by lexicographic_order

  termination norm_wf_btree by lexicographic_order

  termination norm_find_h by lexicographic_order

(*  termination insert_loop by lexicographic_order *)

(*  termination delete_loop by lexicographic_order *)



end
