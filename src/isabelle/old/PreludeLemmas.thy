theory "PreludeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"
	 "TerminationLemmas"
begin


lemma if_find_indices_returns_index_then_the_element_exists [simp]:
"\<forall> p n ns. find_indices p list = n # ns \<longrightarrow>
       (\<exists> e . (index list n = Some e) \<and> e \<in> set list \<and> (p e = p (list ! n)) \<and> p e \<and>  p (list ! n)) \<and> n < length list "
apply (induct list)
  apply auto
  
  apply (case_tac "p a")
    apply auto
done

lemma find_h_is_correct_helper [simp]:
"\<forall> k env n ns .find_indices (\<lambda>x. k = entry_to_key env x) list = n # ns \<longrightarrow>
       k = entry_to_key env (list ! n)"
apply (induct list)
  apply auto
done

lemma find_index_None_iff:
"(find_index p l = None) = ( (l = []) \<or> (\<forall> x \<in> set l. \<not> (p x)) )"
by (case_tac l,simp+)

lemma find_index_Some_iff:
"(find_index p l = Some i) = ( (l \<noteq> []) \<and> i < length l \<and> (p (l!i)) \<and> (\<forall> n < i. \<not> (p (l!n))))"
apply auto
done
  


lemma first_returns_something_only_if [simp]:
"\<forall> p i. first xs p = Some i \<longrightarrow> \<not> (xs = []) \<and> \<not>(i = 0) \<and> (i < Suc (length xs))"
apply auto
apply (simp add:first_def find_index_def)

apply (simp add:first_def)
apply (case_tac "find_index p xs")
apply auto

apply (simp add:first_def)
apply (case_tac "find_index p xs")
  apply auto
done

lemma first_None_iff:
"(first xs p = None) = ((xs = []) \<or> (\<forall> x \<in> set xs. \<not> p x))"
apply rule
 apply (simp add:first_def)
 apply (case_tac "find_index p xs",simp+)

 apply (erule disjE)
 apply (simp add:first_def find_index_def)

 apply (induct xs)
  apply (simp add:first_def find_index_def)

  apply (simp add:first_def find_index_def)
   apply (case_tac "find_indices p xs")
   apply simp+
done 

lemma first_Some_iff:
"(first xs p = Some n) = ((xs \<noteq> []) \<and> (n - 1 < length xs) \<and> (p (xs ! n - 1) \<and> (\<forall>j< n - 1. \<not> p (xs ! j))))"
apply (simp add:first_def)
apply rule+
 (* xs = []*)
 apply (simp add:find_index_def)

 (* (case find_index p xs of None \<Rightarrow> None | Some i \<Rightarrow> Some (i + 1)) = Some n \<Longrightarrow> n < length xs \<and> p (xs ! n - 1) \<and> (\<forall>j<n - Suc 0. \<not> p (xs ! j)) *)
 apply (case_tac "find_index p xs")
  apply simp

  apply (simp add:find_index_Some_iff)
  apply (rename_tac "nth_p_true")
  apply (erule conjE)+
  apply (drule_tac t="n" in sym)
  apply simp
  apply (thin_tac "n = Suc nth_p_true")
  (* this should be solved *)
  defer
  
  apply (erule conjE)+
  
sorry


lemma nth_from_1_is_like_nth [simp]:
"\<forall> list n. (nth_from_1 list 0 = None) \<and> (nth_from_1 list (Suc n) = index list n) "
apply (auto simp add:nth_from_1_def)
done

lemma find_trans_of_None_is_None [simp]:
"\<forall> env p s . find_trans env (None,p,s) = (None,p,s)"
apply (simp add:find_trans_def)
done

lemma find_trans_does_not_alter_store:
"\<forall> env a q s b' q' s'. (find_trans env (a,q,s)) = (b',q',s') \<longrightarrow> s = s'"
apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac "a")
  (* a = None *)
  apply auto

  (* a = Some aa *)
  apply (case_tac "aa")
    (*aa = Find *)
    apply auto
    apply (case_tac "s q")
      (* s q = None *)
      apply auto

      (* s q = Some a *)
      apply (case_tac a)
        apply auto
        apply (case_tac inode)
        apply auto
        apply (case_tac " nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto
       
        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
          apply auto
done

lemma find_trans_result_returns_same_elemen_of_store:
"\<forall> env c p p' s0 s0' r n. 
find_trans env (Some(c),p,s0) = (Some(F_Ret(p',n)),p',s0') \<longrightarrow>
(let page = s0 p in
 let page' = s0' p' in
page = page')
"
apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac c)
  (* c = Find *)
  apply auto
  apply (case_tac "s0 p")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
        apply auto
done        

lemma find_trans_result_returns_f_ret_only_if [simp]:
"\<forall> env c p s0 r n es k. 
find_trans env (Some(c),p,s0) = (Some(F_Ret(p,n)),p,s0) \<longrightarrow>
(case c of
  Find k \<Rightarrow>
( case s0 p of
  Some(LNode(L(es))) \<Rightarrow>
    (case  (first es (\<lambda> x . k = ((entry_to_key   env) x))) of
            Some i => i = n
          | _ => False)
  | _ \<Rightarrow> False)
| _ \<Rightarrow> False)"

apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac c)
  (* c = Find *)
  apply auto
  apply (case_tac "s0 p")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
        apply auto
done

declare norm_find_h.simps [simp del] 

lemma norm_find_h_simps: "
\<forall> env c .
norm_find_h env c (Suc h) = ( (
        (case  c of
          ((Some(F_Ret(p,n)),_,s0)) => (None, s0)
        | (_,_,s0) =>
           (let c' = (find_trans env c) in
           norm_find_h env c' h)
        )))
"
  apply auto
  apply (case_tac h)
    apply (simp add:norm_find_h.simps)
    apply (case_tac a)
      apply auto

      apply (case_tac ab)
        apply auto

    apply (case_tac a)
      apply (simp add:norm_find_h.simps)
    apply auto
    apply (case_tac ab)
      apply auto
      apply (simp_all add:Let_def norm_find_h.simps)
done

lemma find_h_simps:
"
\<forall> env c .
find_h env c (Suc (Suc h)) = ( (
        (case  c of
          ((Some(F_Ret(p,n)),_,s0)) => (None, s0)
        | (_,_,s0) =>
           (let c' = (find_trans env c) in
           norm_find_h env c' h)
        )))
"
apply (simp add:find_h_def norm_find_h_simps Let_def)
done

lemma norm_find_h_simps2:
"\<forall> env k ra s va p i. (find_h env (Some (Find k), ra, s) (Suc (Suc va)) = (Some (p, i), s)) = 
(find_h env (find_trans env (Some (Find k), ra, s)) (Suc va) = (Some (p, i), s))"
apply(simp_all add:find_h_def norm_find_h_simps Let_def)
done

lemma norm_find_h_None_is_None [simp]:
"\<forall> env p s . norm_find_h env (None,p,s) h = (None,s)"
apply (induct h)
  apply (simp add:norm_find_h.simps)

  apply (simp add: norm_find_h_simps)
done

lemma find_h_None_is_None [simp]:
"\<forall> env p s . find_h env (None,p,s) h = (None,s)"
apply (simp add:find_h_def)
apply (case_tac h)
  apply auto
done

lemma norm_find_h_does_not_alter_store:
"\<forall> env c0 p0 s0 opt s1. (norm_find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply auto
apply (induct h)
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac c0)
    (* c0 = None *)
    apply auto

    (* c0 = Some a *)
    apply (case_tac a)
      (* a = Find k *)
      apply (case_tac "s0 p0")
        apply auto

        apply (case_tac aa)
          apply (case_tac inode)
          apply auto
          apply (case_tac "first a (key_lt env key)")
            apply (simp add:nth_from_1_def)
            apply (case_tac b)
              apply auto
              
              apply (case_tac "nth_from_1 b aa")
              apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
            apply auto

      (* a = F_Ret *)
      apply (simp add:norm_find_h_simps find_trans_def)
      apply (case_tac c0)
        apply auto

        apply (case_tac a)
          apply auto
          
          apply (simp add:find_trans_def)
          apply (case_tac "s0 p0")
            apply auto

            apply (case_tac a)
              apply (case_tac inode)
              apply auto
              apply (case_tac "first aa (key_lt env key)")
              apply (simp add:nth_from_1_def)
              apply (case_tac b)
                apply auto
          
                apply (case_tac "nth_from_1 b a")
                apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
            apply auto                
done

lemma find_h_does_not_alter_store:
"\<forall> env c0 p0 s0 opt s1. (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply (simp add:find_h_def)
  apply (case_tac h)
    apply (simp_all add:norm_find_h_does_not_alter_store)
done

lemma find_h_does_not_alter_store_if_wf_btree:
"\<forall> env c0 p0 s0 opt s1.
let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
 let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> set list | None \<Rightarrow> {}) in
wf_btree env s (r, all_entries,n) h \<longrightarrow> (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply (simp add:find_h_does_not_alter_store)
done

lemma norm_find_h_always_return_page_id_in_store:
"\<forall> env k r s0 s i p. norm_find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
apply (simp add:norm_find_h_does_not_alter_store)
apply auto
apply (induct h)
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac "s0 r")
      apply auto

      apply (case_tac a)
        apply (case_tac inode)
        apply auto
        apply (case_tac "nth_from_1 b (case first aa (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto

        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
          apply auto

  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac "s0 r")
      apply auto

      apply (case_tac a)
        apply (case_tac inode)
        apply auto
        apply (case_tac "nth_from_1 b (case first aa (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto

        apply (case_tac lnode)
        apply auto
        apply (simp add:norm_find_h.simps)
          apply (case_tac h)
            apply auto
            apply (simp add:find_trans_def)
              apply (case_tac "s0 r")
                apply auto

                apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
                  apply auto
                  
        apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
          apply auto
done

lemma find_h_always_return_page_id_in_store:
"\<forall> env k r s0 s i p. find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
apply (simp add:find_h_def)
apply (case_tac h)
  apply (simp_all add:norm_find_h_always_return_page_id_in_store)
done

lemma norm_find_h_returns_some_only_if:
"\<forall> env c r s p i k. norm_find_h env (c,r,s) h = (Some(p,i),s) \<longrightarrow>
(
  (h = 0 \<and> (find_trans env (c,r,s) = (Some (F_Ret(p,i)),p,s))) 
\<or>
  (h > 0 \<and> (\<exists> c'. c' = find_trans env (c,r,s) \<and> norm_find_h env c' (h-(1::nat)) = (Some(p,i),s)) )
)
"
apply (case_tac h)
  apply auto
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac c)
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac "s r")
        apply auto

        apply (case_tac a)
          apply (case_tac inode)
          apply auto
          apply (case_tac "first aa (key_lt env key)")
            apply (case_tac b)
              apply auto

              apply (case_tac "nth_from_1 b a")
              apply auto

         apply (case_tac lnode)
          apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
            apply auto

  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac c)
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac "s r")
        apply (simp_all add:find_trans_def)
done



declare norm_entries_list_h.simps [simp del]
lemma norm_entries_list_h_simps:
"\<forall> s0 r. norm_entries_list_h s0 r (Suc h) =
(case   s0 r of
          Some node \<Rightarrow> (
          (case  node of
            LNode _ => None
          | INode(I(_,qs)) => (
            (let list_of_lists_of_entries = (List.map (\<lambda> q .  norm_entries_list_h s0 q h) qs) in
            if ((\<forall> x \<in> (set list_of_lists_of_entries).  \<not> (x = None))) then
              Some(List.concat (List.map the list_of_lists_of_entries))
            else
              None)
          )))
          | _ \<Rightarrow> None)
"
apply auto
apply (simp add:norm_entries_list_h.simps)
apply (case_tac "s0 r")
  apply auto

  apply (case_tac a)
    apply (case_tac inode)
    apply auto
done

lemma norm_entries_list_returns_None_if [simp]:
"\<forall> ds qs s r. norm_entries_list_h s r h = None \<longrightarrow>
(s r = None)
\<or>
(h = 0 \<and> (case s r of Some(LNode(_)) \<Rightarrow> False | _ \<Rightarrow> True))
\<or>
((h > 0) \<and> (case s r of Some(INode(I(_,qs))) \<Rightarrow> (\<exists> q \<in> set qs. (norm_entries_list_h s q (h-(1::nat)) = None)) | _ \<Rightarrow> True))
"
apply (case_tac h)
  apply (simp add:norm_entries_list_h.simps)
  apply auto
  apply (case_tac "s r")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac lnode)
      apply auto

  apply (case_tac "s r")
    apply auto

    apply (case_tac a)
      apply (case_tac inode)
      apply auto

      apply (simp add:norm_entries_list_h_simps)
done

lemma map_and_first_are_equal:
"\<forall> k env.
map_of (map (\<lambda>e. (entry_to_key env e, e)) list) k =
(case first list (\<lambda>x. k = entry_to_key env x) of None \<Rightarrow> None | Some i \<Rightarrow> nth_from_1 list i)"
apply auto
apply (induct list)
  (* list = [] *)
  apply (simp add:first_def find_index_def)

  (* list = a#list *)
  apply (simp add:first_def find_index_def)  
  apply (case_tac "map Suc (find_indices (\<lambda>x. k = entry_to_key env x) list)")
   apply auto
done

lemma nth_first_is_list_find_simp:
"\<forall> p. List.find p list = nth_from_1 list (case first list p of None \<Rightarrow> 0 | Some i \<Rightarrow> i) "
apply (induct list)
  apply (simp add:nth_from_1_def first_def find_index_def)

  apply auto
  apply (simp add:first_def find_index_def)

  apply (simp add:first_def find_index_def)
  apply (case_tac "find_indices p list ")
    apply auto
done

lemma map_and_listfind_equal:
"\<forall> k env.
map_of (map (\<lambda>e. (entry_to_key env e, e)) list) k = List.find (\<lambda> x . k = entry_to_key env x) list"
apply auto
apply (induct list)
  apply auto
done

lemma listfind_append :
"\<forall> P. List.find P (list @ list') = (let res = List.find P list in if res = None then List.find P list' else res)"
apply auto
apply (case_tac "List.find P list")
  apply auto
  apply (induct list)
    apply auto

  apply (induct list)
    apply auto
done

lemma listfind_append_list_with_concat :
"\<forall> k P e list. None = List.find P list \<longrightarrow> List.find P (List.concat list') = List.find P ((List.concat list') @ list)"
apply clarsimp
apply (case_tac " List.find P (List.concat list')")
  apply (simp add:listfind_append)+
done

lemma listfind_and_concat1:
"\<forall> P e list. Some e = List.find P list \<longrightarrow> \<not> None = List.find P ((List.concat list') @ list)"
apply clarsimp
  apply (case_tac "List.find P (List.concat list')")
      apply (simp add:listfind_append)+
done

lemma listfind_concat_a_list_exists [simp]:
"\<forall> P e. Some e = List.find P (List.concat list) \<longrightarrow> (\<exists> list' \<in> set list . Some e  = List.find P list' )"
apply clarsimp
apply (induct list)
  apply (clarsimp)

  apply (case_tac "List.find P a")
    apply (simp add:listfind_append)+
done

lemma nth_from_1_Some_iff [simp]:
"(nth_from_1 xs x = Some e) \<longleftrightarrow> (x\<noteq>0 \<and> (x \<le> length xs) \<and> (e \<in> set xs) \<and> (nth xs (x-(1::nat)) = e))"
apply (simp add:nth_from_1_def)
apply rule
 apply (case_tac x)
  apply simp+

 apply (case_tac x)
  apply simp

  apply clarsimp
done

lemma nth_from_1_None_iff [simp]: 
"nth_from_1 xs x = None \<longleftrightarrow> (x = 0) \<or> (x > length xs) \<or> (xs = [])"
apply (simp add:nth_from_1_def)
apply rule
 apply (case_tac x)
  apply simp+

 apply (case_tac x)
  apply clarsimp+

  apply (case_tac xs)
   apply clarsimp+
done


lemma sorry_fixme: "P"
  sorry

lemma listfind_returns_the_first_element_satisfying_P [simp]: 
"(List.find P xs = None) \<Longrightarrow> List.find P y \<noteq> None \<Longrightarrow> List.find P y = List.find P (List.concat (xs#(y#ys)))"
apply simp
apply (case_tac "List.find P y")
 apply (simp add:listfind_append)+
done

lemma listfind_returns_the_first_element_satisfying_P2 [simp]: 
"(List.find P xs = None) \<Longrightarrow> P y \<Longrightarrow> List.find P (y#ys) = (index (xs@(y#ys)) (length xs))"
apply auto
done


lemma norm_wf_btree_h0_is_true_if:
"\<forall> env s r all_entries n. 
norm_wf_btree env s (r, all_entries,n) 0 \<longrightarrow>
(case s r of 
  Some(LNode (L es)) \<Rightarrow>
    (n = length es)
    \<and>
    (n \<le> maxN env)
    \<and>
    (set es =  all_entries)
    \<and>
    (sorted_by (entry_lt env) es)
  | _ \<Rightarrow> False)
"
apply auto
apply (case_tac "s r")
 apply simp

 apply (case_tac a)
 apply simp

 apply (case_tac lnode)
 apply (simp add:Let_def)
 apply (case_tac "length list = n \<and> length list \<le> maxN env")
  apply simp
  apply (case_tac "all_entries = set list")
   apply simp_all
done

lemma norm_wf_btree_requires_qs_length_to_be_at_least_2_if_inode_exist:
"\<forall> env k c s r ds qs. 
s r = Some(INode(I(ds,qs))) \<longrightarrow>
(let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
 let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> set list | None \<Rightarrow> {}) in
norm_wf_btree env s (r, all_entries,n) h \<longrightarrow> (Suc(length ds) = length qs) \<and> (length ds > 0) \<and> (2 \<le> length qs))"
apply (case_tac h)
  apply simp
  
  apply auto
  apply (case_tac "Suc (length ds) = length qs")
    apply auto

apply (case_tac ds)
  apply auto
done

lemma norm_wf_btree_length_qs: 
"norm_wf_btree env s (r, all_entries,n) h \<longrightarrow>
(h = 0 \<and> (case s r of Some (LNode (L (qs))) \<Rightarrow> (length qs \<ge> 0) | _ \<Rightarrow> False))
\<or>
(h > 0 \<and> (case s r of Some (INode (I (ds,qs))) \<Rightarrow> ((length qs) > 1) \<and> length ds > 0 | _ \<Rightarrow> False))
"
apply (case_tac h)
apply clarsimp
 apply (case_tac "s r")
  apply simp+

  apply (case_tac a)
   apply simp+

   apply (case_tac lnode)
    apply simp

 (*h = Suc h' *)
 apply clarsimp
 apply (case_tac "s r")
  apply simp+

  apply (case_tac a)
   apply simp
   defer
   (* get rid of a = LNode*)
   apply simp+

   apply (case_tac inode)
   apply clarsimp
   apply (case_tac "Suc (length aa) \<noteq> length b")
    (* Suc (length aa) ~= length b*)
    apply clarsimp
     apply (case_tac "n \<noteq> length b")
      apply simp

      apply clarsimp
      apply (case_tac "aa = []")
       apply simp

       apply simp
       apply (case_tac "length aa")
        apply simp+
done

lemma from_to_empty_iff [simp]:
"from_to a b = {} \<longleftrightarrow> (a > b)"
apply (case_tac "b - a")
 apply (simp add:from_to_def)+
done

lemma set_suc_equal_union_suc:
"\<forall> i t . i \<le> Suc t \<longrightarrow> {n. i \<le> n \<and> n \<le> (Suc t)} =  {n. i \<le> n \<and> n \<le> t} \<union> {Suc t}"
apply force
done

lemma from_to_set_h:
"(from_to a (a+b)) = {n. a \<le> n \<and> n \<le> (a+b)}  "
apply(induct b)
apply(simp add:from_to_def)
apply(force)

apply(simp)
apply(simp add: from_to_def)
apply(force)
done

lemma from_to_set:
"(from_to a c) = {n. a \<le> n \<and> n \<le> c}  "
apply (case_tac "c < a")
 apply (simp add:from_to_def)

 apply (case_tac "\<exists>b. c = a+b")
  apply clarify
  apply (simp add:from_to_set_h)

  apply arith
done


lemma forall_elements_equal_forall_from_to_nth:
"(\<forall> x \<in> set l. P x) = (\<forall> j \<in> from_to (Suc 0) (length l) . P(nth l (j - 1)))"
apply (simp add:from_to_set)
apply (induct l)
 apply clarsimp+

 apply auto
 apply (case_tac "j=Suc 0")
  apply simp+
done

lemma forall_elements_equal_forall_from_to_nth2:
"(\<forall> j \<in> from_to (Suc 0) (length l) . P(nth l (j - 1))) = (\<forall> x \<in> set l. P x)" 
apply (simp add:forall_elements_equal_forall_from_to_nth)
done

lemma nth_from1_bis [simp]:
"b \<noteq> [] \<longrightarrow> (\<forall> j \<in> {n. Suc 0 \<le> n \<and> n \<le> length b}. nth_from_1 b j = Some (b!(j-(1::nat))))"
apply clarsimp
done

lemma resolve_ss_wf_btree:
"(
s r = Some (INode (I (a # list, qs))) \<longrightarrow> union_clause all_entries s r (Suc h) \<longrightarrow> (\<forall>i. Suc 0 \<le> i \<and> i \<le> length qs \<longrightarrow>
  (ss (Some ((qs) ! (i - Suc 0))) s h = Some (the ( (case norm_entries_list_h s ((qs) ! (i - Suc 0)) h of None \<Rightarrow> None
                   | Some list \<Rightarrow> Some (set list)))))))"
   apply (simp add:union_clause_def ss.simps)
   apply clarsimp
   apply (case_tac "norm_entries_list_h s r (Suc h) ")
   apply simp

   apply (case_tac " norm_entries_list_h s ((qs) ! (i - Suc 0)) h \<noteq> None")
    apply force

    apply (simp add:norm_entries_list_h_simps)
    apply (case_tac "\<not>((\<forall>x\<in>set qs. \<exists>y. norm_entries_list_h s x h = Some y))")
     apply clarsimp

     apply clarsimp
     (* this is true because list ! index = \<forall> x in list*)
     apply (simp add:forall_elements_equal_forall_from_to_nth from_to_set)
     apply force
done

lemma resolve_mm_wf_btree:
"cond_mj env (length qs) qs s \<longrightarrow> (\<forall>i. Suc 0 \<le> i \<and> i \<le> (length qs) \<longrightarrow> mm (Some ((qs) ! (i - Suc 0))) s = Some  (the(case s ((qs) ! (i - Suc 0)) of None \<Rightarrow> None | Some (INode (I (x, qs))) \<Rightarrow> Some (length qs)
                 | Some (LNode (L es)) \<Rightarrow> Some (length es))))"
apply (case_tac "qs = []")
 apply simp
   
 apply (simp add:cond_mj_def from_to_set qq_def)
 apply clarsimp
 apply (case_tac " mm (Some (qs ! (i - Suc 0))) s")
    apply force

    apply (simp add:mm.simps get_m_def)
done

lemma norm_wf_btree_suc_n_then_norm_wf_btree_n:
"s r = Some (INode(I(ds,qs))) \<Longrightarrow>
norm_wf_btree env s (r, all_entries,n) (Suc h) \<Longrightarrow>
  (\<forall> i \<in> from_to (Suc 0) (length qs). norm_wf_btree env s (qs ! (i - Suc 0), the (ss (Some (qs ! (i - Suc 0))) s h), the (mm (Some (qs ! (i - Suc 0))) s)) h)"
apply simp
apply (case_tac "n \<noteq> length qs")
 (* n \<noteq> length qs *)
 apply simp

 (* n = length qs *)
 apply simp
 apply (case_tac "Suc (length ds) \<noteq> length qs")
  (*Suc (length ds) \<noteq> length qs*)
  apply simp

  (* Suc (length ds) = length qs *)
  apply simp
  apply (case_tac ds)
   apply simp

   apply (simp add:Let_def from_to_set qq_def ss.simps)
   apply (case_tac "qs = []")
   apply simp+     
   
   apply(rule)+
   apply (erule conjE)+
   apply (simp add:resolve_ss_wf_btree resolve_mm_wf_btree)
done

lemma key_lt_not:
"wf_env env \<Longrightarrow>
  (\<not> (key_lt env k k1)) = key_lte env k1 k
 "
apply (simp add:key_lt_def wf_env_def relFromPred_def isTotalOrder_def isPartialOrder_def trans_def antisym_def total_on_def)
apply (rule)
 apply (erule conjE)+
 apply (thin_tac "Suc (maxN env) div 2 < minN env")
 apply (thin_tac "Suc 0 < maxN env")
 apply (case_tac "key_lte env k k1")
  apply simp

  apply clarsimp
  apply (metis iso_tuple_UNIV_I mem_Collect_eq old.prod.case refl_on_def)

 apply (simp add:key_lt_def)
done

lemma key_lte_Cons:
"wf_env env \<Longrightarrow>
  key_lte env k1 k = (\<not> (key_lt env k k1)) "
apply (simp add:key_lt_not)
done

lemma key_lt_transitivity:
"wf_env env \<Longrightarrow>
  key_lt env k k1 \<Longrightarrow>
  key_lt env k1 k2 \<Longrightarrow>
  key_lt env k k2"
apply (simp add:key_lt_def wf_env_def relFromPred_def isTotalOrder_def isPartialOrder_def trans_def antisym_def total_on_def)
apply blast
done

lemma transitivity_with_key_lte:
 "wf_env env \<Longrightarrow> key_lte env a b \<Longrightarrow> key_lt env b c \<Longrightarrow> key_lt env a c"
apply (simp add:wf_env_def relFromPred_def isTotalOrder_def isPartialOrder_def trans_def antisym_def total_on_def key_lt_def)
apply blast
done

lemma transitivity_with_key_lte_forall : 
"wf_env env \<Longrightarrow> l \<noteq> [] \<Longrightarrow> \<forall> s \<in> set l. key_lte env a s \<Longrightarrow> \<forall> s \<in> set l. key_lt env s b \<Longrightarrow> key_lt env a b"
apply (case_tac l,simp)
  apply auto
  apply (simp add:transitivity_with_key_lte)
done

lemma sorted_by_entry_lt_Cons: 
"wf_env env \<longrightarrow> sorted_by (entry_lt env) (x#xs) = (sorted_by (entry_lt env) xs & (ALL y:set xs.  entry_lt env x y))"
apply(induct xs arbitrary: x) 
 apply simp

 apply (simp add:entry_lt_def order_trans)
 apply auto

 apply (simp add:key_lt_transitivity)
done

lemma sorted_by_key_lt_Cons: 
"wf_env env \<longrightarrow> sorted_by (key_lt env) (x#xs) = (sorted_by (key_lt env) xs & (ALL y:set xs.  key_lt env x y))"
apply(induct xs arbitrary: x) 
 apply simp

 apply (simp add:order_trans)
 apply auto

 apply (simp add:key_lt_transitivity)
done

lemma sorted_by_entry_lt_append:
  "wf_env env \<longrightarrow> sorted_by (entry_lt env) (xs@ys) = (sorted_by (entry_lt env) xs & sorted_by (entry_lt env) ys & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. entry_lt env x y))"
apply (induct xs)
 apply simp

 apply (simp add:sorted_by_entry_lt_Cons)
 apply blast
done

lemma sorted_by_ket_lt_append:
  "wf_env env \<longrightarrow> sorted_by (key_lt env) (xs@ys) = (sorted_by (key_lt env) xs & sorted_by (key_lt env) ys & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. key_lt env x y))"
apply (induct xs)
 apply simp

 apply (simp add:sorted_by_key_lt_Cons)
 apply blast
done

(*
lemma "(\<forall> n < (length (l#list)). P ((l#list)!n)) =  (P ((l#list)!0) \<and> (\<forall> n < (length (l#list)) - 1. P (list!n)))"
apply simp
apply auto
apply (simp add:nth_Cons')
done
*)

lemma sorted_by_eq_nth: 
"sorted_by my_ord xs = (! n. n < length xs - 1 \<longrightarrow> my_ord (xs!n) (xs!(Suc n)))"
apply (induct xs)
 apply simp

 apply (simp)
 apply (case_tac xs)
  apply simp

  apply simp
  apply (metis Suc_less_eq gr0_conv_Suc less_antisym nth_Cons' nth_Cons_Suc)
done

lemma sorted_by_e_lt_allDistinct:
"wf_env env \<longrightarrow> sorted_by (entry_lt env) list \<longrightarrow> allDistinct (map (entry_to_key env) list) \<and> allDistinct ( list)"
apply (induct list)
 apply (simp add:allDistinct.simps)

 apply (simp add:allDistinct.simps sorted_by_entry_lt_Cons)
 apply clarsimp
 apply (simp add: entry_lt_def key_lt_def)
 apply blast
done

lemma sorted_by_key_lt_allDistinct:
"wf_env env \<Longrightarrow> sorted_by (key_lt env) list \<Longrightarrow> allDistinct ( list)"
apply (induct list)
 apply (simp add:allDistinct.simps)

 apply (simp add:allDistinct.simps sorted_by_key_lt_Cons)
 apply clarsimp
 apply (simp add: key_lt_def)
 apply blast
done

lemma wf_btree_hgt1_not_empty:
"wf_env env \<Longrightarrow>
 s r = Some (INode (I (d#ds, qs))) \<Longrightarrow>
 h > 0 \<Longrightarrow>
 norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h \<Longrightarrow>
 norm_entries_list_h s r h \<noteq> None \<and> (norm_entries_list_h s r h \<noteq> Some [])
 "
apply (case_tac h,simp)
apply (simp add:mm.simps get_m_def)
apply (case_tac "Suc (Suc (length ds)) \<noteq> length qs",simp)

 (* Suc (Suc (length ds)) = length qs *)
 apply (simp add:Let_def)
 apply (case_tac qs,simp)
  
  (* qs \<noteq> [] *)
  apply (simp add:cond_s1_def dd_def qq_def ss.simps)
  apply (case_tac "norm_entries_list_h s a nat",simp)

   (* norm_entries_list_h s a nat = Some *)
   apply (simp add:norm_entries_list_h_simps)
   (* we need to show that all the norm_entries_list_h are not null *)
   apply (simp add:union_clause_def)
   apply (case_tac "norm_entries_list_h s r (Suc nat)",simp+)
    apply (simp add:norm_entries_list_h_simps)   
    apply (case_tac "\<forall>x\<in>set list. \<exists>y. norm_entries_list_h s x nat = Some y")                            
    apply simp+
done


lemma wf_env_and_btree_ordered_keys: "wf_env env \<Longrightarrow>
 s r = Some (INode (I (d#ds, qs))) \<Longrightarrow>
 h > 0 \<Longrightarrow>
 norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h \<Longrightarrow>
 sorted_by (key_lt env) (d#ds)
"
apply (case_tac h,simp)
apply (case_tac "qs = []",simp)
apply (simp add:mm.simps get_m_def)
apply (case_tac "Suc (Suc (length ds)) \<noteq> length qs",simp)

 (*Suc (length ds) = length qs*)
 (* we solve union_clause to have that norm_entries_list must be a Some *)
 apply (simp add:Let_def union_clause_def norm_entries_list_h_simps ss.simps)
 apply (case_tac "\<not>(\<forall>x\<in>set qs. \<exists>y. norm_entries_list_h s x nat = Some y)",simp)

  (* (\<forall>x\<in>set qs. \<exists>y. norm_entries_list_h s x nat = Some y) *)
  apply simp
  (* we solve cond_sj since it gives us the order of the keys *)
  apply (simp add:cond_sj_def from_to_set qq_def ss.simps key_lte0_def)
  apply (case_tac "length qs = 2",simp)
   apply (case_tac "2 < length qs",simp)
    apply simp_all

    apply clarify
    (* here we want to show that the keys are in order *)
    apply (subgoal_tac "
       ((\<forall>j. Suc 0 \<le> j \<and> j \<le> length qs - 2 \<longrightarrow>
           key_lt env ((d # ds) ! (j - Suc 0)) ((d # ds) ! (j))) )")
    (* we reverse the length equality *)
    apply (simp add:sorted_by_eq_nth)
    apply (drule_tac t="length qs" in sym)
    apply clarsimp
    (* since j is between 1 and length ds while n is less than length ds, we instantiate j with n+1 *)
    apply (drule_tac x="n+1" in spec)+
    apply force

    (* we prove the subgoal: (\<forall>j. Suc 0 \<le> j \<and> j \<le> length qs - 2 \<longrightarrow>
           key_lt env ((d # ds) ! (j - Suc 0)) ((d # ds) ! (j))) ) *)
     apply clarsimp
     apply (drule spec)+
     apply auto
     apply (simp add:ss.simps)
     apply (case_tac "norm_entries_list_h s (qs ! j) nat",simp)

      (* norm_entries_list_h s (qs ! j) nat = Some *)
      apply (simp add:dd_def key_lte0_def)
      apply clarsimp
      apply (force intro:transitivity_with_key_lte_forall)
done

lemma wf_env_wf_btree_sorted_entries:
"wf_env env \<longrightarrow> norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h \<longrightarrow>
sorted_by (entry_lt env) (case norm_entries_list_h s r h of None \<Rightarrow> fail | Some list \<Rightarrow> list)"
apply (case_tac h)
 apply (case_tac "s r")
  (* s r = None *)
  apply simp

  (* s r = Some a *)
  apply (case_tac a)
   apply simp

   (* s r = Some Lnode*)
   apply (case_tac lnode)
   apply (simp add:Let_def mm.simps get_m_def)
   apply (case_tac "length list > maxN env")
    apply simp

    (* length list \<le> maxN env *)
    apply (simp add:ss.simps norm_entries_list_h.simps)

 (* Suc h *)
 (* we know that the keys are ordered, the final entry lists are sorted and the entry list are ordered in respect of the keys.
  We need the cond_s* to show that concat norm_entries_list_h h generates a sorted list *)
  (* here if I s r = Inode, I need to use the induction hypothesis *)
  apply simp
  apply (case_tac "s r")
   (* s r = None *)
   apply simp
   
   (* s r = Some a *)
   apply simp
   apply (case_tac a)
   defer
    (* a = Lnode *) 
    apply (case_tac lnode,simp+)
   
    (* a = Inode *)
    apply (case_tac inode,simp,case_tac prod,simp)
    apply (case_tac b,simp)
     
     (* b = ab #list*)
    apply (simp add:mm.simps get_m_def)
    apply (case_tac "length aa \<noteq> length list",simp)

     (* length aa = length list *)
     apply simp
     apply (case_tac aa,simp)
     
      (* aa = ac #lista*)
      apply (simp add:Let_def)
      (* let's show that norm_entries_list cannot be None using union_clause *)
      apply (simp add:union_clause_def)
      apply (case_tac " norm_entries_list_h s r (Suc nat) ",simp)

       (* norm_entries_list_h s r (Suc h) = Some ad *)
       apply (simp add:ss.simps)
       (* now we need to show that the entries are ordered, and we can do it by using the cond_s* *)
       (* we start from cond_s1 *)
       apply (simp add:cond_s1_def dd_def qq_def ss.simps)
       apply (case_tac "norm_entries_list_h s ab nat",simp)
       
        (* norm_entries_list_h s ab h = Some ae *)
        apply simp
        (* we can proceed with cond_sn *)
        apply (simp add:cond_sn_def dd_def qq_def mm.simps get_m_def ss.simps)
        apply (case_tac "norm_entries_list_h s ((ab # list) ! length list) nat",simp)
      
         (*norm_entries_list_h s ((ab # list) ! length list) h*)
         apply (simp add:key_lte0_def)
         (* finally cond_sj *)
         apply (simp add:cond_sj_def from_to_set)
         (* let's be sure that all norm_entries_list are not None *)
         apply (simp add:norm_entries_list_h_simps)
          apply (case_tac "\<not>(\<forall>x\<in>set list. \<exists>y. norm_entries_list_h s x nat = Some y)",simp)

          apply clarsimp
          apply (simp add:sorted_by_eq_nth entry_lt_def key_lt_def)
          apply clarsimp
          apply (drule_tac x="Suc 0" in spec)+
          apply clarsimp
          apply (case_tac "\<not>(Suc 0 \<le> length list - Suc 0)")
           (* \<not>(Suc 0 \<le> length list - Suc 0) : this means that we have only 1 key *)
           apply clarsimp
           apply (case_tac lista,simp+,case_tac list,simp+)
           (* the problem is that we find the order between the sets and not the order between the entries of a single set
           to solve this we would need to have a definition that says that a list is sorted_by if
            sorted_by2 xs@ys = \<forall> e \<in> set xs. \<forall> e' \<in> set ys. entry_lt e e' \<and> sorted_by2 xs \<and> sorted_by2 ys \<and> allDistinct xs@ys
            but this definition would complicate the proof even further! ! 
           *)
oops

lemma wf_env_wf_btree_no_entry_with_same_key:
"wf_env env \<longrightarrow> norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h \<longrightarrow> 
(allDistinct (map (entry_to_key env) (case norm_entries_list_h s r h of None \<Rightarrow> fail | Some list \<Rightarrow> list))) 
\<and> (allDistinct (case norm_entries_list_h s r h of None \<Rightarrow> fail | Some list \<Rightarrow> list))"
apply (subgoal_tac "wf_env env \<longrightarrow> norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h \<longrightarrow>
sorted_by (entry_lt env) (case norm_entries_list_h s r h of None \<Rightarrow> fail | Some list \<Rightarrow> list)")
defer
 apply (force intro:sorry_fixme) (* this will be solved when I figure out how to solve wf_env_wf_btree_sorted_entries *)
apply (simp add:sorted_by_e_lt_allDistinct)
done

lemma allDistinct_concat:
"allDistinct ((xs)@ys) = ((\<forall> e \<in> (set (xs)). \<forall> e' \<in> (set(ys)). e \<noteq> e'  ) \<and> allDistinct xs \<and> allDistinct ys)"
apply rule
 apply (induct xs)
 apply simp

 apply (simp add:allDistinct.simps)+
 apply clarify

 apply (induct xs)
 apply simp

 apply (simp add:allDistinct.simps)+
 apply force
done

lemma allDistinct_concat_false:
"xs \<noteq> [] \<Longrightarrow> allDistinct ((xs)@xs) = False"
apply (simp add:allDistinct_concat)
apply force
done

lemma allDistinct_eq_distinct:
"allDistinct list = distinct list "
apply (induct list)
 apply (simp add:allDistinct.simps)+
done

lemma allDistinct_concat':
"allDistinct ((xs)@ys) = ((\<forall> e \<in> (set (xs@ys)). \<not>(e \<in> set xs \<and> e \<in> set ys)) \<and> allDistinct xs \<and> allDistinct ys)"
apply (simp add:allDistinct_concat)
 apply force
done

lemma allDistinct_3sublists:
"allDistinct (xs@ys@zs) = (allDistinct (xs@ys) \<and> allDistinct (xs@zs)  \<and> allDistinct (ys@zs) \<and> allDistinct xs \<and> allDistinct ys \<and> allDistinct zs ) "
apply rule
apply (induct xs)
 apply (induct ys)
  apply (case_tac zs)
   apply (simp add:allDistinct.simps)+

apply (induct xs)
 apply (induct ys)
  apply (case_tac zs)
   apply (simp add:allDistinct.simps)+
done

lemma allDistinct_3concat:
"allDistinct (xs@ys@zs) \<Longrightarrow> 
(\<forall> e \<in> (set (xs)). \<forall> e' \<in> (set(ys)). e \<noteq> e'  ) 
\<and> 
(\<forall> e \<in> (set (xs)). \<forall> e' \<in> (set(zs)). e \<noteq> e'  ) 
\<and> 
(\<forall> e \<in> (set (ys)). \<forall> e' \<in> (set(zs)). e \<noteq> e'  )"
apply (subgoal_tac "allDistinct (xs@ys) \<and> allDistinct (xs@zs)  \<and> allDistinct (ys@zs)")
apply clarsimp
apply (simp add:allDistinct_concat)
 apply (simp add:allDistinct_3sublists)
done

lemma allDistinct_3concat':
"allDistinct (xs@ys@zs) =
(
 (\<forall> e \<in> (set (xs@ys)). \<not>(e \<in> set xs \<and> e \<in> set ys))
 \<and> (\<forall> e \<in> (set (ys@zs)). \<not>(e \<in> set ys \<and> e \<in> set zs))
 \<and> (\<forall> e \<in> (set (xs@zs)). \<not>(e \<in> set xs \<and> e \<in> set zs)) 
 \<and> allDistinct xs 
 \<and> allDistinct ys
 \<and> allDistinct zs
)"
apply clarsimp
apply (simp add:allDistinct_3sublists)
apply (simp add:allDistinct_concat)
apply blast
done

 
lemma split_at_append_with_concat_and_map: "(\<forall> P.
   List.concat (map P xs) =  (List.concat (map P (fst (split_at n xs)))) @ (List.concat (map P (snd (split_at n xs)))))"
 apply (simp add:split_at_def)
 apply (metis append_take_drop_id concat_append drop_map take_map)
done

lemma split_at_with_the_middle: 
"2 \<le> length xs \<Longrightarrow> n < length xs \<Longrightarrow> xs = (fst (split_at n xs))@[(xs!n)]@(snd (split_at (Suc n) xs))"
apply (simp add:split_at_def)
apply (subgoal_tac "xs ! n # drop (Suc (n)) xs = drop (n) xs")
 apply simp

apply (case_tac xs)
 apply simp 

 apply (metis drop_Suc_Cons drop_Suc_conv_tl)
done

lemma split_at_append_with_middle_concat_and_map: "(\<forall> P.
   2 \<le> length xs \<Longrightarrow> n < length xs \<Longrightarrow>
   List.concat (map P xs) =  (List.concat (map P (fst (split_at n xs)))) @ P (xs ! n) @ (List.concat (map P (snd (split_at (Suc n) xs)))))"
apply (subgoal_tac " P (xs ! n) @ List.concat (map P (snd (split_at (Suc n) xs))) = List.concat (map P (snd (split_at (n) xs))) ")
apply (simp add:split_at_append_with_concat_and_map)

apply (simp add:split_at_def)
apply (case_tac xs)
 apply simp

 apply simp
 apply (metis List.bind_def bind_simps(2) drop_Suc_Cons drop_Suc_conv_tl length_Cons)
done

lemma listfind_Suc_h_eq_listfind_h_if_ordered_keys1:
"wf_env env \<Longrightarrow>
 s r = Some (INode (I (ab # list, b))) \<Longrightarrow>
 b \<noteq> [] \<Longrightarrow>
 (Suc (length (ab # list))) = length b \<Longrightarrow>
 Suc na \<le> length b \<Longrightarrow> 
 2 \<le> length b \<Longrightarrow>
 n = Suc na \<Longrightarrow>
 union_clause (the (ss (Some r) s (Suc h))) s r (Suc h) \<and>
 cond_sj env (length b) b (ab # list) s h \<and>
           cond_s1 env b (ab # list) s h \<and> cond_sn env (length b) b (ab # list) s h \<Longrightarrow>
 (case first (ab # list) (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i) = Suc na \<Longrightarrow>
 ((List.find (\<lambda>x. k = entry_to_key env x) (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b)))
 =
 (List.find (\<lambda>x. k = entry_to_key env x) ((case (norm_entries_list_h s (b!(n - Suc 0)) h) of None \<Rightarrow> fail | Some list \<Rightarrow> list) )))"
(*FIXME I am assuming that norm_entries_list is sorted
   this should appear as an hypothesis
 *)
apply (subgoal_tac "sorted_by (entry_lt env) (the (norm_entries_list_h s r (Suc h)))")
defer
 apply (force intro:sorry_fixme)
apply (subgoal_tac "allDistinct (the (norm_entries_list_h s r (Suc h))) \<and> allDistinct (map (entry_to_key env) (the (norm_entries_list_h s r (Suc h))))")
defer
 apply (simp add:sorted_by_e_lt_allDistinct)
apply (simp add:allDistinct_eq_distinct)
apply (erule conjE)+

apply (subgoal_tac "(the (norm_entries_list_h s r (Suc h)) = List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b))")
defer
 apply (simp add:union_clause_def norm_entries_list_h_simps)
 apply (case_tac "\<not>(\<forall>x\<in>set b. \<exists>y. norm_entries_list_h s x h = Some y)",simp+)
 apply force

apply simp
apply (subgoal_tac "\<exists> klist. norm_entries_list_h s (b ! na) h = Some klist")
 defer
 apply (simp add:union_clause_def norm_entries_list_h_simps)
 apply (case_tac "\<not>(\<forall>x\<in>set b. \<exists>y. norm_entries_list_h s x h = Some y)",simp+)
apply (erule exE)
apply simp

apply (subgoal_tac "? x. b!na = x")
defer
 apply simp

apply (erule exE)
apply (subgoal_tac "? xs ys. (b = xs@x#ys)")
 defer
 apply (subgoal_tac "x \<in> set b")
 apply (simp add:split_list)
  apply (force)
apply (erule exE)+
apply simp
apply (erule conjE)+
apply (subgoal_tac "? preklist. (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) xs)) = preklist")
defer
 apply simp
apply (erule exE)
apply simp
apply (subgoal_tac "? postklist. (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) ys)) = postklist")
defer
 apply simp
apply (erule exE)
apply simp
apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) (preklist @ klist @ postklist)")
 (*List.find (\<lambda>x. k = entry_to_key env x) (preklist @ klist @ postklist) = none *)
 (* this is the case in which there is no entry for the key k*)
 apply (subgoal_tac "List.find (\<lambda>x. k = entry_to_key env x) klist = None")
 apply simp
  apply (simp add:listfind_append Let_def)
   apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) preklist \<noteq> None",simp)
    apply (simp add:listfind_append Let_def)
    apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) klist \<noteq> None",simp+)

 (* k is in klist: we just need to show that it is not in the first piece of the list *)
 apply (rename_tac kentry)
 apply (subgoal_tac "(k \<in> set (map (entry_to_key env) (preklist@klist@postklist)))")
 defer
  apply (simp add:find_Some_iff)
  apply (erule exE)
  apply (erule conjE)+
  apply (simp add:nth_append)
  
  apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) klist")
   apply (simp add:find_None_iff)
   (* we need to show that klist is not empty and that k must be in it for cond_s* *)
   apply (subgoal_tac "na > 0 \<longrightarrow> \<not>key_lt env k ((ab#list)!(na - 1))")
   prefer 2
     apply (case_tac "first (ab # list) (key_lt env k)")
     (*first (ab # list) (key_lt env k) = None*)
     apply (simp add:first_None_iff)
     apply (erule conjE)+
     apply (drule_tac t=na in sym)
     apply simp
     apply (subgoal_tac "(ab # list) ! length list \<in> set list")
     apply force
     apply (force intro:sorry_fixme)
   
     apply (simp add:first_def)
     apply (case_tac "find_index (key_lt env k) (ab # list)",simp)
     apply (simp add:find_index_Some_iff)

   apply (case_tac na)
    apply (subgoal_tac "key_lt env k ab")
    prefer 2
     apply (simp add:first_def find_index_def)
     apply (case_tac " key_lt env k ab")
      apply simp

      apply simp
      (* here the map Suc cannot return any index equal to 0*)
      apply (force intro:sorry_fixme)
    apply (simp add:cond_s1_def dd_def qq_def ss.simps)
    apply (erule conjE)
    apply (subgoal_tac "\<exists> x \<in> set klist .  k = entry_to_key env x")
    apply simp
    
    (* solve "\<exists> x \<in> set klist .  k = entry_to_key env x"*)
    (* this is true because klist is the first list that satisfies key_lt constraint *)
    apply (force intro: sorry_fixme)
    
   apply (force intro: sorry_fixme)

   apply simp
   (* this is true for 
entry_to_key env ` set klist \<inter> entry_to_key env ` (\<Union>x\<in>set ys. set (the (norm_entries_list_h s x h))) = {} \<Longrightarrow>
       entry_to_key env ` (\<Union>x\<in>set xs. set (the (norm_entries_list_h s x h))) \<inter>
       (entry_to_key env ` set klist \<union> entry_to_key env ` (\<Union>x\<in>set ys. set (the (norm_entries_list_h s x h)))) =
       {}
   *)
   apply (force intro: sorry_fixme)
oops

lemma listfind_Suc_h_eq_listfind_h_if_ordered_keys1:
"wf_env env \<Longrightarrow>
 s r = Some (INode (I (ab # list, b))) \<Longrightarrow>
 b \<noteq> [] \<Longrightarrow>
 (Suc (length (ab # list))) = length b \<Longrightarrow>
 Suc na \<le> length b \<Longrightarrow> 
 2 \<le> length b \<Longrightarrow>
 n = Suc na \<Longrightarrow>
 union_clause (the (ss (Some r) s (Suc h))) s r (Suc h) \<and>
 cond_sj env (length b) b (ab # list) s h \<and>
           cond_s1 env b (ab # list) s h \<and> cond_sn env (length b) b (ab # list) s h \<Longrightarrow>
 (case first (ab # list) (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i) = Suc na \<Longrightarrow>
 ((List.find (\<lambda>x. k = entry_to_key env x) (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b)))
 =
 (List.find (\<lambda>x. k = entry_to_key env x) ((case (norm_entries_list_h s (b!(n - Suc 0)) h) of None \<Rightarrow> fail | Some list \<Rightarrow> list) )))"
(*FIXME I am assuming that norm_entries_list is sorted
   this should appear as an hypothesis
 *)
apply (subgoal_tac "sorted_by (entry_lt env) (the (norm_entries_list_h s r (Suc h)))")
defer
 apply (force intro:sorry_fixme)
apply (subgoal_tac "allDistinct (the (norm_entries_list_h s r (Suc h))) \<and> allDistinct (map (entry_to_key env) (the (norm_entries_list_h s r (Suc h))))")
defer
 apply (simp add:sorted_by_e_lt_allDistinct)

apply (erule conjE)+
apply simp
apply (thin_tac "n=?x")
apply (subgoal_tac "(the (norm_entries_list_h s r (Suc h)) = List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b))")
defer
 apply (simp add:union_clause_def norm_entries_list_h_simps)
 apply (case_tac "\<not>(\<forall>x\<in>set b. \<exists>y. norm_entries_list_h s x h = Some y)",simp+)
 apply force

apply (subgoal_tac "\<exists> klist. norm_entries_list_h s (b ! na) h = Some klist")
 defer
 apply (simp add:union_clause_def norm_entries_list_h_simps)
 apply (case_tac "\<not>(\<forall>x\<in>set b. \<exists>y. norm_entries_list_h s x h = Some y)",simp+)
apply (erule exE)
apply simp

apply (subgoal_tac "? x. b!na = x")
defer
 apply simp

apply (erule exE)
apply (subgoal_tac "? xs ys. (b = xs@x#ys)")
 defer
 apply (subgoal_tac "x \<in> set b")
 apply (simp add:split_list)
  apply (force)
apply (erule exE)+
apply simp

apply (subgoal_tac "allDistinct (xs@x#ys)")
defer
 (*this is true because if there are two page ids directing to the same page in the store we would have duplicated entries*)
 apply (force intro:sorry_fixme)

apply (subgoal_tac "? preklist. (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) xs)) = preklist")
defer
 apply simp
apply (erule exE)
apply simp
apply (subgoal_tac "? postklist. (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) ys)) = postklist")
defer
 apply simp
apply (erule exE)
apply simp
apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) (preklist @ klist @ postklist)")
 (*List.find (\<lambda>x. k = entry_to_key env x) (preklist @ klist @ postklist) = none *)
 (* this is the case in which there is no entry for the key k*)
 apply (subgoal_tac "List.find (\<lambda>x. k = entry_to_key env x) klist = None")
 apply simp
  apply (simp add:listfind_append Let_def)
   apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) preklist \<noteq> None",simp)
    apply (simp add:listfind_append Let_def)
    apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) klist \<noteq> None",simp+)

 (* k is in klist: we just need to show that it is not in the first piece of the list *)
 apply (rename_tac kentry)
 apply (subgoal_tac "(k \<in> set (map (entry_to_key env) (preklist@klist@postklist)))")
 defer
  apply (simp add:find_Some_iff)
  apply (erule exE)
  apply (erule conjE)+
  apply (simp add:nth_append)

 (* we need to know that k is smaller than a given key *)
 apply (subgoal_tac "na > 0 \<longrightarrow> \<not>key_lt env k ((ab#list)!(na - 1))")
 defer
  apply (case_tac "first (ab # list) (key_lt env k)")
   (*first (ab # list) (key_lt env k) = None*)
   apply (simp add:first_None_iff)
   apply (erule conjE)+
   apply (drule_tac t=na in sym)
   apply simp
   apply (subgoal_tac "(ab # list) ! length list \<in> set list")
   apply force
    apply (force intro:sorry_fixme)
   
   apply (simp add:first_def)
   apply (case_tac "find_index (key_lt env k) (ab # list)",simp)
    apply (simp add:find_index_Some_iff)

 apply simp
 apply (subgoal_tac "\<not> (x \<in> set xs) \<and> \<not> (x \<in> set ys)")
 defer
  apply (force intro:sorry_fixme)

 apply (erule conjE)+
 apply (subgoal_tac "\<not> (k \<in> set (map (entry_to_key env) (preklist)))")
 defer
  apply (case_tac "na = 0")
   apply (case_tac xs,simp+)

   apply (case_tac "na < length xs + length ys")
    apply simp
    apply (force intro:sorry_fixme)

    apply simp
    apply (force intro:sorry_fixme)
(*to remove before proceeding*)
  apply simp
  apply (case_tac "preklist=[]",simp)
   (* preklist \<noteq> []*)
   apply (subgoal_tac "\<exists> page_id_of_last_entrylist_of_preklist. (xs @ x # ys) ! (na - 1)= page_id_of_last_entrylist_of_preklist")
   prefer 2
    apply force
   apply (erule exE)
   apply simp
   apply (subgoal_tac "\<exists> last_preklist. norm_entries_list_h s page_id_of_last_entrylist_of_preklist h = Some last_preklist")
   prefer 2
    apply (case_tac "norm_entries_list_h s page_id_of_last_entrylist_of_preklist h")
     apply (simp add:union_clause_def norm_entries_list_h_simps)
     apply (case_tac "\<not>(\<forall>x\<in>set xs \<union> set ys. \<exists>y. norm_entries_list_h s x h = Some y)")
      apply simp

      apply simp
      (* this is true because page_id_of_last_entrylist_of_preklist belongs to xs*)
      apply (force intro:sorry_fixme)
    apply force
   apply (erule exE)
   apply (subgoal_tac "\<exists> preklist'. preklist = preklist'@last_preklist")
   prefer 2
    apply (force intro:sorry_fixme)
  apply (erule exE)+
  apply (simp add:cond_sj_def from_to_set qq_def)
  apply (drule_tac x="na - Suc 0" in spec)
  apply (simp add:ss.simps dd_def key_lte0_def)
  apply (case_tac "na = 0")
   apply simp
   (* entries list must be composed by all distinct entries: here we have two klists!
   allDistinct (preklist' @ klist @ klist @ postklist)
   *)
   apply (force intro:sorry_fixme)
   
   apply simp
   apply rule+
   apply (case_tac "Suc 0 \<le> na - Suc 0 \<and> na - Suc 0 \<le> length xs + length ys - Suc 0")
    (* Suc 0 \<le> na - Suc 0 \<and> na - Suc 0 \<le> length xs + length ys - Suc 0 *)
    apply simp
    apply (erule conjE)+
    (* at this point we know that k cannot be in last_preklist because the preconditions 

     \<not> key_lt env k ((ab # list) ! (na - Suc 0)) 

     \<forall>s\<in>set last_preklist. key_lt env (entry_to_key env s) ((ab # list) ! (na - Suc 0)) 
    are not satisfied *)
    apply (force intro:sorry_fixme)
    
    apply simp
    (* impossible: if Suc 0 \<le> na - Suc 0 then preklist was empty *)
    apply (force intro:sorry_fixme)
(*end to remove *)

 apply (subgoal_tac "\<not> (k \<in> set (map (entry_to_key env) (postklist)))")
 defer
  apply (force intro:sorry_fixme)

 apply (subgoal_tac "k \<in> set (map (entry_to_key env) klist)")
 defer
  apply force

 apply (simp add:listfind_append Let_def)
 apply (subgoal_tac "List.find (\<lambda>x. k = entry_to_key env x) preklist = None")
 defer
  apply (force simp add:find_None_iff)

 apply (simp add:listfind_append Let_def)
 apply (case_tac " List.find (\<lambda>x. k = entry_to_key env x) klist = None")
  apply (force simp add:find_None_iff)
    
  apply force
oops  

lemma listfind_Suc_h_eq_listfind_h_if_ordered_keys:
"wf_env env \<Longrightarrow>
 s r = Some (INode (I (ab # list, b))) \<Longrightarrow>
 b \<noteq> [] \<Longrightarrow>
 (Suc (length (ab # list))) = length b \<Longrightarrow>
 Suc na \<le> length b \<Longrightarrow> 
 2 \<le> length b \<Longrightarrow>
 n = Suc na \<Longrightarrow>
 union_clause (the (ss (Some r) s (Suc h))) s r (Suc h) \<and>
 cond_sj env (length b) b (ab # list) s h \<and>
           cond_s1 env b (ab # list) s h \<and> cond_sn env (length b) b (ab # list) s h \<Longrightarrow>
 (case first (ab # list) (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i) = Suc na \<Longrightarrow>
 ((List.find (\<lambda>x. k = entry_to_key env x) (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b)))
 =
 (List.find (\<lambda>x. k = entry_to_key env x) ((case (norm_entries_list_h s (b!(n - Suc 0)) h) of None \<Rightarrow> fail | Some list \<Rightarrow> list) )))"
(*FIXME I am assuming that norm_entries_list is sorted
   this should appear as an hypothesis
 *)
apply (subgoal_tac "sorted_by (entry_lt env) (the (norm_entries_list_h s r (Suc h)))")
defer
 apply (force intro:sorry_fixme)

apply (subgoal_tac "allDistinct ((map (entry_to_key env) (the (norm_entries_list_h s r (Suc h))))) \<and> allDistinct  (the (norm_entries_list_h s r (Suc h)))")
defer
 apply (simp add:sorted_by_e_lt_allDistinct)

(* now we proof that (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b))) and (the (norm_entries_list_h s r (Suc h))) are equal *)
apply (subgoal_tac "(the (norm_entries_list_h s r (Suc h))) = (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b))")
defer
  apply (simp add:union_clause_def norm_entries_list_h_simps)
  apply (case_tac "\<not>(\<forall>x\<in>set b. \<exists>y. norm_entries_list_h s x h = Some y)",simp,force)

(*let's show also that (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b)) can be splitted *)
apply (case_tac "norm_entries_list_h s (b ! (n - Suc 0)) h")
 (*norm_entries_list_h s (b ! (n - Suc 0)) h = None*)
 (* this is not None for union_clause **)
 apply clarsimp
 apply (subgoal_tac "\<exists> x \<in> set b. norm_entries_list_h s x h = None")
  apply (simp add:union_clause_def norm_entries_list_h_simps)
  apply (case_tac "\<not>(\<forall>x\<in>set b. \<exists>y. norm_entries_list_h s x h = Some y)",simp)
  apply simp

  (* solving the dummy goal \<exists> x \<in> set b. norm_entries_list_h s x h = None *)
  apply force
(*
 (*norm_entries_list_h s (b ! (n - Suc 0)) h = Some a *)
 (* FIXME remove split_at for b1@bk#b2*)
 apply (subgoal_tac "\<exists> xs ys. 
   b = xs@b!na#ys
   ")
 defer
  apply (simp add:split_list)
*)
 apply (subgoal_tac "
   (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b) = 
   (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (fst (split_at (na) b)))
   @a@
   (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (Suc na) b))))))")
 defer
  (* this is true because a@remaining_list is the complement of beginning list: beg_list@a@rem_list = b  *)
  apply (case_tac "(a@
   (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (Suc na) b))))) \<noteq> (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at na b)))) ")
   (* (a@
   (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (na) b))))) \<noteq> (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (na - 1) b)))) *)
   apply clarsimp
   apply (case_tac "a = the (norm_entries_list_h s (b ! na) h)",simp)
    apply clarsimp
    apply (case_tac "na < length b",simp)
     (* na < length b *)
     apply (simp add:split_at_append_with_middle_concat_and_map)

     (* na \<ge> length b*)
     apply simp

    (* a \<noteq> the (norm_entries_list_h s (b ! na) h) *)
    apply simp

   (* (a@
   (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (na) b))))) = (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (na - 1) b))))) *)
   apply (simp add: split_at_append_with_concat_and_map)

 (* given these hypothesis we can proceed solving the main goal*)
 apply simp
 (* now is k among the keys of the entries list? *)
 apply (case_tac "\<not>(k \<in> (set (map (entry_to_key env) (the (norm_entries_list_h s r (Suc h))))))")
  (* if the key is not in the entries list, find is a None *)
  apply (simp add:union_clause_def,case_tac "norm_entries_list_h s r (Suc h)",simp)
  (* norm_entries_list_h s r (Suc h) = Some *)
  apply (simp add:norm_entries_list_h_simps)
  apply (case_tac "\<not>(\<forall>x\<in>set b. \<exists>y. norm_entries_list_h s x h = Some y)",simp)
  
   apply simp
   apply (subgoal_tac "List.find (\<lambda>x. k = entry_to_key env x) a = None ")
   apply clarsimp
   apply (simp add:find_None_iff)
   apply force

    (* solving subgoal: List.find (\<lambda>x. k = entry_to_key env x) a = None *)
    apply (simp add:find_None_iff)
    apply clarsimp

  (* k \<in> (set (map (entry_to_key env) (the (norm_entries_list_h s r (Suc h))))) 
  then we must show that k can only belong to
  (norm_entries_list_h s (b!(n - Suc 0)) h) 
  *)
  apply (subgoal_tac "(k \<in> (set (map (entry_to_key env) a)))")
  defer      
   (* we assume that k is in set a -- this will require the first hypothesis*)
   
   (*now we solve all the other subsubgoals*)
    apply clarsimp
   (* solve subsubgoal : k \<in> set (map (entry_to_key env) a)*)
    apply (erule disjE)
     apply clarsimp
     (* why cannot k be a key in set (fst (split_at na b))?
      because the first key less than k is in b!na (that is not in (fst (split_at na b)))
      so all the keys of fst .. are too small to contain k.
      This means we need to:
       case split on na, and show that in every case (the only hard is the middle one)
       the keys of fst .. are too small (by using cond_s* )
      *)
      apply (case_tac "na = 0")
       (* na = 0 *)
       (* this get solved because the fst.. is empty *)
       apply (simp add:first_def,case_tac "find_index (key_lt env (entry_to_key env x)) (ab # list)",simp+)
       apply (simp add:split_at_def)
       
       (* na \<noteq> 0*)
       apply (case_tac "na < (length b - 1)")
        (* na < (length b - 1) *)
        apply (simp add:first_def,case_tac "find_index (key_lt env (entry_to_key env x)) (ab # list)",simp+)
        apply clarsimp
        apply (simp add:allDistinct_concat'
        (* now I need to show through cond_s1 and cond_sn that 
          \<forall>i'<na. \<not> key_lt env (entry_to_key env x) ((ab # list) ! i')
          does not hold

          the simplest i' should be 0, because we just need cond_s1
        *)
        apply (drule_tac x="0" in spec)
        apply clarsimp
        apply (simp add:cond_s1_def dd_def qq_def ss.simps)
        apply (case_tac "(norm_entries_list_h s (b ! 0) h)",simp+)
        (*FIXME I see a double negation here: x cannot be in both for allDistinct and 
 the condition \<not> key_lt env (entry_to_key env x) ab is not respected by 
norm_entries_list_h s (b ! 0) h since b!0 is one of the xa *)
        apply (case_tac "(b!0) \<in> set (fst (split_at na b))")
         apply clarsimp
         apply (subgoal_tac "\<forall> x \<in> set (the (norm_entries_list_h s (b!0) h)). key_lt env (entry_to_key env x) ab ")
         apply (simp add:allDistinct_3sublists)
         apply (simp add:allDistinct_concat)
         apply clarsimp
         
        apply (force intro:sorry_fixme)apply (force intro:sorry_fixme)apply (force intro:sorry_fixme)

        (* na \<ge> (length b - 1) -- the greater case cannot be! *)
        apply (case_tac "length b - Suc 0 < na",simp)
         apply clarsimp
         (* na = (length b - 1)  *)
         apply (simp add:first_def,case_tac "find_index (key_lt env (entry_to_key env x)) (ab # list)",simp_all)
          apply clarsimp
          apply (simp add:split_at_def cond_sj_def dd_def from_to_set)
          apply (drule_tac x="Suc 0" in spec)
          apply (simp add:qq_def ss.simps)
          apply (case_tac "Suc 0 \<le> length b - 2") (*if we have just two elements we will need to open cond_s1 and cond_sn*)
           apply simp
           apply (case_tac "norm_entries_list_h s (b ! Suc 0) h",simp)
            apply (case_tac "index list 0",simp)

            apply (simp add:key_lte0_def key_lt_def)
            apply (clarsimp)
            (* as in the earlier case
             \<forall>s\<in>set aa. key_lte env ab (entry_to_key env s) makes key_lte env (entry_to_key env x) ab false
             and  entry_to_key env x = ab is false as well, since we have all distinct entries
            *)
            apply (force intro:sorry_fixme)

            (* if we have only two elements in b*)
            apply clarsimp
            apply (simp add:cond_s1_def cond_sn_def dd_def qq_def ss.simps)
            apply (case_tac "norm_entries_list_h s (b ! 0) h ",simp+)
             apply (case_tac "nth_from_1 (ab # list) (length b - Suc 0)",simp+)
             apply (simp add:key_lte0_def key_lt_def)
             apply clarsimp
             (* similar reasoning as above *)
        apply (force intro:sorry_fixme)
        
     apply (erule disjE)
      apply simp
      apply clarsimp
      apply (case_tac "na = 0")
       (* na = 0 -- there is not fst split_at *)
       apply (simp add:split_at_def)
       (* we can use again the same reasoning of the previous cases *)
       apply (force intro:sorry_fixme)
       
       (* na > 0 *)
       apply clarsimp
       apply (case_tac "na < (length b - 1)")
   apply (force intro:sorry_fixme)
  
  apply clarsimp
  apply (subgoal_tac "
  (\<forall> e \<in> (set (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (fst (split_at na b))))). (\<not> (\<lambda>x. k = entry_to_key env x) e))
    \<and>
  (\<forall> e \<in> (set (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (Suc na) b))))) . (\<not> (\<lambda>x. k = entry_to_key env x) e))
  ")
  defer
   apply clarsimp   
   apply (simp add:allDistinct_3sublists)
   apply (simp add:allDistinct_concat)
   apply clarsimp
   apply force

  apply clarsimp  
 (* we show that find on the first part of the list returns None*)
 apply (subgoal_tac " 
    List.find (\<lambda>x. k = entry_to_key env x) (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (fst (split_at (na) b)))) 
     = None")
 defer
  apply (simp add:find_None_iff,force)

 (* we show that find on the last part of the list is None *)
 apply (subgoal_tac " 
  List.find (\<lambda>x. k = entry_to_key env x) (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) (snd (split_at (Suc na) b)))) 
  = None")
 defer
  apply (simp add:find_None_iff,force)

 (*the goal is easy to solve now*)
 apply (simp add:Let_def listfind_append)
done

lemma norm_entries_list_not_emtpy_if_wf_btree:
"wf_env env \<longrightarrow> norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h  \<longrightarrow>
(h = 0 \<and> (case s r of Some (LNode (L (qs))) \<Rightarrow> (norm_entries_list_h s r h = Some qs) | _ \<Rightarrow> False))
\<or>
(h > 0 \<and> (case norm_entries_list_h s r h of Some list \<Rightarrow> list \<noteq> [] | None \<Rightarrow> False)) "
apply (case_tac h)
 apply (case_tac "s r")
  apply simp
  
  apply (case_tac a)
   apply simp

   apply (case_tac lnode)
   apply (simp add:mm.simps get_m_def Let_def)
   apply (case_tac "length list > maxN env")
    apply simp

    apply (simp add:ss.simps norm_entries_list_h.simps)
 (* Suc nat *)
 apply (case_tac "s r")
  apply simp

  apply (case_tac a)
  defer
   apply simp

   (* a Inode *)
   apply (case_tac inode)
   apply (case_tac prod)
   apply (simp add:mm.simps get_m_def)
   apply (case_tac "Suc (length aa) \<noteq> length b")
   apply simp

   apply (case_tac aa)
    apply simp

    apply (case_tac "b = []")
     apply simp
    
     apply (simp add:Let_def cond_mj_def from_to_set qq_def wf_env_def mm.simps get_m_def)
     apply auto
     
sorry

lemma norm_entries_list_cannot_be_None_if_norm_wf_btree_hgt0:
"norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h \<longrightarrow> norm_entries_list_h s r h \<noteq> None"
apply (case_tac h)
 (* h = 0 *)
 apply simp
 apply (case_tac "s r")
  (* s r = None *)
  apply simp

  apply (case_tac a)
   (* a = Inode *)
   apply simp

   (* a = Lnode *)
   apply (case_tac lnode)
   apply (simp add:Let_def mm.simps get_m_def)
   apply (case_tac "\<not>(length list \<le> maxN env)")
    (* \<not>(length list \<le> maxN env) *)
    apply simp

    (* (length list \<le> maxN env)*)
    apply (simp add:ss.simps norm_entries_list_h.simps wf_env_def sorted_by_e_lt_allDistinct)

 (* h = Suc *)
 apply simp
 apply (case_tac "s r")
  (* s r = None *)
  apply simp

  (* s r = Some a *)
  apply (case_tac a)
   (* a = Inode *)
   apply (case_tac inode)
   apply (case_tac prod)
   apply (simp add:mm.simps get_m_def)
   apply (case_tac "Suc (length aa) \<noteq> length b")
    (* Suc (length aa) \<noteq> length b *)
    apply simp

    (* Suc (length aa) = length b *)
    apply (case_tac aa)
     (* aa = [] *)
     apply simp

     (* aa = ab#list *)
     apply (simp add:Let_def union_clause_def)
     apply (case_tac "norm_entries_list_h s r (Suc nat)")
      (* norm_entries_list_h s r (Suc nat) = None *)
      apply simp
      
      (* norm_entries_list_h s r (Suc nat) *)
      apply simp

   (* a = lnode *)
   apply simp
done
end
