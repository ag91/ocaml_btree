theory "Abstract_tree" 

imports 
 	 Main "~~/src/HOL/Library/Multiset" (* for size_change *)
begin

section "preliminaries"

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 100) where
  "rev_apply x f = f x"


(* Quickcheck_Examples/Completeness.thy - should be in Main? simpler defn here*)
definition is_Some :: "'a option => bool" where
  "is_Some x == x ~= None"

primrec dest_Some (* :: "'a option => 'a" *) where 
  "dest_Some (Some x) = x"
  | "dest_Some None = undefined"


definition arb :: "'a" where
  "arb == undefined"  

definition impossible :: "'a" where
  "impossible == undefined"  

datatype 'a rresult = Ok 'a | Error 

definition rresult_to_option :: "'a rresult => 'a option" where
  "rresult_to_option x = (case x of Ok x => Some x | Error => None)"

lemma [simp]: "(Error |> rresult_to_option = None) & ((Ok x) |> rresult_to_option = Some x)"
  apply(force simp: rresult_to_option_def rev_apply_def)
  done


section "page, page_ref, store"

(* type vars: 'bs 'k 'r 'v *)

datatype 'bs page = Page 'bs (* bytes *)

datatype 'r page_ref = Page_ref 'r

definition dest_page_ref :: "'r page_ref => 'r" where
  "dest_page_ref r0 == (case r0 of Page_ref r => r)"

datatype ('r,'bs) store = Store "('r page_ref ~=> 'bs page)"  (* different to paper: we store actual bytes *)

definition dest_store :: "('r,'bs) store => ('r page_ref ~=> 'bs page)" where
  "dest_store s0 == (case s0 of Store f => f)"

definition ref_to_page :: "('r,'bs) store => 'r page_ref => 'bs page option" where
  "ref_to_page s0 r0 == (s0|>dest_store) r0"


section "key and frame"


datatype 'k key = Key 'k

definition dest_key :: "'k key => 'k" where
  "dest_key k = (case k of Key k => k)"


datatype 'v value_t = Value 'v

definition dest_value :: "'v value_t => 'v" where
  "dest_value v == (case v of Value v => v)"


record ('r,'k) node_frame = 
  nf_n :: "nat"
  nf_ks :: "nat => 'k key"
  nf_rs :: "nat => 'r page_ref"

record ('k,'v) leaf_frame = 
  lf_kvs :: "('k key * 'v value_t) list" (* slightly different to paper - we store ks in tree *) 

datatype ('r,'k,'v) frame = Frm_I "('r,'k) node_frame" | Frm_L "('k,'v) leaf_frame"


section "page and frame"

(* interpretation of pages *)
datatype ('bs,'k,'r,'v) page_to_frame = P2f "'bs page => ('r,'k,'v) frame"  (* note that this forces that the page internally stores its type; this is not necessary, but is used by step_find *)

definition dest_p2f :: "('bs,'k,'r,'v) page_to_frame => 'bs page => ('r,'k,'v) frame" where
  "dest_p2f x = (case x of P2f f => f)"

(**********)
(* to convert a page_ref to a frame, lookup the page option and use the above *)
record  ('bs,'k,'r,'v) ctxt =
  ctxt_p2f :: "('bs,'k,'r,'v) page_to_frame"

(* from this point, we don't duplicate 0/Suc defns, to minimize # of defns *)
definition page_ref_to_frame :: "('bs,'k,'r,'v) ctxt => ('r,'bs) store =>  'r page_ref => ('r,'k,'v) frame option" where
  "page_ref_to_frame c0 s0 r0 == (
    case ref_to_page s0 r0 of
    None => (Error |> rresult_to_option)  (* invalid page access *)
    | Some p => (Some( (c0|>ctxt_p2f|>dest_p2f) p))
)"



section "tree"

datatype ('k,'v) tree = Tr_nd "(nat * (nat => 'k key) * (nat => ('k,'v) tree))" | Tr_lf "('k key * 'v value_t) list"

type_synonym tree_height = nat

lemma FIXME: "P" sorry

function tree_to_kvs :: "('k,'v) tree => ('k key *'v value_t) list" where
  "tree_to_kvs (Tr_lf(kvs)) = kvs"
  | "tree_to_kvs (Tr_nd(n,ks,ts)) = ([0..<n+1] |> (List.map ts) |> (List.map tree_to_kvs) |> List.concat)" (* we use n+1 because there must be n (i.e. number of keys + 1 departing from index 0) subtrees in each internal node*)
by pat_completeness auto
termination  (* tree_to_kvs_dom is not right here - the function package seems confused FIXME *)
  apply(force intro:FIXME)
  done


section "page_ref_to_tree, page_ref_to_map, page_ref_key_to_v"

(* NB this has an explicit n argument, whereas wfness gives us that we can just use page_ref_to_frame *)
fun page_ref_to_tree :: "('bs,'k,'r,'v) ctxt =>  ('r,'bs) store => 'r page_ref => tree_height => ('k,'v) tree option" where
  "page_ref_to_tree c0 s0 r0 0 = (
      case page_ref_to_frame c0 s0 r0 of 
      None => (Error |> rresult_to_option) 
      | Some frm => (
        case frm of 
        Frm_L(lf) => (Some(Tr_lf (lf|>lf_kvs)))
        | _ => (Error |> rresult_to_option )))"  (* attempt to access missing page *)
  | "page_ref_to_tree c0 s0 r0 (Suc n') = (
      case page_ref_to_frame c0 s0 r0 of
      None => (Error |> rresult_to_option)  (* attempt to access missing page *)
      | Some frm => (
        case frm of 
        Frm_I(nf) => (
          let n = (nf|>nf_n) in
          let ks = (nf|>nf_ks) in
          let rs = (nf|>nf_rs) :: (nat => 'r page_ref) in
          let f0 = (% r. page_ref_to_tree c0 s0 r n') :: ('r page_ref => ('k,'v) tree option) in
          let prop =
           let not_empty_frames =
            let not_empty = (% r.
              (case page_ref_to_frame c0 s0 r of
              None => False  (* attempt to access missing page *)
              | Some frm => (
                case frm of 
                  Frm_I(nf) => (nf|>nf_n) \<noteq> 0 (* this is not necessary *)
                  | Frm_L(lf) => \<not> (lf|>lf_kvs|>List.null))))
            in
            n \<noteq> 0
            \<and>
            (! (m::nat). m <= n --> m |> rs |> not_empty)
          in
            not_empty_frames
            \<and>
            (! (m::nat). m <= n --> m |> rs |> f0 |> is_Some)
          in
          case prop of
          True => (Some(Tr_nd(n,ks,(% (m::nat). m |> rs |> f0 |> dest_Some))))
          | False => (Error |> rresult_to_option))  (* Frm_I was not wellformed - prop was false *)
        | Frm_L(_) => (Error |> rresult_to_option)))"  (* found Frm_L but tree_height was not 0 *)

(* notice that this ideally belongs in section "page and frame" *)
definition page_ref_to_kvs ::  "('bs,'k,'r,'v) ctxt =>  ('r,'bs) store => 'r page_ref => tree_height => ('k key*'v value_t) list option" where
  "page_ref_to_kvs c0 s0 r0 n0 == (
  (page_ref_to_tree c0 s0 r0 n0)
  |> (% x. case x of
    None => None
    | Some t => Some(tree_to_kvs t)))"

definition kvs_to_map :: "('k key*'v value_t) list => ('k key ~=> 'v value_t)" where
  "kvs_to_map kvs == (map_of kvs)"

definition page_ref_to_map :: "('bs,'k,'r,'v) ctxt =>  ('r,'bs) store => 'r page_ref => tree_height => ('k key ~=> 'v value_t) option" where
  "page_ref_to_map c0 s0 r0 n0 == (page_ref_to_kvs c0 s0 r0 n0) |> (map_option kvs_to_map)"

definition page_ref_key_to_v :: "('bs,'k,'r,'v) ctxt => ('r,'bs) store => 'r page_ref => 'k key => tree_height => 'v value_t option" where
  "page_ref_key_to_v ctxt s0 r0 k0 n0 == (
    let m0 = page_ref_to_map ctxt s0 r0 n0 in
    Option.bind m0 (% m. m k0))"




section "key_to_ref, key_to_v"

(* NB we need some properties of these functions for correctness *)
datatype ('bs,'k,'r,'v) key_to_ref = Key_to_ref "('r,'k) node_frame => 'k key => 'r page_ref" 
(* datatype ('bs,'k,'r,'v) key_to_v = Key_to_v "('k,'v) leaf_frame => 'k key => 'v option"  (* may be no such v *) - there is only one impl! *)

definition key_to_v :: "('k,'v) leaf_frame => 'k key => 'v value_t option" where
  "key_to_v lf k == (lf |> lf_kvs |> map_of) k"

definition dest_key_to_ref :: "('bs,'k,'r,'v) key_to_ref => ('r,'k) node_frame => 'k key => 'r page_ref" where
  "dest_key_to_ref k2r == (case k2r of Key_to_ref f => f)"

(*
definition dest_key_to_v :: "('bs,'k,'r,'v) key_to_v => ('k,'v) leaf_frame => 'k key => 'v value_t option" where
  "dest_key_to_v k2v == (case k2v of Key_to_v f => f)"
*)

(**********)
record  ('bs,'k,'r,'v) ctxt1 =  "('bs,'k,'r,'v) ctxt" +
  key_to_ref :: "('bs,'k,'r,'v) key_to_ref"
(*  key_to_v :: "('bs,'k,'r,'v) key_to_v" *)


section "find"

(* find *)
record ('bs,'k,'r,'v) find_state_l =
  fsl_k :: "'k key"
  fsl_r :: "'r page_ref"
(*   fnd0_s :: "('r,'bs) store" *)

record ('bs,'k,'r,'v) find_state_r =
  fsr_r :: "'r page_ref"
  fsr_v :: "'v value_t option"
(*  fnd1_s :: "('r,'bs) store" *)

datatype ('bs,'k,'r,'v) find_state = Fs_l "('bs,'k,'r,'v) find_state_l" | Fs_r "('bs,'k,'r,'v) find_state_r"



definition fs_step :: "('bs,'k,'r,'v) ctxt1
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) 
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) option" where
  "fs_step ctxt1 s0fs0 == (
  let (s0,fs0) = s0fs0 in
  case fs0 of
  Fs_l fsl => (
    let r0 = (fsl|>fsl_r) in
    let k0 = (fsl|>fsl_k) in
    case (page_ref_to_frame (ctxt.truncate ctxt1) s0 r0) of 
    None => (Error |> rresult_to_option)  (* invalid page access *)
    | Some frm => (
      case frm of 
      Frm_I nf => (
        let k2r = ((ctxt1|>key_to_ref)|>dest_key_to_ref) in
        let r' = k2r nf k0 in
        Some(s0, Fs_l (fsl (| fsl_r := r' |))))
      | Frm_L lf => (
        let k2v = key_to_v in
        let v = k2v lf k0 in
        Some(s0, Fs_r (| fsr_r = r0, fsr_v = v |)))))
  | Fs_r fsr => (Error |> rresult_to_option))"  (* attempt to step Fs_r *)


section "fs_step as a function"

text "iterate the fs_step function n times"

(* FIXME in the following we may want to use a standard isabelle while construction *)
definition fs_step_as_fun :: "('bs,'k,'r,'v) ctxt1 
  => tree_height
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) 
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state)" where
  "fs_step_as_fun ctxt1 n0 s0fs0 == (
  let f0 = % x. x |> (fs_step ctxt1) |> dest_Some in
  (f0^^n0) s0fs0)"


section "wellformedness predicates"

(* FIXME obviously the following need to be filled in properly *)

fun wf_store:: "('bs,'k,'r,'v) ctxt1 => ('r,'bs) store => 'r page_ref => tree_height => bool" where
  "wf_store ctxt1 s0 r0 0 = is_Some (page_ref_to_tree (ctxt.truncate ctxt1) s0 r0 0)"
  | "wf_store ctxt1 s0 r0 (Suc n') = (
    let ctxt = ctxt.truncate ctxt1 in
    let valid_ctxt1_key_to_ref = (
     case page_ref_to_frame ctxt s0 r0 of
       Some (Frm_I(nf)) \<Rightarrow>
         let n = (nf|>nf_n) in
         let ks = (nf|>nf_ks) in
         let rs = (nf|>nf_rs) :: (nat => 'r page_ref) in
         let k2r :: (('r,'k) node_frame => 'k key => 'r page_ref)= (ctxt1 |> key_to_ref |> dest_key_to_ref) in
          (\<exists> m' \<le> n . ! k .
          (* the page_ref returned must be among the inodes page_refs *)
          (k2r nf k) = m'|>rs
          \<and>
          (* the key can be only in the subtree generated by the m' page_ref *)
          (page_ref_key_to_v ctxt s0 r0 k (Suc n') = page_ref_key_to_v ctxt s0 (m'|>rs) k (n'))) 
     | _ \<Rightarrow> False)
      in
      is_Some (page_ref_to_tree ctxt s0 r0 (Suc n'))
      \<and>
      valid_ctxt1_key_to_ref)      
  "

section "correctness of fs_step"

definition fs_step_invariant :: "('bs,'k,'r,'v) ctxt 
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state)
  => tree_height
  => 'v value_t option
  => bool" where
  "fs_step_invariant ctxt s0fs0 n0 v0 == (
    let (s0,fs0) = s0fs0 in
    case fs0 of
    Fs_l fsl => (
      let k0 = (fsl|>fsl_k) in
      let r0 = (fsl|>fsl_r) in
      let v' = page_ref_key_to_v ctxt s0 r0 k0 n0 in
      v' = v0)
    | Fs_r fsr => (
      let v' = (fsr|>fsr_v) in
      v' = v0))"
   
lemma fs_step_is_invariant: "
  ! (ctxt1::('bs,'k,'r,'v) ctxt1) s0 fs0 n0 v0.
  let r0 = (case fs0 of Fs_l fsl \<Rightarrow> fsl |> fsl_r | Fs_r fsr \<Rightarrow> fsr |> fsr_r ) in
  wf_store ctxt1 s0 r0 n0 
  --> (
  let ctxt = (ctxt.truncate ctxt1) in
  fs_step_invariant ctxt (s0,fs0) n0 v0 --> (
  let x = fs_step ctxt1 (s0,fs0) in
  case x of 
  None => True  (* if we are at a Fs_r, no further facts are available *)
  | Some (s',fs') => (
    (* n0 could be 0? but then fs' is Fs_r? *)
    fs_step_invariant ctxt (s',fs') (n0 - 1) v0)))"

apply (simp add:Let_def)
apply rule+
apply (case_tac n0)
 (* 0 *)
 apply (simp add:is_Some_def)
 apply (erule exE)
 apply (rename_tac frm)
 apply (simp add:fs_step_invariant_def)
 apply (case_tac "fs0")
  apply (rename_tac fsl)
  (* fs0 = Fs_l fsl*)
  apply simp
  apply (thin_tac "fs0 = ?x")
  apply (simp add:fs_step_def)
  apply (subgoal_tac "? r0. (fsl |> fsl_r) = r0") prefer 2 apply force
  apply (subgoal_tac "? k0. (fsl |> fsl_k) = k0") prefer 2 apply force
  apply (erule exE)+
  apply simp
  apply (subgoal_tac "? m_frm'. page_ref_to_frame (ctxt.truncate ctxt1) s0 r0 = m_frm'") prefer 2 apply force
  apply (erule exE)
  apply simp
  apply (case_tac "m_frm'")
   (* m_frm' = None *)
   apply simp
   
   apply (rename_tac frm')
   (* m_frm' = Some frm' *)
   apply simp
   apply (thin_tac "m_frm' = Some frm'")
   apply (case_tac "frm'")
    (* frm' = Frm_I _ *)
    apply (simp add:rev_apply_def rresult_to_option_def)

    (* frm' = Frm_L _ *)
    apply (simp add:rev_apply_def rresult_to_option_def fs_step_invariant_def page_ref_key_to_v_def 
      page_ref_to_map_def page_ref_to_kvs_def kvs_to_map_def key_to_v_def)

  (* fs0 = Fs_l fsl*)
  apply (simp add:fs_step_def)

 (* n0 = Suc n' *)
 apply (subgoal_tac "? ctxt. (ctxt.truncate ctxt1) = ctxt") prefer 2 apply force
 apply (erule exE)
 apply (simp add:is_Some_def)
 apply (erule conjE)+
 apply (erule exE)
 apply (rename_tac "tree")
 apply (subgoal_tac "? m_frm. page_ref_to_frame ctxt s0 (case fs0 of Fs_l fsl \<Rightarrow> fsl |> fsl_r | Fs_r fsr \<Rightarrow> fsr |> fsr_r) = m_frm") prefer 2 apply force
 apply (erule exE)
 apply simp
 apply (case_tac "m_frm")
  (* m_frm = None *)
  apply simp

  apply (rename_tac frm)
  (* m_frm = Some frm *)
  apply simp
  apply (case_tac fs0)
   prefer 2
   (* fs0 = Fs_r find_state_r_ext *)
   apply (simp add:fs_step_def)

   apply (rename_tac fsl)
   (* fs0 = Fs_l fsl*)
   apply (case_tac "frm") 
    prefer 2
    (* frm = Frm_L _*)
    apply simp

    apply (rename_tac nf)
    (* frm = Frm_I nf*)    
    apply (simp add:Let_def)
    apply (erule exE)+
    apply (case_tac " 0 < nf |> nf_n \<and>
             (\<forall>m\<le>nf |> nf_n.
                 m |> (nf |> nf_rs) |>
                 (\<lambda>r. case page_ref_to_frame ctxt s0 r of None \<Rightarrow> False | Some (Frm_I nf) \<Rightarrow> nf |> nf_n \<noteq> 0 | Some (Frm_L lf) \<Rightarrow> \<not> lf |> lf_kvs |> List.null)) \<and>
             (\<forall>m\<le>nf |> nf_n. m |> (nf |> nf_rs) |> (\<lambda>r. page_ref_to_tree ctxt s0 r nat) |> is_Some)")
    prefer 2
     (* prop = false *)
     apply simp

     (* prop = true *)
     apply simp
     apply (erule conjE)+
     apply (subgoal_tac "? r0 . fsl |> fsl_r = r0 ") prefer 2 apply force
     apply (subgoal_tac "? k0 . fsl |> fsl_k = k0 ") prefer 2 apply force
     apply (erule exE)+
     apply simp
     apply (drule_tac x="k0" in spec)
     apply (erule conjE)+
     apply (simp add:fs_step_def)
     apply (simp add:fs_step_invariant_def)
     apply (drule_tac t="v0" in sym)
     apply (simp add: rev_apply_def)
done
end