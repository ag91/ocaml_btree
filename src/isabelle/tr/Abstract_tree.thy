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
          let prop = (! (m::nat). m <= n --> m |> rs |> f0 |> is_Some) in (* we use \<le> because the number of subtrees to create is n (number of keys) + 1 --since we start from index 0, it is just n*)
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
  "wf_store ctxt1 s0 r0 0 = (
      case page_ref_to_frame (ctxt.truncate ctxt1) s0 r0 of 
      None => False 
      | Some frm => (
        case frm of 
        Frm_L(lf) => True
        | _ => False))"
  | "wf_store ctxt1 s0 r0 (Suc n') = (
      case page_ref_to_frame (ctxt.truncate ctxt1) s0 r0 of
      None => False  (* attempt to access missing page *)
      | Some frm => (
        case frm of 
        Frm_I(nf) => (
          let n = (nf|>nf_n) in
          let ks = (nf|>nf_ks) :: (nat => 'k key) in
          let rs = (nf|>nf_rs) :: (nat => 'r page_ref) in
          let f0 = (% r. wf_store ctxt1 s0 r n') :: ('r page_ref => bool) in
          let not_empty_frames =
            let not_empty = (% r.
              (case page_ref_to_frame (ctxt.truncate ctxt1) s0 r of
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
          let valid_ctxt1_key_to_ref =
             let k2r :: (('r,'k) node_frame => 'k key => 'r page_ref)= (ctxt1 |> key_to_ref |> dest_key_to_ref) in
             (\<exists> m' \<le> n . ! k .
             (k2r nf k) = m'|>rs)
          in
          (* check that frames are not empty *)
          not_empty_frames
          \<and>
          (* check that key_to_ref returns a ref in rs *)
          valid_ctxt1_key_to_ref
          \<and>
          (* all subframes must be wf*)
          (! (m::nat). m <= n --> m |> rs |> f0))
        | Frm_L(_) => False))  (* found Frm_L but tree_height was not 0 *)
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


lemma wf_store_tree_is_some :
"! (ctxt1::('bs,'k,'r,'v) ctxt1) s0 fs0 v0 r0.
  wf_store ctxt1 s0 r0 n0 -->
  is_Some (page_ref_to_tree (ctxt.truncate ctxt1) s0 r0 n0)
"
apply rule+
apply (induct n0)
 (* 0 *)
 
 apply (simp add:Let_def)
 apply (case_tac "page_ref_to_frame (ctxt.truncate ctxt1) s0 r0")
  (* page_ref_to_frame = None *)
  apply simp

  apply (rename_tac frm)
  (* page_ref_to_frame = Some frm *)
  apply (case_tac frm)
   (* frm = Fr_I *)
   apply simp
   
   (* frm = Fr_L *)
   apply (simp add:is_Some_def)

 (* Suc n0 *)
 apply (simp add:Let_def)
 apply (case_tac "page_ref_to_frame (ctxt.truncate ctxt1) s0 r0")
  (* none *)
  apply simp

  apply (rename_tac frm)
  (* Some frm *)
  apply (case_tac frm)
   defer
   apply simp

   (* frm = Frm_I nf*)
   apply (simp add:Let_def rev_apply_def is_Some_def)
done
   
lemma fs_step_is_invariant: "
  ! (ctxt1::('bs,'k,'r,'v) ctxt1) s0 fs0 n0 v0.
  let r0 = (case fs0 of Fs_l fsl \<Rightarrow> fsl_r fsl | Fs_r fsr \<Rightarrow> fsr_r fsr) in
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
(*
apply (simp add:Let_def)
apply rule+
apply (case_tac n0)
 (* n0 = 0 *)
 apply (simp add:fs_step_invariant_def)
 apply (case_tac fs0)
  (* fs0 = Fs_l find_state_l_ext *)
  apply (rename_tac fsl)
  apply (simp add:page_ref_key_to_v_def page_ref_to_map_def page_ref_to_kvs_def rev_apply_def)
  apply (case_tac "page_ref_to_frame (ctxt.truncate ctxt1) s0 (fsl_r fsl)")
   (*page_ref_to_frame = None *)
   apply simp

   (* page_ref_to_frame = Some a*)
   apply (rename_tac frm)
   apply (case_tac frm)
    (* frm = Frm_I node_frame_ext *)
    apply simp

    (* frm = Frm_L leaf_frame_ext *)
    apply (simp add:fs_step_def Let_def rev_apply_def fs_step_invariant_def)
    apply (simp add:key_to_v_def rev_apply_def kvs_to_map_def)

  (* fs0 = Fs_l find_state_l_ext *)
  apply (simp add:fs_step_def)

 apply (rename_tac n')
 (* n0 = Suc n'*)
 apply (case_tac fs0)
 prefer 2
  apply (simp add:fs_step_def)

  apply (rename_tac fsl)
  (* fs0 = Fs_l fsl *)
  apply (simp)
  (* let's remove useless page_ref_to_frame cases *)
  apply (case_tac "page_ref_to_frame (ctxt.truncate ctxt1) s0 (fsl_r fsl)")
   (* none *)
   apply simp

   apply (rename_tac frm)
   (* page_ref_to_frame = Some frm*)
   apply (case_tac frm)
    prefer 2
    (* frm = Frm_L *)
    apply simp

    apply (rename_tac nf)
    (* frm = Frm_I nf *)
    apply (simp add:fs_step_def Let_def rev_apply_def)
    apply (thin_tac "n0 = ?x")
    apply (thin_tac "fs0 = ?x")
    apply (thin_tac "frm = ?x")
    apply (erule conjE)+
    apply (simp add:fs_step_invariant_def)
    apply (subgoal_tac "\<exists> r . fsl |> fsl_r = r") prefer 2 apply force
    apply (subgoal_tac "\<exists> k . fsl |> fsl_k = k") prefer 2 apply force
    apply (erule exE)+
    apply (erule conjE)+
    apply (subgoal_tac "fsl_r fsl = r") prefer 2 apply (force simp add:rev_apply_def)
    apply (subgoal_tac "fsl\<lparr>fsl_r := nf_rs nf m'\<rparr> |> fsl_r = nf_rs nf m'") prefer 2 apply (simp add:rev_apply_def)
    apply (subgoal_tac "(fsl\<lparr>fsl_r := nf_rs nf m'\<rparr> |> fsl_k) = k") prefer 2 apply (simp add:rev_apply_def)
    apply (subgoal_tac "\<exists> ctxt . (ctxt.truncate ctxt1) = ctxt") prefer 2 apply force
    apply (erule exE)
    apply (drule_tac t="v0" in sym)
    apply simp
    apply (thin_tac "v0=?x")
    apply (thin_tac "fsl_r fsl = r")
    apply (simp add:page_ref_key_to_v_def page_ref_to_map_def page_ref_to_kvs_def)
    apply (simp add:Let_def rev_apply_def)
    apply (case_tac "\<forall>m\<le>nf_n nf. is_Some (page_ref_to_tree ctxt s0 (nf_rs nf m) n')")
     prefer 2
     (*\<not> (\<forall>m\<le>nf_n nf. is_Some (page_ref_to_tree ctxt s0 (nf_rs nf m) n')) *)
     (*this is false for wf: all subtrees must be Some*)
     apply (force simp add:wf_store_tree_is_some)

     (* \<forall>m\<le>nf_n nf. is_Some (page_ref_to_tree ctxt s0 (nf_rs nf m) n') *)
     apply simp
     apply (drule_tac x="m'" in spec) back back
     apply (simp add:rev_apply_def)
     apply (subgoal_tac "\<exists> tree_with_k . page_ref_to_tree ctxt s0 (nf_rs nf m') n' = Some tree_with_k") prefer 2 apply (force simp add:is_Some_def)
     apply (erule exE)+
     apply simp
     apply (thin_tac "is_Some (Some tree_with_k)")
     (* we again need to show that a singular step is equal to the whole recursion*)
      apply (force intro:FIXME)
*)
      

  apply (simp add:Let_def)
  apply(rule)+
  apply(subgoal_tac "? x. fs_step ctxt1 (s0, fs0) = x")
   prefer 2
   apply(force intro: FIXME)
  apply(erule exE)
  apply(simp add: Let_def)
  apply(case_tac x)
   (* none *)
   apply(force)

   (* x = Some a *)
   apply(simp)
   apply(subgoal_tac "? s' fs'. a=(s',fs')")
    prefer 2
    apply(force intro: FIXME)
   apply(erule exE)+
   apply(simp)
   apply(simp add: fs_step_def)
   apply(case_tac fs0)
    prefer 2
    apply(force)
   (* fs0 = Fs_l find_state_l_ex *)
   apply(simp)
   apply(rename_tac "fsl")
   apply(subgoal_tac "? r0. (fsl|>fsl_r) = r0")
    prefer 2 apply(force)
   apply(subgoal_tac "? k0. (fsl|>fsl_k) = k0 ")
    prefer 2 apply(force)
   apply(erule exE)+
   apply(case_tac " (page_ref_to_frame (ctxt.truncate ctxt1) s0 r0)")
    apply(force)

    (*  (page_ref_to_frame (ctxt.truncate ctxt1) s0 r0) = Some r' *)
    apply(rename_tac frm')
    apply(simp)
    apply(case_tac frm')
     (**********)
     (* frm' = Frm_I node_frame_ext *)
     apply(rename_tac nf)
     apply(simp)
     apply(elim conjE)
     apply(drule_tac s=s0 in sym)
     apply(simp)
     apply(thin_tac "s' = s0")
     apply(thin_tac "a = ?x")
     apply(thin_tac "fs0 = ?x")
     apply(thin_tac "frm' = ?x")
     apply(thin_tac "x=?x")
     apply(subgoal_tac "? fsl'. (fsl\<lparr>fsl_r := (ctxt1 |> key_to_ref |> dest_key_to_ref) nf k0\<rparr>) = fsl'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(subgoal_tac "? r'. (ctxt1 |> key_to_ref |> dest_key_to_ref) nf k0 = r'")
      prefer 2 apply(force)
     apply(erule exE)
     (* note how this goal is concise and readable *)
     apply(simp add: fs_step_invariant_def)
     apply(drule_tac t="fs'" in sym)
     apply(simp)
     apply(thin_tac "fs' = ?x")
     apply(drule_tac t="fsl'" in sym)
     apply(simp)
     apply(subgoal_tac "fsl\<lparr>fsl_r := r'\<rparr> = (| fsl_k = k0, fsl_r = r' |)") prefer 2 apply (metis (full_types) find_state_l.surjective find_state_l.update_convs(2) old.unit.exhaust rev_apply_def) 
     apply(thin_tac "fsl' = fsl\<lparr>fsl_r := r'\<rparr> ")
     apply(simp)
     apply(simp add: rev_apply_def)
     apply(simp add: page_ref_key_to_v_def)
     (* page_ref_to_map could be none or some *)
     apply(subgoal_tac "? m0. (page_ref_to_map (ctxt.truncate ctxt1) s0 r0 n0) = m0")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(case_tac m0)
      (* m0 = None *)
      apply (simp add: page_ref_to_map_def page_ref_to_kvs_def rev_apply_def)
      apply (subgoal_tac "\<exists> tree. page_ref_to_tree (ctxt.truncate ctxt1) s0 r0 n0  = Some tree")
       prefer 2
       apply (insert wf_store_tree_is_some)
       apply (force simp add:is_Some_def)
      apply (erule exE)
      apply simp

      (* m0 = Some a *)
      apply(rename_tac m1)
      apply(simp)
      apply(thin_tac "m0 = ?x")
      apply(subgoal_tac "? m0'.  (page_ref_to_map (ctxt.truncate ctxt1) s0 r' (n0 - Suc 0)) = m0'")
       prefer 2 apply(force)
      apply(erule exE)
      apply(simp)
      apply(case_tac "m0'")
       (* none - ruled out because m0 is_Some --> m0' is_Some *)
       apply (simp add:page_ref_to_map_def page_ref_to_kvs_def rev_apply_def)
       apply (erule exE)
       apply (erule conjE)
       apply (case_tac "page_ref_to_tree (ctxt.truncate ctxt1) s0 r0 n0",simp)
       apply simp
       apply (case_tac n0)
        apply simp

        (*here m0' should not be None, and this because page_ref_to_tree (ctxt.truncate ctxt1) s0 r' (n0 - Suc 0) is None
          while page_ref_to_tree (ctxt.truncate ctxt1) s0 r0 n0 is Some
        *)
        apply (thin_tac "(\<And>n0. \<forall>ctxt1 s0 r0. wf_store ctxt1 s0 r0 n0 \<longrightarrow> is_Some (page_ref_to_tree (ctxt.truncate ctxt1) s0 r0 n0))")
        apply (subgoal_tac "\<exists> tree . page_ref_to_tree (ctxt.truncate ctxt1) s0 r' (n0 - Suc 0) = Some tree")
        prefer 2
         apply (simp add:Let_def)
         apply (case_tac "\<not>(\<forall>m\<le>nf |> nf_n. m |> (nf |> nf_rs) |> (\<lambda>r. page_ref_to_tree (ctxt.truncate ctxt1) s0 r nat) |> is_Some)")
          apply simp

          apply (simp add:rev_apply_def)
          (* we can show that
            dest_key_to_ref (key_to_ref ctxt1) nf k0 = r' belongs to the rs of the inode
            by using (\<exists>m'\<le>nf_n nf. \<forall>k. dest_key_to_ref (key_to_ref ctxt1) nf k = nf_rs nf m')
          *)
          apply (erule conjE)+
          apply (erule exE)
          apply simp
          apply (erule conjE)
          apply (drule_tac x="m'" in spec)
          apply (simp add:is_Some_def)
        apply force

       (* m0' = Some a *)
       apply(rename_tac "m1'")
       apply(simp)
       apply(thin_tac "m0'=?x")
       (* m1 k0 = v0 --> m1' k0 = v0 ; this holds by wellformedness of key_to_ref *)
       apply(force intro:FIXME)


     (* frm' = Frm_L leaf_frame_ext - easy case? *)
     apply(rename_tac lf)
     apply(simp)
     apply(elim conjE)
     apply(drule_tac s=s0 in sym)
     apply(simp)
     apply(thin_tac "s' = s0")
     apply(thin_tac "a = ?x")
     apply(thin_tac "fs0 = ?x")
     apply(thin_tac "frm' = ?x")
     apply(thin_tac "x=?x")
     (* we have got to a leaf, and at frm' we return Fs_r *)
     apply(subgoal_tac "? fsr'.  \<lparr>fsr_r = r0, fsr_v = key_to_v lf k0\<rparr> = fsr'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(subgoal_tac "? v'. key_to_v lf k0 = v'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp add: fs_step_invariant_def)
     apply(drule_tac t="fs'" in sym)
     apply(simp)
     apply(thin_tac "fs' = ?x")
     apply(drule_tac t="fsr'" in sym)
     apply(simp)
     apply(thin_tac "fsr' = ?x")
     apply(simp)
     apply(simp add: rev_apply_def)
     apply(simp add: page_ref_key_to_v_def)
     (* page_ref_to_map could be none or some *)
     apply(subgoal_tac "? m0. (page_ref_to_map (ctxt.truncate ctxt1) s0 r0 n0) = m0")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(case_tac m0)
      (* m0 = None *)
      apply(simp)
      (* the map at r0 is none ; but we have a leaf frame; contradiction *)
      apply(simp add: page_ref_to_frame_def)
      apply(case_tac "ref_to_page s0 r0") apply(force)
      apply(simp)
      apply(rename_tac p0)
      (*  ref_to_page s0 r0 = Some p0 *)
      apply(simp add: page_ref_to_map_def)
      apply(case_tac "page_ref_to_kvs (ctxt.truncate ctxt1) s0 r0 n0") 
       (* none *)
       apply(simp)
       apply(simp add: ref_to_page_def)
       apply(simp add: page_ref_to_kvs_def)
       apply(simp add: rev_apply_def)
       apply(case_tac "page_ref_to_tree (ctxt.truncate ctxt1) s0 r0 n0")
        (* none *)
        (* page_ref_to_tree defined by primrec *)
        apply(case_tac n0)
         apply(simp)
         apply(simp add: page_ref_to_frame_def)
         apply(force simp add: ref_to_page_def rev_apply_def)

         (* n0 = suc nat *)
         apply(rename_tac n0')
         apply(simp)
         apply(simp add: page_ref_to_frame_def)
         apply(simp add: ref_to_page_def rev_apply_def)

        (* page_ref_to_tree = Some a *)
        apply(rename_tac t0)
         apply(case_tac n0)
          apply(force)

          (* n0 = suc nat *)
          apply(rename_tac n0')
          apply(force)

       (* page_ref_to_kvs = Some a *)
       apply(rename_tac kvs)
       apply(simp)
       (* but m0 = none, so can't have kvs = some *)
       apply(force simp add:rev_apply_def)

      (* m0 = some a *)
      apply(rename_tac m1)
      apply(simp)
      apply(thin_tac "m0 = ?x")
      apply(simp)
      apply(simp add: page_ref_to_map_def)
      apply(simp add: rev_apply_def)
      apply(elim exE conjE)
      apply(simp add: page_ref_to_kvs_def rev_apply_def)
      apply(case_tac n0)
       (* 0 *)
       apply(simp)
       apply(simp add: rev_apply_def)
       apply(simp add: kvs_to_map_def)
       apply(drule_tac t=z in sym)
       apply(simp)
       apply(thin_tac "z=?x")
       apply(subgoal_tac "fsl = (| fsl_k = k0, fsl_r = r0 |)") prefer 2 apply(force)
       apply(simp)
       apply(simp add:page_ref_to_frame_def)
       apply(case_tac "ref_to_page s0 r0") apply(force)
       apply(rename_tac p0)
       apply(simp)
       apply(simp add: ref_to_page_def)
       apply(subgoal_tac "? kvs. lf = (| lf_kvs=kvs |)") prefer 2 apply (metis leaf_frame.cases)  
       apply(elim exE)
       apply(simp)
       apply(thin_tac "lf=?x")
       apply(thin_tac "fsl=?x")
       apply(thin_tac "n0=0")
       apply(clarsimp)
       apply(force simp add: key_to_v_def rev_apply_def)

       (* suc - should be a contradiction with leaf frame *)
       apply(rename_tac n0')
       apply(force)

  done

end