open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_wpTheory;

open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;

open bir_expLib;
open finite_mapSyntax;
open pairSyntax;

open bir_wp_simpTheory;

load "pairLib";


structure bir_wp_simpLib =
struct



  fun simp_extract goalterm =
    let
      val (prems, beval) = (dest_imp o snd o dest_forall) goalterm;
      val prem = (fst o dest_comb) prems;
      val term = (snd o dest_comb o fst o dest_comb o fst o dest_eq) beval;
    in
      (prem, term)
    end;

  fun is_bir_exp_subst term =
    let
      fun match_pat matchpat t = (let val _ = match_term matchpat t in (true) end) handle _ => (false);
    in
      match_pat ``bir_exp_subst substm e1`` term (* use mk_term!!! *)
    end;

  fun dest_bir_exp_subst term =
    let
      val substsm_var = mk_var ("substsm", ``:bir_var_t |-> bir_exp_t``);
      val e1_var = mk_var ("e1", ``:bir_exp_t``);
      val (substv, _) = match_term ``bir_exp_subst ^substsm_var ^e1_var`` term; (* use mk_term!!! *)
    in
      (subst substv substsm_var, subst substv e1_var)
    end;

  fun lookup_def def_str =
    let
      val (_, (def_thm, _)) = hd (DB.find def_str);
    in
      def_thm
    end;

  fun subsm_is_var_only subsm =
      if is_fempty subsm then true else
      let
        val (subsm1, ve) = dest_fupdate subsm;
        val e = (snd o dest_pair) ve;
      in
        (is_BExp_Den e) andalso (subsm_is_var_only subsm1)
      end;

  val bir_var_ss = rewrites (type_rws ``:bir_var_t``);
  val string_ss = rewrites (type_rws ``:string``);
  fun bir_wp_simp_CONV goalterm =
    let
      val (prem, term) = simp_extract goalterm;
      val get_concl_lhs = fst o dest_eq o concl;
      val get_concl_rhs = snd o dest_eq o concl;
      val thm =
        if is_const term then
          (* 1 - expand a const *)
          let
            val const_n = (fst o dest_const) term;
            val def_thm = lookup_def const_n;
            val thm_1 = REWRITE_CONV [def_thm] goalterm;
            val thm_1_rec = bir_wp_simp_CONV (get_concl_rhs thm_1);
          in
            TRANS thm_1 thm_1_rec
          end
        else if is_bir_exp_subst term then
          let
            val (subsm, e) = dest_bir_exp_subst term;
          in
            if subsm_is_var_only subsm then
              (* 2a - subst with vars in map only *)
              REFL goalterm
            else
              (* 2b - subst simplification *)
              REFL goalterm
          end
        else if is_BExp_BinExp term then
          let
            val (bop, e1, e2) = dest_BExp_BinExp term;
          in
            if is_BIExp_And bop then
              (* 3 - and simplification propagation *)
              let
                val thm_1 = SPECL [prem, e1, e2] bir_wp_simp_eval_and_thm;
                val (term_2a, term_2b) = (dest_conj o snd o dest_eq o concl) thm_1;
                val thm_2a = bir_wp_simp_CONV term_2a handle UNCHANGED => REFL term_2a; (* poor and quick solution *)
                val thm_2b = bir_wp_simp_CONV term_2b handle UNCHANGED => REFL term_2b;
                val thm_2_lhs = (mk_conj (term_2a, term_2b));
                val thm_2 = REWRITE_CONV [Once thm_2a, Once thm_2b] thm_2_lhs handle UNCHANGED => REFL thm_2_lhs;
                val thm_3 = REWRITE_CONV [GSYM bir_wp_simp_eval_and_thm] (get_concl_rhs thm_2);
                val thm = TRANS (TRANS thm_1 thm_2) thm_3;
              in
                thm
              end
            else if is_BIExp_Or bop then
              (* 3 - imp simplification propagation *)
              let
                val thm_1 = SPECL [prem, e1, e2] bir_wp_simp_eval_and_thm;
                val (term_2, term_3) = (dest_conj o snd o dest_eq o concl) thm_1;
                val thm_2 = bir_wp_simp_CONV term_2; (* catch UNCHANGED *)
                val thm_3 = bir_wp_simp_CONV term_3;
                val thm = REWRITE_CONV [Once thm_1, Once thm_2, Once thm_3, GSYM bir_wp_simp_eval_and_thm] goalterm;
                val _ = print "call me imp\r\n";
              in
                thm
              end
            else
              (* other binop, we don't touch this *)
              raise UNCHANGED
          end
        else
          (* other expression, we don't touch this *)
          raise UNCHANGED
        ;
    in
      (* check goalterm matching lhs *)
      if (goalterm = (get_concl_lhs thm)) then
        thm
      else
        raise (ERR "bir_wp_simp_CONV" "term mismatch, some unexpected error, debug me")
    end;

(*
         else if is_bir_exp_subst term then
           let
             val (substs_all, e) = dest_bir_exp_subst term;
             val (substs, substs_update) = dest_fupdate substs_all;
             val (var, t1) = dest_pair substs_update;

             val (var_n, var_t) = dest_BVar_string var;
             val pass_var_n = "pass_v_" ^ var_n ^ "_" ^ "1";
             val pass_var = mk_BVar_string (pass_var_n, var_t); (* mk_var (, ``:bir_var_t``)*)
             val thm_1_wa = SPECL [pass_var, prem, substs, var, t1, e] bir_wp_simp_eval_subst_thm;

             val cond1 = (fst o dest_imp o concl) thm_1_wa;
             val cond2 = (fst o dest_imp o snd o dest_imp o concl) thm_1_wa;
             val cond1_thm = prove (cond1, cheat);
             val cond2_thm = prove (cond2, cheat);
             val thm_1 = MP (MP thm_1_wa cond1_thm) cond2_thm;
             val thm_1_term = (snd o dest_eq o concl) thm_1;
             val (prem_1, term_1) = simp_extract thm_1_term;

             (* apply substitution, here can be issues coming up because of the Once exp_subst, not so clean... *)
             val term1_appl_subst_thm = SIMP_CONV (std_ss++bir_var_ss++string_ss) [bir_exp_subst_def, bir_exp_subst_var_def, finite_mapTheory.FLOOKUP_EMPTY, finite_mapTheory.FLOOKUP_UPDATE, bir_exp_subst_update_exec_thm, Once bir_exp_subst_bir_exp_subst_thm] term_1;
             val thm_1 = TRANS thm_1 (REWRITE_CONV [term1_appl_subst_thm] ((snd o dest_eq o concl) thm_1));

             (* turn into implication of bir_eval_exps *)
             val thm_1 = TRANS thm_1 (REWRITE_CONV [bir_wp_simp_eval_imp_thm] ((snd o dest_eq o concl) thm_1));

             (* then recursive call *)
             val (term_2) = (snd o dest_eq o concl) thm_1;
             val thm_2 = simp_wp_CONV term_2; (* catch UNCHANGED *)
             (* val thm_2 = REFL term_2 *)

             (* and revert to standard prem ==> bil_eval shape *)
             val thm = REWRITE_CONV [(TRANS thm_1 thm_2), GSYM bir_wp_simp_eval_imp_thm] goalterm;
             (*val thm = TRANS thm (REWRITE_CONV [GSYM bir_wp_simp_eval_and_thm] ((snd o dest_eq o concl) thm)*)
             val _ = print "call me subst\r\n";
           in
             thm
           end
*)










(*
(* =================== TESTING ========================================= *)
val i = 1;
val lbl_str = List.nth (lbl_list, (List.length lbl_list) - 2 - i);

val def_thm = lookup_def ("bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str);
val term = (snd o dest_eq o concl) def_thm;


(* include this in the beginning as expansion step from definition, i.e., replace ^term in goalterm by aes_wps variable and propagate definition theorems accordingly *)
val aes_wp_def = Define `aes_wp = ^term`;
val aes_wp_term = ``aes_wp``;
(*
val aes_wp_term = ``(bir_exp_subst
               (FEMPTY |+
                (BVar "R0" (BType_Imm Bit64),
                 BExp_Cast BIExp_UnsignedCast
                   (BExp_Load
                      (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 76w))) BEnd_LittleEndian
                      Bit32) Bit64))
               bir_wp_comp_wps_iter_step2_wp_0x400978w)``;
*)

val btautology = ``BExp_Const (Imm1 1w)``;
val prem_init = ``(\s. (bir_eval_exp ^btautology s) = bir_val_true)``;
val goalterm = ``!s. (^prem_init s) ==> (bir_eval_exp ^aes_wp_term s = bir_val_true)``;
(*
fun expandDef defname goalterm =
  let
    val def_thm = lookup_def defname;
  in
    (snd o dest_eq o concl) (REWRITE_CONV [def_thm] goalterm)
  end;

val goalterm = expandDef "aes_wp" goalterm;
*)


val bir_wp_simp_eval_imp_spec_thm = ((SIMP_RULE std_ss [EVAL ``^prem_init s``]) o (SPEC prem_init) o GSYM) bir_wp_simp_eval_imp_thm;

val simp_thm = bir_wp_simp_CONV goalterm;
val simp_thm = TRANS (GSYM (REWRITE_CONV [EVAL ``^prem_init s``] ((fst o dest_eq o concl) simp_thm))) simp_thm;
val simp_thm = TRANS simp_thm (SIMP_CONV std_ss [boolTheory.BETA_THM, bir_wp_simp_eval_imp_spec_thm] ((snd o dest_eq o concl) simp_thm));

*)


end
