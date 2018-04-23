open aesWpTheory;

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
open bir_wp_simpTheory;

(* look at core/bir_expLib *)

val prop = (snd o dest_eq o concl) aes_wp_taut_thm;
val wp = List.nth((snd o strip_comb o snd o dest_comb) prop, 1);



fun writeFile filename content =
    let val fd = TextIO.openOut filename
        val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
        val _ = TextIO.closeOut fd
    in () end;

writeFile "/tmp/aaa.z3" "(declare-const a (_ BitVec 4)) (declare-const b (_ BitVec 4)) (assert (not (= (bvule a b) (bvsle a b)))) (check-sat) (get-model)";


writeFile "/tmp/aaa.z3" "(declare-const SP (_ BitVec 64)) (assert (not (and (= (bvand SP (_ bv3 64)) 0) true))) (check-sat) (get-model)";

open bir_expSyntax bir_immSyntax bir_envSyntax bir_imm_expSyntax bir_mem_expSyntax;

  fun bop_to_smt bop = if is_BIExp_And bop then
                               "and"
                          else if is_BIExp_Or bop then
                               "or"
                          else if is_BIExp_Xor bop then
                               "xor"
                          else
                               raise (ERR "bop_to_string" "don't know how to print BIR binop")
                          ;

  fun bbv_to_smt bop = if is_BIExp_And bop then
                               "bvand"
                          else if is_BIExp_Or bop then
                               "bvor"
                          else if is_BIExp_Xor bop then
                               "bvxor"
                          else if is_BIExp_Plus bop then
                               "bvadd"
                          else if is_BIExp_Minus bop then
                               "bvsub"
                          else if is_BIExp_Mult bop then
                               "bvmul"
                          else if is_BIExp_Div bop then
                               "bvdiv"
                          else if is_BIExp_SignedDiv bop then
                               "bvsdiv"
                          else if is_BIExp_Mod bop then
                               "bvmod"
                          else if is_BIExp_SignedMod bop then
                               "bvsmod"
                          else if is_BIExp_LeftShift bop then
                               "bvshl"
                          else if is_BIExp_RightShift bop then
                               "bvlshr"
                          else if is_BIExp_SignedRightShift bop then
                               "bvashr"
                          else
                               raise (ERR "bop_to_string" "don't know how to print BIR binop")
                          ;

  fun bpredop_to_smt bpredop = if is_BIExp_Equal bpredop then
                                       "="
                                  else if is_BIExp_NotEqual bpredop then
                                       "<>"
                                  else if is_BIExp_LessThan bpredop then
                                       "bvult"
                                  else if is_BIExp_SignedLessThan bpredop then
                                       "bvslt"
                                  else if is_BIExp_LessOrEqual bpredop then
                                       "bvule"
                                  else if is_BIExp_SignedLessOrEqual bpredop then
                                       "bvsle"
                                  else
                                       raise (ERR "bpredop_to_string" "don't know how to print BIR binpredop")
                                  ;


fun export_to_smt exp =
    if is_BExp_Const exp then
	if exp = ``BExp_Const (Imm1 1w)`` then ("true", ``:word1``)
	else if exp = ``BExp_Const (Imm1 0w)`` then ("false", ``:word1``)
	else 
	    let val (s,w) =(gen_dest_Imm o dest_BExp_Const) exp
	    in
		(String.concat[
		"(_ bv", 
		Arbnumcore.toString(wordsSyntax.dest_word_literal w), 
		" ", Int.toString s, ")"], type_of w)
	    end
    else if is_BExp_Den exp then
        ((fst o dest_BVar_string o dest_BExp_Den) exp, ``:word64``)
    else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
	  val e1 = (export_to_smt exp1)
	  val e2 = (export_to_smt exp2)
          val bpredopstr = if (snd e1) = ``:word1`` then bop_to_smt bop
			   else bbv_to_smt bop;
        in
	    (String.concat ["(", bpredopstr, " ", 
			   (fst e1), " ", 
			   (fst e2), ")"],
	     snd e1)
        end
    else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
	  val e1 = (export_to_smt exp1)
	  val e2 = (export_to_smt exp2)
          val bpredopstr = bpredop_to_smt bpredop;
        in
	    (String.concat ["(", bpredopstr, " ", 
			   (fst e1), " ", 
			   (fst e2), ")"],
	     ``:word1``)
        end
    else
	("?", ``:word1``)
;


val thm1 = SIMP_CONV std_ss [bir_wp_simpTheory.bir_exp_and_def] wp;
val wp1 = (snd o dest_eq o concl) thm1;


val pre = " (and (and (= (bvand SP_EL0 (_ bv3 64)) (_ bv0 64)) (bvugt SP_EL0 (_ bv33554432 64))) (bvult SP_EL0 (_ bv43554432 64)))";
(* val pre = " (= SP_EL0 (_ bv16777216 64) )"; *)

writeFile "/tmp/aaa.z3" (String.concat[
  "(declare-const SP_EL0 (_ BitVec 64)) \n",
  "(assert (not ",
  "(=>", pre,
  fst (export_to_smt wp1),
  ")", 
  "))\n",
  "(check-sat) (get-model)"]);


val exp = ``(BExp_Const (Imm64 3w))``;


