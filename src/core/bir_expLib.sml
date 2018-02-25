open bir_expSyntax bir_immSyntax bir_envSyntax bir_imm_expSyntax bir_mem_expSyntax;

structure bir_expLib =
struct


  val err_str = "$$$$$$$$";

  fun castt_to_string castt = if is_BIExp_LowCast castt then
                                   "CL"
                              else if is_BIExp_HighCast castt then
                                   "CH"
                              else if is_BIExp_SignedCast castt then
                                   "CS"
                              else if is_BIExp_UnsignedCast castt then
                                   "CU"
                              else
                                   err_str
                              ;

  fun bop_to_string bop = if is_BIExp_And bop then
                               "&"
                          else if is_BIExp_Or bop then
                               "|"
                          else if is_BIExp_Xor bop then
                               "^"
                          else if is_BIExp_Plus bop then
                               "+"
                          else if is_BIExp_Minus bop then
                               "-"
                          else if is_BIExp_Mult bop then
                               "*"
                          else if is_BIExp_Div bop then
                               "/"
                          else if is_BIExp_SignedDiv bop then
                               "s/"
                          else if is_BIExp_Mod bop then
                               "%"
                          else if is_BIExp_SignedMod bop then
                               "s<<"
                          else if is_BIExp_LeftShift bop then
                               "<<"
                          else if is_BIExp_RightShift bop then
                               ">>"
                          else if is_BIExp_SignedRightShift bop then
                               "s>>"
                          else
                               err_str
                          ;

  fun bpredop_to_string bpredop = if is_BIExp_Equal bpredop then
                                       "=="
                                  else if is_BIExp_NotEqual bpredop then
                                       "<>"
                                  else if is_BIExp_LessThan bpredop then
                                       "<"
                                  else if is_BIExp_SignedLessThan bpredop then
                                       "s<"
                                  else if is_BIExp_LessOrEqual bpredop then
                                       "<="
                                  else if is_BIExp_SignedLessOrEqual bpredop then
                                       "s<="
                                  else
                                       err_str
                                  ;

  fun uop_to_string uop = if is_BIExp_ChangeSign uop then
                               "-"
                          else if is_BIExp_Not uop then
                               "!"
                          else
                               err_str
                          ;

  fun endi_to_string endi = if is_BEnd_BigEndian endi then
                                 "B"
                            else if is_BEnd_LittleEndian endi then
                                 "L"
                            else if is_BEnd_NoEndian endi then
                                 "N"
                            else
                                 err_str
                            ;


  fun bir_exp_to_string exp =
      if is_BExp_Const exp then
        (term_to_string o snd o gen_dest_Imm o dest_BExp_Const) exp
      else if is_BExp_Den exp then
        ("_" ^ ((fst o dest_BVar_string o dest_BExp_Den) exp))
      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val casttstr = castt_to_string castt;
          val expstr = bir_exp_to_string exp;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          ("(" ^ expstr ^ ":" ^ casttstr ^ szstr ^ ")")
        end
      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val uopstr = uop_to_string uop;
          val expstr = bir_exp_to_string exp;
        in
          ("(" ^ uopstr ^ " " ^ expstr ^ ")")
        end
      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val bopstr = bop_to_string bop;
          val exp1str = bir_exp_to_string exp1;
          val exp2str = bir_exp_to_string exp2;
        in
          ("(" ^ exp1str ^ " " ^ bopstr ^ " " ^ exp2str ^ ")")
        end
      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val bpredopstr = bpredop_to_string bpredop;
          val exp1str = bir_exp_to_string exp1;
          val exp2str = bir_exp_to_string exp2;
        in
          ("(" ^ exp1str ^ " " ^ bpredopstr ^ " " ^ exp2str ^ ")")
        end
      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
          val expcstr = bir_exp_to_string expc;
          val exptstr = bir_exp_to_string expt;
          val expfstr = bir_exp_to_string expf;
        in
          ("(if " ^ expcstr ^ " then " ^ exptstr ^ " else " ^ expfstr ^ ")")
        end
      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val expmstr = bir_exp_to_string expm;
          val expadstr = bir_exp_to_string expad;
          val endistr = endi_to_string endi;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          ("(" ^ expmstr ^ ":" ^ endistr ^ szstr ^ "[" ^ expadstr ^ "])")
        end
      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val expmstr = bir_exp_to_string expm;
          val expadstr = bir_exp_to_string expad;
          val endistr = endi_to_string endi;
          val expvstr = bir_exp_to_string expv;
        in
          ("(" ^ expmstr ^ ":" ^ endistr ^ "[" ^ expadstr ^ "] = " ^ expvstr ^ ")")
        end
      else
        err_str;


  fun bir_exp_pretty_print exp = print ((bir_exp_to_string exp) ^ "\r\n");

(*
val exp = ``BExp_Const (Imm64 0x400574w)``
val exp = ``BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))``
val exp = ``(BExp_Cast BIExp_LowCast
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)``;

val exp = ``(BExp_UnaryExp BIExp_ChangeSign (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 112w))))``;
val exp = ``(BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 112w)))``;
val exp = ``(BExp_BinPred BIExp_LessThan
                  (BExp_BinExp BIExp_Plus
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 112w)))
                     (BExp_Const (Imm64 24w))) (BExp_Const (Imm64 0w)))``;
val exp = ``(BExp_IfThenElse (BExp_Den (BVar "R1" (BType_Imm Bit1))) (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) (BExp_Den (BVar "R2" (BType_Imm Bit64))))``;
val exp = ``(BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)``;
val exp = ``(BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))) BEnd_LittleEndian (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 112w))))``;



val _ = bir_exp_pretty_print exp;
*)

end
