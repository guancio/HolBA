open HolKernel Parse;

open bir_wpTheory bir_wpLib;




val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;



val aes_program_def = Define `
     aes_program =
		           (BirProgram
              [<|bb_label :=
                   BL_Address_HC (Imm64 0x400570w)
                     "D101C3FF (sub sp, sp, #0x70)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 112w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400574w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400574w)
                     "F9000FE0 (str x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400578w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400578w)
                     "B90017E1 (str w1, [sp,#20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64
							 0x40057Cw)))|>
	      ])`;


val aes_post_def = Define `
      aes_post = (BExp_BinPred BIExp_Equal (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) (BExp_Const (Imm64 112w)))
`;

val aes_ls_def = Define `
      aes_ls = \x.(x = (BL_Address (Imm64 0x400578w)))
`;

val aes_wps_def = Define `
      aes_wps = (FEMPTY |+ (BL_Address (Imm64 0x400578w), aes_post))
`;



val program = ``aes_program``;
val post = ``aes_post``;
val ls = ``aes_ls``;
val wps = ``aes_wps``;

val defs = [aes_program_def, aes_post_def, aes_ls_def, aes_wps_def];







(* wps_bool_sound_thm for initial wps *)
val wps_bool_sound_thm = init_wps_bool_sound_thm (program, post, ls) wps defs;




(* prepare "problem-static" part of the theorem *)
val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val prog_thm = proc_step0 reusable_thm (program, post, ls) defs;



(* one step label prep *)
val label = ``BL_Address_HC (Imm64 0x400574w) "XZY"``;
val prog_l_thm = proc_step1 label prog_thm (program, post, ls) defs;




(* one step wps soundness *)
val (wps1, wps1_bool_sound_thm) = proc_step2 (wps, wps_bool_sound_thm) (prog_l_thm) ((program, post, ls), (label)) defs;

(* to make it readable or speedup by incremental buildup *)
val aes_wps1_def = Define `
      aes_wps1 = ^wps1
`;
val wps1_bool_sound_thm_readable = REWRITE_RULE [GSYM aes_wps1_def] wps1_bool_sound_thm;





(* and the recursive procedure *)
val prog_term = (snd o dest_comb o concl) aes_program_def;

val (wps1, wps1_bool_sound_thm) = recursive_proc prog_term prog_thm (wps, wps_bool_sound_thm) (program, post, ls) defs;

(* to make it readable or speedup (copy and paste from a few lines above) *)
val wps1_bool_sound_thm_readable_rec = REWRITE_RULE [GSYM aes_wps1_def] wps1_bool_sound_thm;




