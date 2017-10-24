open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = print_with_style [Bold, Underline] "Lifting gcd-aarch64.da\n";

val (region_map, gcd_sections) = read_disassembly_file (fn n => n = "gcd") "gcd-aarch64.da"

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
  gcd_sections

val _ = print "\n\n\n";
val _ = print_with_style [Bold, Underline] "Lifting gcd-m0.da\n";
val (region_map, gcd_sections) = read_disassembly_file (fn n => n = "gcd") "gcd-m0.da"

val (thm_m0, errors) = bmil_m0_LittleEnd_Process.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x20000))
  gcd_sections

val _ = print "\n\n";

val _ = new_theory "gcd_code";
val _ = save_thm ("gcd_arm8_program_THM", thm_arm8);
val _ = save_thm ("gcd_m0_program_THM", thm_m0);
val _ = export_theory();