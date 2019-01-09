signature HolBACoreSimps =
sig
   include Abbrev

   (* Rewrite rules for all the types defined as part of the HolBIR formalisation. *)
   val bir_TYPES_ss : simpLib.ssfrag;

   (* Simple rewrites *)
   val bir_SIMPLE_REWRS_ss : simpLib.ssfrag

   (* All holBA stuff *)
   val holBACore_ss : simpLib.ssfrag
end
