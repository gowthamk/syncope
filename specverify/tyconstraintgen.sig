signature TY_CONSTRAINT_GEN_STRUCTS = 
sig
  structure VE : VAR_ENV
  structure ANormalCoreML : A_NORMAL_CORE_ML
  sharing VE.Var = ANormalCoreML.Var
  sharing VE.SpecLang.Var = ANormalCoreML.Var
  sharing VE.SpecLang.TypeDesc = ANormalCoreML.TypeDesc
  sharing VE.SpecLang.Var = ANormalCoreML.Var
end
signature TY_CONSTRAINT_GEN = 
sig
  include TY_CONSTRAINT_GEN_STRUCTS
  structure TyCst : TY_CST
  (*
   * Returns all type constraints that need to hole for the expression
   * to have the required type under the given VE.
   *)
  val doIt : VE.t * ANormalCoreML.Exp.t * VE.SpecLang.RefinementType.t 
      -> TyCst.t
end
