signature TY_CONSTRAINT_GEN_STRUCTS = 
sig
  structure VE : VAR_ENV
  structure TyCst : TY_CST
  structure ANormalCoreML : A_NORMAL_CORE_ML
  sharing VE.Var = ANormalCoreML.Var
  sharing TyCst.Var = VE.SpecLang.Var
  sharing VE.SpecLang.Var = ANormalCoreML.Var
  sharing VE.SpecLang.TypeDesc = ANormalCoreML.TypeDesc
  sharing VE.SpecLang.Var = ANormalCoreML.Var
  sharing type TyCst.tyscheme = VE.SpecLang.RefinementTypeScheme.t
end
signature TY_CONSTRAINT_GEN = 
sig
  include TY_CONSTRAINT_GEN_STRUCTS
  (*
   * Returns all type constraints that need to hold for the expression
   * to have the required type under the given VE.
   *)
  val doIt : VE.t * ANormalCoreML.Exp.t * VE.SpecLang.RefinementType.t 
      -> TyCst.t
end
