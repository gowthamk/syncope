signature SPEC_VERIFY_STRUCTS =
sig
  structure VE : VAR_ENV
  structure ANormalCoreML : A_NORMAL_CORE_ML
  structure VSC : VS_CONDITION
  sharing VE = VSC.VE
  sharing VE.Var = ANormalCoreML.Var
  sharing VE.SpecLang.Con = ANormalCoreML.Con
  sharing VE.SpecLang.TypeDesc = ANormalCoreML.TypeDesc
  sharing VE.SpecLang.Tycon = ANormalCoreML.Tycon
  sharing VE.SpecLang.Tyvar = ANormalCoreML.Tyvar
  sharing VE.SpecLang.Var = ANormalCoreML.Var
  sharing VE.SpecLang.Record = ANormalCoreML.Record
  sharing VE.SpecLang.Const = ANormalCoreML.Const
  sharing VE.SpecLang.Prim = ANormalCoreML.Prim
  sharing VE.SpecLang.SourceInfo = ANormalCoreML.SourceInfo
end
signature SPEC_VERIFY = 
sig
  include SPEC_VERIFY_STRUCTS
  (*
   * Verifies program in the context of var env.
   * Returns verification conditions.
   *)
  val doIt : VE.t * ANormalCoreML.Program.t ->
                    VSC.VerificationCondition.t vector
end
