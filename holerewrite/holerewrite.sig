signature HOLE_REWRITE_STRUCTS =
sig
  structure VE : VAR_ENV
  structure ANormalCoreML : A_NORMAL_CORE_ML
  structure SpecLang : SPEC_LANG
  sharing SpecLang = VE.SpecLang
  sharing SpecLang.TyDBinds.Value = ANormalCoreML.TypeDesc
  sharing SpecLang.Tyvar = ANormalCoreML.Tyvar
  sharing VE.Var = ANormalCoreML.Var
end
signature HOLE_REWRITE =
sig
  include HOLE_REWRITE_STRUCTS

  (*
   * Γ ⊢ e??:τ ↪ e
   *)
  val newContext : VE.t * ANormalCoreML.Exp.t * SpecLang.RefinementType.t -> 
    {
      newCandidate : unit -> ANormalCoreML.Exp.t
    }
end
