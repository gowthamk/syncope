signature SYNTHESIZE_STRUCTS =
sig
  structure VE : VAR_ENV
  structure ANormalCoreML : A_NORMAL_CORE_ML
  structure SpecLang : SPEC_LANG
  sharing SpecLang = VE.SpecLang
end
signature SYNTHESIZE =
sig
  include SYNTHESIZE_STRUCTS

  (*
   * Γ ⊢ e??:τ ↪ e
   *)
  val doIt : VE.t * ANormalCoreML.Exp.t * SpecLang.RefinementType.t 
              -> ANormalCoreML.Exp.t
end
