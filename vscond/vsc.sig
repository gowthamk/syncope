(*
 * A VS Condition (sometimes called Syncope Condition) is either a
 * verification condition or a synthesis condition.
 *)
signature VS_CONDITION_STRUCTS =
sig
  include SPEC_LANG
  structure VE : VAR_ENV
  structure RE : REL_ENV
  sharing RefinementType = VE.SpecLang.RefinementType
  sharing type RefinementTypeScheme.t = VE.tyscheme
  sharing type Var.t = VE.Var.t
  sharing type RelLang.RelId.t = RE.SpecLang.RelLang.RelId.t
  sharing type RelLang.RelTypeScheme.t = RE.SpecLang.RelLang.RelTypeScheme.t
end
signature VS_CONDITION =
sig
  include VS_CONDITION_STRUCTS

  datatype simple_pred =  True
                       |  False
                       |  Base of Predicate.BasePredicate.t 
                       |  Rel of Predicate.RelPredicate.t

  datatype vsc_pred =  Simple of simple_pred
                    |  If of vsc_pred * vsc_pred
                    |  Iff of vsc_pred * vsc_pred
                    |  Conj of vsc_pred vector
                    |  Disj of vsc_pred vector
                    |  Not of vsc_pred

  type tydbind = Var.t * TypeDesc.t

  type tydbinds = tydbind vector

  (* hack *)
  val init : RE.t -> unit

  structure VerificationCondition : 
  sig
    
    datatype t = T of tydbinds * vsc_pred* vsc_pred
    
    val fromTypeCheck : VE.t * RefinementType.t * RefinementType.t -> t vector
    val elaborate : t -> t
    val layout : t vector -> Layout.t
    val layouts: t vector * (Layout.t -> unit) -> unit
  end

  structure SynthesisCondition :
  sig
    datatype t = T of tydbinds * vsc_pred

    structure TyCst : TY_CST
    val fromTyCst : VE.t * TyCst.t -> t
    val layout : t -> Layout.t
  end
  
  sharing type SynthesisCondition.TyCst.tyscheme =
            RefinementTypeScheme.t
  sharing SynthesisCondition.TyCst.Var = VE.Var
end
