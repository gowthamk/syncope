signature VC_SOLVE_STRUCTS =
sig
  structure VC : VERIFICATION_CONDITION
  structure ANormalCoreML : A_NORMAL_CORE_ML
  val z3_log : string -> unit
end
signature VC_SOLVE =
sig
  include VC_SOLVE_STRUCTS

  datatype t = T of {holeId:string,
                     expr: ANormalCoreML.Exp.t}

  val doIt : VC.t vector -> ANormalCoreML.Exp.t
end
