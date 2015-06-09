signature VSC_ENCODE_STRUCTS =
sig
  structure VSC : VS_CONDITION
  val z3_log : string -> unit
end
signature VSC_ENCODE =
sig
  include VSC_ENCODE_STRUCTS

  structure CounterExample : MODEL

  structure VCEncode :
  sig
    datatype result = Success 
                    | Undef 
                    | Failure of CounterExample.t

    val discharge : VSC.VerificationCondition.t -> result
  end

  structure SCEncode :
  sig
    type result
    type context
    val newContext : VSC.SynthesisCondition.t -> context
    val solve : context -> result * context
    val ingestNewCE : context * CounterExample.t -> context
    val delContext : context -> unit
  end

end
