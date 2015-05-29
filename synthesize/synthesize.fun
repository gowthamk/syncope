functor Synthesize (S : SYNTHESIZE_STRUCTS) : SYNTHESIZE = 
struct
  open S
  open SpecLang
  open ANormalCoreML

  fun $ (f,arg) = f arg
  infixr 5 $

  val nullvec = fn _ => Vector.new0 ()

  val symbase = "syn_"

  val count = ref 0

  val genVar = fn _ => 
    let val id = symbase ^ (Int.toString (!count))
        val _ = count := !count + 1
    in
      Var.fromString id 
    end

  fun newValDec (v:Var.t,e:Exp.t) : Dec.t =
    Dec.Val {rvbs=Vector.new0 (), 
             tyvars= fn () => Vector.new0 (),
             vbs =Vector.new1 
                    {valbind=Dec.ExpBind (Pat.Val.Atom $ 
                                         Pat.Val.Var v, e),
                     lay = fn _ => Layout.empty,
                     nest=[]}}
  
  fun newVarExp (v:Var.t, typ:Type.t) : Exp.t =
    let
      open Exp
      val node = Value $ Val.Atom $ Val.Var (v,Vector.new0 ())
    in
      make (node,typ)
    end 

  fun bfsSolve (ve, holeExp::rest, refTy) =
    raise (Fail "Unimpl.")


  fun doIt (ve,holeExp,refTy) =
    let
      val holeTy = Exp.ty holeExp
      val newV = genVar ()
      val newVDec = newValDec (newV,holeExp)
      val newVExp = newVarExp (newV,holeTy)
      val letExpNode = Exp.Let (Vector.new1 newVDec, newVExp)
      val letExp = Exp.make (letExpNode, holeTy)
    in
      bfsSolve (ve, [letExp], refTy)
    end
end
