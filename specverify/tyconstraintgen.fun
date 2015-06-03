(*
 * This functor is a reformulation of specverify with some major
 * differences:
 * 1. It does not generate verification conditions. Instead, it
 * generates type constraints.
 * 2. Only accepts subset of ML expressions built using Let, App,
 * Value, and VarChoice. Further, expression has to be a Let at the
 * top-level.
 *)
functor TyConstraintGen(S : TY_CONSTRAINT_GEN_STRUCTS) : TY_CONSTRAINT_GEN = 
struct
  open S
  structure SpecLang = VE.SpecLang

  open SpecLang
  open ANormalCoreML
  structure TyD = TypeDesc
  structure RefTy = RefinementType
  structure RefTyS = RefinementTypeScheme
  structure P = Predicate
  structure BP = Predicate.BasePredicate
  structure RP = Predicate.RelPredicate
  structure L = Layout

  structure TyCst = TyCst(structure VE = VE)

  type subst = Var.t*Var.t
  type substs = subst Vector.t
  fun $ (f,arg) = f arg
  infixr 5 $
  val assert = Control.assert
  fun toRefTyS refTy = RefTyS.generalize (Vector.new0(), refTy)
  val newLongVar = fn (var,fld) => Var.fromString $
    (Var.toString var)^"."^(Var.toString fld)
  val varToExpVal = fn (var,tyvec) => 
    Exp.Val.Atom (Exp.Val.Var (var,tyvec))
  fun mkVarChoiceRefTy (ty,vars) = 
    let
      val RefTy.Base (bv,tyd,_) = RefTy.fromTyD $ Type.toMyType ty
      val varEqProps as prop1::restProps = Vector.toListMap (vars, 
            fn v => P.baseP $ BP.varEq (bv,v))
              handle Match => Error.bug "TyConstraintGen: VarChoice \
                                        \is empty."
      val disj = List.fold (restProps, prop1, P.Disj)
    in
      RefTy.Base (bv,tyd,disj)
    end

  (*
   * Functions duplicated from specverify:
   *  typeSynthValExp, unifyArgs
   *)
  fun typeSynthValExp (ve:VE.t, valexp : Exp.Val.t) : RefTy.t = 
    let
      open Exp
    in
      case valexp of
        Val.Atom (Val.Const c) => RefTy.fromTyD (TyD.makeTunknown ())
      | Val.Atom (Val.Var (v,typv)) =>  
        let
          val tydvec = Vector.map (typv,Type.toMyType)
          val vtys = VE.find ve v handle (VE.VarNotFound _) => Error.bug
            ((Var.toString v) ^ " not found in the current environment\n")
          val vty = RefTyS.instantiate (vtys,tydvec)  
          (*
           * Keep track of variable equality.
           * We currently cannot keep track of equality if rhs
           * is a nullary constructor or a function. Unimpl.
           *)
          val qualifiedvty = case (Vector.length tydvec, vty) of 
              (0,RefTy.Base (bv,td,pred)) => RefTy.Base 
                (bv,td,Predicate.conjP(pred,BP.varEq(bv,v)))
            | (_,RefTy.Tuple refTyBinds) => RefTy.Tuple $ Vector.map
                (refTyBinds, fn (fldvar,refty) => 
                  let
                    val newvar = newLongVar (v,fldvar)
                    val extendedVE = VE.add ve (newvar,toRefTyS refty)
                    val newvarexp = varToExpVal (newvar, Vector.new0 ())
                    val refty' = typeSynthValExp (extendedVE, newvarexp)
                  in
                    (fldvar, refty')
                  end)
            | _ => vty (* Unimpl : refinements for fns. Cannot keep
                   track of equality for functions now.*)
        in
          qualifiedvty
        end
      | Val.Tuple atomvec => RefTy.Tuple $ Vector.mapi (atomvec, fn (i,atm) => 
          let
            val atmTy = typeSynthValExp (ve,Val.Atom atm)
            val fldvar = Var.fromString $ Int.toString (i+1) (* tuple BVs *)
          in
            (fldvar, atmTy)
          end)
      | Val.Record atomrec => RefTy.Tuple $ Vector.map (Record.toVector atomrec, 
          fn (lbl,atm) => 
            let
              val atmTy = typeSynthValExp (ve,Val.Atom atm)
              val fldvar = Var.fromString $ Field.toString lbl (* Record BVs *)
            in
              (fldvar, atmTy)
            end)
    end

  fun unifyArgs (argBind as (argv : Var.t, argTy : RefTy.t) ,
      argExpVal : Exp.Val.t) : ((Var.t*RefTy.t) vector * substs) =
    let
      open Exp.Val
    in
      case (argTy,argExpVal) of
        (RefTy.Base _, Atom (Var (v,typv))) => 
          (Vector.new1 (v,argTy), Vector.new1 (v,argv))
      | (RefTy.Base _,Atom (Const c)) => Error.bug $ 
          "Unimpl const args"
      | (RefTy.Base _,_) => (Vector.new0 (), Vector.new0 ())
      | (RefTy.Tuple argBinds',Tuple atomvec) => 
          (*
           * Unifies v:{1:T0,2:T1} with (v0,v1)
           * Returns binds = [v0 ↦ T0, v1 ↦ T1],
           *        substs = [v0/v.1, v1/v.2]
           *)
          let
            val (reftyss,substss) = (Vector.unzip o Vector.map2)
              (argBinds',atomvec, fn (argBind',atom) => 
                let
                  val (binds,substs') = unifyArgs (argBind', Atom atom)
                  val substs = Vector.map (substs', 
                    fn (n,o') => (n, newLongVar (argv,o')))
                in
                  (binds,substs)
                end)
          in
            (Vector.concatV reftyss, Vector.concatV substss)
          end
      | (RefTy.Tuple argBinds', Record atomrec) => 
          let
            val (reftyss,substss)= (Vector.unzip o Vector.map)
            (argBinds', fn (argBind') =>
              let
                val (argv',_) = argBind'
                val argvStr' = Var.toString argv'
                val lblatomvec = Record.toVector atomrec
                val indx = Vector.index (lblatomvec, fn (lbl,_) =>
                  Field.toString lbl = argvStr')
                val (_,atom) = case indx of 
                    SOME i => Vector.sub (lblatomvec,i)
                  | NONE => Error.bug ("Field " ^ (argvStr') ^ 
                      " could not be found.")
                val (binds,substs') = unifyArgs (argBind',Atom atom)
                  val substs = Vector.map (substs', 
                    fn (n,o') => (n, newLongVar (argv,o')))
              in
                (binds,substs)
              end)
          in
            (Vector.concatV reftyss, Vector.concatV substss)
          end
      | (RefTy.Tuple argBinds', Atom (Var (v,_))) => 
          let
            (* Unifying v0:{x0:T0,x1:T1} with v1 would return
             * v1 ↦ {x0:T0,x1:T1} as the only new bind. However,
             * all references v0 elements should now refer to v1
             * elements. Therefore, substs = [v1.x0/v0.x0, v1.x1/v0.x1]
             *)
            val binds = Vector.new1 (v,argTy)
            val substs = (Vector.concatV o Vector.map)
            (argBinds', fn (argBind') =>
              let
                val (argv',_) = argBind'
                val newVar = newLongVar (v,argv')
                val (_,substs') = unifyArgs (argBind',
                  Atom (Var (newVar, Vector.new0 ())))
                val substs = Vector.map (substs', 
                  fn (n,o') => (n, newLongVar (argv,o')))
              in
                substs
              end)
          in
            (binds,substs)
          end
      | (RefTy.Arrow _, Atom (Var (v,_))) => (Vector.new1 (v,argTy), 
          Vector.new1 (v,argv))
      | _ => raise Fail $ "Invalid argTy-argExpVal pair encountered: \n"
            ^(L.toString $ RefTy.layout argTy)^"\n"
            ^(L.toString $ Exp.Val.layout argExpVal)^"\n"
    end

  fun typeSynthExp (tycst:TyCst.t, ve:VE.t, exp:Exp.t) 
      : (TyCst.t * RefTy.t) =
    let
      open Exp
      val expty = ty exp
    in
      case node exp of
        App (f,valexp) =>
        let
          val fty  = typeSynthValExp (ve,Val.Atom f)
          val (fargBind as (farg,fargty),fresty)  = case fty of 
              RefTy.Arrow x => x
            | _ => Error.bug ("Type of " ^ (Layout.toString $ 
              Val.layout $ Val.Atom f) ^ " not an arrow")
          val argVar = case valexp of 
              Val.Atom (Val.Var (v,targs)) => (
                assert (Vector.length targs = 0, "TyConstraintGen: \
                  \Synthesized expression contains polymorphic \
                  \instantiation in fn argument. Unexpected.\n"); v)
            | _ => raise (Fail "TyConstraintGen: non-variable \
                \fn argument. Unexpected.\n")
            val tycst' = TyCst.add tycst (argVar,toRefTyS fargty)
            val (_,substs) = unifyArgs (fargBind,valexp)
            val resTy = RefTy.applySubsts substs fresty
        in
          (tycst', resTy)
        end
      | Value v => (tycst,typeSynthValExp (ve,v))
      | VarChoice vars => (tycst, mkVarChoiceRefTy (expty,vars))
      | _ => Error.bug "TyConstraintGen: var-bound expression in a \
              \synthesized let expression has unexpected structure."
    end

  and doItValBind (tycst, ve, valbind) : TyCst.t * VE.t = 
    case valbind of 
      Dec.ExpBind (Pat.Val.Atom (Pat.Val.Var v), e) =>
        let
          val (tycst',tau) = typeSynthExp (tycst,ve,e)
          val sigma = toRefTyS tau
        in
          (TyCst.add tycst' (v,sigma), VE.add ve (v,sigma))
        end
    | _ => Error.bug "TyConstraintGen: A valbind in synthesized \
            \expression is expected to be a varbind."

  and doItDecs (tycst,ve,decs) : TyCst.t * VE.t = 
    let
      fun doItDec (tycst, ve, dec) = case dec of
          Dec.Val {vbs, ...} => Vector.fold (vbs,(tycst,ve),
                fn ({valbind,...},(tycst,ve)) => 
                      doItValBind (tycst, ve, valbind))
        | _ => Error.bug "TyConstraintGen: A Dec in synthesized \
                  \expression is not val."
    in
      Vector.fold (decs, (tycst,ve), 
          fn (dec, (tycst,ve)) => doItDec (tycst, ve, dec))
    end

  fun typeCheckExp (tycst: TyCst.t, ve:VE.t, exp: Exp.t, ty: RefTy.t) 
      : TyCst.t =
    case Exp.node exp of
      Exp.Let (decs,e) => 
        let
          val (tycst',ve') = doItDecs (tycst,ve,decs)
        in
          typeCheckExp (tycst',ve',e,ty)
        end
    | Exp.Value (Exp.Val.Atom (Exp.Val.Var (v,targs))) =>
          (assert (Vector.length targs=0, "TyConstraintGen: polymorphic\
              \ value created in synthesized expression. Unexpected.");
          TyCst.add tycst (v,toRefTyS ty))
    | _ => Error.bug "TyConstraintGen: (top-level or let-bound) \
              \synthesized expression is not a variable."

  fun doIt (ve, exp, refTy) =
    let
      val tycst = typeCheckExp (TyCst.empty, ve, exp, refTy)
    in
      tycst
    end
    
end
