functor VSCondition (S : VS_CONDITION_STRUCTS) : VS_CONDITION =
struct
  open S
  structure P = Predicate
  structure BP = Predicate.BasePredicate
  structure RP = Predicate.RelPredicate
  structure RelId = RelLang.RelId
  structure RefTy = RefinementType
  structure RefTyS = RefinementTypeScheme
  structure RelTy = RelLang.RelType
  structure RelTyS = RelLang.RelTypeScheme
  structure RI = RelLang.RelId
  structure TyD = TypeDesc
  structure Env = TyDBinds
  structure L = Layout

  exception TrivialVC (* raised when antecedent has false *)

  type tydbind = Var.t * TyD.t
  type tydbinds = tydbind vector

  datatype simple_pred = True
                       | False
                       | Base of BP.t 
                       | Rel of RP.t

  datatype vsc_pred =  Simple of simple_pred
                   |  If of vsc_pred * vsc_pred
                   |  Iff of vsc_pred * vsc_pred
                   |  Conj of vsc_pred vector
                   |  Disj of vsc_pred vector
                   |  Not of vsc_pred

  (* RelEnv for this session *)
  val thisRE = ref (RE.empty)
  fun init re = thisRE := re

  val assert = Control.assert
  fun $ (f,arg) = f arg
  infixr 5 $
  fun varStrEq (v1,v2) = Var.toString v1 = Var.toString v2
  fun vectorAppend (vec,e) = Vector.concat [vec,Vector.new1 e]
  fun vectorPrepend (e,vec) = Vector.concat [Vector.new1 e,vec]
  fun vectorFoldrFoldr (vec1,vec2,acc,f) = Vector.foldr (vec1,acc,
    fn (el1,acc) => Vector.foldr (vec2,acc,fn (el2,acc) => f (el1,el2,acc)))
  

  fun conj (p1 : vsc_pred,p2 : vsc_pred) : vsc_pred = case (p1,p2) of 
      (Simple True,_) => p2
    | (_, Simple True) => p1
    | (Simple False,_) => Simple False
    | (_, Simple False) => Simple False
    | (Simple sp1,Conj spv) => Conj $ vectorPrepend (p1,spv)
    | (Conj spv,Simple sp2) => Conj $ vectorAppend (spv,p2)
    | (Conj spv1,Conj spv2) => Conj $ Vector.concat [spv1,spv2]
    | _ => Conj $ Vector.new2 (p1,p2)

  fun disj(p1 : vsc_pred,p2 : vsc_pred) : vsc_pred = case (p1,p2) of 
      (Simple True,_) => Simple True
    | (_, Simple True) => Simple True
    | (Simple False,_) => p2
    | (_, Simple False) => p1
    | (Simple sp1,Disj spv) => Disj $ vectorPrepend (p1,spv)
    | (Disj spv,Simple sp2) => Disj $ vectorAppend (spv,p2)
    | (Disj spv1,Disj spv2) => Disj $ Vector.concat [spv1,spv2]
    | _ => Disj $ Vector.new2 (p1,p2)

  fun negate (p : vsc_pred) : vsc_pred = case p of
      Simple True => Simple False
    | Simple False => Simple True
    | _ => Not p
  

  fun coercePTtoT (pt:P.t) : vsc_pred = case pt of
      P.True => Simple True
    | P.False => Simple False
    | P.Hole h => Error.bug "coercePTtoT: Cannot coerce hole\n"
    | P.Base p => Simple $ Base p
    | P.Rel p => Simple $ Rel p
    | P.Not p => negate $ coercePTtoT p
    | P.If (p1,p2) => If (coercePTtoT p1, coercePTtoT p2)
    | P.Iff (p1,p2) => Iff (coercePTtoT p1, coercePTtoT p2)
    | P.Conj (p1,p2) => 
        let
          val t1 = coercePTtoT p1
          val t2 = coercePTtoT p2
        in
          conj (t1,t2)
        end
    | P.Disj (p1,p2) => disj (coercePTtoT p1, coercePTtoT p2)
    | _ => Error.bug "Cannot coerce PT to T"

  fun truee () : vsc_pred = Simple True
  fun falsee () : vsc_pred = Simple False

  (*
   * join-order(vc,vc1,vc2) : binds = binds1@binds2
   *                          envP = envP1 /\ envP2
   *)
  fun joinVCs ((binds1,envP1),(binds2,envP2)) : (tydbinds * vsc_pred) =
    (Vector.concat [binds1,binds2],conj (envP1,envP2))

  (*
   * forall vc1 in vcs1 and vc2 in vcs2, vc is in vcs s.t
   * join-order (vc,vc1,vc2)
   *)
  fun join (vcs1,vcs2) = 
    case (Vector.length vcs1, Vector.length vcs2) of 
      (0,_) => vcs2
    | (_,0) => vcs1
    | _ => 
      let
        val vcs = (Vector.fromList o vectorFoldrFoldr) (vcs1,vcs2,[], 
          fn (vc1,vc2,acc) => (joinVCs (vc1,vc2))::acc)
      in
        vcs
      end

  fun havocPred (pred : P.t) : (tydbinds*vsc_pred) vector =
    let
      fun trivialAns () = Vector.new1 (Vector.new0(),coercePTtoT pred)
    in
      case pred of
        P.Exists (tyDB,p) => 
          let
            val mybinds = TyDBinds.toVector tyDB
            val vcs = havocPred p
          in
            Vector.map (vcs, fn (binds,envP) =>
              (Vector.concat [mybinds,binds],envP))
          end
      | P.Conj (p1,p2) =>
          let
            val vcs1 = havocPred p1
            val vcs2 = havocPred p2
          in
            (* conj is a join point *)
            join (vcs1,vcs2)
          end
      | P.Dot (p1,p2) => Vector.concat [havocPred p1,
          havocPred p2]
      | _ => trivialAns () (* May need havoc here.*)
    end
        
  fun havocTyBind (v : Var.t,refTy : RefTy.t) : (tydbinds*vsc_pred) vector =
    let
      open RefTy
      (* -- These functions duplicated from SpecVerify -- *)
      val newLongVar = fn (var,fld) => Var.fromString $
        (Var.toString var)^"."^(Var.toString fld)
      (*
       * Decomposes single tuple bind of form v ↦ {x0:T0,x1:T1} to
       * multiple binds : [v.x0 ↦ T0, v.x1 ↦ T1]
       *)
      fun decomposeTupleBind (tvar : Var.t, tty as RefTy.Tuple 
        refTyBinds) : (Var.t*RefTy.t) vector =
        let
          val bindss = Vector.map (refTyBinds, 
            fn (refTyBind as (_,refTy)) => 
              case refTy of 
                RefTy.Tuple _ => decomposeTupleBind refTyBind
              | _ => Vector.new1 refTyBind)
          val binds = Vector.map (Vector.concatV bindss, 
            fn (v,ty) => (newLongVar (tvar,v), ty))
        in
          binds
        end
    in
      case refTy of
        (* removing any _mark_ *)
        Base (_,TyD.Tunknown,_) => Vector.new0 ()
      | Base (bv,td,pred) => 
          let
            val pred' = P.applySubst (v,bv) pred
            val vcs = havocPred pred'
            val mybind = (v,td)
          in
            Vector.map (vcs,fn (binds,envP) => 
              (vectorAppend (binds,mybind),envP))
          end
      | Tuple _ => havocTyBindSeq $ decomposeTupleBind (v,refTy)
        (* Bindings for functions not needed *)
      | _ => Vector.new0 ()
    end

  and havocTyBindSeq (tyBinds : (Var.t * RefTy.t) vector)
    : (tydbinds * vsc_pred) vector =
    Vector.fold (tyBinds,
      Vector.new1 (Vector.new0 (),truee()),
      fn (tyBind,vcs1) => join (vcs1,havocTyBind tyBind))

  fun havocVE (ve : VE.t) : (tydbinds*vsc_pred) vector =
    let
      (*
       * Remove polymorphic functions and constructors
       *)
      val vevec = Vector.keepAllMap (VE.toVector ve,
        fn (v,RefTyS.T{tyvars,refty,...}) => case Vector.length tyvars of
            0 =>  SOME (v,refty)
          | _ => NONE)
      (*
       * Remove true and false constructors
       *)
      val vevec = Vector.keepAllMap (vevec, 
        fn (v,refty) => case refty of
          RefTy.Base (_,TyD.Tconstr (tycon,_),_) => 
            if Tycon.isBool tycon andalso (Var.toString v = "true" 
              orelse Var.toString v = "false") then NONE 
              else SOME (v,refty)
        | _ => SOME (v,refty))
    in
      havocTyBindSeq vevec
    end

  (*
   * ------- Generic Elaboration ---------
   *)

  structure RInst = 
  struct
    datatype t = T of RelLang.RelId.t * TypeDesc.t vector
    val layout = fn _ => L.empty
    val idStrEq = fn (id1,id2) => (RI.toString id1 = RI.toString id2)
    fun equal (T (id1,tyds1), T (id2,tyds2)) =
      let
        val eq = (idStrEq (id1,id2)) andalso
            (Vector.length tyds1 = Vector.length tyds2) andalso
            (Vector.forall2 (tyds1,tyds2, TyD.sameType))
      in
        eq
      end
  end

  exception RInstNotFound
  val rinstTab = HashTable.mkTable (MLton.hash, RInst.equal)
                      (117, RInstNotFound)
  fun getSymForRInst rinst = 
    (SOME $ HashTable.lookup rinstTab(RInst.T rinst)) 
      handle RInstNotFound => NONE
  fun addSymForRInst rinst rid =
    HashTable.insert rinstTab(RInst.T rinst, rid)

  val count = ref 0

  val genSym = fn idbase => 
    let
      val symbase = (*"_"^*)(RI.toString idbase)
      val id = symbase ^ (Int.toString (!count))
      val _ = count := !count + 1
    in
      RI.fromString id 
  end
  val inv = fn (x,y) => (y,x)
  fun mapFoldTuple b f (x,y) =
    ((fn (b',x') => 
        ((fn (b'',y') => (b'',(x',y'))) o (f b')) y) 
      o (f b)) x 
  fun mapTuple f (x,y) = (f x, f y)
  fun mapSnd f (x,y) = (x,f y)

  fun elabVSCPred (tyDB: TyDBinds.t) (vscpred:vsc_pred) 
      : (vsc_pred) = 
    let
      fun elabRExpr rexpr =  
        let
          val mapper = mapTuple elabRExpr
          fun tyArgsinTypeOf (v:Var.t) =
            (case TyDBinds.find tyDB v of
              TyD.Tconstr (tycon,targs) => Vector.fromList targs
              (* Hack : special case to deal with 'R *)
            | t => Vector.new1 t)
            (*| _ => Error.bug ("Relation instantiated over variable\
              \ of non-algebraic datatype")) *)
            handle TyDBinds.KeyNotFound _ => Error.bug ("Type of\
              \ variable "^(Var.toString v)^" not found in TyDBinds")
        in
          case rexpr of
            RelLang.T els => rexpr
          | RelLang.X t =>  RelLang.X (mapper t)
          | RelLang.U t =>  RelLang.U (mapper t)
          | RelLang.D t =>  RelLang.D (mapper t)
          | RelLang.R (relId,v) => 
            let
              val relIdStr = RelId.toString relId
              val dTyInsts = tyArgsinTypeOf v
              (* Hack : to deal with 'R *)
              val rTyInsts = fn _ => tyArgsinTypeOf $ 
                Var.fromString "l"
              val rinst = case relIdStr = "qRm" orelse 
                relIdStr = "qRo" of
                  false => (relId,dTyInsts)
                | true => (relId, Vector.concat [dTyInsts, 
                    rTyInsts ()])
            in
              case getSymForRInst rinst of 
                SOME relId' => RelLang.R (relId',v)
              | NONE => (fn r' => (addSymForRInst rinst r';
                  RelLang.R (r',v))) (genSym relId)
            end
        end

      fun elabRPred rpred = case rpred of
          RP.Eq t =>  RP.Eq (mapTuple elabRExpr t)
        | RP.Sub t =>  RP.Sub (mapTuple elabRExpr t)
        | RP.SubEq t =>  RP.SubEq (mapTuple elabRExpr t)

      fun elabSimplePred sp = 
        case sp of
          Rel rpred =>  Rel $ elabRPred rpred
        | _ => sp

      fun doIt  (vscpred:vsc_pred) : (vsc_pred) =
        case vscpred of
          Simple sp  =>  Simple (elabSimplePred sp)
        | Conj vcps =>  Conj $ Vector.map (vcps, doIt)
        | Disj vcps => Conj $ Vector.map (vcps, doIt)
        | Not vcp =>  Not $ doIt vcp
        | If vcps =>  If $ mapTuple doIt vcps
        | Iff vcps =>  Iff $ mapTuple doIt vcps

    in
      doIt vscpred
    end
  (*
   * -------- Generic Layout functions ------------
   *)
  fun laytTyDBinds tybinds = L.vector (Vector.map (tybinds,
    fn (v,tyd) => L.str ((Var.toString v) ^ " : " ^ 
      (TyD.toString tyd))))

  fun laytSimplePred sp = case sp of 
      True => L.str "true"
    | False => L.str "false"
    | Base bp => L.str $ BP.toString bp
    | Rel rp => L.str $ RP.toString rp

  fun laytVSCPred vscpred = case vscpred of 
      Simple p => laytSimplePred p
    | Conj vcv => L.align $ Vector.toListMap (vcv,
        laytVSCPred)
    | Disj vcv => L.align $ Vector.toListMap (vcv,
        fn vc => L.seq [L.str "OR [",laytVSCPred vc, L.str "]"])
    | Not vc => L.seq [L.str "NOT [", laytVSCPred vc, L.str "]"]
    | If (vc1,vc2) => L.seq [laytVSCPred vc1, L.str " => ", 
          laytVSCPred vc2]
    | Iff (vc1,vc2) => L.seq [laytVSCPred vc1, L.str " <=> ", 
          laytVSCPred vc2]


  structure VerificationCondition =
  struct

    datatype t = T of tydbinds * vsc_pred * vsc_pred
  
    fun fromTypeCheck (ve, subTy, supTy) : t vector = 
      let
        open RefTy
      in
        case (subTy,supTy) of
          (Base (_,TyD.Tunknown,p),_) => if P.isFalse p 
            then raise TrivialVC
            else raise (Fail "ML type of subtype is unknown")
        | (Base (v1,t1,p1), Base (v2,t2,p2)) => 
            let
              (*
               * First, make sure that base types are same.
               *)
              val _ = assert (TyD.sameType (t1,t2), (TyD.toString t1)
                ^" is not sub-type of "^(TyD.toString t2))
              (*
               * Second, substitute actuals for formals in p2
               *)
              val p2 = P.applySubst (v1,v2) p2
              (*
               * Third, add base type of actuals to env
               *)
              val ve = VE.add ve (v1,RefTyS.generalize (Vector.new0 (),
                RefTy.fromTyD t1))
              val envVCs = fn _ => havocVE ve
              val anteVCs = fn _ => havocPred p1
              val vcs = fn _ => join (envVCs (),anteVCs ())
              val conseqPs = fn _ => case coercePTtoT p2 of
                  Conj vcps => vcps | vcp => Vector.new1 (vcp)
            in
              case p2 of P.True => Vector.new0()
                | _ => Vector.fromList $ vectorFoldrFoldr 
                  (vcs(), conseqPs(), [],
                    fn ((tybinds,anteP),conseqP,vcacc) =>
                      case anteP of Simple False => vcacc
                      | _ => (T (tybinds,anteP,conseqP))::vcacc)
            end
        | (Tuple t1v,Tuple t2v) => 
            (Vector.concatV o Vector.map2) (t1v,t2v, 
              fn ((v1,t1),(v2,t2)) => fromTypeCheck (ve,t1,t2))
        | (Arrow ((arg1,t11),t12),Arrow ((arg2,t21),t22)) => 
            let
              val vcs1 = fromTypeCheck (ve,t21,t11)
              val t12' = RefTy.applySubsts (Vector.new1 (arg2,arg1)) t12
              val ve'  = VE.add ve (arg2, RefTyS.generalize 
                (Vector.new0 (), t21))
              val vcs2 = fromTypeCheck (ve',t12',t22)
            in
              Vector.concat [vcs1, vcs2]
            end
        | _ => raise TrivialVC
      end handle TrivialVC => Vector.new0 ()

    fun layout (vcs : t vector) =
      let
        fun layoutVC (T (tybinds,vcp1,vcp2)) = 
          Pretty.nest ("bindings",laytTyDBinds tybinds,
            L.align [
              L.indent(laytVSCPred vcp1,3),
              L.str "=>",
              L.indent (laytVSCPred vcp2,3)])
      in
        L.align $ Vector.toListMap (vcs, layoutVC)
      end

    fun layouts (vcs,output) =
      (output $ L.str "Verification Conditions:\n" ; output $ layout vcs)

  fun elaborate vc =
    let
      val T (tydbinds,anteP,conseqP) = vc

      val tyDB = Vector.fold (tydbinds,TyDBinds.empty, 
        fn ((v,tyd),tyDB) => TyDBinds.add tyDB v tyd)

      val anteP' = elabVSCPred tyDB anteP
      val conseqP' = elabVSCPred tyDB conseqP

      val reltydbinds = List.map (HashTable.listItemsi rinstTab,
        fn (RInst.T (relId,tydvec),relId') =>
          let
            val {ty,map} = RE.find (!thisRE) relId 
              handle RE.RelNotFound _ =>
                Error.bug ("Unknown Relation: "
                  ^(RelLang.RelId.toString relId))
            val RelTy.Tuple tydvec = RelTyS.instantiate (ty,tydvec)
            val boolTyD = TyD.makeTconstr (Tycon.bool,[])
            val relArgTyd = TyD.Trecord $ Record.tuple tydvec
            val relTyD = TyD.makeTarrow (relArgTyd,boolTyD)
            val relvid = Var.fromString $ RI.toString relId'
          in
            (relvid,relTyD)
          end)

      val tydbinds' = Vector.concat [tydbinds, Vector.fromList reltydbinds] 

    in
      T (tydbinds',anteP',conseqP')
    end
  end

  structure SynthesisCondition =
  struct
    datatype t = T of tydbinds * vsc_pred
    structure TyCst = TyCst (structure VE = VE)
    fun fromTyCst (ve,tycst) =
      let
        val envSC = case Vector.toList $ havocVE ve of
            [envSC] => envSC
          | _ => raise (Fail "SC.fromTyCst: Hole dominated by \
                  \ a case expression. Synthesis Unimpl.")
        val (scbinds,scpred) = case Vector.toList $ havocVE tycst of
            [tycstSC] => tycstSC
          | _ => raise (Fail "SC.fromTyCst: impossible case\n")
        (* scbinds can contain dupes. Remove them *)
        val scbinds' = Vector.removeDuplicates (scbinds,
            fn ((v1,tyd1),(v2,tyd2)) => varStrEq (v1,v2) andalso
                                        TyD.sameType (tyd1,tyd2))
        val tycstSC = (scbinds',scpred)
      in
        T $ joinVCs (envSC,tycstSC)
      end

    fun layout (T (tydbinds,vscp)) =
        Pretty.nest ("bindings",laytTyDBinds tydbinds,
                      L.indent(laytVSCPred vscp,3))
  end

end
