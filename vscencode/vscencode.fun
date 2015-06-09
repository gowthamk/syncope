functor VSCEncode (S : VSC_ENCODE_STRUCTS) : VSC_ENCODE =
struct
  open S
  open VSC
  structure TyD = TypeDesc
  structure RI = RelLang.RelId
  structure BP = Predicate.BasePredicate
  structure RP = Predicate.RelPredicate
  structure L = Layout
  structure Z3_Encode = Z3_Encode (structure Z3_FFI = Z3_FFI
                                   val z3_log = z3_log)
  structure VC = VerificationCondition
  structure SC = SynthesisCondition

  exception TyDNotFound
  exception ConstNotFound
  exception RelNotFound
  type ('a,'b) hash_table = ('a,'b) HashTable.hash_table
  
  fun $ (f,arg) = f arg
  infixr 5 $
  val assert = Control.assert
  val ignore = fn _ => ()
  type unimpl = unit

  (* Encoding Context *)
  datatype e_ctx = ECtx of {z3_ctx : Z3_Encode.context,
                            tyMap : (TyD.t, Z3_Encode.sort) hash_table,
                            varMap : (string(* varStr *), 
                                      Z3_Encode.ast) hash_table,
                            relMap: (string(* relIdStr *), 
                                     Z3_Encode.struc_rel) hash_table}
  fun mkDefaultECtx () = 
    let
      fun strEq (str1,str2) = (str1 = str2)
      (* z3 *)
      val z3_ctx = Z3_Encode.mkDefaultContext ()
      val z3_api = Z3_Encode.generateAPI z3_ctx
      val bool_sort = #bool_sort z3_api
      val int_sort = #int_sort z3_api
      (* tyMap *)
      val tyMap = HashTable.mkTable (MLton.hash, TyD.sameType) 
                      (117, TyDNotFound)
      val intTyD = TyD.makeTconstr (Tycon.intInf,[])
      val boolTyD = TyD.makeTconstr (Tycon.bool,[])
      val _ = HashTable.insert tyMap (intTyD,int_sort)
      val _ = HashTable.insert tyMap (boolTyD,bool_sort)
      (* varMap *)
      val varMap = HashTable.mkTable (MLton.hash, strEq) 
                      (117, ConstNotFound)
      (* relMap *)
      val relMap = HashTable.mkTable (MLton.hash, strEq)
                      (117, RelNotFound)
    in
        ECtx {z3_ctx = z3_ctx, tyMap = tyMap,
              varMap = varMap, relMap = relMap}
    end

  fun generateEAPI (ECtx {z3_ctx=ctx, tyMap, varMap, relMap}) =
    let
      (*
       * APIs for the current z3 context.
       *)
      val api = Z3_Encode.generateAPI ctx
      val const_true = #const_true api
      val const_false = #const_false api
      val truee = #truee api
      val falsee = #falsee api
      val mkUninterpretedSort = #mkUninterpretedSort api
      val mkConst = #mkConst api
      val mkInt = #mkInt api
      val mkStrucRel = #mkStrucRel api
      val mkStrucRelApp = #mkStrucRelApp api
      val mkNullSet = #mkNullSet api
      val mkSingletonSet = #mkSingletonSet api
      val mkUnion = #mkUnion api
      val mkCrossPrd = #mkCrossPrd api
      val mkDiff = #mkDiff api
      val mkSetEqAssertion = #mkSetEqAssertion api
      val mkSubSetAssertion = #mkSubSetAssertion api
      val mkConstEqAssertion = #mkConstEqAssertion api
      val mkNot = #mkNot api
      val mkIf = #mkIf api
      val mkIff = #mkIff api
      val mkAnd = #mkAnd api
      val mkOr = #mkOr api
      val dischargeAssertion = #dischargeAssertion api
      (*
       * Encoding functions for atoms (TyD, Var, RI)
       *)
      fun addTyD tyd = (fn sort => 
          (HashTable.insert tyMap (tyd,sort); sort))
        (mkUninterpretedSort ())

      fun encodeTyD tyD = case HashTable.find tyMap tyD of
          SOME sort => sort
        | NONE => (case tyD of TyD.Tvar _ =>  addTyD tyD
            | TyD.Tconstr _ => addTyD tyD
            | _ => Error.bug "Unexpected type")

      fun addVarOfTyd (v,tyd) = 
        let
          val vstr = Var.toString v
          val sort = encodeTyD tyd 
          val const = mkConst (vstr,sort)
          val _ = HashTable.insert varMap (vstr,const)
        in
          const
        end

      fun getConstForVar v = (fn vstr => HashTable.lookup varMap vstr
        handle ConstNotFound => Error.bug ("Variable "^vstr^" undec\
          \lared despite processing tydbinds")) (Var.toString v)

      fun addRelOfTyD (rid : RI.t, TyD.Tarrow (t1,_)) =
        let
          val rstr = RI.toString rid
          val sorts = case t1 of 
              TyD.Trecord tydr => Vector.map (#2 $ Vector.unzip $ 
                Record.toVector tydr, encodeTyD)
            | _ => Vector.new1 $ encodeTyD t1
          val sr = mkStrucRel (rstr,sorts)
          val _ = HashTable.insert relMap (rstr,sr)
        in
          sr
        end

      fun getStrucRelForRelId rid = (fn rstr => HashTable.lookup relMap
        rstr handle RelNotFound => Error.bug ("Rel "^rstr^" undec\
          \lared despite processing tydbinds")) (RI.toString rid)

      fun encodeVar (v:Var.t,tyd:TyD.t) = 
        case HashTable.find varMap (Var.toString v) of
            SOME ast => ast
          | NONE => addVarOfTyd (v,tyd)
        
      fun encodeStrucRel (rid:RI.t,tyd:TyD.t) = 
        case HashTable.find relMap (RI.toString rid) of
            SOME sr => sr
          | NONE => addRelOfTyD (rid,tyd)

      fun processTyDBind (v:Var.t,tyd:TyD.t) = case tyd of 
        (*
         * Currently, the only values with function types
         * are structural relations encoded as functions from
         * a val or tuple of vals to bool.
         *)
          TyD.Tarrow (t1,TyD.Tconstr (tycon,_)) => 
            if Tycon.isBool tycon then ignore $ encodeStrucRel 
              (RI.fromString $ Var.toString v, tyd)
            else ignore $ encodeVar (v,tyd)
        | _ => ignore $ encodeVar (v,tyd)

      fun encodeBasePred (bp:BP.t) : Z3_Encode.assertion = 
        let
          open BP
          val encodeBaseExpr = fn (Int i) => mkInt i
            | Bool true => const_true | Bool false => const_false
            | Var v => getConstForVar v
        in
          case bp of Eq (e1,e2) => mkConstEqAssertion 
              (encodeBaseExpr e1, encodeBaseExpr e2)
            | Iff (bp1,bp2) => mkIff (encodeBasePred bp1,
                encodeBasePred bp2)
        end

      fun encodeRelPred (rp:RP.t) : Z3_Encode.assertion =
        let
          open RelLang
          val encodeRelElem = fn (Int i) => mkInt i 
            | Bool true => const_true | Bool false => const_false
            | Var v => getConstForVar v
          fun encodeRelExpr (e:expr) : Z3_Encode.set =
            case e of T els => (case Vector.length els of
                0 => mkNullSet ()
              | _ => mkSingletonSet $ Vector.map (els,
                  encodeRelElem))
            | X (e1,e2) => mkCrossPrd (encodeRelExpr e1, 
                encodeRelExpr e2)
            | U (e1,e2) => mkUnion (encodeRelExpr e1, 
                encodeRelExpr e2)
            | D (e1,e2) => mkDiff (encodeRelExpr e1, 
                encodeRelExpr e2)
            | R (rid,v) => mkStrucRelApp (getStrucRelForRelId rid,
                getConstForVar v)
          val f = encodeRelExpr
          open RP
        in
          case rp of Eq (e1,e2) => mkSetEqAssertion (f e1, f e2)
          | Sub (e1,e2) => mkSubSetAssertion (f e1, f e2)
          | SubEq (e1,e2) => (fn s => mkOr $ Vector.new2 (mkSetEqAssertion s,
              mkSubSetAssertion s)) (f e1, f e2)
        end

      fun encodeSimplePred (sp : VSC.simple_pred) : Z3_Encode.assertion =
        case sp of 
          (Base bp) => encodeBasePred bp
        | (Rel rp) => encodeRelPred rp

      val assertSimplePred  = dischargeAssertion o encodeSimplePred

      fun encodeVSCPred vcp = case vcp of 
          VSC.Simple sp => encodeSimplePred sp
        | VSC.Conj vcps => mkAnd $ Vector.map (vcps, encodeVSCPred)
        | VSC.Disj vcps => mkOr $ Vector.map (vcps, encodeVSCPred)
        | VSC.Not vcp => mkNot $ encodeVSCPred vcp
        | VSC.If (vcp1,vcp2) => mkIf (encodeVSCPred vcp1, 
              encodeVSCPred vcp2)
        | VSC.Iff (vcp1,vcp2) => mkIff (encodeVSCPred vcp1, 
              encodeVSCPred vcp2)

      fun assertVSCPred vcp = case vcp of 
          VSC.Simple sp => assertSimplePred sp
        | VSC.Conj spv => Vector.foreach (spv,assertVSCPred)
        | _ => dischargeAssertion $ encodeVSCPred vcp
     
    in
      {
        processTyDBind = processTyDBind,
        encodeVSCPred = encodeVSCPred,
        (* assertVSCPred simplifies before asserting *)
        assertVSCPred = assertVSCPred
      }
    end
  
  structure Model =
  struct
    type t = unimpl
    fun fromZ3Model (ECtx {z3_ctx, tyMap, varMap, 
                           relMap, ...}, 
                     z3_model:Z3_Encode.model, 
                     tydbinds : VSC.tydbinds) : t =
      let
        val api = Z3_Encode.generateAPI z3_ctx
        val modelToString = #modelToString api
        val evalConst = #evalConst api
        val evalStrucRel = #evalStrucRel api
        val constToString = #constToString api
        val assnToString = #assnToString api
        val bool_sort = #bool_sort api
        val int_sort = #int_sort api
        val isPrimSort = #isPrimSort api
        val debug = #debug api
        val getSortUniverse = #getSortUniverse api
        val mkNewConst = #mkNewConst api
        val mkDistinctness = #mkDistinctness api
        val mkUniverseAssn = #mkUniverseAssn api
        val applySubstsInAssn = #applySubstsInAssn api
        (* tyModel = model(tyMap) *)
        val (tyModel, substss) = (List.unzip o List.keepAllMap) 
          (HashTable.listItemsi tyMap,
            fn (tyd, sort) => if isPrimSort sort then NONE else SOME $
              let
                val univ = getSortUniverse z3_model sort
                val (substs, univ') = (Vector.unzip o Vector.map) 
                  (univ, fn oldAst => 
                    let
                      val newAst = mkNewConst sort
                    in
                      ((newAst,oldAst), newAst)
                    end)
                val univAssn = mkUniverseAssn sort univ'
                val distinctAssn = mkDistinctness univ' 
              in
                ((tyd, sort, univAssn, distinctAssn), substs)
              end)
        val substs = Vector.concat substss
        (* varModel = [a!i/Tj!val!k] model(varMap) *)
        val varModel = List.map (HashTable.listItemsi varMap,
            fn (vStr, ast) => 
              let
                val assn = evalConst z3_model ast
                val assn' = applySubstsInAssn substs assn
              in
                (vStr, assn')
              end)
        (* srModel = [a!i/Tj!val!k] model(srMap) *)
        val srModel = List.map (HashTable.listItemsi relMap,
            fn (vStr, sr) => 
              let
                val assn = evalStrucRel z3_model sr
                val assn' = applySubstsInAssn substs assn
              in
                (vStr, assn')
              end)
        val _  = print "Model:\n"
        val _ = Control.message (Control.Top, fn _ =>
          L.align $ List.concat $ List.map (tyModel, 
            fn (_, _, univAssn, distinctAssn) =>
                [L.str $ (assnToString univAssn),
                 L.str $ assnToString distinctAssn]))
        val _ = Control.message (Control.Top, fn _ =>
          L.align $ List.map (varModel, fn (vStr,assn) =>
            L.str $ (assnToString assn)))
        val _ = Control.message (Control.Top, fn _ =>
          L.align $ List.map (srModel, fn (vStr,assn) =>
            L.str $ (assnToString assn)))
        (* debug:
         val _ = List.map (HashTable.listItemsi relMap, debug z3_model) 
         *)
      in
        ()
      end
  end

  structure CounterExample = Model
  structure VCEncode =
  struct
    datatype result = Success 
                    | Undef 
                    | Failure of CounterExample.t

    fun discharge (VC.T (tydbinds,anteP,conseqP)) =
      let
        val ectx as ECtx {z3_ctx, ...} = mkDefaultECtx ()
        val eapi = generateEAPI ectx
        val processTyDBind = #processTyDBind eapi
        val encodeVSCPred = #encodeVSCPred eapi
        val assertVSCPred = #assertVSCPred eapi
        val _ = Vector.foreach (tydbinds, processTyDBind)
        val _ = assertVSCPred anteP
        (*
         * We check the SAT of ¬conseqP
         *)
        val _ = assertVSCPred $ VSC.Not conseqP
        val res = Z3_Encode.checkContext z3_ctx
        val _ = Z3_Encode.delContext z3_ctx
      in
        case res of Z3_Encode.UNSAT => Success 
          | Z3_Encode.UNSAT => Undef 
          | Z3_Encode.SAT => Failure ()
      end
  end

  structure SCEncode =
  struct
    type result = unimpl

    datatype context = SCtx of {ectx: e_ctx, sc:SC.t}

    fun newContext (sc as SC.T (tydbinds,scP)) = 
      let
        val ectx = mkDefaultECtx ()
        val eapi = generateEAPI ectx
        val processTyDBind = #processTyDBind eapi
        val encodeVSCPred = #encodeVSCPred eapi
        val assertVSCPred = #assertVSCPred eapi
        val _ = Vector.foreach (tydbinds, processTyDBind)
        val _ = assertVSCPred scP
      in
        SCtx {ectx = ectx, sc=sc}
      end 

    exception CantSolve
    fun solve (sctx as SCtx {ectx = ectx as ECtx {z3_ctx, ...}, 
                             sc = SC.T (tydbinds,_)}) = 
      let
        val api = Z3_Encode.generateAPI z3_ctx
        val modelToString = #modelToString api
        val (res,z3_model) = Z3_Encode.checkContextGetModel z3_ctx
        val _ = case res of Z3_Encode.SAT => () | _ => raise CantSolve
        val model = Model.fromZ3Model (ectx,z3_model,tydbinds)
      in
        ((),sctx)
      end handle CantSolve => ((),sctx)

    fun ingestNewCE (SCtx {ectx, ...}, ce) =
      raise (Fail "Unimpl.")

    fun delContext (SCtx {ectx = ECtx {z3_ctx, ...}, ...}) =
      Z3_Encode.delContext z3_ctx
  end
end
