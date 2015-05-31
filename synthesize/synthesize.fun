functor Synthesize (S : SYNTHESIZE_STRUCTS) : SYNTHESIZE = 
struct
  open S
  open SpecLang
  open ANormalCoreML

  structure L = Layout
  structure TyD = TypeDesc
  structure RefTyS = RefinementTypeScheme
  structure RefTy = RefinementType
  structure P = Predicate
  structure List = 
  struct
    open List
    fun snoc (l,x) = append (l,[x])
  end

  fun $ (f,arg) = f arg
  infixr 5 $

  val nullvec = fn _ => Vector.new0 ()

  val snd = fn (x,y) => y

  val symbase = "syn_"

  val count = ref 0

  val genVar = fn _ => 
    let val id = symbase ^ (Int.toString (!count))
        val _ = count := !count + 1
    in
      Var.fromString id 
    end

  val tyvarEq = Tyvar.equals 
  val assert = Control.assert

  fun listHas (l,e) = List.exists (l, fn e' => e'=e)

  datatype 'a partition = Split of 'a list * 'a list

  fun allPartitions [] = [Split ([],[])]
    | allPartitions [a] = [Split ([a],[]), Split ([],[a])]
    | allPartitions (x::xs) = 
        let
          val xsSplits = allPartitions xs
        in
          List.concat $ List.map (xsSplits,
              fn (Split (s1,s2)) => [Split (x::s1,s2),
                                     Split (s1,x::s2)])
        end

  fun mapHolesInDec (d:Dec.t,f) = 
    let
      open Dec
      fun mapHolesInValBind (ExpBind (pv,e),f) =
                  ExpBind (pv,mapHoles (e,f))
        | mapHolesInValBind _ = Error.bug "mapHolesInDec : \
                              \Impossible case\n"
    in
      case d of Val {rvbs,tyvars,vbs} => Val {rvbs=rvbs, tyvars=tyvars,
          vbs = Vector.map (vbs, 
              fn ({valbind, lay, nest}) => {lay=lay, nest=nest,
                        valbind=mapHolesInValBind (valbind,f)})}
    end
  and mapHoles (e:Exp.t,f) = 
    let
      fun mapHolesInDecs (decs,f) = Vector.map (decs, 
                  fn d => mapHolesInDec (d,f))
      open Exp
      val ety = ty e
    in
      case node e of 
        Let (decs,e) => make (Let (mapHolesInDecs (decs,f), 
                             mapHoles (e,f)), ety)
      | Hole _ => f e
      | _ => e
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

  fun allHoleIdsInDec (d:Dec.t) =
    let
      open Dec
      fun allHoleIdsInValBind (ExpBind (_,e)) = allHoleIdsInExpr e
        | allHoleIdsInValBind _ = Error.bug "allHoleIdsInValBind: \
                                              \Impossible case"
    in
      case d of Val {vbs, ...} => Vector.fold (vbs,[],
        fn ({valbind,...},holesAcc) => 
            List.concat[allHoleIdsInValBind valbind, holesAcc])
        | _ => Error.bug "allHoleIdsInDec: Impossible case\n"
    end
  and allHoleIdsInExpr (e:Exp.t) = 
    let
      open Exp
      fun allHoleIdsInDecs decs = List.concat $ Vector.toListMap (decs,
          allHoleIdsInDec)
    in
      case Exp.node e of 
        Let (decs,e) => List.concat [allHoleIdsInDecs decs,
                                     allHoleIdsInExpr e]
      | Hole {id} => [id]
      | _ => []
    end

  fun tyArgsInTyD (tyd:TyD.t) : TyD.t list = case tyd of
      TyD.Tconstr (_,targs) => targs
    | TyD.Tvar tyvar => [TyD.makeTvar tyvar]
    | TyD.Trecord _ => raise (Fail "Unimpl.")
    | _ => Error.bug "tyArgsInTyD: Impossible case\n"

  fun isValidTyDBind (v,refTyS) = 
    let
      val RefTyS.T {refty, ...} = refTyS
      val hasHole = ref false
      val _ = RefTy.mapBaseTy refty
          (fn (btp as (_,_,P.Hole _)) => (hasHole := true; btp)
            | btp => btp)
      val vstr = Var.toString v
      val hasPrefix = fn str => String.hasPrefix (vstr,{prefix=str})
    in
      (not $ (hasPrefix "sv_" orelse hasPrefix "_mark_"
             orelse hasPrefix "hole_f")
       andalso (not $ !hasHole))
    end

  fun doIt (ve,holeExp,refTy) =
    let
      exception Return

      val tydbinds = Vector.keepAll (VE.toVector ve, isValidTyDBind)

      fun varsOfTyd (tyd) : Var.t vector = 
        Vector.keepAllMap (tydbinds, 
          fn (v,RefTyS.T {tyvars,refty,...}) => 
            let
              val _ = if Vector.isEmpty tyvars then ()
                  else raise Return
            in
              case refty of
                RefTy.Base (_,tyd',_) => 
                  if TyD.sameType (tyd,tyd') 
                    then SOME v else NONE
              | _ => NONE
            end handle Return => NONE)

      datatype decl = Decl of Var.t * Exp.t
      
      fun mkDecl e = Decl (genVar (), e)

      fun mkHoleDecls (TyD.Trecord r) : decl list=
          let
            val tyds = Vector.map (Record.toVector r, snd)
            fun doItTyD (tyd, prevDecls) = 
              let
                val decls = mkHoleDecls tyd
                val Decl (v,_) = List.last decls
              in
                (v, List.concat [prevDecls,decls])
              end
            val (vars,varDecls) = Vector.mapAndFold (tyds,[],doItTyD)
            val tupTy = Type.fromMyType $ TyD.Trecord r
            open Exp
            val tupNode = Value $ Val.Tuple $ Vector.map (vars,
              fn var => Val.Var (var,Vector.new0 ()))
            val tupExp = make (tupNode,tupTy)
            val tupDecl = mkDecl tupExp
          in
            List.snoc (varDecls,tupDecl)
          end
        | mkHoleDecls tyd = [mkDecl $ Exp.make (Exp.newHole (), 
                                          Type.fromMyType tyd)]
      fun declToDec (Decl (v,e)) = 
        let
          open Dec
          val patval = Pat.Val.Atom $ Pat.Val.Var v
          val valbind = ExpBind (patval,e)
          val layTh = fn _ => L.empty
          val tyvarTh = fn _ => Vector.new0 ()
        in
          Val {rvbs=Vector.new0 (), tyvars=tyvarTh, 
               vbs = Vector.new1 {valbind=valbind, lay=layTh, nest=[]}}
        end

      (*
       * Given an expression fexp of arrow type, this function
       * creates an application of fexp to holes of appropriate type.
       *)
      fun mkAppSketch (fexp:Exp.t, TyD.Tarrow (argTyd,resFnTyd)) 
              : Exp.t =
          let
            open Exp
            val fatm = case node fexp of 
                Value (Val.Atom fatm) => fatm
              | _ => Error.bug "mkAppSketch: fexp isn't value\n"
            val resFnTy = Type.fromMyType resFnTyd
            val holeDecls = mkHoleDecls argTyd
            val Decl (holeV,_) = List.last holeDecls
            val appE = make (App (fatm, Val.Atom $ Val.Var 
                                      (holeV,Vector.new0 ())), 
                             resFnTy)
            val appDecl as Decl (appV, _) = mkDecl appE
            val appVExp = make (Value $ Val.Atom $ 
                            Val.Var (appV,Vector.new0 ()), resFnTy)
            val skTail = mkAppSketch (appVExp, resFnTyd)
            val skTyp = ty skTail
            (* holeDecls ---> holeDecs *)
            val holeDecs = List.map (holeDecls, declToDec)
            val appDec = declToDec appDecl
            val headDecs = Vector.fromList $ List.concat [holeDecs,
                                                          [appDec]]
            val skNode = case node skTail of 
                Let (tailDecs,e) =>  
                    Let (Vector.concat [headDecs,tailDecs],e)
              | e => Let (headDecs, make (e,skTyp))
          in
            make (skNode,skTyp)
          end
        | mkAppSketch (fexp:Exp.t, TyD.Tarrow _ ) = 
                  raise (Fail "mkAppSketch: Unimpl.")
          (* If ftyd is not a fn type, then fexp is the application
          expression *)
        | mkAppSketch (fexp:Exp.t, ftyd: TyD.t) = fexp

      exception Return 
      fun appSketchesOfTyd tyd = Vector.keepAllMap (tydbinds, 
        fn (v,RefTyS.T {tyvars,refty,...}) => 
          let
            val _ = print $ "Considering "^(Var.toString v)^" for \
                \ the hole of type "^(TyD.toString tyd)^"... \n"
            val _ = case refty of 
                RefTy.Base _ => if Vector.length tyvars > 0 then ()
                                else raise Return
              | _ => ()
            val fTyD = RefTy.toTyD refty
            val resTyD = TyD.resTyDOf fTyD
            val tyvarsInResTyD = Vector.fromList $ List.keepAllMap 
              (tyArgsInTyD resTyD, 
                fn (TyD.Tvar tyvar) => SOME tyvar | _ => NONE)
            (*
             * Special case: when all tyvars (alt. only tyvar) generalized
             * in fn type occur(s) as type args (as type) in its resTyD.
             * General case Unimpl.
             *)
            fun isTyvarInResTyD tyv = Vector.exists (tyvarsInResTyD,
              fn tyv' => tyvarEq (tyv,tyv'))
            val _ = if Vector.forall (tyvars, isTyvarInResTyD)
                    then () else raise Return
            val substs = case TyD.unify (resTyD,tyd) of
              SOME s => s | NONE => raise Return
            fun substToStr (tyd,tyv) = (TyD.toString tyd)^"/"
                    ^(Tyvar.toString tyv)
            val _ = print $ "Unification returned substs: "
                ^(Vector.toString substToStr substs)^"\n"
            val _ = assert (Vector.length tyvars = Vector.length
                substs, "Assumption about tyvars invalid\n")
            fun doSubst tyv = case Vector.peekMap (substs,
              fn (tyd,tyv') => if tyvarEq (tyv,tyv') then SOME tyd
                              else NONE) of 
                  SOME tyd => tyd 
                | NONE => Error.bug "expsOfTyd: No subst found\n"
            val ftargs = Vector.map (tyvars, Type.fromMyType o doSubst)
            val fTyD = TyD.instantiateTyvars substs fTyD
            open Exp
            val instFExp = make (Value $ Val.Atom $ Val.Var (v,ftargs),
                          Type.fromMyType fTyD)
          in
            case refty of 
                RefTy.Base _ => SOME instFExp
              | _ => SOME $ mkAppSketch (instFExp, fTyD)
          end handle Return => NONE)

      exception CantSolveSketch
      exception SketchSolved of Exp.t
      fun solveSketch (sketch, refTy) : Exp.t =
        raise (Fail "Unimpl.")

      fun mkAppChoiceExp holeExp = mapHoles (holeExp,
        fn hole =>
          let
            val holeTy = Exp.ty hole
            val appSketches = appSketchesOfTyd $ Type.toMyType holeTy
          in
            Exp.make (Exp.AppChoice appSketches, holeTy)
          end)

      datatype t2 = T2 of Exp.t * string(* holeId *) list

      fun t2sOfHoleExp (holeIds, holeExp) : t2 list =
        let
          val holeIdSplits = allPartitions holeIds 
          val varChooseExp = fn ty => Exp.make 
              (Exp.VarChoice $ varsOfTyd $ Type.toMyType ty,ty) 
          val t2s = List.map (holeIdSplits,
            fn (Split (s1,s2)) => T2 (mapHoles (holeExp,
              fn hole => 
                let
                  val Exp.Hole {id=holeId} = Exp.node hole
                  val holeTy = Exp.ty hole
                in
                  if listHas (s1,holeId) 
                  then varChooseExp holeTy
                  else hole
                end), s2))
        in
          t2s
        end
      (*
       * A datatype to denote choice.
       *)
      datatype 'a choice = Choose of 'a list
      fun singleChoice a = Choose [a]
      fun mapChoice (Choose l,f) = Choose $ List.map (l,f)
      fun expandChoice (Choose l,f) = Choose $ List.concat $
        List.map (l, fn x => case f x of Choose xs => xs)
      (*
       * A datatype to write the type of functions that take an
       * element of type 'a, and expand it to produce Many 'a choices,
       * or fail to expand it yeilding One 'a.
       *)
      datatype 'a some = One of 'a | Many of 'a choice
      fun expandChoiceInDec (dec:Dec.t) : Dec.t list some = 
        let
          open Dec
          val Val {rvbs,tyvars,vbs} = dec
          val _ = assert (Vector.length vbs=1, "impossible case")
          val [{valbind = ExpBind (pv,e),lay,nest}] = 
                Vector.toList vbs
          val Pat.Val.Atom (Pat.Val.Var v) = pv
          val flatExpChoice = fn _ => expandChoiceInExp e
          fun doItFlatExp (fexp) : Dec.t list = 
            case Exp.node fexp of
              Exp.Let (fdecs,fe) => List.snoc (Vector.toList fdecs,
                  declToDec $ Decl (v,fe))
            | _ => [declToDec $ Decl (v,fexp)]
        in
          if Exp.isAppChoice e 
          then Many $ mapChoice (flatExpChoice (), doItFlatExp)
          else One [dec]
        end

      and expandFirstChoiceInDecs [dec] : Dec.t list some = 
               expandChoiceInDec dec  
        | expandFirstChoiceInDecs (dec::decs) : Dec.t list some = 
            (case expandChoiceInDec dec of
              One [newDec] => 
                let
                  val ndSome = expandFirstChoiceInDecs decs
                in
                  case ndSome of 
                    One newDecs => One $ newDec::newDecs
                  | Many newDecsChoice => Many $ mapChoice 
                      (newDecsChoice, fn newDecs => newDec :: newDecs)
                end
            | Many newDecsChoice => Many $ mapChoice (newDecsChoice,
                  fn newDecs => List.append (newDecs,decs)))
        | expandFirstChoiceInDecs [] = Error.bug "Impossible case\n"

      and expandChoiceInExp (exp: Exp.t) : Exp.t choice =
        let
          open Exp
          val expTy = ty exp
          val expNode = node exp
        in
          case expNode of
              Let (decs,e) => 
                let
                  val ndSome = expandFirstChoiceInDecs $ 
                          Vector.toList decs
                  val mkLetWithNewDecs = fn newDecs => 
                      make (Let (Vector.fromList newDecs,e), expTy)
                  val expandExpChoices = fn choice => 
                      expandChoice (choice,expandChoiceInExp)
                in
                  case ndSome of One _ => singleChoice exp
                    | Many newDecsChoice => expandExpChoices $
                          mapChoice (newDecsChoice, mkLetWithNewDecs)
                end 
            | AppChoice exps => Choose $ Vector.toList exps
            | _ => singleChoice exp
        end

      fun allChildren (holeIds, holeExp:Exp.t) : Exp.t list =
        let
          val t2s = t2sOfHoleExp (holeIds, holeExp)
          val t2exps = List.map (t2s, fn (T2 (e,_)) => e)
          val choiceExps = List.map (t2exps, mkAppChoiceExp)
          val _ = print "---- Choice Exps ----\n"
          val _ = L.print (List.layout Exp.layout choiceExps, print)
          val flatExps = List.concat $ List.map (choiceExps, 
              fn choiceExp => case expandChoiceInExp choiceExp of   
                  Choose flatExps => flatExps)
          val _ = print "---- Flat Exps ----\n"
          val _ = L.print (List.layout Exp.layout flatExps, print)
        in
          raise (Fail "Unimpl.")
        end

      fun bfsSolve (holeExp::rest, refTy) =
        let
          val holeIds = allHoleIdsInExpr holeExp
          val exp =  if List.length holeIds = 0 
              (* then, this is a leaf node *)
              then solveSketch (holeExp, refTy) 
                      handle CantSolveSketch => bfsSolve (rest, refTy)
              else if List.length holeIds > 10
                   (* Artificial limit to keep the search tractable *)
                   then bfsSolve (rest, refTy)
                   else bfsSolve (List.concat [rest, 
                                               allChildren (holeIds, 
                                                            holeExp)], 
                                  refTy)
        in
          exp
        end 
        | bfsSolve ([],refTy) = raise (Fail "Can't solve the sketch!\n")

      val holeTy = Exp.ty holeExp
      val newV = genVar ()
      val newVDec = newValDec (newV,holeExp)
      val newVExp = newVarExp (newV,holeTy)
      val letExpNode = Exp.Let (Vector.new1 newVDec, newVExp)
      val letExp = Exp.make (letExpNode, holeTy)
    in
      bfsSolve ([letExp], refTy)
    end 
end
