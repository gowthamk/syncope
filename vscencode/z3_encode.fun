functor Z3_Encode (S : Z3_ENCODE_STRUCTS) :> Z3_ENCODE =
struct
  open S
  open Z3_FFI
  structure L = Layout
  exception InvalidOperation
  datatype sort = Int of z3_sort
                | Bool of z3_sort
                | T of string * z3_sort
  datatype ast = AST of z3_ast * sort
  datatype satisfiability = SAT | UNSAT | UNKNOWN
  (*
   * Set Invariant : len(ty) = len(domain(pred)) 
   * Null constructor is motivated by two reasons:
   * 1. To get away with not knowing the type of Null
   * set until we use it in an operation, where its type
   * is inferred and, consequently, gets converted to an 
   * empty set.
   * 2. What if it gets used in an operation with another
   * null set? The result can be statically determined 
   * without even having to go to Z3 - second motivation.
   *)
  datatype set = Null
               | Set of {ty : sort vector,
                         pred : ast vector -> z3_ast,
                         z3_func : z3_func_decl}
  datatype struc_rel = SR of {rel : ast -> set,
                              z3_func : z3_func_decl}
  type assertion = z3_ast
  type context = z3_context
  type model = z3_model
  val log = z3_log

  fun $ (f,arg) = f arg
  infixr 5 $
  val assert = Control.assert
  fun mkGenName (cnt,base) =
    let
      val count = ref cnt
    in
      fn () => 
        let 
          val name = base ^ (Int.toString (!count))
          val _ = count := !count + 1
        in
          name
        end
    end
  val genTypeName = mkGenName (0,"T")
  val genSetName = mkGenName (0,"set")
  val genConstName = mkGenName (0,"a!")

  fun mkDefaultContext () =
    let
      val cfg = Z3_mk_config ()
      val _   = Z3_global_param_set ("smt.macro-finder","true")
      val _   = Z3_global_param_set ("model.partial","false")
      val _   = Z3_global_param_set ("timeout","3")
      val _   = Z3_global_param_set ("trace","true") 
      val _   = Z3_global_param_set ("trace_file_name","z3.trace") 
      val ctx = Z3_mk_context cfg
      val _   = Z3_del_config cfg
    in
      ctx
    end

  fun checkContext ctx = 
    let
      val _ = log "(check-sat)"
      val _ = log "\n\n"
      val res = Z3_check ctx
    in
      case res of 1 => SAT | 0 => UNKNOWN | ~1 => UNSAT
        | _ => Error.bug "Integer received when Z3_lbool expected"
    end 

  fun checkContextGetModel ctx = 
    let
      val modelPtr = ref $ dummyModel ()
      val _ = Z3_push ctx
      val _ = log "(push)\n"
      val res = Z3_check_and_get_model (ctx,modelPtr)
      val _ = log "  (check-sat)\n"
      val _ = log "  (get-model)\n"
      val _ = Z3_pop (ctx,1)
      val _ = log "(pop)"
      val _ = log "\n\n"
      val satisfiability = case res of 1 => SAT 
        | 0 => UNKNOWN | ~1 => UNSAT
        | _ => Error.bug "Integer received when Z3_lbool expected"
    in
      (satisfiability, !modelPtr)
    end 

  val delContext = Z3_del_context

  fun isSortEq (Int _,Int _) = true
    | isSortEq (Bool _ , Bool _) = true
    | isSortEq (T (name1,_), T (name2, _)) = (name1 = name2)
    | isSortEq _ = false

  fun isPrimSort (Int _) = true
    | isPrimSort (Bool _) = true
    | isPrimSort _ = false

  (*
   * This function implements an object with encapsulated
   * state (ctx). 
   * Reference : http://mlton.org/ObjectOrientedProgramming
   *)
  fun generateAPI ctx = 
    let
      val mkSym = fn name => Z3_mk_string_symbol (ctx,name)

      (*
       * bool and int sorts declared here are not exposed.
       * Ones that are exposed are declared at the end.
       *)
      val bool_sort = Z3_mk_bool_sort ctx

      val int_sort = Z3_mk_int_sort ctx

      val falsee = Z3_mk_false ctx

      val truee = Z3_mk_true ctx

      fun mkUninterpretedSort () = 
        let
          val name = genTypeName ()
          val z3_sort = Z3_mk_uninterpreted_sort (ctx, mkSym name)
          val _ = log ("(declare-sort "^(Z3_sort_to_string 
            (ctx,z3_sort))^")")
          val _ = log "\n"
        in
          T (name, z3_sort)
        end

      fun astToZ3Ast (AST (z3_ast,sort)) = z3_ast

      fun astToString (AST (z3_ast,_)) =
        Z3_ast_to_string (ctx,z3_ast)

      fun sortOfAst (AST (_,sort)) = sort

      fun sortToZ3Sort sort = case sort of Int t => t 
        | Bool t => t | T (name,t) => t

      fun sortToString sort = Z3_sort_to_string (ctx, sortToZ3Sort sort)

      fun constToString ast = 
        case String.fromCString $ astToString ast of
          SOME str => str 
        | NONE => Error.bug "Z3_ffi: cannot convert C string \
                            \of a Z3 const to SML string\n"

      fun assnToString assnAst = astToString 
                      (AST (assnAst, Bool bool_sort))

      fun strucRelToString sr = raise (Fail "unimpl")

      fun typeCheckAst (AST (_,sort),sort') = isSortEq (sort,sort')

      fun sameTypeAsts (ast1, AST (_,sort2)) = typeCheckAst (ast1,sort2)

      fun mkEq (AST (x1,_),AST (x2,_)) = Z3_mk_eq (ctx,x1,x2)

      fun mkConst (name,sort) =
        let
          val z3_sort = sortToZ3Sort sort
          val const = Z3_mk_const (ctx, mkSym name, z3_sort)
          val _ = log $ "(declare-const "^(Z3_ast_to_string (ctx,const))
            ^" "^(Z3_sort_to_string (ctx,z3_sort))^")"
          val _ = log "\n"
        in
          AST (const,sort)
        end

      fun mkNewConst sort = mkConst (genConstName (), sort)

      fun mkBoundVar ctx (index,sort) = 
        AST (Z3_mk_bound (ctx,index,sortToZ3Sort sort),sort)

      (*
       * Encoding Sets and Structural Relations. 
       * An n-arity set is eta-equivalent of an n-arity boolean 
       * Z3 function. Set s = \(x1,x2,..,xn).z3_f(x1,x2,...,xn)
       * Eg: s = s1 ∪ s2 is encoded as  
       * ∀x1,x2,..,xn, s(x1,x2,..,xn) = s1(x1,x2,..,xn) 
       *                              ∨ s2 (x1,x2,..,xn)
       * An n-arity structural relation is a curried version of
       * eta-equivalent of n-arity boolean Z3 function.
       * Relation Rmem = \x1.\(x2,...,xn).z3_f(x1,x2,...,xn)
       * Relation application will, therefore, produce a function
       * that accepts n-1 arguments and produces an n-arity set.
       * Eg: Rmem(l) = Rmem(l1) U Rmem(l2) is encoded as 
       * ∀x1,..,xn-1, Rmem(l,x1,..,xn-1) = Rmem(l1,x1,..,xn-1) 
       *                                 ∨ Rmem(l2,x1,..,xn-1)
       *)
      fun mkSet (name,sorts) =
        let
          val nargs = Vector.length sorts
          val z3_sorts = Vector.map (sorts, sortToZ3Sort)
          val func = Z3_mk_func_decl (ctx, mkSym name, nargs,
            z3_sorts, bool_sort)
          val _ = log $ Z3_func_decl_to_string (ctx,func)
          val _ = log "\n"
          val pred = fn asts => 
            let
              (* Following results in Size exception. Reason unknown. *)
              (* Update: Fixed. Reason: C strings have to be converted
                        to SML strings. *)
              (*val astStr = fn _ =>(L.toString $ L.vector $ Vector.map 
                (asts, fn ast => L.str $ astToString ast))
              val sortStrs = List.map (Vector.toList sorts, fn s => 
                (sortToString s))
              val f = fn s => print $ (Int.toString $ String.length s)^"\n"
              val sortStr = fn _ => (List.fold (sortStrs, "(", fn (s,acc) =>
                (f s; acc^","^s)))^")"
              val _ = print $ sortStr () *)
              val errMsg = (fn _ => "Type Mismatch. Set: "^name^".\n")
              val _ = assert (Vector.length asts = Vector.length sorts,
                errMsg ())
              val _ = assert (Vector.forall2 (asts,sorts,typeCheckAst),
                errMsg ())
              val z3_asts = Vector.map (asts,astToZ3Ast)
            in
              Z3_mk_app (ctx, func, nargs, z3_asts)
            end
        in
          Set {ty = sorts, pred = pred, z3_func = func}
        end

      fun mkStrucRel (name,sorts) =
        let
          val nargs = Vector.length sorts
          val domainTy = Vector.sub (sorts,0)
          val Set {ty,pred,z3_func} = mkSet (name,sorts)
          val rel = fn ast => 
            let
              val _ = assert (typeCheckAst (ast,domainTy),
                "Type error at app of relation "^name^".\n"
                ^"Expected: "^(sortToString domainTy)^".\n"
                ^"Got: "^(sortToString $ sortOfAst ast)^".\n")
              (*
               * Constructing (n-1)-arity set from an n-arity
               * boolean function. 
               * n >= 2 invariant follows from structural relations.
               *)
              val ty' = Vector.dropPrefix (sorts,1)
              val pred' = fn asts => pred $ Vector.concat 
                [Vector.new1 ast, asts]
            in
              Set {ty = ty', pred = pred', z3_func=z3_func}
            end
        in
          SR {rel = rel, z3_func = z3_func}
        end

      fun mkStrucRelApp (SR {rel, ...}, ast) = rel ast

      fun mkSetProp (sorts : sort vector, propfn : ast vector -> 
        (z3_pattern vector * z3_ast)) =
        let
          val numbvs = Vector.length sorts
          val bvs = Vector.mapi (sorts, fn (i,sort) => 
            mkBoundVar ctx (i,sort))
          (* 
           * De-brujin. Therefore: bv_n:T_n, bv_n-1:T_n-1,...,bv_0:T_0 
           *)
          val bvnames = Vector.tabulate (numbvs, fn i => mkSym 
            ("bv"^(Int.toString (numbvs-i-1))))
          val bvtys = Vector.rev $ Vector.map (sorts,sortToZ3Sort)
          (* 
           * Note: bvs satisfies the inv: ∀i. bvs[i] : sorts[i].
           * Since prop expects (sorts[0] * sorts[1] * ... * sorts[n]), 
           * it is apt to pass (bvs[0] * bvs[1] * ... * bvs[n]).
           *)
          val (patterns,prop) = propfn bvs
          val forall = Z3_mk_forall (ctx, 0, 
                        Vector.length patterns, 
                        patterns,
                        numbvs,
                        bvtys, 
                        bvnames, 
                        prop)
        in
          forall
        end

      fun dischargeAssertion asr = 
        let
          val _ = log $ "(assert "^(Z3_ast_to_string (ctx,asr))^")"
          val _ = log "\n"
        in
           Z3_assert_cnstr (ctx,asr)
        end

      fun assertSetProp (sorts,prop) =
        dischargeAssertion $ mkSetProp (sorts,prop)

      val mkNullSet = fn () => Null

      fun mkEmptySet sorts = 
        let
          val set as Set {ty,pred,...} = mkSet (genSetName (),sorts)
          val _ = assertSetProp (sorts, fn bvAsts =>
            let
              val fnapp = pred bvAsts
              val prop = Z3_mk_eq (ctx,fnapp,falsee)
              val pattern = Z3_mk_pattern (ctx,1,Vector.new1 fnapp)
            in
              (Vector.new1 pattern, prop)
            end)
        in
          set 
        end

      fun mkSingletonSet asts = 
        let
          val sorts = Vector.map (asts,sortOfAst)
          val set as Set {ty,pred,...} = mkSet (genSetName (),sorts)
          val _ = assertSetProp (sorts, fn bvAsts =>
            let
              val fnapp = pred bvAsts
              val eqs = Vector.map2 (bvAsts,asts,mkEq)
              val conj = Z3_mk_and (ctx,Vector.length eqs,eqs)
              val iff = Z3_mk_iff (ctx,fnapp,conj)
              val pattern = Z3_mk_pattern (ctx,1,Vector.new1 fnapp)
            in
              (Vector.new1 pattern, iff)
            end)
        in
          set
        end

      fun mkMultiPatterns multipatlist = Vector.fromList $ List.map 
        (multipatlist, fn terms => Z3_mk_pattern (ctx, List.length terms,
          Vector.fromList terms))

      fun mkSimplePatterns patlist = Vector.fromList $ List.map (patlist,
        fn pat => Z3_mk_pattern (ctx, 1, Vector.fromList [pat]))

      fun mkSetEqAssertion (s1,s2) = case (s1,s2) of 
          (Null,Null) => truee
        | (Null,Set {ty,...}) => mkSetEqAssertion (mkEmptySet ty, s2)
        | (Set {ty,...},Null) => mkSetEqAssertion (s1, mkEmptySet ty)
        | (Set {ty=sorts1,pred=pred1, ...}, 
           Set {ty=sorts2,pred=pred2, ...}) => 
          (*
           * Pre-condition of sorts1 = sorts2 is automatically
           * checked when pred1 and pred2 are applied
           *)
          mkSetProp (sorts1, fn bvAsts => 
            let
              val fnapp1 = pred1 bvAsts
              val fnapp2 = pred2 bvAsts
              val iff = Z3_mk_iff (ctx,fnapp1,fnapp2)
              val pats = mkSimplePatterns [fnapp1,fnapp2]
            in
              (pats,iff)
            end)
       
      fun mkSubSetAssertion (s1,s2) = case (s1,s2) of 
          (Null,Null) => falsee
        | (Null,Set {ty,...}) => truee
        | (Set {ty,...},Null) => falsee
        | (Set {ty=sorts1,pred=pred1, ...}, 
           Set {ty=sorts2,pred=pred2, ...}) => 
          (*
           * Pre-condition of sorts1 = sorts2 is automatically
           * checked when pred1 and pred2 are applied
           *)
          mkSetProp (sorts1, fn bvAsts => 
            let
              val fnapp1 = pred1 bvAsts
              val fnapp2 = pred2 bvAsts
              val implies = Z3_mk_implies (ctx,fnapp1,fnapp2)
              val pats = mkSimplePatterns [fnapp1,fnapp2]
            in
              (pats,implies)
            end)
       
      val mkUnion = fn (Null,s2) => s2 | (s1,Null) => s1 
        | (Set {ty=sorts1,pred=pred1, ...}, 
           Set {ty=sorts2,pred=pred2, ...}) =>
          let
            val s as Set {ty,pred, ...} = mkSet (genSetName (), sorts1)
            val _ = assertSetProp (ty, fn bvAsts =>
              let
                val fnapp = pred bvAsts
                val fnapp1 = pred1 bvAsts
                val fnapp2 = pred2 bvAsts
                val disj = Z3_mk_or (ctx,2,Vector.fromList 
                  [fnapp1,fnapp2])
                val iff = Z3_mk_iff (ctx,fnapp,disj)
                val pats = mkSimplePatterns [fnapp, fnapp1, fnapp2]
              in
                (pats, iff)
              end)
          in
            s
          end
       
      val mkCrossPrd = fn (Null,_) => Null | (_,Null) => Null 
        | (Set {ty=sorts1,pred=pred1, ...}, 
           Set {ty=sorts2,pred=pred2, ...}) =>
          let
            val sorts = Vector.concat [sorts1,sorts2]
            val s as Set {ty,pred, ...} = mkSet (genSetName (), sorts)
            val _ = assertSetProp (ty, fn bvAsts =>
              let
                val bvAsts1 = Vector.prefix (bvAsts,Vector.length 
                  sorts1)
                val bvAsts2 = Vector.dropPrefix (bvAsts, 
                  Vector.length sorts1)
                val fnapp = pred bvAsts
                val fnapp1 = pred1 bvAsts1
                val fnapp2 = pred2 bvAsts2
                val conj = Z3_mk_and (ctx,2,Vector.fromList 
                  [fnapp1,fnapp2])
                val iff = Z3_mk_iff (ctx,fnapp,conj)
                val pats = mkMultiPatterns [[fnapp], [fnapp1,fnapp2]]
              in
                (pats, iff)
              end)
          in
            s
          end

      val mkDiff = fn (Null,s2) => Null | (s1,Null) => s1 
        | (Set {ty=sorts1,pred=pred1, ...}, 
           Set {ty=sorts2,pred=pred2, ...}) =>
          let
            val s as Set {ty,pred, ...} = mkSet (genSetName (), sorts1)
            val _ = assertSetProp (ty, fn bvAsts =>
              let
                val fnapp = pred bvAsts
                val fnapp1 = pred1 bvAsts
                val fnapp2 = pred2 bvAsts
                val nfnapp2 = Z3_mk_not (ctx,fnapp2)
                val conj = Z3_mk_and (ctx,2,Vector.fromList 
                  [fnapp1,nfnapp2])
                val iff = Z3_mk_iff (ctx,fnapp,conj)
                val pats = mkSimplePatterns [fnapp, fnapp1, fnapp2]
              in
                (pats, iff)
              end)
          in
            s
          end

      fun mkNot asr = Z3_mk_not (ctx, asr) 

      fun mkIf (asr1,asr2) = Z3_mk_implies (ctx, asr1, asr2) 

      fun mkIff (asr1,asr2) = Z3_mk_iff (ctx, asr1, asr2) 

      fun mkAnd asrv = Z3_mk_and (ctx, Vector.length asrv, asrv) 

      fun mkOr asrv = Z3_mk_or (ctx, Vector.length asrv, asrv) 

      fun mkConstEqAssertion (ast1 as AST (x1,s1), AST (x2,s2)) = 
        (typeCheckAst (ast1,s2); Z3_mk_eq (ctx,x1,x2))

      fun mkDistinctness asts = 
        let
          val equalities = List.map (List.subsets (asts,2),
              fn [x1,x2] => mkConstEqAssertion (x1,x2))
        in
          (mkNot o mkOr) $ Vector.fromList equalities
        end

      val mkDistinctness = fn asts => if Vector.length asts < 2 
            then truee else mkDistinctness $ Vector.toList asts

      fun mkUniverseAssn sort asts = 
        mkSetProp (Vector.new1 sort, fn bvAsts => 
          let
            val bvAst = Vector.sub (bvAsts,0)
            val equalities = Vector.map (asts, 
              fn ast => mkConstEqAssertion (bvAst,ast))
          in
            (Vector.new0 (), mkOr equalities)
          end)

      fun mkInt i = AST (Z3_mk_int (ctx, i, int_sort), Int int_sort)

      fun applySubstsInAssn substs assn =
        let
          val num_exprs = Vector.length substs
          val (to,from) = Vector.unzip $ Vector.map (substs,
            fn (newAst,oldAst) => 
              (assert (sameTypeAsts (newAst,oldAst), "Invalid \
                      \ substitution attempted\n"); 
               (astToZ3Ast newAst, astToZ3Ast oldAst)))
        in
          Z3_substitute (ctx, assn, num_exprs, from, to)
        end

      fun doPush () = (log "(push)\n"; Z3_push ctx)

      fun doPop () = (log "(pop)\n"; Z3_pop (ctx,1))

      fun modelToString model = Z3_model_to_string (ctx,model)

      fun evalConst model (lhsAst as AST (z3_ast,sort))= 
        let
          val val_ast_ptr = ref truee
          val res = Z3_eval (ctx,model,z3_ast,val_ast_ptr)
          val _ = case res of 1 => ()
            | 0 => Error.bug ("Z3_eval error\n")
          val val_ast = ! val_ast_ptr
          val rhsAst = AST (val_ast, sort)
        in
          mkConstEqAssertion (lhsAst, rhsAst)
        end

      fun evalStrucRel model (SR {z3_func, rel, ...}) =
        let
          val arity = Z3_get_arity (ctx, z3_func)
          val srArgSorts = Vector.tabulate (arity, fn i =>
            let
              val z3_sort = Z3_get_domain (ctx, z3_func, i)
              val str = Z3_sort_to_string (ctx, z3_sort)
            in
              T (str,z3_sort)
            end)
          val fn_body_ptr = ref truee
          fun propfn bvAsts = 
            let
              val bv0 = Vector.sub (bvAsts,0)
              val bvAsts' = Vector.dropPrefix (bvAsts,1)
              val Set {ty, pred, ...} = rel bv0
              val lhs = pred bvAsts'
              val arg_asts = Vector.map (bvAsts,astToZ3Ast)
              val _ = Z3_eval_decl (ctx, model, z3_func,
                              arity, arg_asts, fn_body_ptr)
              val rhs = !fn_body_ptr
              val iff = Z3_mk_iff (ctx,lhs,rhs)
              val pats = mkSimplePatterns [] (* [lhs] *)
            in
              (pats, iff)
            end
          val qprop = mkSetProp (srArgSorts,propfn)
          (*val qprop_str = Z3_ast_to_string (ctx,qprop)
          val _ = print "\tQuantified Prop:\n"
          val _ = print $ "\t"^qprop_str^"\n" *)
        in
          qprop
        end

      fun getSortUniverse model sort = 
        let
          val _ = if isPrimSort sort then raise (Fail "Sort universe\
            \ cannot be enumerated for a primitive type.") else ()
          val z3_sort = sortToZ3Sort sort
          val ast_vec = Z3_model_get_sort_universe (ctx,model,z3_sort)
          val size = Z3_ast_vector_size (ctx,ast_vec)
        in
            Vector.tabulate (size, 
              fn i => AST (Z3_ast_vector_get (ctx, ast_vec, i),sort))
        end

      fun debug model (vStr, SR {z3_func, rel, ...}) =
        let
          val _ = print $ "Details of interpretation for the \
              \function "^vStr^":\n"
          val numParams = Z3_get_decl_num_parameters (ctx, z3_func)
          val numParamsStr = Int.toString numParams
          val interp = Z3_model_get_func_interp (ctx, model, z3_func)
          val arity = Z3_func_interp_get_arity (ctx,interp)
          val arityStr = Int.toString arity
          val srArgSorts = Vector.tabulate (arity, fn i =>
            let
              val z3_sort = Z3_get_domain (ctx, z3_func, i)
              val str = Z3_sort_to_string (ctx, z3_sort)
            in
              T (str,z3_sort)
            end)

          val fn_body_ptr = ref truee
          (*
          val fn_body = !fn_body_ptr
          val _ = print "\tFn Body:\n"
          val _ = print $ "\t"^(Z3_ast_to_string (ctx,fn_body))^"\n"
          val params = Z3_mk_params ctx
          val sym1 = Z3_mk_string_symbol (ctx,"ite_extra_rules")
          val _ = Z3_params_set_bool (ctx, params, sym1, 1)
          val sym2 = Z3_mk_string_symbol (ctx,"local_ctx")
          val _ = Z3_params_set_bool (ctx, params, sym2, 1)
          val simpl_fn_body = Z3_simplify_ex (ctx, fn_body, params)
          val _ = print "\tSimplified Fn Body:\n"
          val _ = print $ "\t"^(Z3_ast_to_string (ctx,simpl_fn_body))^"\n"
          *)
          (* Quantified prop *)
          fun propfn bvAsts = 
            let
              val bv0 = Vector.sub (bvAsts,0)
              val bvAsts' = Vector.dropPrefix (bvAsts,1)
              val Set {ty, pred, ...} = rel bv0
              val lhs = pred bvAsts'
              val arg_asts = Vector.map (bvAsts,astToZ3Ast)
              val _ = Z3_eval_decl (ctx, model, z3_func,
                              arity, arg_asts, fn_body_ptr)
              val rhs = !fn_body_ptr
              val iff = Z3_mk_iff (ctx,lhs,rhs)
              val pats = mkSimplePatterns [] (* [lhs] *)
            in
              (pats, iff)
            end
          val qprop = mkSetProp (srArgSorts,propfn)
          val qprop_str = Z3_ast_to_string (ctx,qprop)
          val _ = print "\tQuantified Prop:\n"
          val _ = print $ "\t"^qprop_str^"\n"
          (*
          val num_entries = Z3_func_interp_get_num_entries (ctx,interp)
          val num_entries_str = Int.toString num_entries
          val entry_strs = List.tabulate (num_entries, 
            fn i => 
              let
                val iStr = (Int.toString i)
                val entry = Z3_func_interp_get_entry (ctx, interp, i)
                val nArgs = Z3_func_entry_get_num_args (ctx, entry)
                val args = List.tabulate (nArgs, 
                  fn i => Z3_func_entry_get_arg (ctx, entry, i))
                val args_str = List.toString (fn arg =>
                    Z3_ast_to_string (ctx, arg)) args
                val entry_ast = Z3_func_entry_get_value (ctx, entry)
                val entry_str = Z3_ast_to_string (ctx, entry_ast)
              in
                "fn "^args_str^" => "^entry_str
              end)
          val else_ast = Z3_func_interp_get_else (ctx,interp)
          val else_ast_str = Z3_ast_to_string (ctx,else_ast)
          val _ = print $ "\tNum Params: "^numParamsStr^"\n"
          val _ = print $ "\tArity: "^arityStr^"\n"
          val _ = print $ "\tNum entries: "^num_entries_str^"\n"
          val _ = print $ "\tEntries:\n"
          val _ = Control.message (Control.Top, fn _ =>
              L.align $ List.map (entry_strs, L.str))
          val _ = print "\t'else' entry:\n"
          val _ = print $ "\t\t"^else_ast_str^"\n"
          *)
          (*
           * What is Z3_get_model_func_entry_arg?
           *)
        in
          ()
        end
 
    in
      {
        bool_sort = Bool bool_sort,
        int_sort = Int int_sort,
        const_false = AST (falsee, Bool bool_sort),
        const_true = AST (truee, Bool bool_sort),
        truee = truee,
        falsee = falsee,
        isSortEq = isSortEq,
        isPrimSort = isPrimSort,
        sortToString = sortToString,
        constToString = constToString,
        strucRelToString = strucRelToString,
        assnToString = assnToString,
        mkUninterpretedSort = mkUninterpretedSort,
        mkConst = mkConst,
        mkNewConst = mkNewConst,
        mkInt = mkInt,
        mkStrucRel = mkStrucRel,
        mkStrucRelApp = mkStrucRelApp,
        mkNullSet = mkNullSet,
        mkSingletonSet = mkSingletonSet,
        mkUnion = mkUnion,
        mkCrossPrd = mkCrossPrd,
        mkDiff = mkDiff,
        mkSetEqAssertion = mkSetEqAssertion,
        mkSubSetAssertion = mkSubSetAssertion,
        mkConstEqAssertion = mkConstEqAssertion,
        mkNot = mkNot,
        mkIf = mkIf,
        mkIff = mkIff,
        mkAnd = mkAnd,
        mkOr = mkOr,
        mkDistinctness = mkDistinctness,
        mkUniverseAssn = mkUniverseAssn,
        applySubstsInAssn = applySubstsInAssn,
        dischargeAssertion = dischargeAssertion,
        doPush = doPush,
        doPop = doPop,
        modelToString = modelToString,
        evalConst = evalConst,
        evalStrucRel = evalStrucRel,
        getSortUniverse = getSortUniverse,
        debug = debug
       }
    end
end
