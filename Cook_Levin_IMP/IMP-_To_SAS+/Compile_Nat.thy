theory Compile_Nat
  imports Primitives_IMP_Minus
begin

ML \<open>
  datatype tc_ast = If of (int * tc_ast * tc_ast * tc_ast) |
                    App of (int * term * tc_ast list)

  datatype imp =
    Skip
  | Seq of (imp * imp)
  | Assign of (indexname * (term * indexname list))
  | Copy of (indexname * indexname)
  | IfNeqZero of (indexname * (indexname * imp * imp))

  fun tc_ast_of_term t =
    let
      fun fold_step a (index, args_ast) =
            let val (index', a_ast) = index_tc_ast index a
            in (index', a_ast :: args_ast) end
      and index_tc_ast index (App (_, f, args)) =
        let
          val (index', rev_args') = fold fold_step args (index, [])
        in
          (index' + 1, App (index', f, rev rev_args'))
        end
        | index_tc_ast index (If (_, c, e1, e2)) =
        let
          val (index', [e2', e1', c']) = fold fold_step [c, e1, e2] (index, [])
        in
          (index' + 1, If (index', c', e1', e2'))
        end
        

      fun build_tc_ast t =
        case Term.strip_comb t of
          (\<^Const>\<open>HOL.If \<^typ>\<open>nat\<close>\<close>
          , [\<^Const>\<open>HOL.Not for \<open>\<^Const>\<open>HOL.eq \<^typ>\<open>nat\<close> for c \<open>\<^Const>\<open>Groups.zero \<^typ>\<open>nat\<close>\<close>\<close>\<close>\<close>\<close>, e1, e2]) =>
            let
              val [c_ast, e1_ast, e2_ast] = map build_tc_ast [c, e1, e2]
            in
              If (~1, c_ast, e1_ast, e2_ast)
            end
        | (f, args) => App (~1, f, map build_tc_ast args)
    in
      t |> build_tc_ast |> index_tc_ast 0 |> snd
    end

  fun reg_of_term idx (Const (s, _)) = (s, idx)
    | reg_of_term idx (Free (s, _)) = (s, idx)

  fun imp_of_tc_ast (App (index, t, args)) =
    let
      val args_instrs = map imp_of_tc_ast args
      val arg_regs = map fst args_instrs;
      val ret_reg = reg_of_term index t
      val assign_ret = Assign (ret_reg, (t, arg_regs))
      val seq_args_instrs = List.foldr (op Seq) Skip (map snd args_instrs)
    in
      (ret_reg, Seq (seq_args_instrs, assign_ret))
    end
   | imp_of_tc_ast (If (idx, astc, ast1, ast2)) =
    let
      val ret_reg = ("IfNeqZero", idx)
      val [impc, imp1, imp2] = map imp_of_tc_ast [astc, ast1, ast2]
    in
      (ret_reg, Seq (snd impc,
        IfNeqZero (ret_reg,
          ( fst impc
          , Seq (snd imp1, Copy (ret_reg, fst imp1))
          , Seq (snd imp2, Copy (ret_reg, fst imp2))
          ))
      ))
    end

  fun let_of_imp (ret_reg, imp) =
    let
      fun reg_of_indexname (n, i) =
        String.map (fn c => if c = #"." then #"_" else c) n
        ^ "_" ^ Int.toString i
      val natT = \<^typ>\<open>nat\<close>
      fun reg_var_of_indexname n = Free (reg_of_indexname n, natT)
      
      fun go target Skip = target
        | go target (Seq (imp1, imp2)) = go (go target imp2) imp1
        | go target (Copy (reg1, reg2)) =
        let
          val (reg1_var, reg2_var) = apply2 reg_var_of_indexname (reg1, reg2)
        in
          \<^Const>\<open>Let natT natT for reg2_var \<open>lambda reg1_var target\<close>\<close>
        end
        | go target (Assign (reg, (f, args))) =
        let
          val reg_var = reg_var_of_indexname reg
          val args_var = map reg_var_of_indexname args
        in
          \<^Const>\<open>Let natT natT for \<open>list_comb (f, args_var)\<close> \<open>lambda reg_var target\<close>\<close>
        end
        (* Ignoring target should work since we can't sequence if in HOL *)
        | go target (IfNeqZero (ret_reg, (cond_reg, e1, e2))) =
        let
          val (ret_reg_var, cond_reg_var) =
            apply2 reg_var_of_indexname (ret_reg, cond_reg)
          val (e1_let, e2_let) = apply2 (go ret_reg_var) (e1, e2)
          val condt = \<^Const>\<open>HOL.Not for
            \<^Const>\<open>HOL.eq natT for cond_reg_var \<^Const>\<open>Groups.zero natT\<close>\<close>\<close>
        in
          \<^Const>\<open>HOL.If natT for condt e1_let e2_let\<close>
        end
        
    in
      go (reg_var_of_indexname ret_reg) imp
    end

  fun define_let_of_def def binding lthy =
    let
      val (args, def_body) =
        Local_Defs.abs_def_rule lthy def
        |> Thm.rhs_of |> Thm.term_of |> Term.strip_abs
      val let_def =
           def_body
        |> curry Term.subst_bounds (map Free args |> rev)
        |> tc_ast_of_term
        |> imp_of_tc_ast
        |> let_of_imp
        |> fold_rev Term.absfree args (* Could go wrong if there are fixed variables in the context *)
    in
      Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), let_def)) lthy
      |> snd
    end
\<close>
definition "test (x :: nat) (y :: nat) \<equiv> if x + y \<noteq> 0 then if y \<noteq> 0 then y else x else 0"

local_setup \<open>
  define_let_of_def @{thm test_def} \<^binding>\<open>test_let\<close>
\<close>
print_theorems

lemma "test x y = test_let x y"
  unfolding test_def test_let_def by (simp add: Let_def)

end
