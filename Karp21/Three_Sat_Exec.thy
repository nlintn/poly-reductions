theory Three_Sat_Exec
  imports Three_Sat_To_Set_Cover TR_Fun_Defs
begin

definition
  "conflict_exec a1 a2 ≡ case (a1, a2) of
    (Pos a1', Neg a2') ⇒ a1' = a2'
  | (Neg a1', Pos a2') ⇒ a1' = a2'
  | (_, _) ⇒ False"

lemma conflict_exec_eq_conflict[simp]: "conflict_exec = conflict"
  by (auto simp: fun_eq_iff conflict_exec_def conflict_def split: lit.split)

definition
  "Set_List_rel r s xs ≡ rel_set r s (set xs)"

lemma Set_List_relI[intro]: 
  assumes "rel_set r s (set xs)"
  shows "Set_List_rel r s xs"
  unfolding Set_List_rel_def using assms .

lemma Set_List_relD[dest]:
  assumes "Set_List_rel r s xs"
  shows "rel_set r s (set xs)" 
  using assms unfolding Set_List_rel_def .

lemma Set_List_rel_iff[simp]: "Set_List_rel r s xs ⟷ rel_set r s (set xs)"
  by blast

definition
  "Set_List_rel_eq ≡ Set_List_rel (=)"

lemma Set_List_rel_eqI[intro]: 
  assumes "s = set xs"
  shows "Set_List_rel_eq s xs"
  unfolding Set_List_rel_eq_def using assms Set_List_relI by (auto simp: rel_set_eq)

lemma Set_List_rel_eqD[dest]:
  assumes "Set_List_rel_eq s xs"
  shows "s = set xs" 
  using assms unfolding Set_List_rel_eq_def Set_List_relD by (auto simp: rel_set_eq)

lemma Set_List_rel_eq_iff[simp]: "Set_List_rel_eq = Set_List_rel (=)"
  unfolding Set_List_rel_eq_def by simp

definition
  "n_Set_List_rel_eq n s xs ≡ Set_List_rel_eq s xs ∧ card s = n"

lemma n_Set_List_rel_eqI[intro]:
  assumes "Set_List_rel_eq s xs" "card s = n"
  shows "n_Set_List_rel_eq n s xs"
  unfolding n_Set_List_rel_eq_def using assms by simp

lemma n_Set_List_rel_eqE[elim]:
  assumes "n_Set_List_rel_eq n s xs"
  obtains "Set_List_rel_eq s xs" "card s = n"
  using assms unfolding n_Set_List_rel_eq_def by simp

definition
  "Sat_List_rel ≡ list_all2 Set_List_rel_eq"

lemma Sat_List_rel_iff[simp]:
    "Sat_List_rel = list_all2 Set_List_rel_eq"
  unfolding Sat_List_rel_def by simp

definition
  "n_Sat_List_rel n ≡ list_all2 (n_Set_List_rel_eq n)"

lemma n_Sat_List_rel_iff[simp]:
    "n_Sat_List_rel n = list_all2 (n_Set_List_rel_eq n)"
  unfolding n_Sat_List_rel_def by simp

lemma Sat_List_rel_if_n_Sat_List_rel:
  assumes "n_Sat_List_rel n s xs" 
  shows "Sat_List_rel s xs"
  using assms by (auto intro: list_all2_mono elim!: n_Set_List_rel_eqE)
 
lemma n_Sat_List_relI:
  assumes "list_all2 Set_List_rel_eq sat_set sat_list"
          "⋀s. s ∈ set sat_set ⟹ card s = n"
  shows "n_Sat_List_rel n sat_set sat_list"
  using assms by (auto elim!: list.rel_mono_strong)

lemma n_Sat_List_relE:
  assumes "n_Sat_List_rel n sat_set sat_list"
  obtains "list_all2 Set_List_rel_eq sat_set sat_list"
          "⋀s. s ∈ set sat_set ⟹ card s = n"
  using assms by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth)

type_synonym 'a sat_list = "'a lit list list"
(*
definition
  "is_3cnf_sat xs ≡ list_all (λx . card (set x) = 3) xs"

lemma is_3cnf_satI[intro]: 
  assumes "⋀x. x ∈ set xs ⟹ card (set x) = 3"
  shows "is_3cnf_sat xs"
  unfolding is_3cnf_sat_def using assms by (simp add: list.pred_set)

lemma is_3cnf_satE[elim]: 
  assumes "is_3cnf_sat xs"
  obtains "⋀x. x ∈ set xs ⟹ card (set x) = 3"
  using assms unfolding is_3cnf_sat_def by (simp add: list.pred_set)
*)

lemma list_all2_memE:
  assumes "list_all2 r ys xs" "x ∈ set xs"
  obtains y where "r y x" "y ∈ set ys"
  using assms(2, 1)
  by (induction xs arbitrary: ys) (fastforce simp: list_all2_Cons2)+

unbundle lifting_syntax

definition
  "si_un_fst F ≡ {{(l1, i), (l2, i)} | l1 l2 i. i < length F ∧ l1 ∈ F ! i ∧ l2 ∈ F ! i ∧ l1 ≠ l2}"

definition
  "si_un_fst'_prod F ≡
    let
      p1 = enumerate 0 F;
      p2 = map (λ(i, xsb). (λx. (x, i)) ` xsb) p1;
      p3 = map (λs. s × s) p2;
      p4 = map (λs. Set.filter (λ((a, _), (b, _)). a ≠ b) s) p3;
      p5 = ⋃ (set p4)
    in p5"

definition
  "si_un_fst' F ≡ (λ(a, b). {a, b}) ` (si_un_fst'_prod F)"

lemma si_un_fst'_eq: "si_un_fst F = si_un_fst' F"
proof -
  have "si_un_fst'_prod F = {((l1, i), (l2, i)) | l1 l2 i. i < length F ∧ l1 ∈ F ! i ∧ l2 ∈ F ! i ∧ l1 ≠ l2}"
    by (fastforce simp: in_set_enumerate_eq si_un_fst'_prod_def)
  then show ?thesis
    unfolding si_un_fst_def si_un_fst'_def by auto
qed

definition
  "si_un_fst_exec F ≡
    let
      p1 = enumerate 0 F;
      p2 = map (λ(xsa, xsb). map (λx. (x, xsa)) xsb) p1;
      p3 = map (λxs. List.product xs xs) p2;
      p4 = map (λxs. filter (λ((a, _), (b, _)). a ≠ b) xs) p3;
      p5 = concat p4;
      p6 = map (λ(a, b). [a, b]) p5
    in p6"

definition
  "si_un_fst_exec_tr F ≡
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (λ(xsa, xsb). map_tr (λx. (x, xsa)) xsb) p1;
      p3 = map_tr (λxs. product_tr xs xs) p2;
      p4 = map_tr (λxs. filter_tr (λ((a, _), (b, _)). a ≠ b) xs) p3;
      p5 = concat_tr p4;
      p6 = map_tr (λ(a, b).  [a, b]) p5
    in p6"

lemma si_un_fst_exec_tr_eq[simp]: "si_un_fst_exec_tr = si_un_fst_exec"
  unfolding si_un_fst_exec_tr_def si_un_fst_exec_def tr_simps by argo

definition
  "IS_List_rel ≡ Set_List_rel (n_Set_List_rel_eq 2)"

lemma IS_List_rel_iff[simp]: "IS_List_rel = Set_List_rel (n_Set_List_rel_eq 2)"
  unfolding IS_List_rel_def by simp
(*
lemma rel_fun_comp:
  assumes "(rel ===> rel') f1 g1" "(rel' ===> rel'') f2 g2"
  shows "(rel ===> rel'') (f2 ∘ f1) (g2 ∘ g1)"

  using assms comp_apply by (auto intro!: rel_funI elim: rel_funE)
*)
definition
  "n_Set_List_enum_rel_eq n ≡ rel_prod (=) (n_Set_List_rel_eq n)"

lemma n_Set_List_enum_rel_eqI[intro]:
  assumes "si = li" "n_Set_List_rel_eq n s l"
  shows "n_Set_List_enum_rel_eq n (si, s) (li, l)"
  unfolding n_Set_List_enum_rel_eq_def using assms by simp

lemma n_Set_List_enum_rel_eqE[elim]:
  assumes "n_Set_List_enum_rel_eq n (si, s) (li, l)"
  obtains "si = li" "n_Set_List_rel_eq n s l"
  using assms unfolding n_Set_List_enum_rel_eq_def by simp

definition
  "n_Sat_List_enum_rel n ≡ list_all2 (n_Set_List_enum_rel_eq n)"

lemma n_Sat_List_enum_rel_iff[simp]: "n_Sat_List_enum_rel n sat_set sat_list ⟷ list_all2 (n_Set_List_enum_rel_eq n) sat_set sat_list"
  unfolding n_Sat_List_enum_rel_def by simp

definition
  "Set_List_rel_eq_prod_diff ≡ Set_List_rel (λa b. a = b ∧ fst a ≠ snd a)"

lemma Set_List_rel_eq_prod_diffI1[intro]:
  assumes "Set_List_rel_eq s xs" "list_all (λ(a, b). a ≠ b) xs"
  shows "Set_List_rel_eq_prod_diff s xs"
  unfolding Set_List_rel_eq_prod_diff_def using assms
  by (simp add: case_prod_beta list.pred_set rel_set_def)

lemma Set_List_rel_eq_prod_diffI2:
  assumes "Set_List_rel_eq s xs" "Powp (λ(a, b). a ≠ b) s"
  shows "Set_List_rel_eq_prod_diff s xs"
  unfolding Set_List_rel_eq_prod_diff_def using assms
  by (simp add: case_prod_beta rel_set_def Powp_def)

lemma Set_List_rel_eq_prod_diffE[elim]:
  assumes "Set_List_rel_eq_prod_diff s xs"
  obtains "Set_List_rel_eq s xs" "list_all (λ(a, b). a ≠ b) xs" "Powp (λ(a, b). a ≠ b) s"
  using assms unfolding Set_List_rel_eq_prod_diff_def
  by (simp add: case_prod_beta' list.pred_set rel_set_def Powp_def)

lemma Set_List_rel_eq_prod_diff_iff: "Set_List_rel_eq_prod_diff = Set_List_rel (λa b. a = b ∧ fst a ≠ snd a)"
  unfolding Set_List_rel_eq_prod_diff_def by simp

definition
  "Sat_List_rel_prod_diff ≡ list_all2 Set_List_rel_eq_prod_diff"

lemma Sat_List_rel_prod_diff_iff[simp]: "Sat_List_rel_prod_diff = list_all2 Set_List_rel_eq_prod_diff"
  unfolding Sat_List_rel_prod_diff_def by simp

lemma Sat_List_rel_if_Sat_List_rel_prod_diff:
  assumes "Sat_List_rel_prod_diff s xs"
  shows "Sat_List_rel s xs"
  using assms by (auto elim!: list_all2_mono)

(* lemma n_Sat_List_enum_relI[intro]: *)
(*   assumes "list_all2 (=) (map fst sat_set) (map fst sat_list)" *)
(*           "n_Sat_List_rel n (map snd sat_set) (map snd sat_list)" *)
(*   shows "n_Sat_List_enum_rel n sat_set sat_list" *)
(*   unfolding n_Sat_List_enum_rel_def using assms by (rule conjI) *)
(**)
(* lemma n_Sat_List_enum_relE[elim]: *)
(*   assumes "n_Sat_List_enum_rel n sat_set sat_list" *)
(*   obtains "list_all2 (=) (map fst sat_set) (map fst sat_list)" *)
(*           "n_Sat_List_rel n (map snd sat_set) (map snd sat_list)" *)
(*   using assms unfolding n_Sat_List_enum_rel_def by (rule conjE) *)

lemma image_map_rel[transfer_rule]: "((r ===> s) ===> Set_List_rel r ===> Set_List_rel s) image map"
  unfolding rel_fun_def Set_List_rel_iff rel_set_def by fastforce

lemma image_map_rel_eq[transfer_rule]: "(((=) ===> (=)) ===> Set_List_rel_eq ===> Set_List_rel_eq) image map"
  unfolding Set_List_rel_eq_iff by transfer_prover

lemma Sfilter_Lfilter_rel[transfer_rule]: "((r ===> (=)) ===> Set_List_rel r ===> Set_List_rel r) Set.filter filter"
  unfolding rel_fun_def Set_List_rel_iff rel_set_def by fastforce

lemma Sprod_Lprod_rel[transfer_rule]: "(n_Set_List_rel_eq n ===> n_Set_List_rel_eq m ===> n_Set_List_rel_eq (n * m)) (×) List.product"
  by fastforce

lemma UN_set_concat_rel[transfer_rule]: "(list_all2 (Set_List_rel r) ===> (Set_List_rel r)) (λs. ⋃ (set s)) concat"
  by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth rel_set_def)

lemma union_append_rel[transfer_rule]: "(Set_List_rel r ===> Set_List_rel r ===> Set_List_rel r) (∪) (@)"
  unfolding rel_fun_def Set_List_rel_iff rel_set_def by auto

lemma si_un_fst_rel: "(n_Sat_List_rel 3 ===> IS_List_rel) si_un_fst si_un_fst_exec_tr"
proof -
  have [transfer_rule]: "(n_Sat_List_rel 3 ===> n_Sat_List_enum_rel 3) (enumerate 0) (enumerate 0)"
    by (auto simp: list_all2_conv_all_nth n_Set_List_enum_rel_eqI nth_enumerate_eq)
  have [transfer_rule]: "(n_Sat_List_enum_rel 3 ===> n_Sat_List_rel 3)
    (map (λ(a, b). (λx. (x, a)) ` b))
    (map (λ(a, b). map (λx. (x, a)) b))" (is "_ (map ?fs2) (map ?fl2)")
  proof -
    define fs fl where def: "fs = ?fs2" "fl = ?fl2"
    have [transfer_rule]: "(n_Set_List_enum_rel_eq 3 ===> n_Set_List_rel_eq 3) fs fl"
      by (fastforce simp: rel_set_eq inj_on_def card_image def)
    show ?thesis
      unfolding n_Sat_List_enum_rel_iff n_Sat_List_rel_iff def[symmetric]
      by transfer_prover
  qed
  have [transfer_rule]: "(n_Sat_List_rel 3 ===> n_Sat_List_rel (3 * 3)) (map (λs. s × s)) (map (λl. List.product l l))"
    unfolding n_Sat_List_rel_iff by transfer_prover
  have [transfer_rule]: "(n_Sat_List_rel (3 * 3) ===> Sat_List_rel_prod_diff)
    (map (Set.filter (λ((a, _), (b, _)). a ≠ b)))
    (map (filter (λ((a, _), (b, _)). a ≠ b)))" (is "_ (map (Set.filter ?f4)) (map (filter ?f4))")
  proof -
    define f where def: "f = ?f4"
    have [transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel_eq_prod_diff) (Set.filter f) (filter f)"
      by (fastforce simp: Set.filter_def rel_set_eq list.pred_set def)
    have "(Sat_List_rel ===> Sat_List_rel_prod_diff) (map (Set.filter f)) (map (filter f))"
      unfolding Sat_List_rel_iff Sat_List_rel_prod_diff_iff by transfer_prover
    from rel_fun_mono[OF this, unfolded def] show ?thesis
      using Sat_List_rel_if_n_Sat_List_rel by blast
  qed
  have [transfer_rule]: "(Sat_List_rel_prod_diff ===> Set_List_rel_eq_prod_diff) (λs. ⋃ (set s)) concat"
    unfolding Sat_List_rel_prod_diff_iff Set_List_rel_eq_prod_diff_iff by transfer_prover
  have [transfer_rule]: "(Set_List_rel_eq_prod_diff ===> IS_List_rel) (image (λ(a, b). {a, b})) (map (λ(a, b). [a, b]))" (is "_ (image ?fs6) (map ?fl6)")
  proof -
    define fs fl where def: "fs = ?fs6" "fl = ?fl6"
    have [transfer_rule]: "((λa b. a = b ∧ fst a ≠ snd a) ===> n_Set_List_rel_eq 2) fs fl"
      by (auto simp: def rel_fun_def rel_set_def)
    show ?thesis
      unfolding def[symmetric] Set_List_rel_eq_prod_diff_def IS_List_rel_iff by transfer_prover
  qed
  show ?thesis
    unfolding si_un_fst'_eq si_un_fst'_def si_un_fst'_prod_def si_un_fst_exec_tr_eq si_un_fst_exec_def Let_def
    by transfer_prover
qed

definition
  "si_un_snd F ≡ {{(l1, i), (l2, j)} | l1 l2 i j. i < length F ∧ j < length F ∧ l1 ∈ F ! i ∧ l2 ∈ F ! j ∧ conflict l1 l2}"

definition
  "si_un_snd'_prod F ≡
    let
      p1 = enumerate 0 F;
      p2 = map (λ(xsa, xsb). (λx. (x, xsa)) ` xsb) p1;
      p3 = List.product p2 p2;
      p4 = map (λ(a, b). a × b) p3;
      p5 = ⋃ (set p4);
      p6 = Set.filter (λ((a, _), (b, _)). conflict a b) p5
    in p6"

definition
  "si_un_snd' F ≡ (λ(a, b). {a, b}) ` si_un_snd'_prod F"

lemma si_un_snd'_eq: "si_un_snd F = si_un_snd' F"
proof -
  have "si_un_snd'_prod F = {((l1, i), (l2, j)) | l1 l2 i j. i < length F ∧ j < length F ∧ l1 ∈ F ! i ∧ l2 ∈ F ! j ∧ conflict l1 l2}"
    by (fastforce simp: in_set_enumerate_eq si_un_snd'_prod_def Let_def)
  then show ?thesis
    unfolding si_un_snd_def si_un_snd'_def by auto
qed

definition
  "si_un_snd_exec F ≡
    let
      p1 = enumerate 0 F;
      p2 = map (λ(xsa, xsb). map (λx. (x, xsa)) xsb) p1;
      p3 = List.product p2 p2;
      p4 = map (λ(a, b). List.product a b) p3;
      p5 = concat p4;
      p6 = filter (λ((a, _), (b, _)). conflict_exec a b) p5;
      p7 = map (λ(a, b). [a, b]) p6
    in p7"

definition
  "si_un_snd_exec_tr F ≡
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (λ(xsa, xsb). map_tr (λx. (x, xsa)) xsb) p1;
      p3 = product_tr p2 p2;
      p4 = map_tr (λ(a, b). product_tr a b) p3;
      p5 = concat_tr p4;
      p6 = filter_tr (λ((a, _), (b, _)). conflict_exec a b) p5;
      p7 = map_tr (λ(a, b). [a, b]) p6
    in p7"

lemma si_un_snd_exec_tr_eq[simp]: "si_un_snd_exec_tr = si_un_snd_exec"
  unfolding si_un_snd_exec_tr_def si_un_snd_exec_def tr_simps by argo

lemma si_un_snd_rel: "(n_Sat_List_rel 3 ===> IS_List_rel) si_un_snd si_un_snd_exec_tr"
proof -
  have [transfer_rule]: "(n_Sat_List_rel 3 ===> n_Sat_List_enum_rel 3) (enumerate 0) (enumerate 0)"
    unfolding n_Sat_List_rel_iff n_Sat_List_enum_rel_iff
    by (auto simp: list_all2_conv_all_nth n_Set_List_enum_rel_eqI nth_enumerate_eq)
  have [transfer_rule]: "(n_Sat_List_enum_rel 3 ===> n_Sat_List_rel 3)
    (map (λ(a, b). (λx. (x, a)) ` b))
    (map (λ(a, b). map (λx. (x, a)) b))" (is "_ (map ?fs2) (map ?fl2)")
  proof -
    define fs fl where def: "fs = ?fs2" "fl = ?fl2"
    have [transfer_rule]: "(n_Set_List_enum_rel_eq 3 ===> n_Set_List_rel_eq 3) fs fl"
      by (fastforce simp: rel_set_eq inj_on_def card_image def)
    show ?thesis
      unfolding n_Sat_List_enum_rel_iff n_Sat_List_rel_iff def[symmetric]
      by transfer_prover
  qed
  have [transfer_rule]: "(n_Sat_List_rel 3 ===> list_all2 (rel_prod (n_Set_List_rel_eq 3) (n_Set_List_rel_eq 3)))
        (λa. List.product a a) (λb. List.product b b)"
    unfolding n_Sat_List_rel_iff by transfer_prover
  have [transfer_rule]: "(list_all2 (rel_prod (n_Set_List_rel_eq 3) (n_Set_List_rel_eq 3)) ===> n_Sat_List_rel (3 * 3))
        (map (λ(a, b). a × b)) (map (λ(a, b). List.product a b))"
    unfolding n_Sat_List_rel_iff by transfer_prover
  have [transfer_rule]: "(n_Sat_List_rel (3 * 3) ===> Set_List_rel_eq) (λs. ⋃ (set s)) concat"
  proof -
    have "(Sat_List_rel ===> Set_List_rel_eq) (λs. ⋃ (set s)) concat"
      unfolding Sat_List_rel_iff Set_List_rel_eq_def by transfer_prover
    from rel_fun_mono[OF this] show ?thesis
      using Sat_List_rel_if_n_Sat_List_rel by blast
  qed
  have "(Set_List_rel_eq ===> Set_List_rel (λa b. a = b ∧ conflict (fst (fst a)) (snd (fst a)))) (Set.filter (λ((a, _), (b, _)). conflict a b))
    (filter (λ((a, _), (b, _)). conflict a b))"
    unfolding Set_List_rel_eq_iff  
    apply (intro rel_funI Set_List_relI rel_setI)
    apply (auto simp: rel_set_eq)
    oops
  have [transfer_rule]: "(n_Sat_List_rel (3 * 3) ===> Sat_List_rel_prod_diff)
    (map (Set.filter (λ((a, _), (b, _)). a ≠ b)))
    (map (filter (λ((a, _), (b, _)). a ≠ b)))" (is "_ (map (Set.filter ?f4)) (map (filter ?f4))")
  proof -
    define f where def: "f = ?f4"
    have [transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel_eq_prod_diff) (Set.filter f) (filter f)"
      by (fastforce simp: Set.filter_def rel_set_eq list.pred_set def)
    have "(Sat_List_rel ===> Sat_List_rel_prod_diff) (map (Set.filter f)) (map (filter f))"
      unfolding Sat_List_rel_iff Sat_List_rel_prod_diff_iff by transfer_prover
    from rel_fun_mono[OF this, unfolded def] show ?thesis
      using Sat_List_rel_if_n_Sat_List_rel by blast
  qed
  have [transfer_rule]: "(Sat_List_rel_prod_diff ===> Set_List_rel_eq_prod_diff) (λs. ⋃ (set s)) concat"
    unfolding Sat_List_rel_prod_diff_iff Set_List_rel_eq_prod_diff_iff
    by (auto intro!: rel_funI simp: in_set_conv_nth list_all2_conv_all_nth rel_set_def ) (metis nth_mem split_pairs)+
  have [transfer_rule]: "(Set_List_rel_eq_prod_diff ===> IS_List_rel) (image (λ(a, b). {a, b})) (map (λ(a, b). [a, b]))" (is "_ (image ?fs6) (map ?fl6)")
  proof -
    define fs fl where def: "fs = ?fs6" "fl = ?fl6"
    have [transfer_rule]: "((λa b. a = b ∧ fst a ≠ snd a) ===> n_Set_List_rel_eq 2) fs fl"
      by (auto simp: def rel_fun_def rel_set_def)
    show ?thesis
      unfolding def[symmetric] Set_List_rel_eq_prod_diff_def IS_List_rel_iff by transfer_prover
  qed
  show ?thesis
    unfolding si_un_fst'_eq si_un_fst'_def si_un_fst'_prod_def si_un_fst_exec_tr_eq si_un_fst_exec_def Let_def
    by transfer_prover
qed
end
