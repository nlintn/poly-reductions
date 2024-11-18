theory TR_Fun_Defs
  imports HOL.List
begin

section "Equivalent tail recursive definitions of standard HOL list functions"

paragraph "Tail recursive reverse"

fun rev_tr_acc :: "'a list ⇒ 'a list ⇒ 'a list"  where
  "rev_tr_acc acc [] = acc"
| "rev_tr_acc acc (x#xs) = rev_tr_acc (x#acc) xs"

lemma rev_tr_acc: "rev_tr_acc acc xs = rev xs @ acc"
  by (induction xs arbitrary: acc) simp_all

definition
  "rev_tr ≡ rev_tr_acc []"

lemma rev_tr_eq_rev[simp]: "rev_tr = rev"
  by (simp add: fun_eq_iff rev_tr_def rev_tr_acc)


paragraph "Tail recursive enumerate"

fun enumerate_tr_acc :: "(nat \<times> 'a) list ⇒ nat ⇒ 'a list ⇒ (nat \<times> 'a) list"  where
  "enumerate_tr_acc acc i [] = rev_tr acc"
| "enumerate_tr_acc acc i (x#xs) = enumerate_tr_acc ((i, x) # acc) (Suc i) xs"

lemma enumerate_tr_acc: "enumerate_tr_acc acc i xs = rev acc @ enumerate i xs"
  by (induction xs arbitrary: acc i) simp_all

definition
  "enumerate_tr ≡ enumerate_tr_acc []"

lemma enumerate_tr_eq_enumerate[simp]: "enumerate_tr = enumerate"
  by (simp add: fun_eq_iff enumerate_tr_def enumerate_tr_acc)


paragraph "Tail recursive map"

fun map_tr_acc :: "'b list ⇒ ('a ⇒ 'b) ⇒ 'a list ⇒ 'b list"  where
  "map_tr_acc acc f [] = rev_tr acc"
| "map_tr_acc acc f (x#xs) = map_tr_acc (f x # acc) f xs"

lemma map_tr_acc: "map_tr_acc acc f xs = rev acc @ map f xs"
  by (induction xs arbitrary: acc) simp_all

definition
  "map_tr ≡ map_tr_acc []"

lemma map_tr_eq_map[simp]: "map_tr = map"
  by (simp add: fun_eq_iff map_tr_def map_tr_acc)


paragraph "Tail recursive filter"

fun filter_tr_acc :: "'a list ⇒ ('a ⇒ bool) ⇒ 'a list ⇒ 'a list"  where
  "filter_tr_acc acc p [] = rev_tr acc"
| "filter_tr_acc acc p (x#xs) = filter_tr_acc (if p x then x # acc else acc) p xs"

lemma filter_tr_acc: "filter_tr_acc acc p xs = rev acc @ filter p xs"
  by (induction xs arbitrary: acc) simp_all

definition
  "filter_tr ≡ filter_tr_acc []"

lemma filter_tr_eq_filter[simp]: "filter_tr = filter"
  by (simp add: fun_eq_iff filter_tr_def filter_tr_acc)


paragraph "Tail recursive append"

fun append_tr_acc :: "'a list ⇒ 'a list ⇒ 'a list"  where
  "append_tr_acc acc [] = acc"
| "append_tr_acc acc (x#xs) = append_tr_acc (x # acc) xs"

lemma append_tr_acc: "append_tr_acc acc xs = rev xs @ acc"
  by (induction xs arbitrary: acc) simp_all

definition append_tr (infixr \<open>@tr\<close> 65) where 
  "xs @tr ys ≡ append_tr_acc ys (rev_tr xs)" 

lemma append_tr_eq_append[simp]: "append_tr = append"
  by (simp add: fun_eq_iff append_tr_def append_tr_acc)


paragraph "Tail recursive concat"

fun concat_tr_acc :: "'a list ⇒ 'a list list ⇒ 'a list"  where
  "concat_tr_acc acc [] = acc"
| "concat_tr_acc acc (l#ls) = concat_tr_acc (acc @tr l) ls"

lemma concat_tr_acc: "concat_tr_acc acc ls = acc @ concat ls"
  by (induction ls arbitrary: acc) simp_all

definition
  "concat_tr ≡ concat_tr_acc []"

lemma concat_tr_eq_concat[simp]: "concat_tr = concat"
  by (simp add: fun_eq_iff concat_tr_def concat_tr_acc)


paragraph "Tail recursive List.product"

fun product_tr_acc :: "('a × 'b) list ⇒ 'a list ⇒ 'b list ⇒ ('a × 'b) list"  where
  "product_tr_acc acc [] _ = acc"
| "product_tr_acc acc (x#xs) ys =  product_tr_acc (acc @ map_tr (Pair x) ys) xs ys"

lemma product_tr_acc: "product_tr_acc acc xs ys = acc @ List.product xs ys"
  by(induction xs arbitrary: acc) simp_all

definition
  "product_tr ≡ product_tr_acc []"

lemma product_tr_eq_product[simp]: "product_tr = List.product"
  by (simp add: fun_eq_iff product_tr_def product_tr_acc)


paragraph "Tail recursive 'λx xs. x ∈ set xs'"

fun isin_tr :: "'a ⇒ 'a list ⇒ bool"  where
  "isin_tr a [] = False"
| "isin_tr a (x#xs) = (if a = x then True else isin_tr a xs)"

lemma isin_tr_eq_in_set[simp]: "isin_tr = (λa xs. a ∈ set xs)"
proof -
  have "isin_tr a xs ⟷ a ∈ set xs" for a::'a and xs::"'a list"
    by (induction xs) simp_all
  then show ?thesis
    by (simp add: fun_eq_iff)
qed


paragraph "Tail recursive remdups"

fun remdups_tr_acc :: "'a list ⇒ 'a list ⇒ 'a list"  where
  "remdups_tr_acc acc [] = rev acc"
| "remdups_tr_acc acc (x#xs) = remdups_tr_acc (if ¬(isin_tr x xs) then x # acc else acc) xs"

lemma remdups_tr_acc: "remdups_tr_acc acc xs = rev acc @ remdups xs"
  by (induction xs arbitrary: acc) simp_all

definition
  "remdups_tr ≡ remdups_tr_acc []"

lemma remdups_tr_eq_remdups[simp]: "remdups_tr = remdups"
  by (simp add: fun_eq_iff remdups_tr_def remdups_tr_acc)


paragraph "Tail recursive list_all"

fun list_all_tr :: "('a ⇒ bool) ⇒ 'a list ⇒ bool"  where
  "list_all_tr p [] = True"
| "list_all_tr p (x#xs) = (if p x then list_all_tr p xs else False)"

lemma list_all_tr_eq_list_all[simp]: "list_all_tr = list_all"
proof -
  have "list_all_tr p xs = list_all p xs" for p::"'a ⇒ bool" and xs::"'a list"
    by (induction xs) simp_all
  then show ?thesis
    by (simp add: fun_eq_iff)
qed


paragraph "Tail recursive length"

fun length_tr_acc :: "nat ⇒ 'a list ⇒ nat"  where
  "length_tr_acc acc [] = acc"
| "length_tr_acc acc (x#xs) = length_tr_acc (Suc acc) xs"

lemma length_tr_acc: "length_tr_acc acc xs = acc + length xs"
  by (induction xs arbitrary: acc) simp_all

definition
  "length_tr ≡ length_tr_acc 0"

lemma length_tr_eq_length[simp]: "length_tr = length"
  by (simp add: fun_eq_iff length_tr_acc length_tr_def)


lemmas tr_simps =
  rev_tr_eq_rev enumerate_tr_eq_enumerate map_tr_eq_map filter_tr_eq_filter
  append_tr_eq_append concat_tr_eq_concat product_tr_eq_product isin_tr_eq_in_set
  remdups_tr_eq_remdups list_all_tr_eq_list_all length_tr_eq_length

end
