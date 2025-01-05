theory IS_Definition
  imports Main
begin

section \<open>Preliminaries\<close>

type_synonym 'a ugraph = "'a set set"

definition
  "ugraph E \<equiv> finite E \<and> (\<forall>e \<in> E. card e = 2)" \<comment> \<open>Allow self-loops?\<close>

section "The problem"

definition
  "is_independent_set E V \<equiv> \<forall>u \<in> V. \<forall>v \<in> V. {u, v} \<notin> E"

definition
  "independent_set \<equiv> {(E, k). \<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> card V \<ge> k \<and> is_independent_set E V}"

end