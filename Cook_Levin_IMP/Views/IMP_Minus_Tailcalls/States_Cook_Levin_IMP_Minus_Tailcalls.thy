\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory States_Cook_Levin_IMP_Minus_Tailcalls
  imports
    IMP_Minus.IMP_Tailcalls_Dynamic
    IMP_Minus_Views.Simps_To
    IMP_Minus_Views.Views_Base
    IMP_Minus_Views.ML_State_Seq
begin

paragraph \<open>Summary\<close>
text \<open>Views adapted to track @{session IMP_Minus} state changes in the
@{session Cook_Levin_IMP} refinement theorems.\<close>

text\<open>The next lemmas are needed since, in the Cook-Levin project,
the correctness theorems for the refinements state their state changes in terms
of functions (i.e. the semantics of states) directly.

In principle, we may not require being able to inject a @{type state} into a @{term State}.\<close>

lemma interp_state_State_eq:
  "interp_state (State s) = s"
  unfolding interp_state_def by simp

text \<open>We now set up the framework that tracks state changes of IMP commands
by using a @{typ "(vname, val) state"}. More precisely, we will keep track of
a state equality that relates the initial state of an IMP program to its current
state.

This tracking happens in a special premise, which we set up next.\<close>

definition "STATE (s :: AExp.state) \<equiv> s"

text \<open>@{term STATE} is just a wrapper that contains a state.\<close>

lemma STATE_eq: "STATE s = s" unfolding STATE_def by simp

text \<open>Prevent simplification of arguments\<close>
lemma STATE_cong [cong]: "STATE s = STATE s" by simp

text \<open>In the beginning, we simply know that the state is equal to itself.\<close>

lemma STATE_start: "STATE (interp_state st) = STATE (interp_state st)" by simp

text \<open>The following is used to rewrite state retrievals according to a tracked
state equality.\<close>

lemma state_state_app_eqI:
  assumes "interp_state st = interp_state st'"
  and "interp_state st = s"
  and "interp_state st' k = val"
  shows "s k = val"
  using assms by simp

lemma STATE_state_app_eqI:
  assumes "STATE (interp_state st) = STATE (interp_state st')"
  and  "SIMPS_TO (interp_state st) s"
  and "SIMPS_TO (interp_state st' k) val"
  shows "s k = val"
  using assms unfolding STATE_eq SIMPS_TO_iff
  by (fact state_state_app_eqI)

text \<open>The following is used to update a state equality according to a new
retrieval condition.\<close>

lemma update_state_state_app_eq:
  assumes "interp_state st = interp_state st'"
  and "interp_state st = s"
  and "s k = val"
  and "val = val'"
  shows "interp_state st = interp_state (update_state st' k val')"
  using assms by auto

lemma update_STATE_state_app_eq:
  assumes "STATE (interp_state st) = STATE (interp_state st')"
  and  "SIMPS_TO (interp_state st) s"
  and "s k = val"
  and "SIMPS_TO val val'"
  shows "STATE (interp_state st) = STATE (interp_state (update_state st' k val'))"
  using assms unfolding STATE_eq SIMPS_TO_iff
  by (fact update_state_state_app_eq)

text \<open>The following is used to update a state equality according to a new
update condition.\<close>

lemma update_state_state_eq_update:
  assumes "interp_state st = interp_state st'"
  and "interp_state st = s"
  and "s' = s(k := val)"
  and "val = val'"
  shows "interp_state (State s') = interp_state (update_state st' k val')"
  using assms by (simp add: interp_state_State_eq)

lemma update_STATE_state_eq_update:
  assumes "STATE (interp_state st) = STATE (interp_state st')"
  and  "SIMPS_TO (interp_state st) s"
  and "s' = s(k := val)"
  and "SIMPS_TO val val'"
  shows "STATE (interp_state (State s')) = STATE (interp_state (update_state st' k val'))"
  using assms unfolding STATE_eq SIMPS_TO_iff by (fact update_state_state_eq_update)


ML_file\<open>state_cook_levin_imp_minus_tailcalls.ML\<close>

(*TODO:
1. the framework currently only collects a big state equality without
simplifying it. As a result, every retrieval from these views needs to simplify
a (complex) series of update operations.
We could instead simplify the states themselves to speed up the proofs and
make them more reliable. Currently, we rely on @{method fastforce} to simplify
the chain of operations.

2. integrate the logger from https://github.com/kappelmann/logger-isabelle
*)

end