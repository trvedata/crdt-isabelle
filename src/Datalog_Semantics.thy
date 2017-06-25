theory
  Datalog_Semantics
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin
  
subsection \<open>Semantics of Datalog rules\<close>

datatype 'val element =
  Var "string" |
  Val "'val"

datatype 'val atom =
  Match "string" "'val element list"

record 'val rule =
  rule_rel    :: "string"
  rule_params :: "string list"
  rule_atoms  :: "'val atom set"

type_synonym 'val fact = "string \<times> 'val list"
type_synonym 'val database = "'val fact set"
type_synonym 'val valuation = "string \<Rightarrow> 'val option"

fun match_vars :: "'val element list \<Rightarrow> 'val list \<Rightarrow> 'val valuation option" where
  "match_vars [] [] = Some Map.empty" |
  "match_vars (Val x # vars) (val # vals) =
     (if x = val then match_vars vars vals else None)" |
  "match_vars (Var v # vars) (val # vals) = do {
     mapping \<leftarrow> match_vars vars vals;
     case mapping v of
       None   \<Rightarrow> Some (mapping (v \<mapsto> val)) |
       Some x \<Rightarrow> if x = val then Some mapping else None
   }" |
  "match_vars _ _ = None"

fun subst_vars :: "'val element list \<Rightarrow> 'val valuation \<Rightarrow> 'val list option" where
  "subst_vars [] mapping = Some []" |
  "subst_vars (elem#vars) mapping = do {
     values \<leftarrow> subst_vars vars mapping;
     case elem of
       Val x \<Rightarrow> Some (x#values) |
       Var v \<Rightarrow> do { x \<leftarrow> mapping v; Some (x#values) }
   }"

definition match_atom :: "'val database \<Rightarrow> string \<Rightarrow> 'val element list \<Rightarrow> 'val database" where
  "match_atom db rel vars \<equiv> {(rel',vars') \<in> db. rel = rel' \<and> match_vars vars vars' \<noteq> None}"

fun satisfies :: "'val database \<Rightarrow> 'val atom \<Rightarrow> bool" (infix "\<Turnstile>" 60) where
  "db \<Turnstile> Match rel vars = (match_atom db rel vars \<noteq> {})"

thm match_vars.cases
thm match_vars.elims
thm match_vars.pelims
thm match_vars.induct
thm match_vars.simps
find_theorems name: match_vars

lemma match_vars_consistent:
  assumes "match_vars vars vals = Some mapping"
  shows "subst_vars vars mapping = Some vals"
using assms apply(induction vars arbitrary: vals mapping)
  apply(metis list.exhaust match_vars.simps(6) option.distinct(1) subst_vars.simps(1))
  apply(subgoal_tac "\<exists>x vals'. vals = x#vals'", (erule exE)+, simp)
  prefer 2
  apply(metis list.exhaust match_vars.simps(5) option.distinct(1))
  apply(erule_tac x="vals'" in meta_allE)
  apply(subgoal_tac "\<exists>map'. match_vars vars vals' = Some map'", erule exE, simp)
  prefer 2
  apply(case_tac a, simp, meson bind_eq_Some_conv)
  apply(metis match_vars.simps(2) option.discI)
  apply(erule_tac x="map'" in meta_allE, simp)
  apply(subgoal_tac "subst_vars vars map' = subst_vars vars mapping")
  apply(case_tac a, simp)
  apply(subgoal_tac "mapping x1 = Some x", simp)
  apply(case_tac "map' x1", force)
  apply(case_tac "aa = x", simp, simp)
  apply(simp, metis option.simps(3))
  oops

end
