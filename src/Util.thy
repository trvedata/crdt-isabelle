theory
  Util
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin

section\<open>Kleisli arrow composition for the option monad\<close>

definition kleisli :: "('b \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'b option)" (infixr "\<rhd>" 65) where
  "f \<rhd> g \<equiv> \<lambda>x. f x \<bind> (\<lambda>fx. g fx)"

lemma kleisli_comm_cong:
  assumes "x \<rhd> y = y \<rhd> x"
  shows   "z \<rhd> x \<rhd> y = z \<rhd> y \<rhd> x"
using assms by(clarsimp simp add: kleisli_def)

lemma kleisli_assoc:
  shows "(z \<rhd> x) \<rhd> y = z \<rhd> (x \<rhd> y)"
by(auto simp add: kleisli_def)

section\<open>Technical set lemmas\<close>

lemma distinct_set_notin [dest]:
  assumes "distinct (x#xs)"
  shows   "x \<notin> set xs"
using assms by(induction xs, auto)

lemma set_membership_equality_technicalD [dest]:
  assumes "{x} \<union> (set xs) = {y} \<union> (set ys)"
    shows "x = y \<or> y \<in> set xs"
using assms by(induction xs, auto)

lemma set_equality_technical:
  assumes "{x} \<union> (set xs) = {y} \<union> (set ys)"
      and "x \<notin> set xs"
      and "y \<notin> set ys"
      and "y \<in> set xs"
  shows "{x} \<union> (set xs - {y}) = set ys"
using assms by (induction xs) auto

lemma list_nil_or_snoc:
  shows "xs = [] \<or> (\<exists>y ys. xs = ys@[y])"
by (induction xs, auto)

lemma suffix_eq_distinct_list:
  assumes "distinct xs"
      and "ys@suf1 = xs"
      and "ys@suf2 = xs"
    shows "suf1 = suf2"
using assms by(induction xs arbitrary: suf1 suf2 rule: rev_induct, simp) (metis append_eq_append_conv)

lemma pre_suf_eq_distinct_list:
  assumes "distinct xs"
      and "ys \<noteq> []"
      and "pre1@ys@suf1 = xs"
      and "pre2@ys@suf2 = xs"
    shows "pre1 = pre2 \<and> suf1 = suf2"
using assms
  apply(induction xs arbitrary: pre1 pre2 ys, simp)
  apply(case_tac "pre1"; case_tac "pre2"; clarify)
  apply(metis suffix_eq_distinct_list append_Nil)
  apply(metis Un_iff append_eq_Cons_conv distinct.simps(2) list.set_intros(1) set_append suffix_eq_distinct_list)
  apply(metis Un_iff append_eq_Cons_conv distinct.simps(2) list.set_intros(1) set_append suffix_eq_distinct_list)
  apply(metis distinct.simps(2) hd_append2 list.sel(1) list.sel(3) list.simps(3) tl_append2)
done

lemma set_elem_nth:
  assumes "x \<in> set xs"
  shows   "\<exists>m. m < length xs \<and> xs ! m = x"
using assms by(induction xs, simp) (meson in_set_conv_nth)

section\<open>Technical list lemmas\<close>

lemma list_nth_split_technical:
  assumes "m < length cs"
      and "cs \<noteq> []"
    shows "\<exists>xs ys. cs = xs@(cs!m)#ys"
using assms
  apply(induction m arbitrary: cs)
  apply(meson in_set_conv_decomp nth_mem)
  apply(metis in_set_conv_decomp length_list_update set_swap set_update_memI)
done

lemma list_nth_split:
  assumes "m < length cs"
      and "n < m"
      and "1 < length cs"
    shows "\<exists>xs ys zs. cs = xs@(cs!n)#ys@(cs!m)#zs"
using assms
  apply(induction n arbitrary: cs m)
  apply(rule_tac x="[]" in exI, clarsimp)
  apply(case_tac cs; clarsimp)
  apply(rule list_nth_split_technical, simp, force)
  apply(case_tac cs; clarsimp)
  apply(erule_tac x="list" in meta_allE, erule_tac x="m-1" in meta_allE)
  apply(subgoal_tac "m-1 < length list", subgoal_tac "n<m-1", clarsimp)
  apply(rule_tac x="a#xs" in exI, rule_tac x="ys" in exI, rule_tac x="zs" in exI)
  apply auto
done

lemma map_filter_append:
  shows "List.map_filter P (xs @ ys) = List.map_filter P xs @ List.map_filter P ys"
by(auto simp add: List.map_filter_def)

end