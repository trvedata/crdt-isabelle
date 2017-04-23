(* Victor B. F. Gomes, University of Cambridge
   Martin Kleppmann, University of Cambridge
   Dominic P. Mulligan, University of Cambridge
*)

section\<open>Technical Lemmas\<close>

text\<open>This section contains a list of helper definitions and lemmas about sets, lists and
     the option monad.\<close>

theory
  Util
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin

subsection\<open>Kleisli arrow composition\<close>

definition kleisli :: "('b \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'b option)" (infixr "\<rhd>" 65) where
  "f \<rhd> g \<equiv> \<lambda>x. (f x \<bind> (\<lambda>y. g y))"

lemma kleisli_comm_cong:
  assumes "x \<rhd> y = y \<rhd> x"
  shows   "z \<rhd> x \<rhd> y = z \<rhd> y \<rhd> x"
using assms by(clarsimp simp add: kleisli_def)

lemma kleisli_assoc:
  shows "(z \<rhd> x) \<rhd> y = z \<rhd> (x \<rhd> y)"
by(auto simp add: kleisli_def)

subsection\<open>Lemmas about sets\<close>

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
    
lemma set_elem_nth:
  assumes "x \<in> set xs"
  shows   "\<exists>m. m < length xs \<and> xs ! m = x"
  using assms by(induction xs, simp) (meson in_set_conv_nth)

subsection\<open>Lemmas about nondeterministic choice and let\<close>

lemma unpack_let:
  assumes "(let x = y in f x) = z"
  and "\<And>x. x = y \<Longrightarrow> f x = z \<Longrightarrow> R"
  shows R
using assms by auto

lemma some_set_memb:
  assumes "y \<noteq> {}"
  shows "(SOME x. x \<in> y) \<in> y"
by (rule someI_ex, simp add: assms ex_in_conv)

lemma choose_set_memb:
  assumes "y \<noteq> {}"
  and "x = (SOME x. x \<in> y)"
  shows "x \<in> y"
using assms by (simp add: some_set_memb)

lemma let_some_elim:
  assumes "(let x = (SOME x. P x) in f x) = z"
    and "\<exists>x. P x"
    and "\<And>x. P x \<Longrightarrow> f x = z \<Longrightarrow> R"
  shows R
  using assms by (metis someI)

lemma let_some_set_elim:
  assumes "(let x = (SOME x'. x' \<in> y) in f x) = z"
  and "y \<noteq> {}"
  and "\<And>x. (x \<in> y \<and> f x = z) \<Longrightarrow> R"
  shows R
by (metis assms some_set_memb)

subsection\<open>Lemmas about list\<close>

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

lemma list_head_unaffected:
  assumes "hd (x @ [y, z]) = v"
    shows "hd (x @ [y   ]) = v"
  using assms by (metis hd_append list.sel(1))

lemma list_head_butlast:
  assumes "hd xs = v"
  and "length xs > 1"
  shows "hd (butlast xs) = v"
  using assms by (metis hd_conv_nth length_butlast length_greater_0_conv less_trans nth_butlast zero_less_diff zero_less_one)

lemma list_head_length_one:
  assumes "hd xs = x"
    and "length xs = 1"
  shows "xs = [x]"
using assms by(metis One_nat_def Suc_length_conv hd_Cons_tl length_0_conv list.sel(3))

lemma list_two_at_end:
  assumes "length xs > 1"
  shows "\<exists>xs' x y. xs = xs' @ [x, y]"
  using assms apply(induction xs rule: rev_induct, simp)
  apply(case_tac "length xs = 1", simp)
  apply(rule_tac x="[]" in exI, rule_tac x="hd xs" in exI)
  apply(simp_all add: list_head_length_one)
  apply(rule_tac x="butlast xs" in exI, rule_tac x="last xs" in exI, simp)
done

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
  apply force+
done

lemma list_split_two_elems:
  assumes "distinct cs"
      and "x \<in> set cs"
      and "y \<in> set cs"
      and "x \<noteq> y"
    shows "\<exists>pre mid suf. cs = pre @ x # mid @ y # suf \<or> cs = pre @ y # mid @ x # suf"
  using assms
  apply(subgoal_tac "\<exists>xi. xi < length cs \<and> x = cs ! xi")
  apply(subgoal_tac "\<exists>yi. yi < length cs \<and> y = cs ! yi")
  apply clarsimp
  apply(subgoal_tac "xi \<noteq> yi")
  apply(case_tac "xi < yi")
  apply(metis list_nth_split One_nat_def less_Suc_eq linorder_neqE_nat not_less_zero)
  apply(subgoal_tac "yi < xi")
  apply(metis list_nth_split One_nat_def less_Suc_eq linorder_neqE_nat not_less_zero)
  using set_elem_nth linorder_neqE_nat apply fastforce+
done

lemma split_list_unique_prefix:
  assumes "x \<in> set xs"
  shows "\<exists>pre suf. xs = pre @ x # suf \<and> (\<forall>y \<in> set pre. x \<noteq> y)"
using assms
  apply(induction xs; clarsimp)
  apply(case_tac "a = x")
  apply(rule_tac x="[]" in exI, force)
  apply(subgoal_tac "x \<in> set xs", clarsimp)
  apply(rule_tac x="a # pre" in exI)
  apply force+
done

lemma map_filter_append:
  shows "List.map_filter P (xs @ ys) = List.map_filter P xs @ List.map_filter P ys"
by(auto simp add: List.map_filter_def)

lemma drop_final_append:
  assumes "xs = ys1 @ zs1"
      and "xs = ys2 @ zs2"
      and "length zs1 \<le> length zs2"
    shows "\<exists>short. ys2 @ short = ys1"
  using assms
  apply(induction zs1 arbitrary: xs zs2 rule: rev_induct, force)
  apply(subgoal_tac "zs2 \<noteq> []") defer apply force
  apply(erule_tac x="butlast xsa" in meta_allE)
  apply(erule_tac x="butlast zs2" in meta_allE)
  apply(subgoal_tac "length xs \<le> length (butlast zs2)")
  apply(metis append_assoc butlast_append butlast_snoc, simp)
done

lemma unique_first_occurrence:
  assumes "xs = ys1 @ zs1"
      and "xs = ys2 @ [hd zs1] @ zs2"
      and "hd zs1 \<notin> set ys1"
      and "hd zs1 \<notin> set ys2"
      and "zs1 \<noteq> []"
    shows "ys1 = ys2"
  using assms
  apply(induction zs1 arbitrary: xs zs2 rule: rev_induct, force)
  apply(case_tac "zs2 = []", simp)
  using hd_append2 hd_in_set apply force
  apply(erule_tac x="butlast xsa" in meta_allE)
  apply(erule_tac x="butlast zs2" in meta_allE)
  apply(case_tac "xs = []", simp)
  apply(metis butlast.simps(2) butlast_append butlast_snoc in_set_conv_decomp)
  apply(metis append_Cons append_Nil2 butlast_append butlast_snoc hd_append2 in_set_conv_decomp)
done

end