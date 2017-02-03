theory
  Convergence
imports
  Main
begin

section\<open>Network events to...\<close>

lemma distinct_set_notin:
  assumes "distinct (x#xs)"
  shows   "x \<notin> set xs"
using assms by(induction xs, auto)

lemma set_insert_inject:
  assumes "a \<notin> set xs"
          "a \<notin> set ys" 
          "set (a#xs) = set (a#ys)"
  shows   "set xs = set ys"
using assms
  apply(induction xs arbitrary: ys)
  apply fastforce+
done

lemma remove1_head:
  shows "remove1 x (x#xs) = xs"
by(induction xs, auto)

lemma set_comm_rearrange:
  assumes "\<And>x y. {x, y} \<subseteq> set ys \<Longrightarrow> x \<circ> y = y \<circ> x"
          "a \<in> set ys"
  shows   "a \<circ> foldr op \<circ> (remove1 a ys) id = foldr op \<circ> ys id"
using assms
  apply(induction ys arbitrary: a, simp)
  apply simp
  apply(erule disjE, clarify)
  apply clarsimp
  apply(erule_tac x=aa in meta_allE)
  apply(erule meta_impE, assumption)
  apply(erule_tac x=a in meta_allE, erule_tac x=aa in meta_allE)
  apply clarsimp
  apply(metis o_assoc)
done

locale happens_before = preorder hb_weak hb
    for hb_weak :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" and hb :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"

abbreviation (in happens_before) concurrent :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "concurrent s1 s2 \<equiv> \<not> (hb s1 s2) \<and> \<not> (hb s2 s1)"

inductive (in happens_before) hb_consistent :: "('a \<Rightarrow> 'a) list \<Rightarrow> bool" where
  "hb_consistent []" |
  "\<lbrakk> hb_consistent xs; \<forall>x \<in> set xs. hb x y \<and> \<not> hb y x \<rbrakk> \<Longrightarrow> hb_consistent (xs @ [y])"

inductive_cases (in happens_before) hb_consistent_elim: "hb_consistent zs"

lemma (in happens_before) hb_consistent_append_elim1 [elim]:
  assumes "hb_consistent (xs @ ys)"
  shows   "hb_consistent xs"
using assms
  apply(induction ys arbitrary: xs rule: List.rev_induct)
  apply clarsimp
  apply(erule hb_consistent_elim, simp)
  apply clarsimp
done

lemma (in happens_before) hb_consistent_append_elim2 [elim]:
  assumes "hb_consistent (xs @ ys)"
  shows   "hb_consistent ys"
using assms
  apply(induction ys arbitrary: xs rule: List.rev_induct)
  apply(blast intro: hb_consistent.intros)
  apply(rule hb_consistent.intros)
  apply(erule hb_consistent_elim, simp)
  apply auto
  apply(erule hb_consistent_elim, simp)
  apply auto
  apply(erule hb_consistent_elim, simp)
  apply auto
done

lemma (in happens_before) hb_consistent_append_elim_Cons [elim]:
  assumes "hb_consistent (y#ys)"
  shows   "hb_consistent ys"
using assms hb_consistent_append_elim2 by(metis append_Cons append_Nil)

lemma (in happens_before) hb_consistent_remove1:
  assumes "hb_consistent xs"
  shows   "hb_consistent (remove1 x xs)"
using assms
  apply(induction rule: hb_consistent.induct)
  apply(auto intro: hb_consistent.intros)
  apply(subst remove1_append)
  apply(simp split: split_if)
  apply safe
  apply(rule hb_consistent.intros, assumption)
  apply clarsimp
  apply(subgoal_tac "xa \<in> set xs", force)
  apply blast
  apply(rule hb_consistent.intros, assumption)
  apply clarsimp
  apply(subgoal_tac "xa \<in> set xs", force)
  apply force
  apply(rule hb_consistent.intros, assumption)
  apply force
done

lemma (in happens_before) hb_consistent_singleton [intro!]:
  shows "hb_consistent [x]"
using hb_consistent.intros by fastforce

lemma foldr_foldr_cong:
  assumes "foldr (op \<circ>) ys f = foldr (op \<circ>) zs f"
          "xs1 = xs2"
  shows   "foldr (op \<circ>) (xs1 @ ys) f = foldr (op \<circ>) (xs2 @ zs) f"
using assms by(induction xs1, auto)

lemma foldr_snoc_unfold:
  shows "foldr (op \<circ>) (ys @ [x]) f = foldr (op \<circ>) ys (x \<circ> f)"
  apply(induction ys arbitrary: f)
  apply auto
done

lemma foldr_foldr_cong':
  fixes  f :: "'a \<Rightarrow> 'a"
  assumes "\<And>(x::'a\<Rightarrow>'a). foldr (op \<circ>) ys x = foldr (op \<circ>) zs x"
  shows   "foldr (op \<circ>) (ys @ [x]) f = foldr (op \<circ>) (zs @ [x]) f"
using assms
  apply(induction ys arbitrary: f zs rule: rev_induct)
  apply auto
done
  
lemma foldr_circ_append:
  shows "foldr (op \<circ>) (f @ g) id = foldr (op \<circ>) f id \<circ> foldr (op \<circ>) g id"
by(induction f, auto)

lemma (in happens_before) foldr_concurrent_rearrange:
  assumes "\<And>s. s \<in> set xs \<Longrightarrow> concurrent x s"
          "\<And>y z. {y, z} \<subseteq> set xs \<union> {x} \<Longrightarrow> concurrent y z \<Longrightarrow> y \<circ> z = z \<circ> y"
  shows "x \<circ> foldr (op \<circ>) xs id = foldr (op \<circ>) xs id \<circ> x"
using assms
  apply(induction xs)
  apply simp
  apply clarsimp
  apply(subgoal_tac "(\<And>y z. (y = x \<or> y \<in> set xs) \<and> (z = x \<or> z \<in> set xs) \<Longrightarrow> concurrent y z \<Longrightarrow> y \<circ> z = z \<circ> y)")
  apply(subst comp_assoc[symmetric])
  apply(erule_tac x=x in meta_allE) back
  apply(erule_tac x=a in meta_allE) back back
  apply clarsimp
  apply(metis o_assoc)
  apply force
done

lemma foldr_comp_append_rearrange:
  fixes x :: "'a \<Rightarrow> 'a"
  shows "foldr op \<circ> prefix (foldr op \<circ> suffix id) \<circ> x = foldr op \<circ> prefix (foldr op \<circ> suffix id \<circ> x)"
  apply(induction prefix)
  apply simp
  apply simp
  apply metis
done

lemma foldr_comp_f_absorb:
  shows "foldr op \<circ> xs x = foldr op \<circ> (xs @ [x]) id"
by(induction xs, auto)

lemma set_membership_equality_technical:
  assumes "{x} \<union> (set xsa) = {y} \<union> (set xs)"
          "x \<notin> set xsa"
          "y \<notin> set xs"
          "distinct xsa"
          "distinct xs"
  shows "x = y \<or> y \<in> set xsa"
using assms by(induction xsa, auto)

lemma set_equality_technical:
  assumes "{x} \<union> (set xsa) = {y} \<union> (set xs)"
          "x \<notin> set xsa"
          "y \<notin> set xs"
          "y \<in> set xsa"
          "distinct xsa"
          "distinct xs"
  shows "{x} \<union> (set xsa - {y}) = set xs"
using assms
  apply(induction xsa arbitrary: xs)
  apply auto
done

lemma (in happens_before) hb_consistent_prefix_suffix_exists:
  assumes "hb_consistent ys"
          "hb_consistent (xs @ [x])"
          "{x} \<union> set xs = set ys"
          "distinct (x#xs)"
          "distinct ys"
  shows "\<exists>prefix suffix. ys = prefix @ [x] @ suffix \<and>
    (\<forall>s\<in>set suffix. concurrent x s)"
using assms
  apply(induction arbitrary: xs rule: hb_consistent.induct)
  apply simp
  apply clarsimp
  apply(erule_tac x="remove1 y xsa" in meta_allE, clarsimp)
  apply(insert hb_consistent_remove1)
  apply(erule_tac x="xsa@[x]" in meta_allE)
  apply(erule_tac x=y in meta_allE)
  apply clarsimp
  apply (subgoal_tac "x = y \<or> y \<in> set xsa")
defer
  apply(rule set_membership_equality_technical, simp, simp, simp, simp, simp)
  apply(erule disjE)
  apply clarsimp
  apply(rule_tac x=xs in exI, rule_tac x="[]" in exI)
  apply clarsimp
  apply(subst (asm) remove1_append)
  apply(simp split: split_if_asm)
  apply(insert set_equality_technical)
  apply(erule_tac x=x in meta_allE, erule_tac x=xsa in meta_allE, erule_tac x=y in meta_allE, erule_tac x=xs in meta_allE)
  apply clarsimp
  apply(rule_tac x=prefix in exI, rule_tac x="suffix@[y]" in exI)
  apply(rule conjI, simp)
  apply(erule hb_consistent_elim) back
  apply simp
  apply clarsimp
done

lemma (in happens_before) hb_consistent_append:
  assumes "hb_consistent suffix"
          "hb_consistent prefix"
          "\<And>s p. s \<in> set suffix \<Longrightarrow> p \<in> set prefix \<Longrightarrow> hb p s \<and> \<not> hb s p"
  shows "hb_consistent (prefix @ suffix)"
using assms
  apply(induction rule: hb_consistent.induct, simp)
  apply clarsimp
  apply(subgoal_tac "hb_consistent ((prefix @ xs) @ [y])", clarsimp)
  apply(rule hb_consistent.intros, assumption)
  apply clarsimp
  apply(erule disjE; clarsimp)
done

abbreviation (in happens_before) porder :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "porder x y \<equiv> hb x y \<or> concurrent x y"

lemma (in happens_before) hb_consistent_append_porder:
  assumes "hb_consistent (xs @ ys)"
          "x \<in> set xs"
          "y \<in> set ys"
  shows   "hb x y \<and> \<not> hb y x"
using assms
  apply(induction ys arbitrary: xs rule: List.rev_induct)
  apply simp
  apply clarsimp
  apply(erule hb_consistent_elim, simp)
  apply clarsimp
  apply(erule disjE, clarsimp)
  apply clarsimp
done

theorem (in happens_before) convergence:
  fixes   f :: "'a \<Rightarrow> 'a"
  assumes "set xs = set ys"
  assumes "distinct xs"
          "distinct ys"
  assumes "\<And>x y. {x, y} \<subseteq> set xs \<Longrightarrow> concurrent x y \<Longrightarrow> x \<circ> y = y \<circ> x"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "foldr (op \<circ>) xs id = foldr (op \<circ>) ys id"
using assms
  apply -
  apply(induction xs arbitrary: f ys rule: List.rev_induct)
  apply simp
  apply clarsimp
  apply(subgoal_tac "\<exists>prefix suffix. ys = prefix @ [x] @ suffix \<and>
          (\<forall>s\<in>set suffix. concurrent x s)")
  apply(clarsimp)
  apply(subst foldr_concurrent_rearrange, clarsimp)
  apply(erule_tac x=y in meta_allE, erule_tac x=z in meta_allE, clarsimp)
  apply(erule disjE, clarsimp, erule disjE, metis, clarsimp, clarsimp)
  apply(erule disjE, clarsimp)
  apply(erule_tac x=y in ballE)
  apply(subgoal_tac "concurrent y x")
  apply simp apply simp apply simp
  apply(erule_tac x="prefix@suffix" in meta_allE)
  apply clarsimp
  apply(subgoal_tac "set xs = set prefix \<union> set suffix \<and> hb_consistent xs \<and> hb_consistent (prefix @ suffix)")
  apply clarsimp
  apply(subst foldr_comp_f_absorb)
  apply(subst foldr_circ_append)
  apply clarsimp
  apply(rule foldr_comp_append_rearrange)
  apply(rule conjI)
  apply(simp add: insert_eq_iff)
  apply(rule conjI)
  apply(erule hb_consistent_append_elim1)
  apply(rule hb_consistent_append)
  apply(drule hb_consistent_append_elim2) back
  apply(erule hb_consistent_append_elim_Cons)
  apply(erule hb_consistent_append_elim1)
  apply(rule hb_consistent_append_porder)
  apply(assumption) back
  apply(assumption)
  apply clarsimp
  apply(rule hb_consistent_prefix_suffix_exists, simp_all)
done

end