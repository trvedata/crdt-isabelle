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
using assms by (induction xs arbitrary: ys) fastforce+

lemma remove1_head:
  shows "remove1 x (x#xs) = xs"
  by(induction xs, auto)

lemma set_membership_equality_technicalD [dest]:
  assumes "{x} \<union> (set xs) = {y} \<union> (set ys)"
  shows "x = y \<or> y \<in> set xs"
using assms by(induction xs, auto)

lemma set_equality_technical:
  assumes "{x} \<union> (set xs) = {y} \<union> (set ys)"
          "x \<notin> set xs" "y \<notin> set ys" "y \<in> set xs"
  shows "{x} \<union> (set xs - {y}) = set ys"
using assms by (induction xs) auto

lemma fold_comp_eq:
  shows "fold op \<circ> xs x = fold op \<circ> xs id \<circ> x"
  apply(induction xs rule: rev_induct)
  apply auto
done

subsection\<open>Happens before relations and consistency\<close>

locale happens_before = preorder hb_weak hb
    for hb_weak :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" and hb :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"

abbreviation (in happens_before) (input) concurrent :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "concurrent s1 s2 \<equiv> \<not> (hb s1 s2) \<and> \<not> (hb s2 s1)"

definition (in happens_before) concurrent_set :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) list \<Rightarrow> bool" where
  "concurrent_set x xs \<equiv> \<forall>y \<in> set xs. concurrent x y"

lemma (in happens_before) concurrent_set_empty [simp, intro!]:
  "concurrent_set x []"
  by (auto simp: concurrent_set_def)

lemma (in happens_before) concurrent_set_ConsD [dest!]:
  "concurrent_set x (a # xs) \<Longrightarrow> concurrent_set x xs \<and> concurrent x a"
  by (auto simp: concurrent_set_def)

lemma (in happens_before) concurrent_set_ConsI [intro!]:
  "concurrent_set a xs \<Longrightarrow> concurrent a x \<Longrightarrow> concurrent_set a (x#xs)"
  by (auto simp: concurrent_set_def)

lemma (in happens_before) concurrent_set_Cons_Snoc [simp]:
  "concurrent_set a (xs@[x]) = concurrent_set a (x#xs)"
  by (auto simp: concurrent_set_def)

definition (in happens_before) concurrent_elems_commute :: "('a \<Rightarrow> 'a) list \<Rightarrow> bool" where
  "concurrent_elems_commute xs \<equiv> (\<forall>x y. {x, y} \<subseteq> set xs \<and> concurrent x y \<longrightarrow> x \<circ> y = y \<circ> x)"

lemma (in happens_before) concurrent_elems_commute_ConsD [dest]:
  assumes "concurrent_elems_commute (x # xs)"
  shows   "concurrent_elems_commute xs"
using assms by (auto simp: concurrent_elems_commute_def)

lemma (in happens_before) concurrent_elems_commute_ConsD2 [dest]:
  assumes "concurrent_elems_commute (x # y # xs)"
  shows   "concurrent_elems_commute (x # xs) \<and> (concurrent x y \<longrightarrow> x \<circ> y = y \<circ> x)"
using assms by (auto simp: concurrent_elems_commute_def)

lemma (in happens_before) concurrent_elems_commute_Cons_eq [simp]:
  shows "concurrent_elems_commute (xs @ [x]) = concurrent_elems_commute (x # xs)"
  by (auto simp: concurrent_elems_commute_def)

lemma (in happens_before) concurrent_elems_commute_subset [intro]:
  assumes "concurrent_elems_commute ys" "set xs \<subseteq> set ys"
  shows   "concurrent_elems_commute xs"
using assms by (auto simp: concurrent_elems_commute_def)

inductive (in happens_before) hb_consistent :: "('a \<Rightarrow> 'a) list \<Rightarrow> bool" where
  [intro!]: "hb_consistent []" |
  [intro!]: "\<lbrakk> hb_consistent xs; \<forall>x \<in> set xs. hb x y \<or> \<not> hb y x \<rbrakk> \<Longrightarrow> hb_consistent (xs @ [y])"

lemma (in happens_before) [intro!]:
  assumes "hb_consistent (xs @ ys)"
  and     "\<forall>x \<in> set (xs @ ys). hb x z \<or> \<not> hb z x"
  shows   "hb_consistent (xs @ ys @ [z])"
using assms hb_consistent.intros append_assoc by metis

inductive_cases (in happens_before) hb_consistent_elim [elim]:
  "hb_consistent []"
  "hb_consistent (xs@[y])"
  "hb_consistent (xs@ys@[z])"

inductive_cases (in happens_before) hb_consistent_elim_gen:
  "hb_consistent zs"

lemma (in happens_before) hb_consistent_append_D1 [dest]:
  assumes "hb_consistent (xs @ ys)"
  shows   "hb_consistent xs"
using assms by(induction ys arbitrary: xs rule: List.rev_induct) auto

lemma (in happens_before) hb_consistent_append_D2 [dest]:
  assumes "hb_consistent (xs @ ys)"
  shows   "hb_consistent ys"
using assms
  apply(induction ys arbitrary: xs rule: List.rev_induct)
  apply fastforce+
done

lemma (in happens_before) hb_consistent_append_elim_ConsD [elim]:
  assumes "hb_consistent (y#ys)"
  shows   "hb_consistent ys"
using assms hb_consistent_append_D2 by(metis append_Cons append_Nil)

lemma (in happens_before) hb_consistent_remove1 [intro]:
  assumes "hb_consistent xs"
  shows   "hb_consistent (remove1 x xs)"
using assms by (induction rule: hb_consistent.induct) (auto simp: remove1_append)

lemma (in happens_before) hb_consistent_singleton [intro!]:
  shows "hb_consistent [x]"
using hb_consistent.intros by fastforce

lemma (in happens_before) fold_concurrent_rearrange:
  assumes "concurrent_set x xs"
          "concurrent_elems_commute (x#xs)"
  shows "x \<circ> fold (op \<circ>) xs id = fold (op \<circ>) xs id \<circ> x"
using assms
  apply(induction xs rule: rev_induct, clarsimp)
  apply clarsimp
  apply(metis (no_types, hide_lams) append_Cons concurrent_elems_commute_ConsD concurrent_elems_commute_ConsD2 concurrent_elems_commute_Cons_eq o_assoc)
done

lemma (in happens_before) fold_concurrent_rearrange':
  assumes "concurrent_set x xs"
          "concurrent_elems_commute (x#xs)"
  shows "fold (op \<circ>) (x#xs) id = fold (op \<circ>) (xs@[x]) id"
using assms
  apply clarsimp
  apply(subst fold_concurrent_rearrange, clarsimp, clarsimp)
  apply(rule fold_comp_eq)
done

lemma (in happens_before) hb_consistent_prefix_suffix_exists:
  assumes "hb_consistent ys"
          "hb_consistent (xs @ [x])"
          "{x} \<union> set xs = set ys"
          "distinct (x#xs)"
          "distinct ys"
  shows "\<exists>prefix suffix. ys = prefix @ x # suffix \<and> concurrent_set x suffix"
using assms proof (induction arbitrary: xs rule: hb_consistent.induct, simp)
  fix xs y ys
  assume IH: "(\<And>xs. hb_consistent (xs @ [x]) \<Longrightarrow>
               {x} \<union> set xs = set ys \<Longrightarrow>
               distinct (x # xs) \<Longrightarrow> distinct ys \<Longrightarrow>
             \<exists>prefix suffix. ys = prefix @ x # suffix \<and> concurrent_set x suffix)"
  assume assms: "hb_consistent ys" "\<forall>x\<in>set ys. hb x y \<or> \<not> hb y x"
                "hb_consistent (xs @ [x])"
                "{x} \<union> set xs = set (ys @ [y])"
                "distinct (x # xs)" "distinct (ys @ [y])"
  hence "x = y \<or> y \<in> set xs"
    using assms by auto
  moreover {
    assume "x = y"
    hence "\<exists>prefix suffix. ys @ [y] = prefix @ x # suffix \<and> concurrent_set x suffix"
      by force
  }
  moreover {
    assume y_in_xs: "y \<in> set xs"
    hence "{x} \<union> (set xs - {y}) = set ys"
      using assms by (auto intro: set_equality_technical)
    hence remove_y_in_xs: "{x} \<union> set (remove1 y xs) = set ys"
      using assms by auto
    moreover have "hb_consistent ((remove1 y xs) @ [x])"
      using assms hb_consistent_remove1 by force        
    moreover have "distinct (x # (remove1 y xs))"
      using assms by simp
    moreover have "distinct ys"
      using assms by simp
    ultimately obtain prefix suffix where ys_split: "ys = prefix @ x # suffix \<and> concurrent_set x suffix"
      using IH by force
    moreover {
      have "concurrent x y"
        using assms y_in_xs remove_y_in_xs by (metis hb_consistent_elim(2) insert_is_Un list.set_intros(1) list.simps(15) local.less_asym)
      hence "concurrent_set x (suffix@[y])"
        using ys_split by clarsimp
    }
    ultimately have "\<exists>prefix suffix. ys @ [y] = prefix @ x # suffix \<and> concurrent_set x suffix"
      by force
  }
  ultimately show "\<exists>prefix suffix. ys @ [y] = prefix @ x # suffix \<and> concurrent_set x suffix"
    by auto
qed


lemma (in happens_before) hb_consistent_append [intro!]:
  assumes "hb_consistent suffix"
          "hb_consistent prefix"
          "\<And>s p. s \<in> set suffix \<Longrightarrow> p \<in> set prefix \<Longrightarrow> hb p s \<or> \<not> hb s p"
  shows "hb_consistent (prefix @ suffix)"
using assms by (induction rule: hb_consistent.induct) force+

abbreviation (in happens_before) porder :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "porder x y \<equiv> hb x y \<or> concurrent x y"

lemma (in happens_before) hb_consistent_append_porder:
  assumes "hb_consistent (xs @ ys)"
          "x \<in> set xs"
          "y \<in> set ys"
  shows   "hb x y \<or> \<not> hb y x"
using assms by (induction ys arbitrary: xs rule: rev_induct) force+

theorem (in happens_before) convergence:
  assumes "set xs = set ys"
          "concurrent_elems_commute xs"
          "distinct xs"
          "distinct ys"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "fold (op \<circ>) xs id = fold (op \<circ>) ys id"
using assms proof(induction xs arbitrary: ys rule: rev_induct, simp)
  fix x xs ys
  assume IH: "(\<And>ys. set xs = set ys \<Longrightarrow>
                    concurrent_elems_commute xs \<Longrightarrow> 
                     distinct xs \<Longrightarrow> distinct ys \<Longrightarrow>
                     hb_consistent xs \<Longrightarrow>
                     hb_consistent ys \<Longrightarrow> 
               fold op \<circ> xs id = fold op \<circ> ys id)"
   assume assms: "set (xs @ [x]) = set ys"
                 "concurrent_elems_commute (xs @ [x])"
                 "distinct (xs @ [x])"      "distinct ys"
                 "hb_consistent (xs @ [x])" "hb_consistent ys"
  then obtain prefix suffix where ys_split: "ys = prefix @ x # suffix \<and> concurrent_set x suffix"
    using hb_consistent_prefix_suffix_exists by fastforce
  moreover have "distinct (prefix @ suffix)" "hb_consistent xs"
    using ys_split assms by fastforce+
  moreover {
    have "hb_consistent prefix" "hb_consistent suffix"
      using ys_split assms by fastforce+
    hence "hb_consistent (prefix @ suffix)"
    using ys_split assms
        apply clarsimp
        apply(rule hb_consistent_append)
        apply force apply force
        apply(rule hb_consistent_append_porder)
        apply(assumption) back
        apply fastforce+
      done
  }
  ultimately have IH': "fold op \<circ> xs id = fold op \<circ> (prefix@suffix) id"
    using ys_split assms by (fastforce intro!: IH)

  have "concurrent_elems_commute (x # suffix)"
    using ys_split assms concurrent_elems_commute_subset by auto
  have conc: "fold op \<circ> (suffix @ [x]) id = fold op \<circ> (x # suffix) id"
    using ys_split assms by (subst fold_concurrent_rearrange') auto
  show "fold op \<circ> (xs @ [x]) id = fold op \<circ> ys id"
    using ys_split fold_append by (metis IH' conc fold_comp_eq o_apply)
qed

end