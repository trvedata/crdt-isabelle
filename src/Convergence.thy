theory
  Convergence
imports
  Util
begin

section\<open>Convergence Theorem\<close>

subsection\<open>Happens before relations and consistency\<close>

locale happens_before = preorder hb_weak hb
  for hb_weak :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<preceq>" 50)
  and hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool"       (infix "\<prec>" 50) +
  fixes interp :: "'a \<Rightarrow> 'b \<rightharpoonup> 'b" ("\<langle>_\<rangle>" [0] 1000)
begin

(*************************************************************************)
subsection\<open>Concurrent Operations\<close>
(*************************************************************************)

definition concurrent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<parallel>" 50) where
  "s1 \<parallel> s2 \<equiv> \<not> (s1 \<prec> s2) \<and> \<not> (s2 \<prec> s1)"

lemma [intro!]: "\<not> (s1 \<prec> s2) \<Longrightarrow> \<not> (s2 \<prec> s1) \<Longrightarrow> s1 \<parallel> s2"
  by (auto simp: concurrent_def)

lemma [dest]: "s1 \<parallel> s2 \<Longrightarrow> \<not> (s1 \<prec> s2)"
  by (auto simp: concurrent_def)

lemma [dest]: "s1 \<parallel> s2 \<Longrightarrow> \<not> (s2 \<prec> s1)"
  by (auto simp: concurrent_def)

lemma [intro!, simp]: "s \<parallel> s"
  by (auto simp: concurrent_def)

lemma concurrent_comm: "s1 \<parallel> s2 \<longleftrightarrow> s2 \<parallel> s1"
  by (auto simp: concurrent_def)

definition  concurrent_set :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "concurrent_set x xs \<equiv> \<forall>y \<in> set xs. x \<parallel> y"

lemma concurrent_set_empty [simp, intro!]:
  "concurrent_set x []"
  by (auto simp: concurrent_set_def)

lemma concurrent_set_ConsE [elim!]:
  "concurrent_set a (x#xs) \<Longrightarrow> (concurrent_set a xs \<Longrightarrow> concurrent x a \<Longrightarrow> G) \<Longrightarrow> G"
  by (auto simp: concurrent_set_def)

lemma concurrent_set_ConsI [intro!]:
  "concurrent_set a xs \<Longrightarrow> concurrent a x \<Longrightarrow> concurrent_set a (x#xs)"
  by (auto simp: concurrent_set_def)

lemma concurrent_set_appendI [intro!]:
  "concurrent_set a xs \<Longrightarrow> concurrent_set a ys \<Longrightarrow> concurrent_set a (xs@ys)"
  by (auto simp: concurrent_set_def)

lemma concurrent_set_Cons_Snoc [simp]:
  "concurrent_set a (xs@[x]) = concurrent_set a (x#xs)"
  by (auto simp: concurrent_set_def)

(*************************************************************************)
subsection\<open>Happens-before Consistency\<close>
(*************************************************************************)

inductive hb_consistent :: "'a list \<Rightarrow> bool" where
  [intro!]: "hb_consistent []" |
  [intro!]: "\<lbrakk> hb_consistent xs; \<forall>x \<in> set xs. \<not> y \<prec> x \<rbrakk> \<Longrightarrow> hb_consistent (xs @ [y])"

lemma "(x \<prec> y \<or> concurrent x y) = (\<not> y \<prec> x)"
  using less_asym by blast

lemma [intro!]:
  assumes "hb_consistent (xs @ ys)"
  and     "\<forall>x \<in> set (xs @ ys). \<not> z \<prec> x"
  shows   "hb_consistent (xs @ ys @ [z])"
using assms hb_consistent.intros append_assoc by metis

inductive_cases  hb_consistent_elim [elim]:
  "hb_consistent []"
  "hb_consistent (xs@[y])"
  "hb_consistent (xs@ys)"
  "hb_consistent (xs@ys@[z])"

inductive_cases  hb_consistent_elim_gen:
  "hb_consistent zs"

lemma hb_consistent_append_D1 [dest]:
  assumes "hb_consistent (xs @ ys)"
  shows   "hb_consistent xs"
using assms by(induction ys arbitrary: xs rule: List.rev_induct) auto

lemma hb_consistent_append_D2 [dest]:
  assumes "hb_consistent (xs @ ys)"
  shows   "hb_consistent ys"
using assms
  by(induction ys arbitrary: xs rule: List.rev_induct) fastforce+

lemma hb_consistent_append_elim_ConsD [elim]:
  assumes "hb_consistent (y#ys)"
  shows   "hb_consistent ys"
using assms hb_consistent_append_D2 by(metis append_Cons append_Nil)

lemma hb_consistent_remove1 [intro]:
  assumes "hb_consistent xs"
  shows   "hb_consistent (remove1 x xs)"
using assms by (induction rule: hb_consistent.induct) (auto simp: remove1_append)

lemma hb_consistent_singleton [intro!]:
  shows "hb_consistent [x]"
using hb_consistent.intros by fastforce

lemma hb_consistent_prefix_suffix_exists:
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
             \<exists>prefix suffix. ys = prefix @ x # suffix \<and> concurrent_set x suffix) "
  assume assms: "hb_consistent ys" "\<forall>x\<in>set ys. \<not> hb y x"
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
        using assms y_in_xs remove_y_in_xs concurrent_def by blast
      hence "concurrent_set x (suffix@[y])"
        using ys_split by clarsimp
    }
    ultimately have "\<exists>prefix suffix. ys @ [y] = prefix @ x # suffix \<and> concurrent_set x suffix"
      by force
  }
  ultimately show "\<exists>prefix suffix. ys @ [y] = prefix @ x # suffix \<and> concurrent_set x suffix"
    by auto
qed

lemma hb_consistent_append [intro!]:
  assumes "hb_consistent suffix"
          "hb_consistent prefix"
          "\<And>s p. s \<in> set suffix \<Longrightarrow> p \<in> set prefix \<Longrightarrow> \<not> s \<prec> p"
  shows "hb_consistent (prefix @ suffix)"
using assms by (induction rule: hb_consistent.induct) force+

lemma hb_consistent_append_porder:
  assumes "hb_consistent (xs @ ys)"
          "x \<in> set xs"
          "y \<in> set ys"
  shows   "\<not> y \<prec> x"
using assms by (induction ys arbitrary: xs rule: rev_induct) force+

(*************************************************************************)
subsection\<open>Apply Operations\<close>
(*************************************************************************)

definition apply_operations :: "'a list \<Rightarrow> 'b \<rightharpoonup> 'b" where
  "apply_operations es \<equiv> foldl (op \<rhd>) Some (map interp es)"

lemma apply_operations_empty [simp]: "apply_operations [] s = Some s"
by(auto simp: apply_operations_def)

lemma apply_operations_Snoc [simp]: "apply_operations (xs@[x]) = (apply_operations xs) \<rhd> \<langle>x\<rangle>"
by(auto simp add: apply_operations_def kleisli_def)

(*************************************************************************)
subsection\<open>Concurrent Operations Commute\<close>
(*************************************************************************)

definition concurrent_ops_commute :: "'a list \<Rightarrow> bool" where
  "concurrent_ops_commute xs \<equiv>
    \<forall>x y. {x, y} \<subseteq> set xs \<longrightarrow> concurrent x y \<longrightarrow> \<langle>x\<rangle>\<rhd>\<langle>y\<rangle> = \<langle>y\<rangle>\<rhd>\<langle>x\<rangle>"

lemma concurrent_ops_commute_empty [intro!]: "concurrent_ops_commute []"
  by(auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_singleton [intro!]: "concurrent_ops_commute [x]"
  by(auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_appendD [dest]: "concurrent_ops_commute (xs@ys) \<Longrightarrow> concurrent_ops_commute xs"
  by (auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_rearrange: "concurrent_ops_commute (xs@x#ys) = concurrent_ops_commute (xs@ys@[x])"
  by (clarsimp simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_concurrent_set:
  assumes "concurrent_ops_commute (prefix@suffix@[x])"
          "concurrent_set x suffix"
          "distinct (prefix @ x # suffix)"
  shows   "apply_operations (prefix @ suffix @ [x]) = apply_operations (prefix @ x # suffix)"
using assms proof(induction suffix arbitrary: rule: rev_induct, force)
  fix a xs
  assume IH: "concurrent_ops_commute (prefix @ xs @ [x]) \<Longrightarrow>
              concurrent_set x xs \<Longrightarrow> distinct (prefix @ x # xs) \<Longrightarrow> 
              apply_operations (prefix @ xs @ [x]) = apply_operations (prefix @ x # xs)"
  assume assms: "concurrent_ops_commute (prefix @ (xs @ [a]) @ [x])"
                "concurrent_set x (xs @ [a])" "distinct (prefix @ x # xs @ [a])"
  hence ac_comm: "\<langle>a\<rangle> \<rhd> \<langle>x\<rangle> = \<langle>x\<rangle> \<rhd> \<langle>a\<rangle>"
    by (clarsimp simp: concurrent_ops_commute_def) blast
  have copc: "concurrent_ops_commute (prefix @ xs @ [x])"
    using assms by (clarsimp simp: concurrent_ops_commute_def) blast
  have "apply_operations ((prefix @ x # xs) @ [a]) = (apply_operations (prefix @ x # xs)) \<rhd> \<langle>a\<rangle>"
    by (simp del: append_assoc)
  also have "... = (apply_operations (prefix @ xs @ [x])) \<rhd> \<langle>a\<rangle>"
    using IH assms copc by auto
  also have "... = ((apply_operations (prefix @ xs)) \<rhd> \<langle>x\<rangle>) \<rhd> \<langle>a\<rangle>"
    by (simp add: append_assoc[symmetric] del: append_assoc)
  also have "... = (apply_operations (prefix @ xs)) \<rhd> (\<langle>a\<rangle> \<rhd> \<langle>x\<rangle>)"
    using ac_comm kleisli_comm_cong kleisli_assoc by simp
  finally show "apply_operations (prefix @ (xs @ [a]) @ [x]) = apply_operations (prefix @ x # xs @ [a])"
    by (metis Cons_eq_appendI append_assoc apply_operations_Snoc kleisli_assoc)
qed

(*************************************************************************)
subsection\<open>Convergence Theorem\<close>
(*************************************************************************)
theorem  convergence:
  assumes "set xs = set ys"
          "concurrent_ops_commute xs"
          "concurrent_ops_commute ys"
          "distinct xs"
          "distinct ys"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "apply_operations xs = apply_operations ys"
using assms proof(induction xs arbitrary: ys rule: rev_induct, simp)
  case assms: (snoc x xs)
  then obtain prefix suffix where ys_split: "ys = prefix @ x # suffix \<and> concurrent_set x suffix"
    using hb_consistent_prefix_suffix_exists by fastforce
  moreover hence *: "distinct (prefix @ suffix)" "hb_consistent xs"
    using assms by auto
  moreover {
    have "hb_consistent prefix" "hb_consistent suffix"
      using ys_split assms hb_consistent_append_D2 hb_consistent_append_elim_ConsD by blast+
    hence "hb_consistent (prefix @ suffix)"
      by (metis assms(8) hb_consistent_append hb_consistent_append_porder list.set_intros(2) ys_split)
  }
  moreover have **: "concurrent_ops_commute (prefix @ suffix @ [x])"
    using assms ys_split by (clarsimp simp: concurrent_ops_commute_def)
  moreover hence "concurrent_ops_commute (prefix @ suffix)"
    by (force simp del: append_assoc simp add: append_assoc[symmetric])
  ultimately have "apply_operations xs = apply_operations (prefix@suffix)"
    using assms by simp (metis Diff_insert_absorb Un_iff * concurrent_ops_commute_appendD set_append)
  moreover have "apply_operations (prefix@suffix @ [x]) = apply_operations (prefix@x # suffix)"
    using ys_split assms ** concurrent_ops_commute_concurrent_set by force
  ultimately show ?case
    using ys_split by (force simp: append_assoc[symmetric] simp del: append_assoc)
qed

corollary convergence_ext:
  assumes "set xs = set ys"
          "concurrent_ops_commute xs"
          "concurrent_ops_commute ys"
          "distinct xs"
          "distinct ys"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "apply_operations xs s = apply_operations ys s"
  using convergence assms by metis
end


section\<open>Specification that an Operation-Based CRDT must satisfy\<close>

locale strong_eventual_consistency = happens_before +
  fixes op_history :: "'a list \<Rightarrow> bool"
    and initial_state :: "'b"
  assumes causality:     "op_history xs \<Longrightarrow> hb_consistent xs"
  assumes distinctness:  "op_history xs \<Longrightarrow> distinct xs"
  assumes commutativity: "op_history xs \<Longrightarrow> concurrent_ops_commute xs"
  assumes no_failure:    "op_history(xs@[x]) \<Longrightarrow> apply_operations xs initial_state = Some state \<Longrightarrow> \<langle>x\<rangle> state \<noteq> None"
  assumes trunc_history: "op_history(xs@[x]) \<Longrightarrow> op_history xs"
begin

theorem sec_convergence:
  assumes "set xs = set ys"
          "op_history xs"
          "op_history ys"
  shows   "apply_operations xs = apply_operations ys"
by (meson assms convergence causality commutativity distinctness)

theorem sec_progress:
  assumes "op_history xs"
  shows   "apply_operations xs initial_state \<noteq> None"
using assms
  apply(induction xs rule: rev_induct)
  apply simp
  apply(subgoal_tac "apply_operations xs initial_state \<noteq> None")
  apply(subgoal_tac "apply_operations (xs @ [x]) = apply_operations xs \<rhd> \<langle>x\<rangle>")
  apply(simp add: kleisli_def bind_def)
  apply(erule exE)
  apply(case_tac "\<langle>x\<rangle> y")
  using no_failure apply blast
  apply simp+
  using trunc_history apply blast
done

end

(*  
locale foo = happens_before +
    fixes op_history :: "'a list \<Rightarrow> bool"
    and initial_state :: "'b"
  assumes "\<And>xs ys. set xs = set ys \<Longrightarrow> op_history xs \<Longrightarrow> op_history ys \<Longrightarrow> apply_operations xs = apply_operations ys"
    and "\<And>xs. op_history xs \<Longrightarrow> apply_operations xs initial_state \<noteq> None"
*)

end