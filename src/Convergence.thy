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
  fixes interp :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" ("\<langle>_\<rangle>" [0] 1000)
    and initial_state :: "'b"
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

lemma [intro!, elim!, dest!]: "s \<parallel> s"
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
subsection\<open>Valid Operation\<close>
(*************************************************************************)

(* Assumming xs is a list of operations where x is can be applied,
   then ss is a prefix of xs which guarantees the validity of x. *) 
definition valid :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "valid xs x ss \<equiv> \<exists>ys zs. xs = ss@ys@x#zs \<and> concurrent_set x ys"

lemma [intro!]: "valid (xs@[x]) x xs"
  by (auto simp: valid_def)

lemma [intro!]: "valid (xs@[x]@ys) x xs"
  by (auto simp: valid_def)

lemma valid_append [intro]: "valid xs x ys \<Longrightarrow> valid (xs@zs) x ys"
  by (force simp: valid_def)

lemma validE [elim]: "valid (xs@[x]) x ss \<Longrightarrow> distinct (x#xs) \<Longrightarrow> (\<And>ys. xs = ss@ys \<Longrightarrow> concurrent_set x ys \<Longrightarrow> G) \<Longrightarrow> G "
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "xs = ss @ ys \<and> zs = []", clarsimp)
  apply (metis append_assoc append_same_eq distinct.simps(2) distinct1_rotate distinct_append last.simps last_appendR last_in_set list.discI rotate1.simps(2))
done

lemma validI [intro]: "distinct (xs@[x]) \<Longrightarrow> valid (ss@[x]) x ss \<Longrightarrow> xs=ss@ys  \<Longrightarrow> concurrent_set x ys \<Longrightarrow> valid (xs@[x]) x ss"
  by (force simp: valid_def)

lemma valid_concurrent [intro]: "distinct (xs@[y,x]) \<Longrightarrow> x \<parallel> y \<Longrightarrow> valid (xs@[y,x]) x xs"
  apply (subgoal_tac "valid ((xs @ [y]) @ [x]) x xs", force)
  apply (rule validI, force+)
done

lemma valid_singletonE [elim!]: "valid [x] y ss \<Longrightarrow> (x = y \<Longrightarrow> ss = [] \<Longrightarrow> G) \<Longrightarrow> G"
  by (clarsimp simp: valid_def Cons_eq_append_conv)

lemma valid_concurrent_elim [intro]: "valid (xs@[x]) z ss \<Longrightarrow> distinct (xs@[y,x]) \<Longrightarrow> concurrent x y \<Longrightarrow> valid (xs@[y,x]) z ss"
  apply (clarsimp simp: valid_def)
  apply (case_tac zs rule: rev_cases)
  apply (rule_tac x="ys@[y]" in exI, force, force)
done

lemma valid_concurrent_elim2: "valid ([y,x]) x ss \<Longrightarrow> distinct ([y,x]) \<Longrightarrow> concurrent x y \<Longrightarrow> valid ([x]) x ss"
  apply (clarsimp simp: valid_def)
  apply (case_tac zs rule: rev_cases; clarsimp)
  apply (case_tac ys rule: rev_cases; clarsimp)
done

lemma valid_concurrent_elim2: "valid (xs@[y,x]) z ss \<Longrightarrow> distinct (xs@[y,x]) \<Longrightarrow> concurrent x y \<Longrightarrow> valid (xs@[x]) z ss"
  apply (clarsimp simp: valid_def)
  apply (case_tac zs rule: rev_cases; clarsimp)
  apply (case_tac ys rule: rev_cases; clarsimp)
done

lemma valid_concurrent_elim [intro]: "distinct (xs@ys@[x]) \<Longrightarrow> valid (xs@ys@[x]) x ss \<Longrightarrow> concurrent_set x ys \<Longrightarrow> valid (xs@[x]) x ss"

apply (induct ys rule: rev_induct)
apply clarsimp
apply (subgoal_tac "distinct (xs @ xsa @ [x]) \<and> valid (xs @ xsa @ [x]) x ss \<and> concurrent_set x xsa")
apply clarsimp
apply (rule conjI)
apply force
apply (rule conjI)
prefer 2
apply force
apply simp
apply (subst (asm) valid_def) back back
apply (erule exE)+
apply (subst valid_def)
apply simp
apply (case_tac ys rule: rev_cases; clarsimp)
apply (case_tac zs rule: rev_cases)
apply clarsimp

thm valid_concurrent_elim
apply (drule valid_concurrent_elim)
apply clarify
  apply (clarsimp simp: valid_def)
  apply (case_tac zs rule: rev_cases; clarsimp)
  apply (rule_tac x="ys@[y]" in exI, force, force
done

lemma valid_SnocD [dest]: "distinct (xs@[x]) \<Longrightarrow> valid (xs@[x]) y ss \<Longrightarrow> y \<in> set xs \<Longrightarrow> valid xs y ss"
  apply (clarsimp simp: valid_def)
  apply (case_tac zs rule: rev_cases)
  apply auto
done

lemma valid_appendD [dest]: "valid (xs@ys) y ss \<Longrightarrow> distinct (xs@ys) \<Longrightarrow> y \<in> set xs \<Longrightarrow> valid xs y ss"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "\<exists>xs1 xs2. xs=xs1@y#xs2")
  apply clarsimp
  apply (subgoal_tac "xs1 = ss @ ysa \<and> xs2 @ ys = zs")
  apply clarsimp
  apply force
  apply (rule_tac ys="[y]" in pre_suf_eq_distinct_list2)
  apply (thin_tac "xs1 @ y # xs2 @ ys = ss @ ysa @ y # zs")
  apply force
  apply force
  apply force
by (meson split_list_first)

lemma valid_in_setD [dest]: "valid xs y ss \<Longrightarrow> y \<in> set xs"
  by (clarsimp simp: valid_def)

lemma valid_Snoc_pairD [dest]: "valid (xs @ [b, a]) x ss \<Longrightarrow> a \<noteq> x \<Longrightarrow> valid (xs @ [b]) x ss"
  apply (clarsimp simp: valid_def)
  apply (case_tac zs rule: rev_cases; clarsimp)
  apply (case_tac ysa rule: rev_cases; force)
done

lemma foo1: "a \<noteq> b \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid [b, a] b ss \<Longrightarrow> valid [a, b] b ss"
apply (clarsimp simp: valid_def)
apply (case_tac zs rule: rev_cases; clarsimp)
apply (case_tac ysa rule: rev_cases; clarsimp)
apply (rule_tac x="[a]" in exI)
apply clarsimp
apply force
done

lemma foo2: "a \<noteq> b \<Longrightarrow> valid [b, a] b ss \<Longrightarrow> ss = []"
  apply (clarsimp simp: valid_def)
  apply (case_tac zs rule: rev_cases; clarsimp)
  apply (case_tac ysa rule: rev_cases; clarsimp)
done

lemma valid_concurrent_comm: "distinct [a,b] \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid [b, a] x ss \<Longrightarrow> valid [a, b] x ss"
  apply (subgoal_tac "x=a \<or> x=b")
defer
  apply force
  apply (subgoal_tac "ss = [] \<or> ss =[b] \<or> ss=[b,a]")
defer
apply (clarsimp simp: valid_def)
apply (case_tac zs rule: rev_cases; clarsimp)
apply (case_tac ys rule: rev_cases; clarsimp)
apply (case_tac ysa rule: rev_cases; clarsimp)
apply safe
apply (subst valid_def)
apply force
apply clarsimp
apply (clarsimp simp: valid_def)
oops

(*************************************************************************)
subsection\<open>Apply Operations\<close>
(*************************************************************************)

definition apply_operations :: "'a list \<Rightarrow> 'b" where
  "apply_operations es \<equiv> (fold (op \<circ>) (map interp es) id) initial_state"

lemma apply_operations_empty [simp]: "apply_operations [] = initial_state"
  by (auto simp: apply_operations_def)

lemma apply_operations_Snoc [simp]: "apply_operations (xs@[x]) = \<langle>x\<rangle> (apply_operations xs)"
  by (auto simp: apply_operations_def)

(*************************************************************************)
subsection\<open>Concurrent Operations Commute\<close>
(*************************************************************************)

definition concurrent_ops_commute :: "'a list \<Rightarrow> bool" where
  "concurrent_ops_commute xs \<equiv>
    \<forall>x y. {x, y} \<subseteq> set xs \<longrightarrow> concurrent x y \<longrightarrow> 
    (\<forall>ss. valid xs x ss \<longrightarrow> valid xs y ss \<longrightarrow> 
      apply_operations (ss @ [x, y]) = apply_operations (ss @ [y, x]))"

lemma concurrent_ops_commute_empty [intro!]: "concurrent_ops_commute []"
  by(auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_singleton [intro!]: "concurrent_ops_commute [x]"
  by(auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_appendD [dest]: "concurrent_ops_commute (xs@ys) \<Longrightarrow> concurrent_ops_commute xs"
  by (auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_dest:
  assumes "concurrent_ops_commute xs"
          "x \<parallel> y" "valid xs x ss" "valid xs y ss"
    shows "apply_operations (ss @ [x, y]) = apply_operations (ss @ [y, x])"
using assms by (auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commute_SnocI [intro]:
  assumes "concurrent_ops_commute xs" "distinct (xs@[x])"
      and "\<forall>y \<in> set xs. concurrent x y \<longrightarrow> (\<forall>ss. valid (xs@[x]) x ss \<longrightarrow> valid (xs@[x]) y ss \<longrightarrow> apply_operations (ss @ [x, y]) = apply_operations (ss @ [y, x]))"
    shows "concurrent_ops_commute (xs@[x])"
  using assms
  apply (subst concurrent_ops_commute_def; clarsimp)
  apply (erule disjE, force)
  apply (erule disjE, clarsimp)
  apply (erule_tac x=xa in ballE; clarsimp simp: concurrent_comm)
  apply (drule concurrent_ops_commute_dest, force)
  apply (rule valid_SnocD, force, force, force)+
  apply force
done

lemma concurrent_ops_commute_single_elim:
  "concurrent_ops_commute (xs@[y,x]) \<Longrightarrow> distinct (xs@[y,x]) \<Longrightarrow> x \<parallel> y \<Longrightarrow> concurrent_ops_commute (xs@[x])"
  apply (rule concurrent_ops_commute_SnocI, force, force, clarsimp)
  apply (drule concurrent_ops_commute_dest) prefer 4 apply assumption
  apply auto
done

(*
lemma concurrent_ops_commute_last_rearrange_Snoc_pair:
  shows "distinct (xs@[a,b]) \<Longrightarrow> concurrent a b \<Longrightarrow> concurrent_ops_commute (xs@[a,b]) \<Longrightarrow> concurrent_ops_commute (xs@[b,a])"

lemma concurrent_ops_commute_last_rearrange':
  shows "concurrent_ops_commute (xs@[a,b]@ys) \<Longrightarrow> concurrent a b \<Longrightarrow> concurrent_ops_commute (xs@[b,a]@ys)"
using assms
by (auto simp: concurrent_ops_commute_def)

lemma concurrent_ops_commuteE:
  "concurrent_ops_commute (xs@[x]) \<Longrightarrow> y \<in> set xs \<Longrightarrow> concurrent x y \<Longrightarrow>
    cond (xs@[x]) x ss \<Longrightarrow> cond (xs@[x]) y ss \<Longrightarrow>
      fold (op \<circ>) (map interp (ss @ [x, y])) id initial_state =
       fold (op \<circ>) (map interp (ss @ [y, x])) id initial_state"
by (auto simp: concurrent_ops_commute_def)


lemma concurrent_ops_commuteE:
  "concurrent_ops_commute (xs@[x]) \<Longrightarrow> y \<in> set xs \<Longrightarrow> concurrent x y \<Longrightarrow>
    valid (xs@[x]) x ss \<Longrightarrow> valid (xs@[x]) y ss \<Longrightarrow>
      fold (op \<circ>) (map interp (ss @ [x, y])) id initial_state =
       fold (op \<circ>) (map interp (ss @ [y, x])) id initial_state"
by (auto simp: concurrent_ops_commute_def)

*)

lemma "a \<noteq> b \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid [b, a] x ss \<Longrightarrow> valid [b, a] y ss \<Longrightarrow> ss = []"
apply (clarsimp simp: valid_def)
apply (case_tac zs rule: rev_cases; clarsimp)
apply (case_tac zsa rule: rev_cases; clarsimp)
oops

lemma concurrent_ops_commute_pair_comm: "a \<noteq> b \<Longrightarrow> a \<parallel> b \<Longrightarrow> concurrent_ops_commute [a, b] \<Longrightarrow> concurrent_ops_commute [b, a]"
apply (clarsimp simp: concurrent_ops_commute_def)
apply (erule disjE)+
apply clarsimp
apply clarsimp
apply (subgoal_tac "ss=[]")
apply clarsimp
prefer 2
apply (rule foo2, assumption, force)
apply (erule_tac x=a in allE, erule_tac x=b in allE)
apply clarsimp
apply (erule_tac x="[]" in allE)
apply clarsimp
defer
apply (erule disjE)
apply clarsimp
apply (subgoal_tac "ss=[]")
apply clarsimp
prefer 2
apply (rule foo2, assumption, force)
prefer 2
apply clarsimp
sorry

lemma foo3: "distinct (a#b#xs) \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid (xs @ [b, a]) b ss \<Longrightarrow> valid (xs @ [b, a]) a ss \<Longrightarrow> valid (xs @ [a, b]) a ss"
  sorry

lemma foo4: "distinct (a#b#xs) \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid (xs @ [b, a]) b ss \<Longrightarrow> valid (xs @ [b, a]) a ss \<Longrightarrow> valid (xs @ [a, b]) b ss"
  sorry

lemma foo5: "distinct (a#b#xs) \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid (xs @ [b, a]) b ss \<Longrightarrow> valid (xs @ [b, a]) y ss \<Longrightarrow>  y \<in> set xs \<Longrightarrow> valid (xs @ [a, b]) b ss"
  sorry

lemma foo6: "distinct (a#b#xs) \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid (xs @ [b, a]) b ss \<Longrightarrow> valid (xs @ [b, a]) y ss \<Longrightarrow>  y \<in> set xs \<Longrightarrow> valid (xs @ [a, b]) y ss"
  sorry

lemma foo7: "distinct (a#b#xs) \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid (xs @ [b, a]) a ss \<Longrightarrow> valid (xs @ [b, a]) y ss \<Longrightarrow>  y \<in> set xs \<Longrightarrow> valid (xs @ [a, b]) a ss"
  sorry

lemma foo8: "distinct (a#b#xs) \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid (xs @ [b, a]) a ss \<Longrightarrow> valid (xs @ [b, a]) y ss \<Longrightarrow>  y \<in> set xs \<Longrightarrow> valid (xs @ [a, b]) y ss"
  sorry

lemma foo9: "distinct (a#b#xs) \<Longrightarrow> a \<parallel> b \<Longrightarrow> valid (xs @ [b, a]) x ss \<Longrightarrow> valid (xs @ [b, a]) y ss \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> valid (xs @ [a, b]) y ss"
  sorry

lemma concurrent_ops_commute_last_rearrange_Snoc_pair:
  shows "distinct (xs@[a,b]) \<Longrightarrow> concurrent a b \<Longrightarrow> concurrent_ops_commute (xs@[a,b]) \<Longrightarrow> concurrent_ops_commute (xs@[b,a])"
apply (clarsimp simp: concurrent_ops_commute_def)
apply safe

  apply (erule_tac x=a in allE, erule_tac x=b in allE, clarsimp, erule_tac x=ss in allE)
  apply (erule impE, rule foo3, force, force, force, force)
  apply (erule impE, rule foo4, force, force, force, force)
  apply force

  apply (erule_tac x=b in allE, erule_tac x=y in allE, clarsimp, erule_tac x=ss in allE)
  apply (erule impE, rule foo5, force, force, force)
    apply assumption back apply force
  apply (erule impE, rule foo6, force, force, force)
    apply assumption apply force
  apply force

  apply (erule_tac x=a in allE, erule_tac x=b in allE, clarsimp, erule_tac x=ss in allE)
  apply (erule impE, rule foo3, force, force, force, force)
  apply (erule impE, rule foo4, force, force, force, force)
  apply force

  apply (erule_tac x=x in allE, erule_tac x=b in allE, clarsimp, erule_tac x=ss in allE)
  apply (erule impE, rule foo6, force, force, force, force, force)
  apply (erule impE, rule foo5, force, force, force, force, force)
  apply force

  apply (erule_tac x=a in allE, erule_tac x=y in allE, clarsimp, erule_tac x=ss in allE)
  apply (erule impE, rule foo7, force, force, force)
    apply assumption back apply force
  apply (erule impE, rule foo8, force, force, force, force, force)
  apply force

  apply (erule_tac x=x in allE, erule_tac x=a in allE, clarsimp, erule_tac x=ss in allE)
  apply (erule impE, rule foo8, force, force, force, force, force)
  apply (erule impE, rule foo7, force, force, force, force, force)
  apply force

  apply (erule_tac x=x in allE, erule_tac x=y in allE, clarsimp, erule_tac x=ss in allE)
  apply (erule impE, rule foo9, force, force, force, force, force, force)+
  apply force
done



lemma concurrent_ops_commute_rearrange_last: "distinct (x#y#xs@ys) \<Longrightarrow> concurrent_ops_commute (xs @ ys @ [x]) \<Longrightarrow>
              concurrent_set x ys \<Longrightarrow> x \<parallel> y \<Longrightarrow> concurrent_ops_commute (xs @ ys @ [y, x])"
apply (subst append_assoc[symmetric])
apply (rule concurrent_ops_commute_last_rearrange_Snoc_pair)
apply force
apply force
oops

lemma valid_concurrent_setD [dest]: "valid (ss @ ys @ [x]) x ss \<Longrightarrow> distinct (ss@ys@[x]) \<Longrightarrow>  concurrent_set x ys"
apply (clarsimp simp: valid_def)
apply (case_tac zs rule: rev_cases; clarsimp)
done

lemma goo1: "distinct(xs @ ys @ [x]) \<Longrightarrow> valid (xs @ ys @ [x]) x ss \<Longrightarrow> valid (xs @ ys @ [x]) y ss \<Longrightarrow> y \<in> set xs \<Longrightarrow> valid (xs @ x # ys) x ss"
apply (drule valid_appendD) back
apply force
apply force
apply (subgoal_tac "\<exists>zs. xs = ss@zs")
prefer 2
apply (force simp: valid_def)
apply (erule exE, clarify)
apply (subgoal_tac "valid (ss @ (zs @ ys) @ [x]) x ss")
apply (drule valid_concurrent_setD)
apply force
apply (subst valid_def, clarsimp)
apply (rule_tac x="zs" in exI)
apply (clarsimp simp: concurrent_set_def)
apply force
done

lemma goo2: "distinct(xs @ ys @ [x]) \<Longrightarrow> x \<parallel> y \<Longrightarrow> concurrent_set x ys \<Longrightarrow> valid (xs @ ys @ [x]) x ss \<Longrightarrow> valid (xs @ ys @ [x]) y ss \<Longrightarrow> y \<in> set ys \<Longrightarrow> valid (xs @ x # ys) x ss"
apply (subst (asm) append_assoc[symmetric]) back back
apply (drule valid_appendD) back
apply force
apply force
apply (subgoal_tac "\<exists>ys1 ys2. ys=ys1@y#ys2")
apply clarify
apply (subgoal_tac "xs= ss@ys1")
apply clarify
apply (subst valid_def)
apply (rule_tac x=ys1 in exI)
apply clarsimp
apply (subst (asm) valid_def) back
apply clarsimp

done

lemma concurrent_ops_commute_rearrange_concurrent_set:
  shows "distinct (x#xs@ys) \<Longrightarrow> concurrent_ops_commute (xs@x#ys) \<Longrightarrow> concurrent_set x ys \<Longrightarrow> concurrent_ops_commute (xs@ys@[x])"
apply (clarsimp simp: concurrent_ops_commute_def)
apply safe

apply (erule_tac x=x in allE, erule_tac x=y in allE, clarsimp, erule_tac x=ss in allE)
apply (erule impE, rule goo1, force, force)
  apply assumption back apply force
apply (erule impE)
apply(rule valid_append)
apply (rule valid_appendD, force, force, force)
apply force

apply (erule_tac x=x in allE, erule_tac x=y in allE, clarsimp, erule_tac x=ss in allE)
apply (erule impE)


(*
apply (induct ys rule: rev_induct)
apply force
apply clarsimp
apply (subgoal_tac "concurrent_ops_commute (xs @ x # xsa)")
apply clarsimp
apply (rule concurrent_ops_commute_rearrange_last)
apply force
apply force
apply force
apply force
apply (subgoal_tac "concurrent_ops_commute ((xs @ x # xsa) @ [xa])")
apply (force simp del: append_assoc)
apply force
done
*)
lemma concurrent_ops_commute_concurrent_set:
  assumes "concurrent_ops_commute (prefix@suffix@[x])"
          "concurrent_set x suffix"
          "distinct (prefix @ x # suffix)"
  shows   "apply_operations (prefix @ suffix @ [x]) = apply_operations (prefix @ x # suffix)"
using assms
  apply(induction suffix arbitrary: rule: rev_induct)
  apply force
  apply clarsimp
  apply (subst (asm) append_assoc[symmetric])
  apply (frule concurrent_ops_commute_single_elim)
  apply force
  apply force
  apply clarsimp
  apply (subgoal_tac "apply_operations (prefix @ xs @ [xa, x]) = apply_operations ((prefix @ x # xs) @ [xa])")
  apply force
  apply (subst apply_operations_Snoc)
  apply (subgoal_tac "apply_operations (prefix @ xs @ [xa, x]) = \<langle>xa\<rangle> (apply_operations ((prefix @ xs) @ [x]))")
  apply force
  apply (subst apply_operations_Snoc[symmetric])
  apply simp
  apply (subgoal_tac "apply_operations ((prefix @ xs) @ [xa, x]) = apply_operations ((prefix @ xs) @ [x, xa])")
  apply force
  apply (rule concurrent_ops_commute_dest)
  apply assumption
  apply force
  apply (subgoal_tac "valid ((prefix @ xs @ [xa]) @ [x]) xa (prefix @ xs)")
  apply force
  apply (rule valid_append)
  apply (subst append_assoc[symmetric])
  apply force
  apply (subgoal_tac "valid ((prefix @ xs) @ [xa, x]) x (prefix @ xs)", force)
  apply (rule valid_concurrent)
  apply force
  apply force
done

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
  fix x xs ys
  assume IH: "(\<And>ys. set xs = set ys \<Longrightarrow>
                    concurrent_ops_commute xs \<Longrightarrow> 
                    concurrent_ops_commute ys \<Longrightarrow>
                     distinct xs \<Longrightarrow> distinct ys \<Longrightarrow>
                     hb_consistent xs \<Longrightarrow>
                     hb_consistent ys \<Longrightarrow> 
               apply_operations xs = apply_operations ys)"
   assume assms: "set (xs @ [x]) = set ys"
                 "concurrent_ops_commute (xs @ [x])"
                 "concurrent_ops_commute ys"
                 "distinct (xs @ [x])"      "distinct ys"
                 "hb_consistent (xs @ [x])" "hb_consistent ys"
  then obtain prefix suffix where ys_split: "ys = prefix @ x # suffix \<and> concurrent_set x suffix"
    using hb_consistent_prefix_suffix_exists by fastforce
  moreover have "distinct (prefix @ suffix)" "hb_consistent xs"
    using ys_split assms by(auto simp add: disjoint_insert(1) distinct.simps(2) distinct_append list.simps(15))
  moreover {
    have "hb_consistent prefix" "hb_consistent suffix"
      using ys_split assms hb_consistent_append_D1 apply blast
      using ys_split assms hb_consistent_append_D2 hb_consistent_append_elim_ConsD by blast
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
  moreover have CPS: "concurrent_ops_commute (prefix @ suffix @ [x])"
    using assms ys_split
    apply -
    apply (rule concurrent_ops_commute_rearrange_concurrent_set)
    apply clarsimp+
    done
  moreover hence "concurrent_ops_commute (prefix @ suffix)"
    apply (subst (asm) append_assoc[symmetric])
    apply (force simp del: append_assoc)
  done
  ultimately have IH': "apply_operations xs = apply_operations (prefix@suffix)"
    using ys_split assms
    apply -
    apply(rule IH)
    apply clarsimp
    apply(metis Diff_insert_absorb Un_iff)
    apply force
    apply force
    apply force
    apply force
    apply force
    apply force
  done
  hence conc: "apply_operations (prefix@suffix @ [x]) = apply_operations (prefix@x # suffix)"
    using ys_split assms CPS by(force intro!: concurrent_ops_commute_concurrent_set)
  show "apply_operations (xs @ [x]) = apply_operations ys"
    using ys_split by (force simp: IH' conc[symmetric] append_assoc[symmetric] simp del: append_assoc)
qed

end
end