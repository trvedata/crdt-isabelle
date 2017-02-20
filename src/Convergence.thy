theory
  Convergence
imports
  Util
begin

section\<open>Convergence Theorem\<close>

subsection\<open>Happens before relations and consistency\<close>

locale happens_before = preorder hb_weak hb
  for hb_weak :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes interp :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" ("\<langle>_\<rangle>" [100] 100)
    and initial_state :: "'b"

abbreviation (in happens_before) (input) concurrent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "concurrent s1 s2 \<equiv> \<not> (hb s1 s2) \<and> \<not> (hb s2 s1)"

definition (in happens_before) concurrent_set :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
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

inductive (in happens_before) concurrent_elems_commute :: "'a list \<Rightarrow> bool" where
  [intro!]: "concurrent_elems_commute []" |
  [intro]: "\<lbrakk> concurrent_elems_commute ops;
     \<forall>x \<in> set ops. concurrent x y \<longrightarrow> (\<exists>ops1 ops2 s. ops = ops1@x#ops2 \<and>
     s = fold (op \<circ>) (map interp (ops1)) id initial_state \<and>
     (\<langle>x\<rangle> \<circ> \<langle>y\<rangle>) s = (\<langle>y\<rangle> \<circ> \<langle>x\<rangle>) s)
   \<rbrakk> \<Longrightarrow> concurrent_elems_commute (ops@[y])"

(*
inductive (in happens_before) concurrent_elems_commute :: "'a list \<Rightarrow> bool" where
  [intro!]: "concurrent_elems_commute []" |
  [intro!]: "concurrent_elems_commute [x]" |
  [intro]: "\<lbrakk> concurrent_elems_commute (pre@[x]@mid);
     concurrent x y;
     s = fold (op \<circ>) (map interp pre) id initial_state;
     (\<langle>x\<rangle> \<circ> \<langle>y\<rangle>) s = (\<langle>y\<rangle> \<circ> \<langle>x\<rangle>) s
   \<rbrakk> \<Longrightarrow> concurrent_elems_commute (pre@x#mid@[y])"
*)

inductive_cases (in happens_before) concurrent_elems_commute_elim [elim]:
  "concurrent_elems_commute []"
  "concurrent_elems_commute (xs@[x])"
  "concurrent_elems_commute xs"














(*
lemma (in happens_before) concurrent_elems_commute_ConsD2 [dest]:
  assumes "concurrent_elems_commute (x # y # xs)"
  shows   "concurrent_elems_commute (x # xs) \<and> (\<forall>xs. P xs \<longrightarrow> concurrent x y \<longrightarrow> (\<langle>x\<rangle> \<circ> \<langle>y\<rangle>) xs = (\<langle>y\<rangle> \<circ> \<langle>x\<rangle>) xs)"
using assms by (auto simp: concurrent_elems_commute_def)

lemma (in happens_before) concurrent_elems_commute_Cons_eq [simp]:
  shows "concurrent_elems_commute (xs @ [x]) = concurrent_elems_commute (x # xs)"
  by (auto simp: concurrent_elems_commute_def)

lemma (in happens_before) concurrent_elems_commute_subset [intro]:
  assumes "concurrent_elems_commute ys P" "set xs \<subseteq> set ys"
  shows   "concurrent_elems_commute xs P"
using assms by (auto simp: concurrent_elems_commute_def)
*)

inductive (in happens_before) hb_consistent :: "'a list \<Rightarrow> bool" where
  [intro!]: "hb_consistent []" |
  [intro!]: "\<lbrakk> hb_consistent xs; \<forall>x \<in> set xs. \<not> hb y x \<rbrakk> \<Longrightarrow> hb_consistent (xs @ [y])"

lemma (in happens_before) "(hb x y \<or> concurrent x y) = (\<not> hb y x)"
using local.less_asym by blast

lemma (in happens_before) [intro!]:
  assumes "hb_consistent (xs @ ys)"
  and     "\<forall>x \<in> set (xs @ ys). \<not> hb z x"
  shows   "hb_consistent (xs @ ys @ [z])"
using assms hb_consistent.intros append_assoc by metis

inductive_cases (in happens_before) hb_consistent_elim [elim]:
  "hb_consistent []"
  "hb_consistent (xs@[y])"
  "hb_consistent (xs@ys)"
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
          "concurrent_elems_commute (pre@x#xs)"
  shows "(\<langle>x\<rangle> \<circ> fold (op \<circ>) (map interp xs) id) z = (fold (op \<circ>) (map interp xs) id \<circ> \<langle>x\<rangle>) z"
using assms
  apply(induction xs rule: rev_induct, clarsimp)
  apply clarsimp                   
  apply(subgoal_tac "concurrent_elems_commute (x # xs) P")
defer
  apply(subst (asm) append_Cons[symmetric])
  apply(subst (asm) concurrent_elems_commute_Cons_eq)
  apply(drule concurrent_elems_commute_ConsD)
  apply clarsimp
  apply clarsimp
  apply(subgoal_tac "P (fold op \<circ> (map interp xs) id z)")
  apply clarsimp
  apply(subgoal_tac "((\<langle>x\<rangle>) \<circ> (\<langle>xa\<rangle>)) (fold op \<circ> (map interp xs) id z) = ((\<langle>xa\<rangle>) \<circ> (\<langle>x\<rangle>)) (fold op \<circ> (map interp xs) id z)")
  apply clarsimp
  apply(subst (asm) append_Cons[symmetric])
  apply(subst (asm) concurrent_elems_commute_Cons_eq)
  apply(drule concurrent_elems_commute_ConsD2)
  apply auto
  apply(subgoal_tac "P (fold op \<circ> (map interp xs) id z)")
  apply presburger
  apply(erule allE, erule impE, assumption)
  
(*  apply(metis (no_types, hide_lams) append_Cons concurrent_elems_commute_ConsD concurrent_elems_commute_ConsD2 concurrent_elems_commute_Cons_eq o_assoc)*)


lemma (in happens_before) fold_concurrent_rearrange':
  assumes "concurrent_set x xs"
          "concurrent_elems_commute (x#xs)"
  shows "fold (op \<circ>) (map interp (pre@x#xs)) id = fold (op \<circ>) (map interp (pre@xs@[x])) id"
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
          "\<And>s p. s \<in> set suffix \<Longrightarrow> p \<in> set prefix \<Longrightarrow> \<not> hb s p"
  shows "hb_consistent (prefix @ suffix)"
using assms by (induction rule: hb_consistent.induct) force+

abbreviation (in happens_before) porder :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "porder x y \<equiv> hb x y \<or> concurrent x y"

lemma (in happens_before) hb_consistent_append_porder:
  assumes "hb_consistent (xs @ ys)"
          "x \<in> set xs"
          "y \<in> set ys"
  shows   "\<not> hb y x"
using assms by (induction ys arbitrary: xs rule: rev_induct) force+

lemma (in happens_before) " hb x y \<Longrightarrow> \<not> hb y x"
apply (simp add: local.less_not_sym)
done

lemma (in happens_before) " concurrent x x"

by simp

lemma (in happens_before) concurrent_elems_commute_append_D [dest]:
  assumes "concurrent_elems_commute (xs@[x])"
  shows   "concurrent_elems_commute xs"
using assms
  apply -
  apply(erule concurrent_elems_commute_elim)
  apply force
done

lemma "concurrent_elems_commute (xs @[x]) \<Longrightarrow> concurrent_elems_commute (xs)"
oops

lemma (in happens_before) concurrent_elems_commute_singleton [intro!]: "concurrent_elems_commute [x]"
sorry

lemma (in happens_before) "concurrent_elems_commute (xs@[a,b]) \<Longrightarrow> concurrent a b \<Longrightarrow> concurrent_elems_commute (xs@[b,a])"
apply (induct xs rule: rev_induct)
apply clarsimp
apply (erule concurrent_elems_commute_elim)
apply clarsimp
apply clarsimp
apply (subgoal_tac "ops1 = [] \<and> ops2 = []")
apply clarify
apply (subgoal_tac "fold op \<circ> (map interp []) id initial_state = initial_state")
apply simp
apply (subgoal_tac "concurrent_elems_commute ([b]@[a])")
apply force
apply (rule concurrent_elems_commute.intros)
apply force
apply clarsimp
apply (rule_tac x="[]" in exI)
apply clarsimp
apply clarsimp
apply (metis Nil_is_append_conv butlast.simps(2) butlast_append list.distinct(1))
apply clarsimp
apply (erule concurrent_elems_commute_elim)
apply force
apply clarsimp
apply (subgoal_tac "ops1 = xs @ [x]  \<and> ops2 = []")
apply clarify
apply (erule_tac x=a in ballE)
apply (erule impE) back
apply force
apply (erule exE)
apply (erule conjE)+
apply (erule exE)

apply (thin_tac "xs @ [x, a] = (xs @ [x]) @ [a]")
apply (subgoal_tac "concurrent_elems_commute ((xs @ [x, b]) @ [a])")
apply simp
apply (rule concurrent_elems_commute.intros)
apply clarsimp
oops


oops

lemma (in happens_before) goo:
shows "concurrent_elems_commute (prefix @ xs @ [xa, x]) \<Longrightarrow>
             hb_consistent (prefix @ x # xs @ [xa]) \<Longrightarrow>
             distinct (prefix @ x # xs @ [xa]) \<Longrightarrow>
             concurrent_set x xs \<Longrightarrow>
             concurrent x xa \<Longrightarrow> concurrent_elems_commute (prefix @ xs @ [x])"
apply (erule concurrent_elems_commute_elim)
apply force
apply clarsimp
  apply (subgoal_tac "prefix@xs = ops1 \<and> [] = ops2")
prefer 2
apply (rule_tac ys="[xa]" and xs = "ops1 @ xa # ops2" in pre_suf_eq_distinct_list)
prefer 3
apply force
apply (subgoal_tac "distinct (prefix @ xs @ [xa])")
apply force
apply (thin_tac "prefix @ xs @ [xa] = ops1 @ xa # ops2")
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp

sorry


lemma (in happens_before) foo:
  shows "concurrent_elems_commute (prefix@suffix@[x]) \<Longrightarrow>
    concurrent_set x suffix \<Longrightarrow> 
    distinct (prefix @ x # suffix) \<Longrightarrow>
    hb_consistent(prefix @ x # suffix) \<Longrightarrow>
    fold op \<circ> (map interp (prefix @ suffix @ [x])) id initial_state =
    fold op \<circ> (map interp (prefix @ x # suffix)) id initial_state"
using assms
  apply(induction suffix arbitrary: rule: rev_induct)
  apply clarsimp
  apply clarsimp
  apply (subgoal_tac "concurrent_elems_commute (prefix @ xs @ [x]) \<and>
                    x \<notin> set xs \<and> x \<notin> set prefix \<and>
                    hb_consistent (prefix @ x # xs)")
apply clarsimp
  apply (subgoal_tac "(\<langle>x\<rangle>) ((\<langle>xa\<rangle>) (fold op \<circ> (map interp xs) (fold op \<circ> (map interp prefix) id) initial_state)) = (\<langle>xa\<rangle>) ((\<langle>x\<rangle>) (fold op \<circ> (map interp xs) (fold op \<circ> (map interp prefix) id) initial_state))")
apply force
  apply(subgoal_tac "concurrent_elems_commute (prefix @ (xs @ [xa]) @ [x])")
  apply(erule concurrent_elems_commute_elim)
  apply force
  apply (erule_tac x=xa in ballE)
  apply(subgoal_tac "x = y \<and> ops = prefix @ xs @ [xa]")
  apply clarsimp
  apply (subgoal_tac "prefix@xs = ops1 \<and> [] = ops2")
apply clarify
apply (metis comp_apply fold_append map_append)
apply (rule_tac ys="[xa]" and xs = "ops1 @ xa # ops2" in pre_suf_eq_distinct_list)
prefer 3
apply force
apply (subgoal_tac "distinct (prefix @ xs @ [xa])")
apply force
apply (thin_tac "prefix @ xs @ [xa] = ops1 @ xa # ops2")
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply (rule conjI)
defer
apply (rule conjI)
apply force
apply (rule conjI)
apply force

apply (metis append_Cons hb_consistent_elim(4))
apply (rule goo, auto)
done

















  apply(erule_tac x="x" in meta_allE)
  apply(subst (asm) append_assoc[symmetric])
  apply(frule concurrent_elems_commute_append_D)
  apply clarsimp  


lemma (in happens_before) foo:
  shows "concurrent_elems_commute (prefix@suffix@[x]) \<Longrightarrow>
    concurrent_set x suffix \<Longrightarrow>
    distinct (prefix @ x # suffix) \<Longrightarrow>
    hb_consistent(prefix @ x # suffix) \<Longrightarrow>
    fold op \<circ> (map interp (prefix @ suffix @ [x])) id initial_state =
    fold op \<circ> (map interp (prefix @ x # suffix)) id initial_state"
using assms
  apply(induction suffix arbitrary: x rule: rev_induct)
  apply clarsimp
  apply clarsimp
  apply(subgoal_tac "concurrent_elems_commute (prefix @ (xs @ [x]) @ [xa])")
  apply(erule concurrent_elems_commute_elim)
  apply force
  apply(subgoal_tac "x = y \<and> ops = prefix @ xs @ [xa]")
  apply clarsimp
  apply(erule_tac x="x" in meta_allE)
  apply(subst (asm) append_assoc[symmetric])
  apply(frule concurrent_elems_commute_append_D)
  apply clarsimp  








  apply(induction suf1 arbitrary: suf2 rule: rev_induct)
  apply clarsimp
  apply clarsimp
  apply(erule_tac x="xa#suf2" in meta_allE)
  apply clarsimp
  apply(subgoal_tac "concurrent x xa")
  apply(erule concurrent_elems_commute_elim)
  apply clarsimp
  apply(subgoal_tac "xa \<in> set xs")
  apply(erule_tac x=xa in ballE)
  apply clarsimp



  apply(induction arbitrary: prefix suffix rule: concurrent_elems_commute.induct)
  apply clarsimp
  apply clarsimp

apply (subgoal_tac "y = x \<and> ops = xs")
prefer 2

apply simp
apply(subgoal_tac "ops = prefix@suffix")
apply clarsimp
apply(erule_tac x="prefix" in meta_allE)
apply(erule_tac x="suffix" in meta_allE)
apply(erule_tac x=x in meta_allE)




apply (subgoal_tac "ops = [] \<or> (\<exists>ox os. ops = os @ [ox])")
apply (erule disjE)
apply clarsimp
apply (simp add: subset_insert)
defer
apply auto[1]

apply (erule exE)+
apply (subgoal_tac "ox \<in> set prefix \<or> ox \<in> set suffix")
apply (erule disjE)

apply (erule_tac x="remove1 ox prefix" in meta_allE)
apply (erule_tac x=suffix in meta_allE)
apply (erule_tac x=x in meta_allE)
apply (erule_tac x="os@[ox]" in meta_allE)
apply clarsimp





oops
theorem (in happens_before) convergence:
  assumes "set xs = set ys"
          "concurrent_elems_commute xs"
          "distinct xs"
          "distinct ys"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "fold (op \<circ>) (map interp xs) id initial_state = fold (op \<circ>) (map interp ys) id initial_state"
using assms proof(induction xs arbitrary: ys rule: rev_induct, simp)
  fix x xs ys
  assume IH: "(\<And>ys. set xs = set ys \<Longrightarrow>
                    concurrent_elems_commute xs \<Longrightarrow> 
                     distinct xs \<Longrightarrow> distinct ys \<Longrightarrow>
                     hb_consistent xs \<Longrightarrow>
                     hb_consistent ys \<Longrightarrow> 
               fold op \<circ> (map interp xs) id initial_state = fold op \<circ> (map interp ys) id initial_state)"
   assume assms: "set (xs @ [x]) = set ys"
                 "concurrent_elems_commute (xs @ [x])"
                 "distinct (xs @ [x])"      "distinct ys"
                 "hb_consistent (xs @ [x])" "hb_consistent ys"
  then obtain prefix suffix where ys_split: "ys = prefix @ x # suffix \<and> concurrent_set x suffix"
    using hb_consistent_prefix_suffix_exists by fastforce
  moreover have "distinct (prefix @ suffix)" "hb_consistent xs"
    using ys_split assms by(auto simp add: disjoint_insert(1) distinct.simps(2) distinct_append list.simps(15))
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
  ultimately have IH': "fold op \<circ> (map interp xs) id initial_state = fold op \<circ> (map interp (prefix@suffix)) id initial_state"
    using ys_split assms by (fastforce intro!: IH)
  have "concurrent_elems_commute (prefix@suffix@[x])"
    using ys_split assms sorry
  have conc: "fold op \<circ> (map interp (prefix@suffix @ [x])) id initial_state = fold op \<circ> (map interp (prefix@x # suffix)) id initial_state"
    using ys_split assms by(rule foo)
  show "fold op \<circ> (map interp (xs @ [x])) id initial_state = fold op \<circ> (map interp ys) id initial_state"
    apply (insert ys_split)
    apply clarify
    apply(subst conc[symmetric])
    apply (subst map_append)
    apply (subst fold_append)
    apply (subst o_apply)
    apply (subst fold_comp_eq)
    apply (subst IH')
    apply clarsimp
  done
qed

theorem (in happens_before) convergence:
  assumes "set xs = set ys"
          "concurrent_elems_commute xs"
          "distinct xs"
          "distinct ys"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "fold (op \<circ>) (map interp xs) id = fold (op \<circ>) (map interp ys) id"
using assms proof(induction xs arbitrary: ys rule: rev_induct, simp)
  fix x xs ys
  assume IH: "(\<And>ys. set xs = set ys \<Longrightarrow>
                    concurrent_elems_commute xs \<Longrightarrow> 
                     distinct xs \<Longrightarrow> distinct ys \<Longrightarrow>
                     hb_consistent xs \<Longrightarrow>
                     hb_consistent ys \<Longrightarrow> 
               fold op \<circ> (map interp xs) id = fold op \<circ> (map interp ys) id)"
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
  ultimately have IH': "fold op \<circ> (map interp xs) id = fold op \<circ> (map interp (prefix@suffix)) id"
    using ys_split assms by (fastforce intro!: IH)

  have "concurrent_elems_commute (x # suffix)"
    using ys_split assms concurrent_elems_commute_subset by auto
  have conc: "fold op \<circ> (map interp (suffix @ [x])) id = fold op \<circ> (map interp (x # suffix)) id"
    using ys_split assms by (subst fold_concurrent_rearrage') auto
  show "fold op \<circ> (map interp (xs @ [x])) id = fold op \<circ> (map interp ys) id"
    apply (insert ys_split)
    apply clarify
    apply (subst map_append) back
    apply (subst fold_append)
    apply (subst o_apply)
    apply (subst fold_comp_eq) back
    apply (subst conc[symmetric])
    apply (subst map_append)
    apply (subst fold_append)
    apply (subst o_apply)
    apply (subst fold_comp_eq)
    apply (subst IH')
    apply clarsimp
    apply (metis fold_comp_eq o_assoc)
  done
qed

corollary (in happens_before) convergence_point:
  assumes "set xs = set ys"
          "concurrent_elems_commute xs"
          "distinct xs"
          "distinct ys"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "fold (op \<circ>) (map interp xs) id a = fold (op \<circ>) (map interp ys) id a"
using assms by (simp add: convergence)

end