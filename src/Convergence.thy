theory
  Convergence
imports
  Util
  "~~/src/HOL/Library/Permutation"
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

(*
inductive (in happens_before) concurrent_elems_commute :: "'a list \<Rightarrow> bool" where
  [intro!]: "concurrent_elems_commute []" |
  [intro]: "\<lbrakk> concurrent_elems_commute ops;
     \<forall>x \<in> set ops. concurrent x y \<longrightarrow> (\<exists>ops1 ops2 s. ops = ops1@x#ops2 \<and>
     s = fold (op \<circ>) (map interp (ops1)) id initial_state \<and>
     (\<langle>x\<rangle> \<circ> \<langle>y\<rangle>) s = (\<langle>y\<rangle> \<circ> \<langle>x\<rangle>) s)
   \<rbrakk> \<Longrightarrow> concurrent_elems_commute (ops@[y])"
*)

definition (in happens_before) concurrent_elems_commute' :: "'a list \<Rightarrow> bool" where
  "concurrent_elems_commute' ss \<equiv>
     \<forall>x y pre suf. ss = pre @ [x, y] @ suf \<longrightarrow> concurrent x y \<longrightarrow>
       fold (op \<circ>) (map interp (pre @ [x, y])) id initial_state =
       fold (op \<circ>) (map interp (pre @ [y, x])) id initial_state"

definition (in happens_before) concurrent_elems_commute :: "'a list \<Rightarrow> bool" where
  "concurrent_elems_commute ss \<equiv>
     \<forall>pre mid suf. ss = pre @ mid @ suf \<and> (\<forall>x \<in> set mid. \<forall>y \<in> set mid. concurrent x y) \<longrightarrow>
       (\<forall>p. p <~~> mid \<longrightarrow>
        fold (op \<circ>) (map interp (pre @ mid)) id initial_state =
        fold (op \<circ>) (map interp (pre @ p)) id initial_state)"

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
(*
inductive_cases (in happens_before) concurrent_elems_commute_elim [elim]:
  "concurrent_elems_commute []"
  "concurrent_elems_commute (xs@[x])"
  "concurrent_elems_commute xs"
*)













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

(*
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
*)
(*
lemma (in happens_before) fold_concurrent_rearrange':
  assumes "concurrent_set x xs"
          "concurrent_elems_commute (x#xs)"
  shows "fold (op \<circ>) (map interp (pre@x#xs)) id = fold (op \<circ>) (map interp (pre@xs@[x])) id"
using assms
  apply clarsimp
  apply(subst fold_concurrent_rearrange, clarsimp, clarsimp)
  apply(rule fold_comp_eq)
done
*)

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
  apply(unfold concurrent_elems_commute_def)
  apply force
done

lemma (in happens_before) concurrent_elems_commute_append_D2 [dest]:
  assumes "concurrent_elems_commute (xs@ys)"
  shows   "concurrent_elems_commute xs"
using assms
  apply -
  apply(unfold concurrent_elems_commute_def)
  apply force
done

lemma (in happens_before) concurrent_elems_commute_singleton [intro!]:
  shows "concurrent_elems_commute [x]"
  apply(unfold concurrent_elems_commute_def)
  apply auto
  apply(case_tac "pre = [x] \<or> mid = [x]\<or> suf = [x]")
  apply(auto simp add: Cons_eq_append_conv)
done

(*
lemma (in happens_before)
  assumes "concurrent_elems_commute xs"
      and "fold (op \<circ>) (map interp (xs@[x, y])) id initial_state =
           fold (op \<circ>) (map interp (xs@[y, x])) id initial_state"
      and "concurrent x y"
      and "distinct (xs@[x,y])"
    shows "concurrent_elems_commute (xs@[x,y])"
using assms
    apply(clarsimp simp: concurrent_elems_commute_def)
apply (case_tac suf)
apply clarsimp
*)
(*
  apply(induction xs rule: rev_induct)
  apply(clarsimp simp: concurrent_elems_commute_def)
  apply(metis append_Nil append_is_Nil_conv butlast.simps(2) butlast_append fold_Nil id_apply last_snoc list.sel(3) list.simps(3) list.simps(8))
  apply clarsimp
  apply(subgoal_tac "concurrent_elems_commute xs")
  apply(clarsimp simp: concurrent_elems_commute_def)
*)

(*
lemma (in happens_before) concurrent_elems_commuteD: "concurrent_elems_commute (xs @ [a, b]) \<Longrightarrow> concurrent a b \<Longrightarrow> fold (op \<circ>) (map interp (xs @ [a, b])) id initial_state =
       fold (op \<circ>) (map interp (xs @ [b, a])) id initial_state"
by (auto simp: concurrent_elems_commute_def)

lemma (in happens_before) concurrent_elems_commuteD2: "concurrent_elems_commute (xs @ [a, b] @ ys) \<Longrightarrow> concurrent a b \<Longrightarrow> fold (op \<circ>) (map interp (xs @ [a, b])) id initial_state =
       fold (op \<circ>) (map interp (xs @ [b, a])) id initial_state"
by (auto simp: concurrent_elems_commute_def)

lemma (in happens_before)
  shows "concurrent_elems_commute ([x,a,b]) \<Longrightarrow> distinct ([x,a,b]) \<Longrightarrow> concurrent a b \<Longrightarrow> concurrent x b \<Longrightarrow>
    fold (op \<circ>) (map interp ([b, x])) id initial_state = fold (op \<circ>) (map interp ([x, b])) id initial_state"
unfolding concurrent_elems_commute_def
*)

lemma (in happens_before) concurrent_elems_commute_last_rearrange:
  shows "concurrent_elems_commute (xs@[a,b]) \<Longrightarrow> distinct (xs@[a,b]) \<Longrightarrow> concurrent a b \<Longrightarrow> concurrent_elems_commute (xs@[b,a])"
  apply(unfold concurrent_elems_commute_def)
  apply clarsimp


apply (subst concurrent_elems_commute_def)
apply (rule allI)+
apply (rule impI)+
apply (case_tac suf)
apply clarsimp
apply (drule concurrent_elems_commuteD)
apply force
apply force
apply (case_tac list)
defer
apply clarsimp
apply (subgoal_tac "\<exists>ys. xs = pre @ x # y # ys")
apply (erule exE)
apply (subgoal_tac "concurrent_elems_commute (pre @ [x, y] @ ys)")
apply (drule concurrent_elems_commuteD2)
apply force
apply force
apply (drule concurrent_elems_commute_append_D2)
apply force
apply (metis append_Nil2 butlast.simps(2) butlast_append list.simps(3))
apply clarsimp
apply (subgoal_tac "concurrent_elems_commute ((pre @ [x])@[a, b])")
apply (frule concurrent_elems_commuteD)
apply force
apply clarsimp
apply (subgoal_tac "concurrent_elems_commute (pre @ [x, a] @ [b])")
apply (frule concurrent_elems_commuteD2)
apply force




apply (rule_tac ys=suf in concurrent_elems_commuteD2)
apply force
apply clarsimp

apply (induct xs rule: rev_induct)
using concurrent_elems_commute_two apply simp
apply clarsimp
apply (subst concurrent_elems_commute_def)
apply clarsimp




apply (case_tac suf)
apply clarsimp
apply (subgoal_tac "concurrent_elems_commute ((xs @ [x]) @ [ a, b])")
apply (drule concurrent_elems_commuteD)
apply force
apply force










    apply(clarsimp simp: concurrent_elems_commute_def)
apply (case_tac suf)
apply clarsimp

apply (case_tac list)
apply clarsimp

apply (erule_tac x=x in allE)
apply (erule_tac x=a in allE)
apply (erule_tac x=pre in allE)
apply clarsimp
(*
  apply(unfold concurrent_elems_commute_def)
  apply(rule allI)+
  apply(rule impI)
  apply(erule_tac x=y in allE, erule_tac x=x in allE, erule_tac x=pre in allE, erule_tac x=suf in allE)
  apply clarsimp
  apply(erule impE)
*)

(*
  apply clarsimp
  apply(subgoal_tac "pre = [] \<and> suf = [] \<and> b = x \<and> a = y")
  apply force
  apply(metis append_Cons append_Nil append_is_Nil_conv butlast_append butlast_snoc in_set_conv_decomp not_Cons_self2 set_ConsD)
  apply clarsimp
  apply(erule meta_impE)
  *)
  

(*
  apply(erule concurrent_elems_commute_elim, force)+
  apply(subgoal_tac "concurrent_elems_commute ((xs @ [b]) @ [a])", force)
  apply(subgoal_tac "ops = xs @ [a] \<and> b = y \<and> opsa = xs \<and> ya = a")
  apply(rule concurrent_elems_commute.intros)+
  apply force
  apply clarsimp
  apply(erule_tac x=x in ballE) back
  apply clarsimp
  apply(rule_tac x="ops1a" in exI, clarsimp)
  apply(case_tac "a \<in> set ops2a")
  apply(subgoal_tac "\<exists>zs. ops2a = zs@[a]", clarsimp)
  apply(metis last.simps last_appendR list.simps(3) snoc_eq_iff_butlast)
  apply(subgoal_tac "ops2a=[]")
  apply blast
  apply(metis last.simps last_appendR last_in_set list.simps(3))
  apply(erule_tac x=x in ballE)
  apply clarsimp
  apply(rule_tac x="ops1" in exI, clarsimp)
  apply(rule ballI, rule impI, (erule conjE)+)
  apply(subgoal_tac "x \<in> set xs \<or> x = b")
  apply(erule disjE)
  apply clarify
  apply(erule_tac x="x" in ballE) back
  apply(erule impE, force)
  apply(erule exE)+
  apply(erule conjE)
  apply(erule exE)
  apply(rule_tac x=ops1 in exI)
  apply clarsimp
  apply force
  apply(rule_tac x=xs in exI) 
  apply clarsimp
  apply(subgoal_tac "ops1=xs \<and> ops2=[]")
  apply force
  apply(metis append_Nil2 butlast.simps(2) butlast_append in_set_conv_decomp)
  apply clarsimp
  apply force
done
*)

corollary (in happens_before) concurrent_elems_commute_last_rearrange_iff:
  shows "distinct (xs@[a,b]) \<Longrightarrow> concurrent a b \<Longrightarrow> concurrent_elems_commute (xs@[a,b]) = concurrent_elems_commute (xs@[b,a])"
using concurrent_elems_commute_last_rearrange by auto

lemma (in happens_before)
  assumes "concurrent_elems_commute xs = concurrent_elems_commute ys"
          "fold (op \<circ>) (map interp xs) id = fold (op \<circ>) (map interp ys) id"
          "set xs = set ys"
          "distinct (xs@[x])"
  shows   "concurrent_elems_commute (xs@[x]) = concurrent_elems_commute (ys@[x])"
using assms
  apply -
  apply(rule iffI)
  apply(rule concurrent_elems_commute.intros, force)
  apply(erule concurrent_elems_commute_elim)
  apply(rule ballI, rule impI)
  apply(erule_tac x=xa in ballE, clarsimp)
sorry
(*
  apply(induction xs arbitrary: ys rule: rev_induct)
  apply simp
  apply(rule iffI)
  apply(rule concurrent_elems_commute.intros, force)
  apply(erule concurrent_elems_commute_elim)
*)
(*
  apply(rule iffI)
  apply(erule concurrent_elems_commute_elim)
  apply(rule concurrent_elems_commute.intros, force)
  apply(rule ballI, rule impI)
  apply(erule_tac x=xa in ballE, erule impE, force)
  apply(erule exE, (erule conjE)+, erule exE)
*)

lemma (in happens_before)
  assumes "concurrent a b"
          "distinct (xs@[a, b]@ys)"
  shows   "concurrent_elems_commute (xs@[a, b]@ys) = concurrent_elems_commute (xs@[b, a]@ys)"
using assms
  apply(induction ys arbitrary: xs a b)
  apply clarsimp
  apply(rule concurrent_elems_commute_last_rearrange_iff, force, force)
  apply clarsimp
  apply(erule_tac x="xs@[aa]" in meta_allE)
  apply(erule_tac x=b in meta_allE)
  apply(erule_tac x=a in meta_allE)

lemma (in happens_before) concurrent_elems_commute_trans:
  assumes "concurrent_elems_commute (xs@[x])"
          "distinct (xs@[x, y])"
          "concurrent x y"
   shows  "concurrent_elems_commute ((xs @ [x]) @ [y])"
using assms
  apply -
  apply(rule concurrent_elems_commute.intros)
  apply assumption
  apply(rule ballI)
  apply(subgoal_tac "xa \<in> set xs \<or> xa = x")
  apply(erule disjE)
prefer 2
  apply clarsimp
  apply(rule_tac x="xs" in exI, clarsimp)
  apply(erule concurrent_elems_commute_elim)
oops

lemma (in happens_before) concurrent_elems_commute_first_last_swap:
  assumes "distinct (y#ys)"
      and "concurrent_set y ys"
      and "concurrent_elems_commute (y#ys)"
    shows "concurrent_elems_commute (ys@[y])"
using assms
sorry

lemma (in happens_before) fold_cong:
  assumes "\<langle>x\<rangle> \<circ> (\<langle>y\<rangle> \<circ> fold (op \<circ>) (map interp prefix) id) = \<langle>y\<rangle> \<circ> (\<langle>x\<rangle> \<circ> fold (op \<circ>) (map interp prefix) id)"
          "concurrent_set x suffix"
          "concurrent_elems_commute prefix"
    shows "True"
sorry

lemma (in happens_before) hoo:
  assumes "concurrent_elems_commute (prefix @ [x, y] @ suffix)"
      and "concurrent x y"
      and "distinct (prefix @ [x, y] @ suffix)"
    shows "concurrent_elems_commute (prefix @ [y, x] @ suffix)"
using assms
  apply -
  apply(induction suffix rule: rev_induct)
  using concurrent_elems_commute_last_rearrange_iff apply force
  apply(subgoal_tac "concurrent_elems_commute (prefix @ [x, y] @ xs)")
  apply(subst append_assoc[symmetric]) back
  apply(subst append_assoc[symmetric])
  apply(rule concurrent_elems_commute.intros)
  apply force
  apply(rule ballI, rule impI)
  apply clarsimp
  apply(erule disjE)
  apply clarsimp
  apply(rule_tac x="prefix" in exI)
  apply clarsimp

lemma (in happens_before) concurrent_elems_commute_last_append_rearrange:
  shows "
    concurrent_elems_commute (prefix @ x # suffix) \<Longrightarrow>
    concurrent_set x suffix \<Longrightarrow>
    distinct (prefix@x#suffix) \<Longrightarrow>
    concurrent_elems_commute (prefix @ suffix @ [x])"
using assms
  apply -
  apply(induction suffix arbitrary: prefix x)
  apply force
  apply(erule_tac x="prefix @ [a]" in meta_allE)
  apply(erule_tac x="x" in meta_allE)
  apply(subgoal_tac "concurrent_elems_commute ((prefix @ [a]) @ x # suffix)")
  apply clarsimp
  using hoo apply force
done

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
apply(subst (asm) append_assoc[symmetric]) back
apply(drule concurrent_elems_commute_last_rearrange)
apply force
apply force
apply force
done

theorem (in happens_before) convergence:
  assumes "set xs = set ys"
          "concurrent_elems_commute xs"
          "concurrent_elems_commute ys"
          "distinct xs"
          "distinct ys"
          "hb_consistent xs"
          "hb_consistent ys"
  shows   "fold (op \<circ>) (map interp xs) id initial_state = fold (op \<circ>) (map interp ys) id initial_state"
using assms proof(induction xs arbitrary: ys rule: rev_induct, simp)
  fix x xs ys
  assume IH: "(\<And>ys. set xs = set ys \<Longrightarrow>
                    concurrent_elems_commute xs \<Longrightarrow> 
                    concurrent_elems_commute ys \<Longrightarrow>
                     distinct xs \<Longrightarrow> distinct ys \<Longrightarrow>
                     hb_consistent xs \<Longrightarrow>
                     hb_consistent ys \<Longrightarrow> 
               fold op \<circ> (map interp xs) id initial_state = fold op \<circ> (map interp ys) id initial_state)"
   assume assms: "set (xs @ [x]) = set ys"
                 "concurrent_elems_commute (xs @ [x])"
                 "concurrent_elems_commute ys"
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
  moreover have CPS: "concurrent_elems_commute (prefix @ suffix @ [x])"
    using assms ys_split
    apply -
    apply clarsimp
    apply(rule concurrent_elems_commute_last_append_rearrange)
    apply auto
    done
  moreover hence "concurrent_elems_commute (prefix @ suffix)"
    by force
  ultimately have IH': "fold op \<circ> (map interp xs) id initial_state = fold op \<circ> (map interp (prefix@suffix)) id initial_state"
    using ys_split assms
    apply -
    apply(rule IH)
    apply clarsimp
    apply(metis Diff_insert_absorb Un_iff)
    apply force+
    done
  hence conc: "fold op \<circ> (map interp (prefix@suffix @ [x])) id initial_state = fold op \<circ> (map interp (prefix@x # suffix)) id initial_state"
    using ys_split assms CPS
      apply -
      apply(rule foo)
      apply auto
    done
  show "fold op \<circ> (map interp (xs @ [x])) id initial_state = fold op \<circ> (map interp ys) id initial_state"
    apply (insert ys_split)
    apply clarify
    apply(subst conc[symmetric])
    apply (subst map_append)
    apply (subst fold_append)
    apply (subst o_apply)
    using IH' apply(simp add: comp_def fold_comp_eq fold_map)
    done
qed

end
  