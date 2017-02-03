theory
  Fresh_Start
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


(*

  




































definition next_lamport :: "(lamport, 'v) elt list \<Rightarrow> nat \<Rightarrow> lamport" where
  "next_lamport xs node_name \<equiv>
     let ss = fst ` fst ` set xs in
       if ss = {} then
         (node_name, 0)
       else
         (node_name, Suc (Max ss))"

inductive possible_broadcasts :: "(lamport, 'v) elt list \<Rightarrow> nat \<Rightarrow> 'v operation event \<Rightarrow> bool" where
  possible_broadcasts_Nil [intro!]: "\<lbrakk> next_lamport ([]::(lamport,'v) elt list) node_name = next \<rbrakk> \<Longrightarrow> possible_broadcasts [] node_name (node_name, Broadcast, (Insert next v None))" |
  possible_broadcasts_Cons_tail [intro!]: "\<lbrakk> possible_broadcasts xs node_name tail \<rbrakk> \<Longrightarrow> possible_broadcasts (x#xs) node_name tail" |
  possible_broadcasts_Cons_head [intro!]: "\<lbrakk> next_lamport xs node_name = next; (node_name, Broadcast, Insert next v (Some i)) = oper \<rbrakk> \<Longrightarrow> possible_broadcasts ((i,_)#xs) node_name oper"



inductive node_state_evolution :: "(lamport, 'a) elt list \<Rightarrow> nat \<Rightarrow> 'a operation event \<Rightarrow> (lamport, 'a) elt list \<Rightarrow> bool" where
  "\<lbrakk> interpret_delivery xs oper = Some ys \<rbrakk> \<Longrightarrow> node_state_evolution xs node_name (node_name, Deliver, oper) ys" |
  "\<lbrakk> possible_broadcasts xs node_name ev \<rbrakk> \<Longrightarrow> node_state_evolution xs node_name ev xs"

inductive (in node_state_evolution' :: "(lamport, 'a) elt list \<Rightarrow> 'a operation event set \<Rightarrow> (lamport, 'a) elt list \<Rightarrow> bool" where
  "node_state_evolution' [] {} []" |
  "\<lbrakk> node_state_evolution' xs es ys"

locale infinite_stateful_network = infinite_event_structure +
  fixes states :: "nat \<Rightarrow> (lamport, 'a) elt list"
  

end

section\<open>Modal logic of networks\<close>

datatype 'a action
  = Broadcast "'a"
  | Deliver   "'a"

datatype 'a formula
  = True   ("\<top>" 65)
  | False  ("\<bottom>" 65)
  | Conjunction "'a formula" "'a formula" ("_/ &/  _" [75,75]75)
  | Implication "'a formula" "'a formula" ("_/ \<rightarrow>/ _" [65,65]65)
  | Atomic "nat" "'a action"
  | Diamond "'a formula"                  ("\<diamondop>/ _" [85]85)
  | Dnomaid "'a formula"                 ("\<diamondop>\<^sup>-\<^sup>1/ _" [85]85)
  | Box "'a formula"                      ("\<box>/ _" [85]85)
  | Xob "'a formula"                     ("\<box>\<^sup>-\<^sup>1/ _" [85]85)

syntax
  Broadcast_syntax :: "nat \<Rightarrow> 'a \<Rightarrow> 'a formula" ("\<B>/_/_" [85,85]85)
  Deliver_syntax   :: "nat \<Rightarrow> 'a \<Rightarrow> 'a formula" ("\<D>/_/_" [85,85]85)

translations
  "\<B> node msg" \<rightleftharpoons> "CONST Atomic node (CONST Broadcast msg)"
  "\<D> node msg" \<rightleftharpoons> "CONST Atomic node (CONST Deliver msg)"

fun quantN :: "nat \<Rightarrow> (nat \<Rightarrow> 'a formula) \<Rightarrow> ('a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula) \<Rightarrow> 'a formula \<Rightarrow> 'a formula" where
  "quantN 0       f j e = e" |
  "quantN (Suc m) f j e = j (f m) (quantN m f j e)"

fun satisfaction :: "(nat \<Rightarrow> 'a action \<times> nat) \<times> nat \<Rightarrow> 'a formula \<Rightarrow> bool" ("_/ \<Turnstile>/ _" [65,65]65) where
  "(\<M>, a) \<Turnstile> \<top>      = HOL.True" |
  "(\<M>, a) \<Turnstile> \<bottom>     = HOL.False" |
  "(\<M>, a) \<Turnstile> \<phi> & \<psi> = ((\<M>, a) \<Turnstile> \<phi> \<and> (\<M>, a) \<Turnstile> \<psi>)" |
  "(\<M>, a) \<Turnstile> \<phi> \<rightarrow> \<psi> = ((\<M>, a) \<Turnstile> \<phi> \<longrightarrow> (\<M>, a) \<Turnstile> \<psi>)" |
  "(\<M>, a) \<Turnstile> \<diamondop> \<phi> = (\<exists>a'. a < a' \<and> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> \<box> \<phi> = (\<forall>a'. a < a' \<longrightarrow> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> \<diamondop>\<^sup>-\<^sup>1 \<phi> = (\<exists>a'. a' < a \<and> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> \<box>\<^sup>-\<^sup>1 \<phi> = (\<forall>a'. a' < a \<longrightarrow> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> Atomic node action = (\<M> a = (action, node))"

definition Negation :: "'a formula \<Rightarrow> 'a formula" ("not/ _" [85]85) where
  "Negation \<phi> \<equiv> \<phi> \<rightarrow> \<bottom>"

definition Disjunction :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" ("_/ orelse/ _" [75,75]75) where
  "\<phi> orelse \<psi> \<equiv> not ((not \<phi>) & (not \<psi>))"

lemma Negation_satisfaction:
  shows "\<M> \<Turnstile> not \<phi> = (\<not> (\<M> \<Turnstile> \<phi>))"
unfolding Negation_def by (cases "\<M>", simp)

lemma Diamond_Box_deMorgan1:
  shows "\<M> \<Turnstile> not \<diamondop> \<phi> = \<M> \<Turnstile> \<box> not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Diamond_Box_deMorgan2:
  shows "\<M> \<Turnstile> not \<box> \<phi> = \<M> \<Turnstile> \<diamondop> not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Dnomaid_Xob_deMorgan1:
  shows "\<M> \<Turnstile> not \<diamondop>\<^sup>-\<^sup>1 \<phi> = \<M> \<Turnstile> \<box>\<^sup>-\<^sup>1 not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Dnomaid_Xob_deMorgan2:
  shows "\<M> \<Turnstile> not \<box>\<^sup>-\<^sup>1 \<phi> = \<M> \<Turnstile> \<diamondop>\<^sup>-\<^sup>1 not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Disjunction_Conjunction_deMorgan1:
  shows "\<M> \<Turnstile> not (\<phi> orelse \<psi>) = \<M> \<Turnstile> (not \<phi>) & (not \<psi>)"
unfolding Disjunction_def Negation_def by (cases "\<M>", simp)

lemma Disjunction_Conjunction_deMorgan2:
  shows "\<M> \<Turnstile> not (\<phi> & \<psi>) = \<M> \<Turnstile> (not \<phi>) orelse (not \<psi>)"
unfolding Disjunction_def Negation_def by (cases "\<M>", simp)

definition valid :: "'a formula \<Rightarrow> bool" ("\<Turnstile>/ _" [50]50) where
  "\<Turnstile> \<phi> \<equiv> \<forall>\<M>. \<M> \<Turnstile> \<phi>"

locale fixed_nodes =
  fixes node_count :: "nat"

definition (in fixed_nodes) exists :: "(nat \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" (binder "Ex" 55) where
  "exists f \<equiv> quantN node_count f Disjunction False"

definition (in fixed_nodes) forall :: "(nat \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" (binder "All" 55) where
  "forall f \<equiv> quantN node_count f Conjunction True"

locale network = fixed_nodes +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes all_messages_delivered: "\<And>p::nat. \<And>m::'a. \<Turnstile> (\<B> p m) \<rightarrow> \<diamondop> (\<D> p m)"
  and messages_are_unique: "\<And>p::nat. \<And>m::'a. \<Turnstile> (\<D> p m) \<rightarrow> \<box> not (\<D> p m)"
  and no_out_thin_air: "\<And>p::nat. \<And>m::'a. \<Turnstile> \<D> p m \<rightarrow> (Ex q. (\<diamondop>\<^sup>-\<^sup>1 (\<B> q m)))"
  and no_message_lost: "\<And>p::nat. \<And>m::'a. \<Turnstile> (\<D> p m) \<rightarrow> (All q. ((\<diamondop> (\<D> q m)) orelse (\<diamondop>\<^sup>-\<^sup>1 (\<D> q m))))"
  and causal_delivery: "\<And>p::nat. \<And>m1 m2::'a. R m1 m2 \<Longrightarrow> \<Turnstile> (\<D> p m2) \<rightarrow> \<diamondop>\<^sup>-\<^sup>1 (\<D> p m1)"

lemma (in network) All_elim:
  assumes "\<Turnstile> All p. f p"
  shows   "\<And>p. p < node_count \<Longrightarrow> \<Turnstile> f p"
using assms unfolding forall_def valid_def
  apply clarsimp
  apply(induction node_count; clarsimp)
  apply(subgoal_tac "p = node_count \<or> p < node_count")
  apply force+
done

lemma (in network) All_intro:
  assumes "\<And>p. p < node_count \<Longrightarrow> \<Turnstile> f p"
  shows   "\<Turnstile> All p. f p"
using assms unfolding forall_def valid_def
  apply clarsimp
  apply(induction node_count; clarsimp)
done

lemma (in network) Implication_intro:
  assumes "\<Turnstile> p \<Longrightarrow> \<Turnstile> q"
  shows   "\<Turnstile> p \<rightarrow> q"
using assms unfolding valid_def
  apply simp
  apply standard+
  

lemma (in network)
  shows "\<Turnstile> \<B> p m \<rightarrow> (All q. \<diamondop> (D q m))"
unfolding valid_def
  apply standard+
  

section\<open>Modelling the network\<close>

locale network =
  fixes node_count :: "nat"
*)