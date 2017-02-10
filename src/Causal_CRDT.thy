theory
  Causal_CRDT
imports
  Network
  Ordered_List
  Convergence
begin

lemma filter_empty:
  shows "Set.filter p {} = {}"
by auto

lemma set_filter_Un:
  shows "Set.filter p (xs \<union> ys) = Set.filter p xs \<union> Set.filter p ys"
by auto

corollary set_filter_insert:
  shows "Set.filter p (Set.insert x xs) = (if p x then Set.insert x (Set.filter p xs) else Set.filter p xs)"
using set_filter_Un by(auto split: split_if)

lemma finite_filter:
  assumes "finite A"
  shows   "finite (Set.filter p A)"
using assms
  apply(induction rule: finite.induct)
  apply(auto simp add: filter_empty)
  apply(simp add: set_filter_insert)
done

lemma set_filter_pred:
  assumes "x \<in> Set.filter p xs"
  shows   "p x"
using assms by simp

lemma list_filter_pred:
  assumes "x \<in> set (List.filter p xs)"
  shows   "p x"
using assms by simp

lemma set_elem_nth:
  assumes "x \<in> set xs"
  shows   "\<exists>m. m < length xs \<and> xs ! m = x"
using assms
  apply(induction xs, auto)
  apply(rule_tac x="m+1" in exI)
  apply auto
done

(*
lemma (in finite_event_structure) hb_consistent_lt_hb:
  assumes "hb.hb_consistent cs"
          "i < j" "j < length cs"
  shows   "hb (cs ! i) (cs ! j) \<or> \<not> hb (cs ! j) (cs ! i)"
using assms
  apply(induction rule: hb.hb_consistent.induct)
  apply force
  apply(subgoal_tac "j < length xs \<or> j = length xs")
  apply(erule disjE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)+
  apply clarsimp
prefer 2
  apply force
  apply(clarsimp simp add: hb_def)
  apply(subst (asm) nth_append, simp)+
done
*)

lemma (in finite_event_structure) hb_consistent_technical:
  assumes "\<And>m n. m < length cs \<Longrightarrow> n < m \<Longrightarrow> cs ! n \<sqsubset>\<^sup>i cs ! m"
  shows   "hb.hb_consistent (ordered_node_operations cs)"
using assms
  apply -
  apply(induction cs rule: rev_induct)
  apply(unfold ordered_node_operations_def)
  apply force
  apply clarsimp
  apply(case_tac aa; clarsimp)
defer
  apply(rule hb.hb_consistent.intros)
prefer 2
  apply clarsimp
  apply(case_tac "ab"; clarsimp)
  apply(unfold hb_def)
  apply clarsimp
  apply(erule disjE)
  apply(subgoal_tac "(i, Deliver, ba) \<sqsubset>\<^sup>i (i, Deliver, b)")
  apply(frule local_order_carrier_closed) back
  apply(drule delivery_fifo_order[rotated], force)
  using node_total_order_irrefl node_total_order_trans apply (meson insert_subset)
defer
  apply(subgoal_tac "(i, Deliver, ba) \<sqsubset>\<^sup>i (i, Deliver, b)")
  apply(erule_tac x=i in allE)
  apply(frule local_order_carrier_closed) back
  apply(drule broadcast_causal[rotated], force)
  using node_total_order_irrefl node_total_order_trans apply (meson insert_subset)
  apply(drule set_elem_nth)
  apply(erule exE, erule conjE)
  apply(erule_tac x="length xs" in meta_allE)
  apply(erule_tac x="m" in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)
  apply(frule local_order_carrier_closed) back
  apply clarsimp
  apply(drule carriers_message_consistent)+
  apply clarsimp
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(erule_tac x=m in meta_allE)
  apply(erule_tac x=n in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)+
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(erule_tac x=m in meta_allE)
  apply(erule_tac x=n in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)+
  apply(drule set_elem_nth)
  apply(erule exE, erule conjE)
  apply(erule_tac x="length xs" in meta_allE)
  apply(erule_tac x="m" in meta_allE)
  apply clarsimp
  apply(frule local_order_carrier_closed) back
  apply clarsimp
  apply(drule carriers_message_consistent)+
  apply clarsimp
done

lemma horror_size2:
  assumes "m < length cs"
          "length cs > 0"
  shows   "\<exists>xs ys. cs = xs@(cs!m)#ys"
using assms
apply (induct m arbitrary: cs)
apply clarsimp
apply (rule_tac x="[]" in exI)
apply (rule_tac x="tl cs" in exI)
apply clarsimp
apply (case_tac cs)
apply force
apply force
apply clarsimp
apply (case_tac cs)
apply clarsimp
apply clarsimp
apply (case_tac "list = []")
apply clarsimp
apply (erule_tac x=list in meta_allE)
apply clarsimp
apply (rule_tac x="a#xs" in exI)
apply (rule_tac x="ys" in exI)
apply clarsimp
done

lemma horror_size3:
  assumes "m < length cs"
          "n < m"
          "length cs > 1"
  shows   "\<exists>xs ys zs. xs@(cs!n)#ys@(cs!m)#zs=cs"
using assms
apply (induct n arbitrary: cs m)
apply clarsimp
apply (rule_tac x="[]" in exI)
apply clarsimp
apply (insert horror_size2)
apply (erule_tac x="m-1" in meta_allE)
apply (erule_tac x="tl cs" in meta_allE)
apply clarsimp
apply (subgoal_tac "m - Suc 0 < length cs - Suc 0")
apply clarsimp
apply (rule_tac x=xs in exI)
apply (rule_tac x=ys in exI)
apply (subgoal_tac "cs ! m = tl cs ! (m - Suc 0)")
apply clarsimp
apply (metis gr_implies_not0 length_0_conv list.collapse nth_Cons_0)
apply (metis One_nat_def Suc_pred length_tl nth_tl)
using Suc_leI diff_less_mono apply blast
apply clarsimp
apply (thin_tac "(\<And>m cs. m < length cs \<Longrightarrow> cs \<noteq> [] \<Longrightarrow> \<exists>xs ys. cs = xs @ cs ! m # ys)")
apply (case_tac cs)
apply clarsimp
apply clarsimp
apply (case_tac "list = []")
apply clarsimp
apply (erule_tac x=list in meta_allE)
apply (erule_tac x="m-1" in meta_allE)
apply clarsimp
apply (subgoal_tac "m - Suc 0 < length list")
defer
apply linarith
apply clarsimp
apply (subgoal_tac "n < m - Suc 0")
defer
apply linarith
apply clarsimp
apply (rule_tac x="a#xs" in exI)
apply clarsimp
apply force
done

corollary (in finite_event_structure)
  shows "hb.hb_consistent (ordered_node_operations (carriers i))"
  apply(subgoal_tac "carriers i = [] \<or> (\<exists>c. carriers i = [c]) \<or> (length (carriers i) \<ge> 2)")
  apply(erule disjE, clarsimp simp add: ordered_node_operations_def)
  apply(erule disjE, clarsimp simp add: ordered_node_operations_def)
  apply(case_tac aa; clarsimp)
defer
  apply(cases "carriers i"; clarsimp; case_tac "list"; clarsimp)
  apply(rule hb_consistent_technical[where i=i])
  apply(subst carriers_compatible)
  apply (rule horror_size3, simp+)
done

end