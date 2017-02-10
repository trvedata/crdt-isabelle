theory
  Application
imports
  Network
  Ordered_List
begin

definition Insert :: "('id, 'v) elt \<Rightarrow> 'id option \<Rightarrow> ('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt list" where
  "Insert e n \<equiv> (\<lambda>xs. the (insert xs e n))"

definition Delete :: "'id \<Rightarrow> ('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt list" where
  "Delete n \<equiv> (\<lambda>xs. the (delete xs n))"

locale example = finite_event_structure carriers for
  carriers :: "nat \<Rightarrow> ((('id::{linorder}, 'v) elt) list) event list" +
  assumes insert_flag: "(i, Broadcast, Insert e n) \<in> set (carriers i) \<Longrightarrow> snd (snd e) = False"
  assumes allowed_insert: "(i, Broadcast, Insert e n) \<in> set (carriers i) \<Longrightarrow> n = None \<or> 
                            (\<exists>n' n'' v b. n = Some n' \<and> (i, Deliver, Insert (n', v, b) n'') \<sqsubset>\<^sup>i (i, Broadcast, Insert e n))"
  assumes insert_id_unique: "id1 = id2 \<Longrightarrow> (i, Broadcast, Insert (id1, v1, b1) n1) \<in> set (carriers i) \<Longrightarrow> (j, Broadcast, Insert (id2, v2, b2) n2) \<in> set (carriers j) \<Longrightarrow> v1 = v2 \<and> n1 = n2"
  assumes allowed_delete: "(i, Broadcast, Delete x) \<in> set (carriers i) \<Longrightarrow> (\<exists>n' v b. (i, Deliver, Insert (x, v, b) n') \<sqsubset>\<^sup>i (i, Broadcast, Delete x))"
  assumes insert_or_delete: "(j, f, m) \<in> set (carriers j) \<Longrightarrow> (\<exists>x. m = Delete x) \<or> (\<exists>x y. m = Insert x y)"

lemma (in example) allowed_delete_deliver:
  assumes "(i, Deliver, Delete x) \<in> set (carriers i)"
  shows "\<exists>n' v b. (i, Deliver, Insert (x, v, b) n') \<sqsubset>\<^sup>i (i, Deliver, Delete x)"
using assms apply -
  apply(drule delivery_has_a_cause)
  apply clarsimp
  apply(frule no_message_lost[where j=i])
  apply(drule allowed_delete)
  apply clarsimp
  apply(frule local_order_carrier_closed)
  apply clarsimp
  apply(drule delivery_has_a_cause) back
  apply clarsimp
  apply(frule no_message_lost[where j=i]) back
  apply(drule broadcast_causal[rotated, where j=i])
  apply force
  apply force
done
  
lemma (in example) allowed_insert_deliver:
  assumes "(i, Deliver, Insert e n) \<in> set (carriers i)"
  shows   "n = None \<or> (\<exists>n' n'' v b. n = Some n' \<and> (i, Deliver, Insert (n', v, b) n'') \<sqsubset>\<^sup>i (i, Deliver, Insert e n))"
using assms
  apply -
  apply(frule delivery_has_a_cause)
  apply(erule exE)
  apply(cases n; clarsimp)
  apply(frule allowed_insert)
  apply clarsimp
  apply(frule local_order_carrier_closed)
  apply clarsimp
  apply(frule delivery_has_a_cause) back
  apply clarsimp
  apply(frule no_message_lost[where j=i]) back
  apply(drule broadcast_causal[rotated, where j=i])
  apply force
  apply force
done

lemma (in example) 
  assumes "fst e1 = fst e2"
          "(i, Broadcast, Insert e1 n1) \<in> set (carriers i)"
          "(j, Broadcast, Insert e2 n2) \<in> set (carriers j)"
  shows   "Insert e1 n1 = Insert e2 n2"
  using assms
  apply (subgoal_tac "e1 = e2")
  apply (metis surjective_pairing insert_id_unique)
  apply (cases e1, cases e2; clarsimp)
  by (metis insert_flag snd_conv insert_id_unique)


lemma (in example) insert_id_unique_node:
  assumes "fst e1 = fst e2" 
          "(i, Broadcast, Insert e1 n1) \<in> set (carriers i)"
          "(j, Broadcast, Insert e2 n2) \<in> set (carriers j)"
  shows   "i = j"
  using assms broadcasts_unique insert_id_unique
  by (smt insert_flag prod.collapse)


lemma (in example) insert_commute_assms:
  assumes "{(i, Deliver, Insert e n), (i, Deliver, Insert e' n')} \<subseteq> set (carriers i)"
     and  "hb.concurrent (Insert e n) (Insert e' n')"
 shows    "n = None \<or> n \<noteq> Some (fst e')"
using assms
apply (clarsimp simp: hb_def)
apply (case_tac e')
apply clarsimp
apply (frule delivery_has_a_cause)
apply (frule delivery_has_a_cause) back
apply clarsimp
apply (frule allowed_insert)
apply clarsimp
apply (erule_tac x=j in allE) back
apply clarsimp
apply (subgoal_tac "(j, Deliver, Insert (a, v, ba) n'') = (j, Deliver, Insert (a, b, c) n')")
apply clarsimp
using insert_id_unique 
by (smt delivery_has_a_cause example.insert_flag example_axioms insert_subset local_order_carrier_closed prod.sel(2))

lemma (in example)
  assumes "(i, Deliver, Insert e n) \<in> set (carriers i)"
 shows    "n = None \<or> n \<noteq> Some (fst e)"
using assms
apply clarsimp
apply (frule delivery_has_a_cause)
apply clarsimp
apply (frule allowed_insert)
apply clarsimp
apply (drule_tac j=j in broadcast_before_delivery)
apply (drule_tac i=j in global_order_to_local[rotated])
apply clarsimp
apply (meson insert_subset local_order_carrier_closed no_message_lost)
apply (subgoal_tac "(j, Deliver, Insert (fst e, v, b) n'') = (j, Deliver, Insert e (Some (fst e)))")
apply clarsimp
apply (subgoal_tac "(j, Broadcast, Insert e (Some (fst e))) \<sqsubset>\<^sup>j (j, Broadcast, Insert e (Some (fst e)))")
apply (meson insert_subset local_order_carrier_closed node_total_order_irrefl)
apply (rule node_total_order_trans)
apply assumption+
oops


lemma (in example)
  assumes "{(i, Deliver, Insert e n), (i, Deliver, Delete n')} \<subseteq> set (carriers i)"
     and  "hb.concurrent (Insert e n) (Delete n')"
 shows    "n' \<noteq> fst e"
using assms
apply (clarsimp simp: hb_def)
apply (drule delivery_has_a_cause)
apply (drule delivery_has_a_cause)
apply clarsimp
apply (drule allowed_delete)
apply clarsimp
apply (erule_tac x=ja in allE)
apply clarsimp
apply(subgoal_tac "(ja, Broadcast, Insert (fst e, v, b) n'a) = (j, Broadcast, Insert e n)")
apply clarsimp
apply (case_tac e)
apply clarsimp
apply (subgoal_tac "j = ja")
apply clarsimp
apply (smt delivery_has_a_cause example.insert_flag example_axioms insert_id_unique insert_subset local_order_carrier_closed prod.sel(2))
using insert_id_unique_node
by (smt delivery_has_a_cause insert_flag insert_id_unique insert_subset local_order_carrier_closed prod.sel(2))


lemma (in example) insert_no_failure:
  assumes "(i, Deliver, Insert e n) \<in> set (carriers i)"
          "hb.hb_consistent xs"
          "insert XS e n = xs'"
  shows   "\<exists>xs''. xs' = Some xs''"
using assms
oops

lemma prefix_set_mem:
  assumes "xs@ys = zs"
          "x \<in> set ys"
  shows   "x \<in> set zs"
using assms by auto

definition (in example) apply_operations :: "(nat \<times> event_type \<times> (('id \<times> 'v \<times> bool) list \<Rightarrow> ('id \<times> 'v \<times> bool) list)) list \<Rightarrow> ('id \<times> 'v \<times> bool) list" where
  "apply_operations opers \<equiv> (fold (op \<circ>) (ordered_node_operations opers) id) []"

lemma (in finite_event_structure) carriers_head_lt:
  assumes "y#ys = carriers i"
  shows   "\<not>(x \<sqsubset>\<^sup>i y)"
using assms
  apply -
  apply clarsimp
  apply(subst (asm) carriers_compatible[symmetric])
  apply clarsimp
sorry

lemma (in example) apply_operations_singleton:
  assumes "es = apply_operations [oper]"
          "oper#ys = carriers i"
  shows   "\<exists>j e m. oper = (i, e, Insert j m) \<and> (e = Broadcast \<longrightarrow> es = []) \<and> (e = Deliver \<longrightarrow> es = [j])"
using assms
  apply(clarsimp simp add: apply_operations_def ordered_node_operations_def)
  apply(case_tac oper; clarsimp)
  apply(subgoal_tac "a=i")
  apply(case_tac b; clarsimp)
prefer 3
  using carriers_message_consistent apply (metis list.set_intros(1))
  apply(subgoal_tac "(i, Broadcast, c) \<in> set (carriers i)")
  apply(erule disjE[OF insert_or_delete])
  apply clarsimp
  apply(subgoal_tac "(i, Broadcast, Delete x) \<in> set (carriers i)")
  apply(drule allowed_delete)
  apply clarsimp
  using carriers_head_lt apply force
  apply (metis list.set_intros(1))
  apply force
  apply (metis list.set_intros(1))
  apply(subgoal_tac "(i, Deliver, c) \<in> set (carriers i)")
  apply(erule disjE[OF insert_or_delete])
  apply clarsimp
  apply(subgoal_tac "(i, Deliver, Delete x) \<in> set (carriers i)")
  apply(frule delivery_has_a_cause, erule exE)
  apply(drule broadcast_before_delivery[where j=i])
  apply(drule allowed_delete_deliver, clarsimp)
  using carriers_head_lt apply force
  apply (metis list.set_intros(1))
  apply clarsimp
  apply(rule_tac x=a in exI, rule_tac x=aa in exI, rule_tac x=b in exI)
  apply(rule conjI)
  apply force
  apply(subgoal_tac "y=None", clarsimp)
  apply(clarsimp simp add: Insert_def)
  apply(subgoal_tac "(i, Deliver, Insert (a, aa, b) y) \<in> set (carriers i)")
  apply(drule allowed_insert_deliver)
  apply(erule disjE, assumption)
  apply clarsimp
  using carriers_head_lt apply force  
  apply (metis list.set_intros(1))+
done

lemma (in example) apply_operations_singleton_Broadcast:
  shows "apply_operations (xs @ [(i, Broadcast, f)]) = apply_operations xs"
by(clarsimp simp add: apply_operations_def ordered_node_operations_def)

lemma (in example) apply_operations_singleton_Deliver:
  shows "apply_operations (xs @ [(i, Deliver, f)]) = f (apply_operations xs)"
  apply(clarsimp simp add: apply_operations_def ordered_node_operations_def)
done

lemma (in example)
  assumes "\<exists>v b. (m, v, b) \<in> set (apply_operations xs)"
  shows "map fst (Delete m (apply_operations xs)) = map fst (apply_operations xs)"
using assms
  apply(induction xs rule: rev_induct)
  apply(clarsimp simp add: Delete_def apply_operations_def ordered_node_operations_def)
  apply clarsimp
  apply(case_tac aa; clarsimp)
  apply(subst apply_operations_singleton_Broadcast)+
  apply(subst (asm) apply_operations_singleton_Broadcast)
  apply clarsimp apply force
  apply(subst apply_operations_singleton_Deliver)+
  apply(subst (asm) apply_operations_singleton_Deliver)
  apply(unfold Delete_def)
sorry

lemma (in example) deliver_delete_neq_head:
  shows "carriers i \<noteq> (i, Deliver, Delete e)#ys"
  apply clarsimp
  apply(subgoal_tac "(i, Deliver, Delete e) \<in> set (carriers i)")
  apply(drule sym)
  apply(frule delivery_has_a_cause)
  apply clarsimp
  apply(drule allowed_delete)
  apply clarsimp
  apply(frule local_order_carrier_closed)
  apply clarsimp
  apply(drule delivery_has_a_cause) back
  apply clarsimp
  apply(frule no_message_lost[where j=i]) back
  apply(drule broadcast_causal[rotated, where j=i])
  apply force
  using carriers_head_lt apply blast
  apply force
done

lemma (in example)
  assumes "\<exists>ys. xs@(i, Deliver, Delete e)#ys = carriers i"
  shows   "\<exists>v b. (e, v, b) \<in> set (apply_operations xs)"
using assms
  apply -
  apply clarsimp
  apply(induction xs rule: rev_induct)
  apply clarsimp
  using deliver_delete_neq_head apply metis
  apply clarsimp
(*
  apply(drule apply_operations_singleton[rotated], rule refl)  
  apply clarsimp
  using deliver_delete_neq_head
*)

lemma (in example)
  assumes "\<exists>xs ys. xs@(i, Deliver, Insert e p)#ys = carriers i"
          "\<exists>zs. prefix@zs = carriers i"
  shows   "e \<notin> set (apply_operations prefix)"
using assms 
  apply -
  apply clarsimp
  apply(induction prefix rule: rev_induct)
  apply(clarsimp simp add: apply_operations_def ordered_node_operations_def)
  apply clarsimp
  apply(erule_tac x=xsa in meta_allE, erule_tac x="(a,aa,b)#zs" in meta_allE, erule_tac x="ys" in meta_allE)
  apply clarsimp
  apply(case_tac aa; clarsimp)
  apply(clarsimp simp add: apply_operations_singleton_Broadcast)
  apply(clarsimp simp add: apply_operations_singleton_Deliver)
  apply(erule disjE[OF insert_or_delete])

lemma (in example) distinct_ordered_node_operations_prefix:
  assumes "\<exists>ys. prefix@ys = carriers i"
  shows   "distinct (map fst (apply_operations prefix))"
using assms
  apply -
  apply(induction prefix rule: rev_induct)
  apply(clarsimp simp add: ordered_node_operations_def apply_operations_def)+
  apply(case_tac aa; clarsimp)
  apply(subgoal_tac "\<exists>ys. xs @ ys = carriers i", clarsimp)
  apply force
  apply(subgoal_tac "\<exists>ys. xs @ ys = carriers i", clarsimp)

lemma (in example)
  assumes "es = apply_operations prefix"
          "\<exists>ys. prefix@ys = carriers i"
  


  shows   "\<exists>j e m. oper = (i, e, Insert j m) \<and> (e = Broadcast \<longrightarrow> es = []) \<and> (e = Deliver \<longrightarrow> es = [j])"


lemma (in example)
  assumes "hb.concurrent (Insert e n) (Insert e' n')"
          "\<exists>ys. prefix@ys = carriers i \<and> {(i, Deliver, Insert e n), (i, Deliver, Insert e' n')} \<subseteq> set ys"
          "xs = apply_operations prefix"
  shows   "(Insert e n \<circ> Insert e' n') xs = (Insert e' n' \<circ> Insert e n) xs"
using assms
apply (subst Insert_def)+
apply clarsimp
apply (insert insert_commutes[of e e' _ n n'])
apply (erule_tac x=xs in meta_allE)
apply (subgoal_tac "distinct (map fst (e # e' # xs))")
apply (subgoal_tac "n = None \<or> n \<noteq> Some (fst e')")
apply (subgoal_tac "n' = None \<or> n' \<noteq> Some (fst e)")
apply clarsimp
apply (subgoal_tac "\<exists>ys. insert xs e n = Some ys")
apply (subgoal_tac "\<exists>ys'. insert xs e' n' = Some ys'")
apply clarsimp


defer
defer

apply(subgoal_tac "(i, Deliver, Insert e' n') \<in> set (carriers i)")
apply(subgoal_tac "(i, Deliver, Insert e n) \<in> set (carriers i)")
apply (rule insert_commute_assms)
apply clarsimp
apply (rule conjI)
apply assumption+
apply clarsimp
apply(rule prefix_set_mem, assumption, assumption)+

apply(subgoal_tac "(i, Deliver, Insert e' n') \<in> set (carriers i)")
apply(subgoal_tac "(i, Deliver, Insert e n) \<in> set (carriers i)")
apply (rule insert_commute_assms)
apply clarsimp
apply (rule conjI)
apply assumption+
apply clarsimp
apply(rule prefix_set_mem, assumption, assumption)+

apply(rule distinct_ordered_node_operations_prefix[where i="i"])
defer


sorry



end