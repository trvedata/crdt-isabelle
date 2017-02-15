theory
  RGA
imports
  Causal_CRDT
  Ordered_List
begin

datatype ('id, 'v) operation =
  Insert "('id, 'v) elt" "'id option" |
  Delete "'id"

fun interpret_opers :: "('id::linorder, 'v) operation \<Rightarrow> ('id, 'v) elt list \<Rightarrow> ('id, 'v) elt list" ("\<langle>_\<rangle>" [100] 100) where
  "interpret_opers (Insert e n) = (\<lambda>xs. the (insert xs e n))" |
  "interpret_opers (Delete n)   = (\<lambda>xs. the (delete xs n))"

(* Replicated Growable Array Network *)
locale rga = network_with_ops _ _ _ interpret_opers +
  assumes insert_flag: "(i, Broadcast, Insert e n) \<in> set (carriers i) \<Longrightarrow> snd (snd e) = False"
  assumes allowed_insert: "(i, Broadcast, Insert e n) \<in> set (carriers i) \<Longrightarrow> n = None \<or> 
                            (\<exists>n' n'' v b. n = Some n' \<and> (i, Deliver, Insert (n', v, b) n'') \<sqsubset>\<^sup>i (i, Broadcast, Insert e n))"
  assumes insert_id_unique: "id1 = id2 \<Longrightarrow> (i, Broadcast, Insert (id1, v1, b1) n1) \<in> set (carriers i) \<Longrightarrow> (j, Broadcast, Insert (id2, v2, b2) n2) \<in> set (carriers j) \<Longrightarrow> v1 = v2 \<and> n1 = n2"
  assumes allowed_delete: "(i, Broadcast, Delete x) \<in> set (carriers i) \<Longrightarrow> (\<exists>n' v b. (i, Deliver, Insert (x, v, b) n') \<sqsubset>\<^sup>i (i, Broadcast, Delete x))"

lemma (in rga) allowed_delete_deliver:
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

lemma (in rga) allowed_delete_deliver_in_set:
  assumes "(es@[(i, Deliver, Delete m)]) prefix of i"
  shows   "\<exists>n v b. (i, Deliver, Insert (m, v, b) n) \<in> set es"
using assms
  apply -
  apply(frule_tac x="(i, Deliver, Delete m)" in prefix_to_carriers)
  apply force
  apply(frule allowed_delete_deliver)
  apply clarsimp
  apply(drule local_order_prefix_closed_last, assumption)
  apply force
done

lemma (in rga) allowed_insert_deliver:
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

lemma (in rga) allowed_insert_deliver_in_set:
  assumes "(es@[(i, Deliver, Insert e m)]) prefix of i"
  shows   "m = None \<or> (\<exists>m' n v b. m = Some m' \<and> (i, Deliver, Insert (m', v, b) n) \<in> set es)"
using assms
  apply -
  apply(frule_tac x="(i, Deliver, Insert e m)" in prefix_to_carriers)
  apply force
  apply(frule allowed_insert_deliver)
  apply(erule disjE)
  apply force
  apply clarsimp
  apply(drule local_order_prefix_closed_last, assumption)
  apply force
done

lemma (in rga) allowed_insert_Some_deliver:
  assumes "(es@[(i, Deliver, Insert e (Some m))]) prefix of i"
  shows   "\<exists>n v b. (i, Deliver, Insert (m, v, b) n) \<in> set es"
  using assms allowed_insert_deliver_in_set[where es=es and i=i and e=e and m="Some m"] by force

lemma (in rga) delete_is_not_first_msg:
  shows "\<not> ([(i, Deliver, Delete n)] prefix of i)"
  apply (clarsimp simp: prefix_of_carrier_def)
  apply(subgoal_tac "(i, Deliver, Delete n) \<in> set (carriers i)")
  apply(drule allowed_delete_deliver)
  apply clarsimp
  using carriers_head_lt apply force
  apply (metis list.set_intros(1))
done

lemma (in rga) insert_Some_is_not_first_msg:
  shows "\<not> ([(i, Deliver, Insert e (Some n))] prefix of i)"
  by (clarsimp, insert allowed_insert_deliver_in_set[where es="[]" and i=i and e=e and m="Some n"], force)

definition (in rga) apply_operations :: "('a, 'b) operation event list \<Rightarrow> ('a, 'b) elt list" where
  "apply_operations es \<equiv> (fold (op \<circ>) (map interpret_opers (node_deliver_messages es)) id) []"

lemma (in rga) apply_operations_empty[simp]: "apply_operations [] = []"
  by (auto simp: apply_operations_def)

lemma (in rga) apply_operations_Broadcast [simp]: "apply_operations (xs @ [(i, Broadcast, m)]) = apply_operations xs"
  by (auto simp: apply_operations_def node_deliver_messages_def)

lemma (in rga) apply_operations_Deliver [simp]: "apply_operations (xs @ [(i, Deliver, m)]) = interpret_opers m (apply_operations xs)"
  by (auto simp: apply_operations_def node_deliver_messages_def)

definition filter_deliver_inserts :: "_" where
  "filter_deliver_inserts \<equiv> List.filter (\<lambda>e. case e of (_, Deliver, Insert _ _) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma [simp]: "filter_deliver_inserts [] = []"
  by (auto simp: filter_deliver_inserts_def)

lemma [simp]: "filter_deliver_inserts (xs@ys) = (filter_deliver_inserts xs) @ (filter_deliver_inserts ys)"
  by (auto simp: filter_deliver_inserts_def)

lemma [simp]: "filter_deliver_inserts [(a, Broadcast, b)] = []"
  by (auto simp: filter_deliver_inserts_def)

definition index_elem_inserted :: "_" where
  "index_elem_inserted \<equiv> map (\<lambda>e. case e of (_, Deliver, Insert (n, _, _) _) \<Rightarrow> n)"

lemma [simp]: "index_elem_inserted [] = []"
  by (auto simp: index_elem_inserted_def)

lemma [simp]: "index_elem_inserted (xs@ys) = (index_elem_inserted xs) @ (index_elem_inserted ys)"
  by (auto simp: index_elem_inserted_def)

lemma [simp]: "index_elem_inserted (filter_deliver_inserts [(i, Deliver, Insert (a, b, c) n)]) = [a]"
  by (auto simp: index_elem_inserted_def filter_deliver_inserts_def)

lemma [simp]: "index_elem_inserted (filter_deliver_inserts [(i, Deliver, Delete n)]) = []"
  by (auto simp: index_elem_inserted_def filter_deliver_inserts_def)

lemma (in rga) idx_in_elem_inserted [intro]: "(i, Deliver, Insert (m, v, b) n) \<in> set xs \<Longrightarrow> m \<in> set (index_elem_inserted (filter_deliver_inserts xs))"
  by (induct xs) (auto simp: index_elem_inserted_def filter_deliver_inserts_def)

lemma (in rga) apply_opers_idx_elems:
  assumes "es prefix of i"
  shows   "fst ` set (apply_operations es) = set (index_elem_inserted (filter_deliver_inserts es))"
using assms apply (induct es rule: rev_induct)
apply clarsimp
apply clarsimp
apply (case_tac aa)
apply force
apply clarsimp
apply (case_tac b)
apply clarsimp
apply (subgoal_tac "a=i")
apply clarsimp
apply (frule allowed_insert_deliver_in_set)
apply (erule disjE)
apply clarsimp
apply force
apply clarsimp
apply (subgoal_tac "\<exists>ys. insert (apply_operations xs) (aa, ab, ba) (Some m') = Some ys")
prefer 2
apply (rule insert_no_failure)
apply clarsimp
apply (subgoal_tac "m' \<in> set (index_elem_inserted (filter_deliver_inserts xs))")
prefer 2
apply force
apply force
apply (frule insert_preserve_element)
apply clarsimp
apply force
apply (rule prefix_consistent)
apply assumption
apply force
apply clarsimp
apply (subgoal_tac "a=i")
apply clarsimp
apply (frule allowed_delete_deliver_in_set)
apply clarsimp
apply (subgoal_tac "\<exists>ys. delete (apply_operations xs) x2 = Some ys")
apply clarsimp
apply (frule delete_element_preserve)
apply clarsimp
apply (subgoal_tac "xs prefix of i")
apply force
apply force
apply (rule delete_no_failure)
apply force
apply (rule prefix_consistent)
apply assumption
apply force
done

lemma (in rga) insert_in_apply_set:
  assumes "es @ [(i, Deliver, Insert e (Some a))] prefix of i"
          "(i, Deliver, Insert (a, v, b) n) \<in> set es"
  shows   "\<exists>v b. (a, v, b) \<in> set (apply_operations es)"
using assms
apply (case_tac e)
apply clarsimp
apply (drule idx_in_elem_inserted)
apply (subst (asm) apply_opers_idx_elems[symmetric])
apply force
apply force
done

lemma (in rga) Insert_no_failure:
  assumes "es @ [(i, Deliver, Insert e n)] prefix of i"
  shows "\<exists>ys. insert (apply_operations es) e n = Some ys"
  using assms apply -
  apply (frule allowed_insert_deliver_in_set)
  apply (case_tac n)
  apply clarsimp
  apply clarsimp
  apply (rule insert_no_failure)
  apply clarsimp
  using insert_in_apply_set apply metis
done

lemma (in rga) delete_no_failure:
  assumes "es @ [(i, Deliver, Delete n)] prefix of i"
  shows   "\<exists>ys. delete (apply_operations es) n = Some ys"
  using assms apply -
  apply (frule allowed_delete_deliver_in_set)
  apply clarsimp
  apply (rule delete_no_failure)
  apply (drule idx_in_elem_inserted)
  apply (subst (asm) apply_opers_idx_elems[symmetric])
  apply force
  apply force
done

lemma (in rga) 
  assumes "fst e1 = fst e2"
          "(i, Broadcast, Insert e1 n1) \<in> set (carriers i)"
          "(j, Broadcast, Insert e2 n2) \<in> set (carriers j)"
  shows   "Insert e1 n1 = Insert e2 n2"
  using assms
  apply (subgoal_tac "e1 = e2")
  apply (metis surjective_pairing insert_id_unique)
  apply (cases e1, cases e2; clarsimp)
  by (metis insert_flag snd_conv insert_id_unique)

lemma (in rga) insert_id_unique_node:
  assumes "fst e1 = fst e2" 
          "(i, Broadcast, Insert e1 n1) \<in> set (carriers i)"
          "(j, Broadcast, Insert e2 n2) \<in> set (carriers j)"
  shows   "i = j"
  using assms broadcasts_unique insert_id_unique
  by (smt insert_flag prod.collapse)

lemma (in rga) insert_commute_assms:
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
by (smt delivery_has_a_cause rga.insert_flag rga_axioms insert_subset local_order_carrier_closed prod.sel(2))

lemma (in rga)
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
apply (smt delivery_has_a_cause rga.insert_flag rga_axioms insert_id_unique insert_subset local_order_carrier_closed prod.sel(2))
using insert_id_unique_node
by (smt delivery_has_a_cause insert_flag insert_id_unique insert_subset local_order_carrier_closed prod.sel(2))

lemma (in rga) node_deliver_messages_distinct:
  assumes "xs prefix of i"
  shows "distinct (node_deliver_messages xs)"
using assms
  apply (induct xs rule: rev_induct)
  apply simp
  apply (clarsimp simp add: node_deliver_messages_append)
  apply safe
  apply force
  apply (clarsimp simp: node_deliver_messages_def)
  apply clarsimp
  apply (frule prefix_distinct)
  apply clarsimp
  apply (subst (asm) node_deliver_messages_def) back back back
  apply clarsimp
  apply (case_tac aa; clarsimp)
  apply (subst (asm) node_deliver_messages_def) back
  apply clarsimp
  apply (case_tac ab; clarsimp)
  apply (subgoal_tac "a=i")
  apply (subgoal_tac "aa=i")
  apply clarsimp
  apply (rule_tac b=Deliver and c=ba in prefix_consistent)
  apply assumption
  apply force
  apply (rule_tac b=Deliver and c=ba in prefix_consistent)
  apply assumption
  apply force
done

lemma (in rga) deliver_delete_neq_head:
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

lemma (in rga)
  assumes "es prefix of i"
  shows  "distinct (map fst (apply_operations es))"
  apply(induction es rule: rev_induct)
sorry

lemma (in rga) Insert_Insert_commute:
  assumes "es prefix of i"
          "{Insert e n, Insert e' n'} \<subseteq> set (node_deliver_messages es)"
          "hb.concurrent (Insert e n) (Insert e' n')"
  shows   "\<langle>Insert e n\<rangle> \<circ> \<langle>Insert e' n'\<rangle> = \<langle>Insert e' n'\<rangle> \<circ> \<langle>Insert e n\<rangle>"
using assms
apply clarsimp
apply (rule ext)
apply clarsimp
apply (insert insert_commutes[of e e' _ n n'])
apply (erule_tac x=x in meta_allE)
apply (subgoal_tac "distinct (map fst (e # e' # x))")
apply (subgoal_tac "n = None \<or> n \<noteq> Some (fst e')")
apply (subgoal_tac "n' = None \<or> n' \<noteq> Some (fst e)")
apply clarsimp
apply (subgoal_tac "\<exists>ys. insert x e n = Some ys")
apply (subgoal_tac "\<exists>ys'. insert x e' n' = Some ys'")
apply clarsimp
defer
defer
apply(subgoal_tac "(i, Deliver, Insert e' n') \<in> set (carriers i)")
apply(subgoal_tac "(i, Deliver, Insert e n) \<in> set (carriers i)")
apply (rule insert_commute_assms)
apply clarsimp
apply (rule conjI)
apply assumption
apply assumption
apply clarsimp
apply simp
apply (rule prefix_msg_in_carrier)
apply assumption
apply simp
apply (rule prefix_msg_in_carrier)
apply assumption
apply simp

apply(subgoal_tac "(i, Deliver, Insert e' n') \<in> set (carriers i)")
apply(subgoal_tac "(i, Deliver, Insert e n) \<in> set (carriers i)")
apply (rule insert_commute_assms)
apply clarsimp
apply (rule conjI)
apply assumption+
apply clarsimp
apply simp
apply (rule prefix_msg_in_carrier)
apply assumption
apply simp
apply (rule prefix_msg_in_carrier)
apply assumption
apply simp

defer
apply (rule Insert_no_failure)
oops

corollary (in rga) hb_consistent_prefix:
  assumes "xs prefix of i"
  shows   "hb.hb_consistent (node_deliver_messages xs)"
using assms
apply (clarsimp simp: prefix_of_carrier_def)
apply (rule_tac i=i in hb_consistent_technical)
apply (subst carriers_compatible)
apply(subgoal_tac "xs = [] \<or> (\<exists>c. xs = [c]) \<or> (length (xs) > 1)")
apply (erule disjE)
apply clarsimp
apply (erule disjE)
apply clarsimp
apply (drule horror_size3)
apply assumption
apply clarsimp
apply clarsimp
apply (rule_tac x=xsa in exI)
apply (rule_tac x=ysa in exI)
apply (rule_tac x="zs@ys" in exI)
apply (metis Cons_eq_appendI append_assoc)
apply force
done

lemma (in rga) Delete_Delete_commute:
  shows "Delete xa \<circ> Delete xb = Delete xb \<circ> Delete xa"
oops

lemma (in rga) Delete_Insert_commute:
  shows "Delete xa \<circ> Insert x ya = Insert x ya \<circ> Delete xa"
oops

lemma (in rga) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_elems_commute (node_deliver_messages xs)"
using assms
  apply (auto simp: hb.concurrent_elems_commute_def)
  apply (frule_tac i=i in prefix_opers_option[rotated])
  apply clarsimp
  apply (frule_tac i=i in prefix_opers_option[rotated]) back
  apply clarsimp
  apply safe
  using Delete_Delete_commute apply blast
  using Delete_Insert_commute apply blast
  using Delete_Insert_commute[symmetric] apply blast
  using Insert_Insert_commute apply blast
done

lemma (in rga)
  assumes "distinct (map fst xs)"
  shows   "distinct (map fst ((Delete n) xs)) \<or> xs = []"
using assms
apply -
apply (induct xs)
apply simp
apply clarsimp
apply (erule disjE)
defer
apply clarsimp



apply (clarsimp simp: Delete_def)
oops

corollary (in rga) main_result_of_paper:
  assumes "set (ordered_node_operations xs) = set (ordered_node_operations ys)"
          "xs prefix of i"
          "ys prefix of j"
  shows  "apply_operations xs = apply_operations ys"
using assms by (auto simp: apply_operations_def intro: hb.convergence_point concurrent_operations_commute ordered_node_operations_distinct hb_consistent_prefix)

end