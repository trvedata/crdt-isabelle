theory
  Application
imports
  Network
  Ordered_list
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

lemma (in example) insert_id_unique_node:
  assumes "id1 = id2" 
          "(i, Broadcast, Insert (id1, v1, b1) n1) \<in> set (carriers i)"
          "(j, Broadcast, Insert (id2, v2, b2) n2) \<in> set (carriers j)"
  shows   "i = j"
  using assms broadcasts_unique insert_id_unique
  by (smt insert_flag snd_conv)

lemma insert_id_unique_deliver:
  "id1 = id2 \<Longrightarrow> (i, Deliver, Insert (id1, v1, b1) n1) \<in> set (carriers i) \<Longrightarrow> (j, Deliver, Insert (id2, v2, b2) n2) \<in> set (carriers j) \<Longrightarrow> v1 = v2 \<and> n1 = n2"
  sorry

lemma (in example)
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
using insert_id_unique_deliver oops


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
          "hb.hb_consistent XS"
          "insert xs e n = xs'"
  shows   "\<exists>xs''. xs' = Some xs''"


lemma (in example) insert_no_failure:
  assumes "(i, Deliver, Insert e n) \<in> set (carriers i)"
          "insert xs e n = xs'"
  shows   "\<exists>xs''. xs' = Some xs''"

lemma (in example) insert_no_failure:
  assumes "(i, Deliver, Insert e n) \<in> set (carriers i)"
  shows   "n = None \<or> (\<exists>n'. n = Some n' \<and> (\<exists>n'' v b. (i, Deliver, Insert (n', v, b) n'') \<in> set (carriers i)))"
using assms apply clarsimp
apply (cases n)
apply clarsimp
apply clarsimp
apply (drule delivery_has_a_cause)
apply clarsimp
apply (drule allowed_insert)
apply auto
thm 


lemma (in example)
  assumes "{(i, Deliver, Insert e n)} \<subseteq> set (carriers i)"
          "hb.concurrent (Insert e n) (Insert e' n')"
  shows   "Insert e n \<circ> Insert e' n' = Insert e' n' \<circ> Insert e n"


end