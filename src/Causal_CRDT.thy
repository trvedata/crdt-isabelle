theory
  Causal_CRDT
imports
  Network
begin

lemma (in network_with_ops) hb_consistent_technical:
  assumes "\<And>m n. m < length cs \<Longrightarrow> n < m \<Longrightarrow> cs ! n \<sqsubset>\<^sup>i cs ! m"
  shows   "hb.hb_consistent (node_deliver_messages cs)"
using assms
  apply -
  apply(induction cs rule: rev_induct)
  apply(unfold node_deliver_messages_def)
  apply(simp add: hb.hb_consistent.intros(1) map_filter_simps(2))
  apply(case_tac x; clarify)
  apply(simp add: List.map_filter_def)
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(smt Suc_less_eq less_SucI less_trans_Suc nth_append)
  apply(subst map_filter_append)
  apply(clarsimp simp add: map_filter_def)
  apply(rule hb.hb_consistent.intros)
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(smt Suc_less_eq less_SucI less_trans_Suc nth_append)
  apply clarsimp
  apply(case_tac x; clarsimp)
  apply(drule set_elem_nth, erule exE, erule conjE)
  apply(erule_tac x="length xs" in meta_allE, erule_tac x=m in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)
  apply(meson causal_network.causal_delivery causal_network_axioms insert_subset node_histories.local_order_carrier_closed node_histories_axioms node_total_order_irrefl node_total_order_trans)
done

corollary (in network_with_ops)
  shows "hb.hb_consistent (node_deliver_messages (history i))"
  apply(subgoal_tac "history i = [] \<or> (\<exists>c. history i = [c]) \<or> (length (history i) \<ge> 2)")
  apply(erule disjE, clarsimp simp add: node_deliver_messages_def map_filter_def)
  apply(erule disjE, clarsimp simp add: node_deliver_messages_def map_filter_def)
  apply blast
  apply(cases "history i"; clarsimp; case_tac "list"; clarsimp)
  apply(rule hb_consistent_technical[where i=i])                                         
  apply(subst history_order_def, clarsimp)
  apply(metis list_nth_split One_nat_def Suc_le_mono cancel_comm_monoid_add_class.diff_cancel
          le_imp_less_Suc length_Cons less_Suc_eq_le less_imp_diff_less nat.simps neq0_conv nth_Cons_pos)
  apply(cases "history i"; clarsimp; case_tac "list"; clarsimp)
done

end