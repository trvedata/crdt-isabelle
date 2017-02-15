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

corollary (in network_with_ops)
  shows "hb.hb_consistent (node_deliver_messages (carriers i))"
  apply(subgoal_tac "carriers i = [] \<or> (\<exists>c. carriers i = [c]) \<or> (length (carriers i) \<ge> 2)")
  apply(erule disjE, clarsimp simp add: node_deliver_messages_def)
  apply(erule disjE, clarsimp simp add: node_deliver_messages_def)
  apply(case_tac aa; clarsimp)
defer
  apply(cases "carriers i"; clarsimp; case_tac "list"; clarsimp)
  apply(rule hb_consistent_technical[where i=i])
  apply(subst carriers_compatible)
  apply (rule horror_size3, simp+)
done

end