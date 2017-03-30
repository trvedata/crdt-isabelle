theory
  ORSet
imports
  Network
begin

datatype ('id, 'a) operation = Add "'id" "'a" | Rem "'id set" "'a"

type_synonym ('id, 'a) state = "'a \<Rightarrow> 'id set"

definition op_elem :: "('id, 'a) operation \<Rightarrow> 'a" where
  "op_elem oper \<equiv> case oper of Add i e \<Rightarrow> e | Rem is e \<Rightarrow> e"

definition interpret_op :: "('id, 'a) operation \<Rightarrow> ('id, 'a) state \<rightharpoonup> ('id, 'a) state" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state \<equiv>
     let before = state (op_elem oper);
         after  = case oper of Add i e \<Rightarrow> before \<union> {i} | Rem is e \<Rightarrow> before - is
     in  Some (state ((op_elem oper) := after))"
    
definition valid_behaviours :: "(('id, 'a) operation \<Rightarrow> 'id) \<Rightarrow> ('id, 'a) state \<Rightarrow> ('id, 'a) operation \<Rightarrow> bool" where
  "valid_behaviours msg_id state oper \<equiv>
     case oper of
       Add i  e \<Rightarrow> i = msg_id oper
     | Rem is e \<Rightarrow> is = state e"
  
locale orset = network_with_constrained_ops msg_id history interpret_op "\<lambda>x. {}" "valid_behaviours msg_id"
  for msg_id :: "('id, 'a) operation \<Rightarrow> 'id" and history :: "nat \<Rightarrow> ('id, 'a) operation event list"

lemma (in orset) add_add_commute:
  shows "\<langle>Add i1 e1\<rangle> \<rhd> \<langle>Add i2 e2\<rangle> = \<langle>Add i2 e2\<rangle> \<rhd> \<langle>Add i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) add_rem_commute:
  assumes "i \<notin> is"
  shows "\<langle>Add i e1\<rangle> \<rhd> \<langle>Rem is e2\<rangle> = \<langle>Rem is e2\<rangle> \<rhd> \<langle>Add i e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)
    
definition (in orset) element_ids :: "('id, 'a) state \<Rightarrow> 'id set" where
  "element_ids f \<equiv> \<Union>i. f i"
  
definition (in orset) indices :: "('id, 'a) operation event list \<Rightarrow> 'id list" where
  "indices es \<equiv> List.map_filter (\<lambda>x. case x of Deliver (Add i e) \<Rightarrow> Some i | _ \<Rightarrow> None) es"
    
lemma (in orset) apply_operations_never_fails:
  assumes "xs prefix of i"
  shows "apply_operations xs \<noteq> None"
  using assms
  apply(induction xs rule: rev_induct)
   apply clarsimp
  apply(case_tac "x"; clarsimp)
   apply force
  using interpret_op_def apply (metis bind.bind_lunit prefix_of_appendD)
  done
    
lemma (in orset) Broadcast_Deliver_prefix_closed:
  assumes "pre@[Broadcast (Rem is e)] prefix of j"
    and "i \<in> is"
  shows "Deliver (Add i e) \<in> set pre"
  sorry
    
lemma (in orset) concurrent_add_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "Add i e \<in> set (node_deliver_messages xs)" and "Rem is e \<in> set (node_deliver_messages xs)"
  shows "hb (Add i e) (Rem is e)"
    using assms
  apply(subgoal_tac "\<exists>pre k. pre@[Broadcast (Rem is e)] prefix of k")
   apply clarsimp
     apply(frule broadcast_only_valid_ops, clarsimp simp add: valid_behaviours_def)
     apply(subgoal_tac "Deliver (Add i e) \<in> set pre")
      apply(rule_tac i=k in hb.intros(2))
    using events_in_local_order apply blast
     apply(rule Broadcast_Deliver_prefix_closed, assumption, assumption)
    using delivery_has_a_cause events_before_exist prefix_msg_in_history apply blast
    done
      
lemma (in orset) Deliver_Add_same_id_same_message:
  assumes "Deliver (Add i e1) \<in> set (history j)" and "Deliver (Add i e2) \<in> set (history j)"
  shows "e1 = e2"
    sorry
      
lemma (in orset) ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "Add i e1 \<in> set (node_deliver_messages xs)" and "Rem is e2 \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
  using assms
      apply(subgoal_tac "\<exists>pre k. pre@[Broadcast (Rem is e2)] prefix of k")
   apply clarsimp
     apply(frule broadcast_only_valid_ops, clarsimp simp add: valid_behaviours_def)
   apply(subgoal_tac "Deliver (Add i e2) \<in> set pre")
    apply(rule_tac j=j and i=i in Deliver_Add_same_id_same_message)
  using prefix_msg_in_history apply blast
  using causal_broadcast events_in_local_order local_order_prefix_closed prefix_contains_msg prefix_to_carriers apply blast
   apply(rule Broadcast_Deliver_prefix_closed, assumption, assumption)
  using delivery_has_a_cause events_before_exist prefix_msg_in_history apply blast
  done

corollary (in orset) concurrent_add_remove_independent:
  assumes "\<not> hb (Add i e1) (Rem is e2)" and "\<not> hb (Rem is e2) (Add i e1)"
    and "xs prefix of j"
    and "Add i e1 \<in> set (node_deliver_messages xs)" and "Rem is e2 \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms ids_imply_messages_same concurrent_add_remove_independent_technical by fastforce

lemma (in orset) rem_rem_commute:
  shows "\<langle>Rem i1 e1\<rangle> \<rhd> \<langle>Rem i2 e2\<rangle> = \<langle>Rem i2 e2\<rangle> \<rhd> \<langle>Rem i1 e1\<rangle>"
  by(unfold interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(case_tac "x"; case_tac "y")
  apply(auto simp add: hb.concurrent_def add_add_commute add_rem_commute rem_rem_commute concurrent_add_remove_independent)
  done
  
theorem (in orset) convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i" and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)
              
context orset begin

sublocale sec: strong_eventual_consistency weak_hb hb interpret_op
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "\<lambda>x.{}"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix node_deliver_messages_distinct concurrent_operations_commute)
   apply (metis (no_types, lifting) interpret_op_def)
    using drop_last_message apply blast
done

end
end

  