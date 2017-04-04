theory
  Counter
imports
  Network
begin

definition increment :: "int \<Rightarrow> int" where
  "increment x \<equiv> 1 + x"
  
definition decrement :: "int \<Rightarrow> int" where
  "decrement x \<equiv> x - 1"
  
lemma increment_decrement_commute:
  shows "increment (decrement x) = decrement (increment x)"
  by(simp add: decrement_def increment_def)
    
datatype 'id operation = Increment "'id" | Decrement "'id"
    
fun interpret_operation :: "'id operation \<Rightarrow> int \<rightharpoonup> int" where
  "interpret_operation (Increment _) = Some o increment" |
  "interpret_operation (Decrement _) = Some o decrement"
  
definition msg_id :: "'id operation \<Rightarrow> 'id" where
  "msg_id oper \<equiv> case oper of Increment i \<Rightarrow> i | Decrement i \<Rightarrow> i"
    
locale counter = network_with_ops msg_id _ interpret_operation 0
  
lemma (in counter) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(case_tac "x"; case_tac "y")
   apply(auto simp add: kleisli_def increment_decrement_commute)
done
  
corollary (in counter) counter_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context counter begin

sublocale sec: strong_eventual_consistency weak_hb hb interpret_operation
  "\<lambda>ops. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" 0
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix drop_last_message node_deliver_messages_distinct concurrent_operations_commute)
    apply(metis (mono_tags, lifting) interpret_operation.elims o_apply)
  using drop_last_message apply blast
done

end
end