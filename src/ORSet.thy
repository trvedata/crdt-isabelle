theory
  ORSet
imports
  Network
begin
  
fun opt_default :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "opt_default (Some x) _ = x" |
  "opt_default  None    x = x"

datatype 'a operation = Add 'a | Rem 'a

type_synonym 'a state = "'a \<rightharpoonup> 'a operation set"

locale orset_base = network_with_ops msg_id history interp "Map.empty"
  for msg_id :: "'a operation \<Rightarrow> 'a" and history :: "nat \<Rightarrow> 'a operation event list"
    and interp :: "'a operation \<Rightarrow> 'a state \<rightharpoonup> 'a state"

definition op_elem where
  "op_elem oper \<equiv> case oper of Add e \<Rightarrow> e | Rem e \<Rightarrow> e"

definition (in orset_base) interpret_op :: "'a operation \<Rightarrow> 'a state \<rightharpoonup> 'a state" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state \<equiv>
     let before = opt_default (state (op_elem oper)) {};
         after  = case oper of Add e \<Rightarrow> before \<union> {oper} | Rem e \<Rightarrow> {add \<in> before. \<not> hb add oper}
     in  Some (state ((op_elem oper) \<mapsto> after))"

locale orset = orset_base _ _ "orset_base.interpret_op history"

lemma (in orset) add_add_commute:
  shows "\<langle>Add e1\<rangle> \<rhd> \<langle>Add e2\<rangle> = \<langle>Add e2\<rangle> \<rhd> \<langle>Add e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) add_rem_commute:
  assumes "\<not> hb (Add e1) (Rem e2) \<and> \<not> hb (Rem e2) (Add e1)"
  shows "\<langle>Add e1\<rangle> \<rhd> \<langle>Rem e2\<rangle> = \<langle>Rem e2\<rangle> \<rhd> \<langle>Add e1\<rangle>"
  using assms by(cases "e1 = e2"; fastforce simp add: interpret_op_def op_elem_def kleisli_def)

lemma (in orset) rem_rem_commute:
  shows "\<langle>Rem e1\<rangle> \<rhd> \<langle>Rem e2\<rangle> = \<langle>Rem e2\<rangle> \<rhd> \<langle>Rem e1\<rangle>"
  by(unfold interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(case_tac "x"; case_tac "y")
  apply(auto simp add: hb.concurrent_def add_add_commute add_rem_commute rem_rem_commute)
done

theorem (in orset) convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i" and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context orset begin

sublocale sec: strong_eventual_consistency weak_hb hb interpret_op
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "Map.empty"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix node_deliver_messages_distinct concurrent_operations_commute)
   apply (metis (no_types, lifting) interpret_op_def)
    using drop_last_message apply blast
done

end
end
