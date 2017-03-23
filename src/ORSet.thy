theory
  ORSet
imports
  Network
begin

fun opt_default :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" (infix "default to" 50) where
  "opt_default (Some x) _ = x" |
  "opt_default  None    x = x"

datatype 'elem operation
  = Add 'elem
  | Rem 'elem

type_synonym 'elem state = "'elem \<rightharpoonup> 'elem operation set"

locale orset_base = network_with_ops msg_id history interp "Map.empty"
  for msg_id :: "'elem operation \<Rightarrow> 'a"
  and history :: "nat \<Rightarrow> 'elem operation event list"
  and interp :: "'elem operation \<Rightarrow> 'elem state \<rightharpoonup> 'elem state"

definition op_elem where
  "op_elem oper \<equiv> case oper of Add e \<Rightarrow> e | Rem e \<Rightarrow> e"

definition (in orset_base) interpret_op :: "'elem operation \<Rightarrow> 'elem state \<rightharpoonup> 'elem state" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state = (
    let before = (state (op_elem oper)) default to {} in
    let after = case oper of
      Add e \<Rightarrow> before \<union> {oper} |
      Rem e \<Rightarrow> {add \<in> before. \<not> hb add oper}
    in Some (state ((op_elem oper) \<mapsto> after)))"

locale orset = orset_base _ _ "orset_base.interpret_op history"

lemma (in orset) apply_operations_empty [simp]:
  shows "apply_operations [] = Some Map.empty"
by auto

lemma map_assign_commute:
  assumes "k1 \<noteq> k2"
  shows "(\<lambda>x. Some (x(k1 \<mapsto> f (x k1 default to {}), k2 \<mapsto> g (x k2 default to {})))) =
         (\<lambda>x. Some (x(k2 \<mapsto> g (x k2 default to {}), k1 \<mapsto> f (x k1 default to {}))))"
  using assms apply -
  apply(subgoal_tac "\<And>x y. x = y \<Longrightarrow>
         x(k1 \<mapsto> f (x k1 default to {}), k2 \<mapsto> g (x k2 default to {})) =
         y(k2 \<mapsto> g (y k2 default to {}), k1 \<mapsto> f (y k1 default to {}))")
  apply auto
done

lemma (in orset) add_add_commute:
  shows "\<langle>Add e1\<rangle> \<rhd> \<langle>Add e2\<rangle> = \<langle>Add e2\<rangle> \<rhd> \<langle>Add e1\<rangle>"
  apply(unfold interpret_op_def op_elem_def kleisli_def)
  apply(clarsimp)
  apply(case_tac "e1=e2", simp)
  apply(auto split: if_split_asm)
  using map_assign_commute apply fastforce
done

lemma (in orset) add_rem_commute:
  assumes "\<not> hb (Add e1) (Rem e2) \<and> \<not> hb (Rem e2) (Add e1)"
  shows "\<langle>Add e1\<rangle> \<rhd> \<langle>Rem e2\<rangle> = \<langle>Rem e2\<rangle> \<rhd> \<langle>Add e1\<rangle>"
  using assms apply(unfold interpret_op_def op_elem_def kleisli_def)
  apply(clarsimp)
  apply(case_tac "e1=e2", simp)
  apply(subgoal_tac "\<And>x y. x = y \<Longrightarrow>
    x(e2 \<mapsto> {add. (add = Add e2 \<or> add \<in> (x e2 default to {})) \<and> \<not> hb add (Rem e2)}) =
    y(e2 \<mapsto> insert (Add e2) {add \<in> y e2 default to {}. \<not> hb add (Rem e2)})")
  apply(simp)
  using Collect_cong apply auto[1]
  apply(simp)
  using map_assign_commute apply fastforce
  done

lemma (in orset) rem_rem_commute:
  shows "\<langle>Rem e1\<rangle> \<rhd> \<langle>Rem e2\<rangle> = \<langle>Rem e2\<rangle> \<rhd> \<langle>Rem e1\<rangle>"
  apply(unfold interpret_op_def op_elem_def kleisli_def)
  apply(clarsimp)
  apply(case_tac "e1=e2", simp, simp)
  using map_assign_commute apply fastforce
  done

lemma (in orset) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(case_tac "x"; case_tac "y")
  apply(simp add: hb.concurrent_def add_add_commute)
  apply(simp add: hb.concurrent_def add_rem_commute)
  apply(simp add: hb.concurrent_def add_rem_commute)
  apply(simp add: hb.concurrent_def rem_rem_commute)
done

theorem (in orset) convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context orset begin

sublocale crdt: op_based_crdt weak_hb hb interpret_op
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "Map.empty"
  apply standard
  apply(erule exE)+
  using hb_consistent_prefix apply blast
  apply(erule exE)+
  using node_deliver_messages_distinct apply blast
  apply(erule exE)+
  using concurrent_operations_commute apply blast
  apply(erule exE)+
  unfolding interpret_op_def apply (metis (no_types, lifting) option.distinct(1))
  apply(erule exE, erule exE)
  using drop_last_message apply blast
done

end
end
