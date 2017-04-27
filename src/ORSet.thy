(* Victor B. F. Gomes, University of Cambridge
   Martin Kleppmann, University of Cambridge
   Dominic P. Mulligan, University of Cambridge
*)

section\<open>Observed-Remove Set\<close>
 
text\<open>The ORSet is a well-known CRDT for implementing replicated sets, supporting two operations:
     the \emph{insertion} and \emph{deletion} of an arbitrary element in the shared set.\<close>

theory
  ORSet
imports
  Network
  "~~/src/HOL/Library/Code_Target_Numeral"
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
  
definition valid_behaviours :: "nat \<Rightarrow> ('id, 'a) state \<Rightarrow> ('id \<times> ('id, 'a) operation) set" where
  "valid_behaviours node state \<equiv>
     { (i::'id, oper::('id, 'a) operation). case oper of
         Add j  e \<Rightarrow> i = j |
         Rem is e \<Rightarrow> is = state e }"

export_code Add interpret_op valid_behaviours in OCaml file "ocaml/orset.ml"

locale orset = network_with_constrained_ops _ interpret_op "\<lambda>x. {}" valid_behaviours

lemma (in orset) add_add_commute:
  shows "\<langle>Add i1 e1\<rangle> \<rhd> \<langle>Add i2 e2\<rangle> = \<langle>Add i2 e2\<rangle> \<rhd> \<langle>Add i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) add_rem_commute:
  assumes "i \<notin> is"
  shows "\<langle>Add i e1\<rangle> \<rhd> \<langle>Rem is e2\<rangle> = \<langle>Rem is e2\<rangle> \<rhd> \<langle>Add i e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)

lemma (in orset) apply_operations_never_fails:
  assumes "xs prefix of i"
  shows "apply_operations xs \<noteq> None"
  using assms
  apply(induction xs rule: rev_induct)
   apply clarsimp
  apply(case_tac "x"; clarsimp)
   apply force
  apply(metis interpret_op_def interp_msg_def bind.bind_lunit prefix_of_appendD)
  done

lemma (in orset) add_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Add i2 e) \<in> set xs"
  shows "i1 = i2"
  apply(subgoal_tac "\<exists>j state. (i1, Add i2 e) \<in> valid_behaviours j state")
  apply(simp add: valid_behaviours_def)
  using assms deliver_in_prefix_is_valid apply blast
done

definition (in orset) added_ids :: "('id \<times> ('id, 'b) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
  "added_ids es p \<equiv> List.map_filter (\<lambda>x. case x of Deliver (i, Add j e) \<Rightarrow> if e = p then Some j else None | _ \<Rightarrow> None) es"

lemma (in orset) [simp]:
  shows "added_ids [] e = []"
  by (auto simp: added_ids_def map_filter_def)
    
lemma (in orset) [simp]:
  shows "added_ids (xs @ ys) e = added_ids xs e @ added_ids ys e"
    by (auto simp: added_ids_def map_filter_append)

lemma (in orset) added_ids_Broadcast_collapse [simp]:
  shows "added_ids ([Broadcast e]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Rem_collapse [simp]:
  shows "added_ids ([Deliver (i, Rem is e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Add_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_ids ([Deliver (i, Add j e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Add_same_collapse [simp]:
  shows "added_ids ([Deliver (i, Add j e)]) e = [j]"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in orset) added_id_not_in_set:
  assumes "i1 \<notin> set (added_ids [Deliver (i, Add i2 e)] e)"
  shows "i1 \<noteq> i2"
  using assms by simp

lemma (in orset) apply_operations_added_ids:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "f x \<subseteq> set (added_ids es x)"
  using assms
  apply (induct es arbitrary: f rule: rev_induct)
   apply force
  apply (case_tac xa)
   apply clarsimp
   apply force
  apply clarsimp
  apply (case_tac b)
   apply(subgoal_tac "xs prefix of j", clarsimp split: bind_splits)
   apply(clarsimp simp add: interp_msg_def)
    apply(erule_tac x="xb" in meta_allE, clarsimp simp add: interpret_op_def)
    apply(clarsimp split: if_split_asm simp add: op_elem_def added_id_not_in_set)
     apply force
    apply force
   apply force
  apply(subgoal_tac "xs prefix of j", clarsimp split: bind_splits)
   apply(erule_tac x="xb" in meta_allE, clarsimp simp add: interpret_op_def interp_msg_def)
   apply(clarsimp split: if_split_asm simp add: op_elem_def)
    apply force
   apply force
  apply force
done

lemma (in orset) Deliver_added_ids:
  assumes "xs prefix of j"
    and "i \<in> set (added_ids xs e)"
  shows "Deliver (i, Add i e) \<in> set xs"
    using assms
  apply (induct xs rule: rev_induct)
     apply clarsimp
    apply (case_tac x)
     apply(simp add: prefix_of_appendD)
    apply clarsimp
    apply (case_tac b)
     apply clarsimp
     apply (metis added_ids_Deliver_Add_diff_collapse added_ids_Deliver_Add_same_collapse
       empty_iff list.set(1) set_ConsD add_id_valid in_set_conv_decomp prefix_of_appendD)
    apply (metis added_ids_Deliver_Rem_collapse empty_iff list.set(1) prefix_of_appendD)
    done

lemma (in orset) Broadcast_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (r, Rem ix e)] prefix of j"
    and "i \<in> ix"
  shows "Deliver (i, Add i e) \<in> set xs"
  using assms
  apply(subgoal_tac "\<exists>y. apply_operations xs = Some y")
   apply clarsimp
   apply(subgoal_tac "ix = y e")
    apply clarsimp
    apply(frule_tac x=e in apply_operations_added_ids)
     apply force
    apply(clarsimp)
  using Deliver_added_ids apply blast
   apply(subgoal_tac "(r, Rem ix e) \<in> valid_behaviours j y") prefer 2
  using broadcast_only_valid_msgs apply fastforce
    apply(simp add: valid_behaviours_def)
  using broadcast_only_valid_msgs apply blast
  done

lemma (in orset) Broadcast_Deliver_prefix_closed2:
  assumes "xs prefix of j"
    and "Broadcast (r, Rem ix e) \<in> set xs"
    and "i \<in> ix"
  shows "Deliver (i, Add i e) \<in> set xs"
  using assms
  apply(induction xs rule: rev_induct)
   apply clarsimp
  apply(erule meta_impE, force)
  apply clarsimp
  apply(erule disjE)
    defer
   apply force
  apply clarsimp
    using Broadcast_Deliver_prefix_closed apply metis
done

lemma (in orset) concurrent_add_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Add i e) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Add i e) (ir, Rem is e)"
    using assms
  apply(subgoal_tac "\<exists>pre k. pre@[Broadcast (ir, Rem is e)] prefix of k")
   apply clarsimp
     apply(frule broadcast_only_valid_msgs, clarsimp simp add: valid_behaviours_def)
     apply(subgoal_tac "Deliver (i, Add i e) \<in> set pre")
      apply(rule_tac i=k in hb.intros(2))
    using events_in_local_order apply blast
     apply(insert Broadcast_Deliver_prefix_closed2)
     apply(erule_tac x="pre @ [Broadcast (ir, Rem (state e) e)]" in meta_allE)
     apply(erule_tac x=k in meta_allE, erule_tac x=ir in meta_allE, erule_tac x="is" in meta_allE)
     apply(erule_tac x="e" in meta_allE, erule_tac x=i in meta_allE)
      apply clarsimp
    using delivery_has_a_cause events_before_exist prefix_msg_in_history apply blast
    done

lemma (in orset) Deliver_Add_same_id_same_message:
  assumes "Deliver (i, Add i e1) \<in> set (history j)" and "Deliver (i, Add i e2) \<in> set (history j)"
  shows "e1 = e2"
  apply(subgoal_tac "\<exists>pre k. pre@[Broadcast (i, Add i e1)] prefix of k")
   apply(subgoal_tac "\<exists>pre k. pre@[Broadcast (i, Add i e2)] prefix of k")
    apply clarsimp
    apply(subgoal_tac "Broadcast (i, Add i e1) \<in> set (history k)")
    apply(subgoal_tac "Broadcast (i, Add i e2) \<in> set (history ka)")
    apply(drule msg_id_unique, assumption)
       apply(drule broadcast_only_valid_msgs)+
       apply(clarsimp simp add: valid_behaviours_def)
      apply force
  using prefix_of_node_history_def apply(metis Un_insert_right insert_subset list.simps(15) prefix_to_carriers set_append)
  using prefix_of_node_history_def apply(metis Un_insert_right insert_subset list.simps(15) prefix_to_carriers set_append)
  using assms(2) delivery_has_a_cause events_before_exist apply blast
  using assms(1) delivery_has_a_cause events_before_exist apply blast
  done
      
lemma (in orset) ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
  using assms
      apply(subgoal_tac "\<exists>pre k. pre@[Broadcast (ir, Rem is e2)] prefix of k")
   apply clarsimp
     apply(frule broadcast_only_valid_msgs, clarsimp simp add: valid_behaviours_def)
   apply(subgoal_tac "Deliver (i, Add i e2) \<in> set pre")
    apply(rule_tac j=j and i=i in Deliver_Add_same_id_same_message)
  using prefix_msg_in_history apply blast
  using causal_broadcast events_in_local_order local_order_prefix_closed prefix_contains_msg prefix_to_carriers apply blast
   apply(rule Broadcast_Deliver_prefix_closed, assumption, assumption)
  using delivery_has_a_cause events_before_exist prefix_msg_in_history apply blast
  done

corollary (in orset) concurrent_add_remove_independent:
  assumes "\<not> hb (i, Add i e1) (ir, Rem is e2)" and "\<not> hb (ir, Rem is e2) (i, Add i e1)"
    and "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
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
  apply(unfold interp_msg_def, simp)
  apply(case_tac "b"; case_tac "ba")
  apply(simp add: add_add_commute hb.concurrent_def)
  apply(metis add_rem_commute concurrent_add_remove_independent hb.concurrent_def add_id_valid prefix_contains_msg)
  apply(metis add_rem_commute concurrent_add_remove_independent hb.concurrent_def add_id_valid prefix_contains_msg)
  apply(simp add: rem_rem_commute hb.concurrent_def)
  done

theorem (in orset) convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i" and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)
              
context orset begin

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "\<lambda>x.{}"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix node_deliver_messages_distinct
        concurrent_operations_commute)
   apply(metis (no_types, lifting) apply_operations_def bind.bind_lunit not_None_eq
     hb.apply_operations_Snoc kleisli_def apply_operations_never_fails interp_msg_def)
  using drop_last_message apply blast
done

end
end

  