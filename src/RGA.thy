theory
  RGA
imports
  Network
  Ordered_List
begin
  
datatype ('id, 'v) operation =
  Insert "('id, 'v) elt" "'id option" |
  Delete "'id"

fun interpret_opers :: "('id::linorder, 'v) operation \<Rightarrow> ('id, 'v) elt list \<rightharpoonup> ('id, 'v) elt list" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_opers (Insert e n) xs  = insert xs e n" |
  "interpret_opers (Delete n)   xs  = delete xs n"

definition element_ids :: "('id, 'v) elt list \<Rightarrow> 'id set" where
 "element_ids list \<equiv> set (map fst list)"

definition valid_list_op :: "(('id::linorder, 'v) operation \<Rightarrow> 'id) \<Rightarrow> ('id, 'v) elt list \<Rightarrow> ('id::linorder, 'v) operation \<Rightarrow> bool" where
 "valid_list_op msg_id list oper \<equiv> case oper of
    Insert e  None      \<Rightarrow> fst e = msg_id oper |
    Insert e (Some pos) \<Rightarrow> fst e = msg_id oper \<and> pos \<in> element_ids list |
    Delete         pos  \<Rightarrow> pos \<in> element_ids list"

(* Replicated Growable Array Network *)
locale rga = network_with_constrained_ops msg_id _ interpret_opers "[]" "valid_list_op msg_id"
  for msg_id :: "('id::linorder, 'v) operation \<Rightarrow> 'id"

locale id_consistent_rga_network = rga +
  assumes ids_consistent: "hb (Insert e2 n2) (Insert e1 n1) \<Longrightarrow> fst e2 < fst e1"

definition indices :: "('id, 'v) operation event list \<Rightarrow> 'id list" where
  "indices xs \<equiv>
     List.map_filter (\<lambda>x. case x of Deliver (Insert e i) \<Rightarrow> Some (fst e) | _ \<Rightarrow> None) xs"

lemma indices_Nil [simp]:
  shows "indices [] = []"
by(auto simp: indices_def map_filter_def)

lemma indices_append [simp]:
  shows "indices (xs@ys) = indices xs @ indices ys"
by(auto simp: indices_def map_filter_def)

lemma indices_Broadcast_singleton [simp]:
  shows "indices [Broadcast b] = []"
by(auto simp: indices_def map_filter_def)

lemma indices_Deliver_Insert [simp]:
  shows "indices [Deliver (Insert e n)] = [fst e]"
by(auto simp: indices_def map_filter_def)

lemma indices_Deliver_Delete [simp]:
  shows "indices [Deliver (Delete n)] = []"
by(auto simp: indices_def map_filter_def)

lemma (in rga) idx_in_elem_inserted [intro]:
  assumes "Deliver (Insert e n) \<in> set xs"
  shows   "fst e \<in> set (indices xs)"
using assms by(induction xs, auto simp add: indices_def map_filter_def)

lemma (in rga) apply_opers_idx_elems:
  assumes "es prefix of i"
      and "apply_operations es = Some xs"
    shows "element_ids xs = set (indices es)"
using assms unfolding element_ids_def
  apply(induction es arbitrary: xs rule: rev_induct; clarsimp)
  apply(case_tac x; clarsimp)
  apply blast
  apply(case_tac "x2"; clarsimp)
  apply(auto split: bind_splits)
  apply(metis (no_types, hide_lams) Un_insert_right image_eqI insert_iff insert_preserve_indices
        option.sel prefix_of_appendD prod.sel(1) sup_bot.comm_neutral)
  apply(metis Un_insert_right fst_conv insert_iff insert_preserve_indices option.sel)
  apply(metis (no_types, hide_lams) Un_insert_right insert_iff insert_preserve_indices' option.sel
        prefix_of_appendD sup_bot.comm_neutral)
  apply(metis delete_preserve_indices fst_conv image_eqI prefix_of_appendD)
  using delete_preserve_indices apply blast
done

lemma (in rga) delete_does_not_change_element_ids:
  assumes "es @ [Deliver (Delete n)] prefix of i"
  and "apply_operations es = Some xs1"
  and "apply_operations (es @ [Deliver (Delete n)]) = Some xs2"
  shows "element_ids xs1 = element_ids xs2"
proof -
  have "indices es = indices (es @ [Deliver (Delete n)])"
    by simp
  then show ?thesis
    by (metis (no_types) assms prefix_of_appendD rga.apply_opers_idx_elems rga_axioms)
qed

lemma (in rga) someone_inserted_id:
  assumes "es @ [Deliver (Insert (k, v, f) n)] prefix of i"
  and "apply_operations es = Some xs1"
  and "apply_operations (es @ [Deliver (Insert (k, v, f) n)]) = Some xs2"
  and "a \<in> element_ids xs2"
  and "a \<noteq> k"
  shows "a \<in> element_ids xs1"
using assms apply_opers_idx_elems by auto

lemma (in rga) deliver_insert_exists:
  assumes "es prefix of i"
      and "apply_operations es = Some xs"
      and "a \<in> element_ids xs"
    shows "\<exists>v f n. Deliver (Insert (a, v, f) n) \<in> set es"
using assms unfolding element_ids_def
  apply(induction es arbitrary: xs rule: rev_induct; clarsimp)
  apply(case_tac x; clarsimp)
  apply(metis image_eqI prefix_of_appendD prod.sel(1))
  apply(case_tac "x2"; clarsimp)
  defer
  apply(drule prefix_of_appendD, clarsimp simp add: bind_eq_Some_conv)
  apply(metis delete_preserve_indices image_eqI prod.sel(1))
  apply(case_tac "ab=a")
  apply blast
  apply(subgoal_tac "\<exists>xs'. apply_operations xsa = Some xs'")
  defer
  apply(meson bind_eq_Some_conv)
  apply(erule exE)
  apply(metis (no_types, lifting) someone_inserted_id apply_operations_Deliver element_ids_def
    image_eqI prefix_of_appendD prod.sel(1) set_map)
done

lemma (in rga) insert_in_apply_set:
  assumes "es @ [Deliver (Insert e (Some a))] prefix of i"
      and "Deliver (Insert e' n) \<in> set es"
      and "apply_operations es = Some s"
    shows "fst e' \<in> element_ids s"
using assms apply_opers_idx_elems idx_in_elem_inserted prefix_of_appendD by blast

lemma (in rga) insert_msg_id:
  assumes "Broadcast (Insert e n) \<in> set (history i)"
  shows "fst e = msg_id (Insert e n)"
  apply(subgoal_tac "\<exists>state. valid_list_op msg_id state (Insert e n)")
  defer
  using assms broadcast_is_valid apply blast
  apply(erule exE)
  apply(unfold valid_list_op_def)
  apply(clarsimp)
  apply(case_tac n)
  apply(simp, simp)
done

lemma (in rga) allowed_insert:
  assumes "Broadcast (Insert e n) \<in> set (history i)"
  shows "n = None \<or> (\<exists>e' n'. n = Some (fst e') \<and> Deliver (Insert e' n') \<sqsubset>\<^sup>i Broadcast (Insert e n))"
  apply(subgoal_tac "\<exists>pre. pre @ [Broadcast (Insert e n)] prefix of i")
  defer
  apply(simp add: assms events_before_exist)
  apply(erule exE)
  apply(subgoal_tac "\<exists>state. apply_operations pre = Some state \<and> valid_list_op msg_id state (Insert e n)")
  defer
  apply(simp add: broadcast_only_valid_ops)
  apply(erule exE, erule conjE)
  apply(unfold valid_list_op_def)
  apply(case_tac n)
  apply simp+
  apply(subgoal_tac "a \<in> element_ids state")
  defer
  using apply_opers_idx_elems apply blast
  apply(subgoal_tac "\<exists>v' f' n'. Deliver (Insert (a, v', f') n') \<in> set pre")
  defer
  using deliver_insert_exists apply auto[1]
  using events_in_local_order apply blast
done

lemma (in rga) allowed_delete:
  assumes "Broadcast (Delete x) \<in> set (history i)"
  shows "\<exists>n' v b. Deliver (Insert (x, v, b) n') \<sqsubset>\<^sup>i Broadcast (Delete x)"
  apply(subgoal_tac "\<exists>pre. pre @ [Broadcast (Delete x)] prefix of i")
  defer
  apply(simp add: assms events_before_exist)
  apply(erule exE)
  apply(subgoal_tac "\<exists>state. apply_operations pre = Some state \<and> valid_list_op msg_id state (Delete x)")
  defer
  apply(simp add: broadcast_only_valid_ops)
  apply(erule exE, erule conjE)
  apply(unfold valid_list_op_def)
  apply(subgoal_tac "x \<in> element_ids state")
  defer
  using apply_opers_idx_elems apply simp
  apply(subgoal_tac "\<exists>v' f' n'. Deliver (Insert (x, v', f') n') \<in> set pre")
  defer
  using deliver_insert_exists apply auto[1]
  using events_in_local_order apply blast
done

lemma (in rga) insert_id_unique:
  assumes "fst e1 = fst e2"
  and "Broadcast (Insert e1 n1) \<in> set (history i)"
  and "Broadcast (Insert e2 n2) \<in> set (history j)"
  shows "Insert e1 n1 = Insert e2 n2"
using assms insert_msg_id msg_id_unique by metis

lemma (in rga) allowed_delete_deliver:
  assumes "Deliver (Delete x) \<in> set (history i)"
    shows "\<exists>n' v b. Deliver (Insert (x, v, b) n') \<sqsubset>\<^sup>i Deliver (Delete x)"
  using assms by (meson allowed_delete bot_least causal_broadcast delivery_has_a_cause insert_subset)

lemma (in rga) allowed_delete_deliver_in_set:
  assumes "(es@[Deliver (Delete m)]) prefix of i"
  shows   "\<exists>n v b. Deliver (Insert (m, v, b) n) \<in> set es"
by(metis (no_types, lifting) Un_insert_right insert_iff list.simps(15) assms
    local_order_prefix_closed_last rga.allowed_delete_deliver rga_axioms set_append subsetCE prefix_to_carriers)

lemma (in rga) allowed_insert_deliver:
  assumes "Deliver (Insert e n) \<in> set (history i)"
  shows   "n = None \<or> (\<exists>n' n'' v b. n = Some n' \<and> Deliver (Insert (n', v, b) n'') \<sqsubset>\<^sup>i Deliver (Insert e n))"
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
  apply(drule causal_broadcast[rotated, where j=i])
  apply auto
done

lemma (in rga) allowed_insert_deliver_in_set:
  assumes "(es@[Deliver (Insert e m)]) prefix of i"
  shows   "m = None \<or> (\<exists>m' n v b. m = Some m' \<and> Deliver (Insert (m', v, b) n) \<in> set es)"
by(metis assms Un_insert_right insert_subset list.simps(15) set_append prefix_to_carriers
    allowed_insert_deliver local_order_prefix_closed_last)

lemma (in rga) Insert_no_failure:
  assumes "es @ [Deliver (Insert e n)] prefix of i" 
      and "apply_operations es = Some s"
    shows "\<exists>ys. insert s e n = Some ys"
by(metis (no_types, lifting) element_ids_def allowed_insert_deliver_in_set assms fst_conv
    insert_in_apply_set insert_no_failure set_map)

lemma (in rga) delete_no_failure:
  assumes "es @ [Deliver (Delete n)] prefix of i"
      and "apply_operations es = Some s"
    shows "\<exists>ys. delete s n = Some ys"
using assms 
  apply -
  apply(frule allowed_delete_deliver_in_set)
  apply clarsimp
  apply(rule delete_no_failure)
  apply(drule idx_in_elem_inserted)
  apply(metis apply_opers_idx_elems element_ids_def prefix_of_appendD prod.sel(1) set_map)
done

lemma (in rga) Insert_equal:
  assumes "fst e1 = fst e2"
      and "Broadcast (Insert e1 n1) \<in> set (history i)"
      and "Broadcast (Insert e2 n2) \<in> set (history j)"
    shows "Insert e1 n1 = Insert e2 n2"
using assms
  apply(subgoal_tac "e1 = e2")
  apply(metis insert_id_unique)
  apply(cases e1, cases e2; clarsimp)
  using insert_id_unique by force

lemma (in rga) insert_id_unique_node:
  assumes "fst e1 = fst e2" 
      and "Broadcast (Insert e1 n1) \<in> set (history i)"
      and "Broadcast (Insert e2 n2) \<in> set (history j)"
    shows "i = j"
by(metis assms Insert_equal network.broadcasts_unique network_axioms)

lemma (in rga) same_insert:
  assumes "fst e1 = fst e2"
      and "xs prefix of i"
      and "(Insert e1 n1) \<in> set (node_deliver_messages xs)"
      and "(Insert e2 n2) \<in> set (node_deliver_messages xs)"
    shows "Insert e1 n1 = Insert e2 n2"
using assms
  apply -
  apply(subgoal_tac "Deliver (Insert e1 n1) \<in> set (history i)")
  apply(subgoal_tac "Deliver (Insert e2 n2) \<in> set (history i)")
  apply(subgoal_tac "\<exists>j. Broadcast (Insert e1 n1) \<in> set (history j)")
  apply(subgoal_tac "\<exists>j. Broadcast (Insert e2 n2) \<in> set (history j)")
  apply(erule exE)+
  apply(rule Insert_equal, force, force, force) 
  apply(simp add: delivery_has_a_cause)
  apply(simp add: delivery_has_a_cause)
  apply(auto simp add: node_deliver_messages_def prefix_msg_in_history)
done

lemma (in rga) insert_commute_assms:
  assumes "{Deliver (Insert e n), Deliver (Insert e' n')} \<subseteq> set (history i)"
      and "hb.concurrent (Insert e n) (Insert e' n')"
    shows "n = None \<or> n \<noteq> Some (fst e')"
using assms
  apply(clarsimp simp: hb.concurrent_def)
  apply(case_tac e')
  apply clarsimp
  apply(frule delivery_has_a_cause)
  apply(frule delivery_has_a_cause) back
  apply clarsimp
  apply(frule allowed_insert)
  apply clarsimp
  apply(metis Insert_equal delivery_has_a_cause fst_conv hb.intros(2) insert_subset local_order_carrier_closed)
done

lemma (in rga) Insert_Insert_concurrent:
  assumes "{Deliver (Insert e k), Deliver (Insert e' (Some m))} \<subseteq> set (history i)"
      and "hb.concurrent (Insert e k) (Insert e' (Some m))"
    shows "fst e \<noteq> m"
by(metis (no_types, hide_lams) hb.concurrent_comm insert_commute insert_commute_assms option.simps(3) assms)

lemma (in rga) insert_valid_assms:
 assumes "Deliver (Insert e n) \<in> set (history i)"
   shows "n = None \<or> n \<noteq> Some (fst e)"
using assms by(meson allowed_insert_deliver hb.concurrent_def hb.less_asym insert_subset local_order_carrier_closed rga.insert_commute_assms rga_axioms)

lemma (in rga) Insert_Delete_concurrent:
  assumes "{Deliver (Insert e n), Deliver (Delete n')} \<subseteq> set (history i)"
      and "hb.concurrent (Insert e n) (Delete n')"
    shows "n' \<noteq> fst e"
by (metis assms Insert_equal allowed_delete delivery_has_a_cause fst_conv hb.concurrent_def hb.intros(2) insert_subset local_order_carrier_closed)

lemma (in rga) apply_operations_distinct:
  assumes "xs prefix of i"
      and "apply_operations xs = Some ys"
    shows "distinct (map fst ys)"
oops

lemma (in rga) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(rule ext)
  apply(unfold kleisli_def)
  apply(case_tac x; case_tac y)
  apply clarsimp
  apply(case_tac "a = ab")
  apply(subgoal_tac "(a, aa, b) = (ab, ac, ba) \<and> x12a = x12")
  apply force
  defer
  apply(subgoal_tac "Ordered_List.insert xa (a, aa, b) x12 \<bind> (\<lambda>x. Ordered_List.insert x (ab, ac, ba) x12a) = Ordered_List.insert xa (ab, ac, ba) x12a \<bind> (\<lambda>x. Ordered_List.insert x (a, aa, b) x12)")
  apply(metis (no_types, lifting) Option.bind_cong interpret_opers.simps(1))
  apply(rule insert_commutes)
  apply simp
  prefer 2
  apply(subst (asm) hb.concurrent_comm)
  apply(rule insert_commute_assms)
  prefer 2
  apply assumption
  apply clarsimp
  apply(rule conjI)
  apply(rule prefix_msg_in_history, assumption, force)
  apply(rule prefix_msg_in_history, assumption, force)
  apply(rule insert_commute_assms)
  prefer 2
  apply assumption
  apply clarsimp
  apply(rule conjI)
  apply(rule prefix_msg_in_history, assumption, force)
  apply(rule prefix_msg_in_history, assumption, force)
  apply(clarsimp simp del: delete.simps)
  apply(subgoal_tac "Ordered_List.insert xa (a, aa, b) x12 \<bind> (\<lambda>x. Ordered_List.delete x x2) = delete xa x2 \<bind> (\<lambda>x. Ordered_List.insert x (a, aa, b) x12)")
  apply(metis (no_types, lifting) Option.bind_cong interpret_opers.simps)
  apply(rule insert_delete_commute)
  apply(rule Insert_Delete_concurrent)
  apply clarsimp
  using prefix_msg_in_history apply blast
  apply(clarsimp)
  apply(clarsimp simp del: delete.simps)
  apply(subgoal_tac "delete xa x2 \<bind> (\<lambda>x. insert x (a, aa, b) x12) = Ordered_List.insert xa (a, aa, b) x12 \<bind> (\<lambda>x. delete x x2)")
  apply(metis (no_types, lifting) Option.bind_cong interpret_opers.simps)
  apply(rule insert_delete_commute[symmetric])
  apply(rule Insert_Delete_concurrent)
  using prefix_msg_in_history apply blast
  apply(subst (asm) hb.concurrent_comm)
  apply assumption
  apply(clarsimp simp del: delete.simps)
  apply(subgoal_tac "delete xa x2 \<bind> (\<lambda>x. delete x x2a) = delete xa x2a \<bind> (\<lambda>x. delete x x2)")
  apply(metis (mono_tags, lifting) Option.bind_cong interpret_opers.simps(2))
  apply(rule delete_commutes)
  using same_insert apply force
done

lemma (in rga) apply_operations_never_fails:
  assumes "xs prefix of i"
  shows "apply_operations xs \<noteq> None"
  using assms
  apply(induction xs rule: rev_induct)
   apply clarsimp
  apply(case_tac "x"; clarsimp)
   apply force
  apply(case_tac "x2"; clarsimp)
   apply (metis bind.bind_lunit interpret_opers.simps(1) prefix_of_appendD rga.Insert_no_failure rga_axioms)
  apply(metis bind.bind_lunit interpret_opers.simps(2) local.delete_no_failure prefix_of_appendD)
  done
  
corollary (in rga) rga_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context rga begin

sublocale sec: strong_eventual_consistency weak_hb hb interpret_opers
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "[]"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix node_deliver_messages_distinct
        concurrent_operations_commute apply_operations_def)
   apply(metis apply_operations_def bind.bind_lunit not_None_eq hb.apply_operations_Snoc kleisli_def apply_operations_never_fails)
  using drop_last_message apply blast
  done

end
  
section\<open>Interpretations\<close>
  
interpretation trivial_rga_implementation: rga "\<lambda>x. []"
  by (standard, auto simp add: trivial_node_histories.history_order_def trivial_node_histories.prefix_of_node_history_def)

interpretation non_trivial_rga_implementation: rga "\<lambda>m. if m = 0 then [Broadcast (Insert (0, 0, False) None), Deliver (Insert (0, 0, False) None)] else []"
oops

end