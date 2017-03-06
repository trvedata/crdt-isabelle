theory
  RGA
imports
  Causal_CRDT
  Ordered_List
begin
  
datatype ('id, 'v) operation =
  Insert "('id, 'v) elt" "'id option" |
  Delete "'id"

fun interpret_opers :: "('id::linorder, 'v) operation \<Rightarrow> ('id, 'v) elt list \<rightharpoonup> ('id, 'v) elt list" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_opers (Insert e n) xs  = insert xs e n" |
  "interpret_opers (Delete n)   xs  = delete xs n"

(* Replicated Growable Array Network *)
locale rga = network_with_ops _ interpret_opers +
  assumes insert_flag: "Broadcast (Insert e n) \<in> set (history i) \<Longrightarrow> snd (snd e) = False"
  assumes allowed_insert: "Broadcast (Insert e n) \<in> set (history i) \<Longrightarrow> n = None \<or> 
                            (\<exists>n' n'' v b. n = Some n' \<and> Deliver (Insert (n', v, b) n'') \<sqsubset>\<^sup>i Broadcast (Insert e n))"
  assumes insert_id_unique: "id1 = id2 \<Longrightarrow> Broadcast (Insert (id1, v1, b1) n1) \<in> set (history i) \<Longrightarrow> Broadcast (Insert (id2, v2, b2) n2) \<in> set (history j) \<Longrightarrow> v1 = v2 \<and> n1 = n2"
  assumes allowed_delete: "Broadcast (Delete x) \<in> set (history i) \<Longrightarrow> (\<exists>n' v b. Deliver (Insert (x, v, b) n') \<sqsubset>\<^sup>i Broadcast (Delete x))"
    
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
  apply(frule no_message_lost[where j=i]) back
  apply(drule causal_broadcast[rotated, where j=i])
  apply auto
done

lemma (in rga) allowed_insert_deliver_in_set:
  assumes "(es@[Deliver (Insert e m)]) prefix of i"
  shows   "m = None \<or> (\<exists>m' n v b. m = Some m' \<and> Deliver (Insert (m', v, b) n) \<in> set es)"
by(metis assms Un_insert_right insert_subset list.simps(15) set_append prefix_to_carriers
    allowed_insert_deliver local_order_prefix_closed_last)

abbreviation (in rga) apply_operations :: "('a, 'b) operation event list \<Rightarrow> ('a, 'b) elt list option" where
  "apply_operations es \<equiv> hb.apply_operations (node_deliver_messages es) []"

lemma (in rga) apply_operations_empty [simp]:
  shows "apply_operations [] = Some []"
by auto

lemma (in rga) apply_operations_Broadcast [simp]:
  shows "apply_operations (xs @ [Broadcast m]) = apply_operations xs"
by(auto simp add: node_deliver_messages_def map_filter_def)

lemma (in rga) apply_operations_Deliver [simp]:
  shows "apply_operations (xs @ [Deliver m]) = (apply_operations xs \<bind> \<langle>m\<rangle>)"
by(auto simp add: node_deliver_messages_def map_filter_def kleisli_def)

definition indices :: "('a, 'b) operation event list \<Rightarrow> 'a list" where
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
    shows "fst ` set xs = set (indices es)"
using assms
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

lemma (in rga) insert_in_apply_set:
  assumes "es @ [Deliver (Insert e (Some a))] prefix of i"
      and "Deliver (Insert e' n) \<in> set es"
      and "apply_operations es = Some s"
    shows "fst e' \<in> fst ` set s"
using assms apply_opers_idx_elems idx_in_elem_inserted prefix_of_appendD by blast

lemma (in rga) Insert_no_failure:
  assumes "es @ [Deliver (Insert e n)] prefix of i" 
      and "apply_operations es = Some s"
    shows "\<exists>ys. insert s e n = Some ys"
by(metis allowed_insert_deliver_in_set assms fst_conv insert_in_apply_set insert_no_failure)

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
  apply(auto simp add: apply_opers_idx_elems)
done

lemma (in rga) Insert_equal:
  assumes "fst e1 = fst e2"
      and "Broadcast (Insert e1 n1) \<in> set (history i)"
      and "Broadcast (Insert e2 n2) \<in> set (history j)"
    shows "Insert e1 n1 = Insert e2 n2"
using assms
  apply(subgoal_tac "e1 = e2")
  apply(metis surjective_pairing insert_id_unique)
  apply(cases e1, cases e2; clarsimp)
  apply(metis insert_flag snd_conv insert_id_unique)
done

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
  apply(simp add: node_deliver_messages_def prefix_msg_in_history)+
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

lemma (in rga) node_deliver_messages_distinct:
  assumes "xs prefix of i"
  shows "distinct (node_deliver_messages xs)"
using assms
  apply(induction xs rule: rev_induct)
  apply simp
  apply(clarsimp simp add: node_deliver_messages_append)
  apply safe
  apply force
  apply(clarsimp simp: node_deliver_messages_def map_filter_def)
  apply clarsimp
  apply(frule prefix_distinct)
  apply clarsimp
  apply(subst (asm) node_deliver_messages_def) back back back
  apply(clarsimp simp add: map_filter_def)
  apply(case_tac x; clarsimp)
  apply(subst (asm) node_deliver_messages_def) back
  apply(clarsimp simp add: map_filter_def)
  apply(case_tac x; clarsimp)
done

lemma (in rga) hb_consistent_prefix:
  assumes "xs prefix of i"
    shows "hb.hb_consistent (node_deliver_messages xs)"
using assms
  apply(clarsimp simp: prefix_of_node_history_def)
  apply(rule_tac i=i in hb_consistent_technical)
  apply(subst history_order_def)
  apply(subgoal_tac "xs = [] \<or> (\<exists>c. xs = [c]) \<or> (length (xs) > 1)")
  apply(erule disjE)
  apply clarsimp
  apply(erule disjE)
  apply clarsimp
  apply(drule list_nth_split)
  apply assumption
  apply clarsimp
  apply clarsimp
  apply(rule_tac x=xsa in exI)
  apply(rule_tac x=ysa in exI)
  apply(rule_tac x="zs@ys" in exI)
  apply(metis Cons_eq_appendI append_assoc)
  apply force
done

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
  apply(rule insert_valid_assms)
  using prefix_msg_in_history apply blast
  apply(rule Insert_Delete_concurrent)
  apply clarsimp
  using prefix_msg_in_history apply blast
  apply(clarsimp)
  apply(clarsimp simp del: delete.simps)
  apply(subgoal_tac "delete xa x2 \<bind> (\<lambda>x. insert x (a, aa, b) x12) = Ordered_List.insert xa (a, aa, b) x12 \<bind> (\<lambda>x. delete x x2)")
  apply(metis (no_types, lifting) Option.bind_cong interpret_opers.simps)
  apply(rule insert_delete_commute[symmetric])
  apply(rule insert_valid_assms)
  using prefix_msg_in_history apply blast
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

corollary (in rga) rga_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

end