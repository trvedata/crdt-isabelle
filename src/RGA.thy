theory
  RGA
imports
  Causal_CRDT
  Ordered_List
begin

datatype ('id, 'v) operation =
  Insert "('id, 'v) elt" "'id option" |
  Delete "'id"

fun interpret_opers :: "('id::linorder, 'v) operation \<Rightarrow> ('id, 'v) elt list \<Rightarrow> ('id, 'v) elt list" where
  "interpret_opers (Insert e n) = (\<lambda>xs. the (insert xs e n))" |
  "interpret_opers (Delete n)   = (\<lambda>xs. the (delete xs n))"

(* Replicated Growable Array Network *)
locale rga = network_with_ops _ _ _ interpret_opers +
  assumes insert_flag: "(i, Broadcast, Insert e n) \<in> set (carriers i) \<Longrightarrow> snd (snd e) = False"
  assumes allowed_insert: "(i, Broadcast, Insert e n) \<in> set (carriers i) \<Longrightarrow> n = None \<or> 
                            (\<exists>n' n'' v b. n = Some n' \<and> (i, Deliver, Insert (n', v, b) n'') \<sqsubset>\<^sup>i (i, Broadcast, Insert e n))"
  assumes insert_id_unique: "id1 = id2 \<Longrightarrow> (i, Broadcast, Insert (id1, v1, b1) n1) \<in> set (carriers i) \<Longrightarrow> (j, Broadcast, Insert (id2, v2, b2) n2) \<in> set (carriers j) \<Longrightarrow> v1 = v2 \<and> n1 = n2"
  assumes allowed_delete: "(i, Broadcast, Delete x) \<in> set (carriers i) \<Longrightarrow> (\<exists>n' v b. (i, Deliver, Insert (x, v, b) n') \<sqsubset>\<^sup>i (i, Broadcast, Delete x))"

lemma (in rga) allowed_delete_deliver:
  assumes "(i, Deliver, Delete x) \<in> set (carriers i)"
  shows "\<exists>n' v b. (i, Deliver, Insert (x, v, b) n') \<sqsubset>\<^sup>i (i, Deliver, Delete x)"
using assms apply -
  apply(drule delivery_has_a_cause)
  apply clarsimp
  apply(frule no_message_lost[where j=i])
  apply(drule allowed_delete)
  apply clarsimp
  apply(frule local_order_carrier_closed)
  apply clarsimp
  apply(drule delivery_has_a_cause) back
  apply clarsimp
  apply(frule no_message_lost[where j=i]) back
  apply(drule broadcast_causal[rotated, where j=i])
  apply force
  apply force
done

lemma (in rga) allowed_insert_deliver:
  assumes "(i, Deliver, Insert e n) \<in> set (carriers i)"
  shows   "n = None \<or> (\<exists>n' n'' v b. n = Some n' \<and> (i, Deliver, Insert (n', v, b) n'') \<sqsubset>\<^sup>i (i, Deliver, Insert e n))"
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
  apply(drule broadcast_causal[rotated, where j=i])
  apply force
  apply force
done

lemma (in rga) allowed_insert_deliver_in_set:
  assumes "(es@[(i, Deliver, Insert e m)]) prefix of i"
  shows   "m = None \<or> (\<exists>m' n v b. m = Some m' \<and> (i, Deliver, Insert (m', v, b) n) \<in> set es)"
using assms
  apply -
  apply(frule_tac x="(i, Deliver, Insert e m)" in prefix_to_carriers)
  apply force
  apply(frule allowed_insert_deliver)
  apply(erule disjE)
  apply force
  apply clarsimp
  apply(drule local_order_prefix_closed_last, assumption)
  apply force
done

lemma (in rga) allowed_insert_Some_deliver:
  assumes "(es@[(i, Deliver, Insert e (Some m))]) prefix of i"
  shows   "\<exists>n v b. (i, Deliver, Insert (m, v, b) n) \<in> set es"
  using assms allowed_insert_deliver_in_set[where es=es and i=i and e=e and m="Some m"] by force

lemma (in rga) delete_is_not_first_msg:
  shows "\<not> ([(i, Deliver, Delete n)] prefix of i)"
  apply (clarsimp simp: prefix_of_carrier_def)
  apply(subgoal_tac "(i, Deliver, Delete n) \<in> set (carriers i)")
  apply(drule allowed_delete_deliver)
  apply clarsimp
  using carriers_head_lt apply force
  apply (metis list.set_intros(1))
done

lemma (in rga) insert_Some_is_not_first_msg:
  shows "\<not> ([(i, Deliver, Insert e (Some n))] prefix of i)"
  by (clarsimp, insert allowed_insert_deliver_in_set[where es="[]" and i=i and e=e and m="Some n"], force)

definition (in rga) apply_operations :: "('a, 'b) operation event list \<Rightarrow> ('a, 'b) elt list" where
  "apply_operations es \<equiv> (fold (op \<circ>) (map interpret_opers (node_deliver_messages es)) id) []"

lemma (in rga) apply_operations_empty[simp]: "apply_operations [] = []"
  by (auto simp: apply_operations_def)

lemma (in rga) apply_operations_Broadcast [simp]: "apply_operations (xs @ [(i, Broadcast, m)]) = apply_operations xs"
  by (auto simp: apply_operations_def node_deliver_messages_def)

lemma (in rga) apply_operations_Deliver [simp]: "apply_operations (xs @ [(i, Deliver, m)]) = interpret_opers m (apply_operations xs)"
  by (auto simp: apply_operations_def node_deliver_messages_def)

lemma (in rga) insert_same_set:
  assumes "es @ es' @ [(i, Deliver, Insert e (Some a))] prefix of i"
          "(i, Deliver, Insert (a, v, b) n) \<in> set es"
  shows   "\<exists>v b. (a, v, b) \<in> set (apply_operations es)"
using assms
apply (induct es arbitrary: es' e a rule: rev_induct)
apply clarsimp
apply clarsimp
apply (case_tac aa)
apply clarsimp
apply (erule_tac x="(a, Broadcast, ba) # es'" in meta_allE)
apply clarsimp
apply clarsimp

apply (case_tac ba)
apply clarsimp

apply (case_tac x12)
apply clarsimp
defer

apply clarsimp
apply (erule disjE)
defer
apply (erule_tac x="[]" in meta_allE)
apply (erule_tac x="aa" in meta_allE)
apply (erule_tac x="ae" in meta_allE)
apply (erule_tac x="bb" in meta_allE)
apply (erule_tac x="af" in meta_allE)
apply clarsimp
apply (subgoal_tac "a=i")
prefer 2
apply (rule prefix_consistent, assumption, force)
apply clarsimp
apply (subgoal_tac "xs @ [(i, Deliver, Insert (aa, ae, bb) (Some af))] prefix of i")
apply clarsimp
prefer 2
  apply (rule prefix_of_appendD)
  apply fastforce

sorry


lemma (in rga)
  assumes "es @ [(i, Deliver, Insert e n)] prefix of i"
  shows "\<exists>ys. Ordered_List.insert (apply_operations es) e n = Some ys"
using assms apply -
apply (frule allowed_insert_deliver_in_set)
apply (case_tac n)
apply clarsimp
apply clarsimp
apply (rule insert_no_failure)
apply clarsimp
using insert_same_set apply metis
done

lemma (in rga)
  assumes "es @ es' @ [(i, Deliver, Insert e n)] prefix of i"
          "\<forall>m. n = Some m \<longrightarrow> (\<forall>n v b. (i, Deliver, Insert (m, v, b) n) \<notin> set es')"
  shows "\<exists>ys. Ordered_List.insert (apply_operations es) e n = Some ys \<and> e \<in> set ys"
using assms
  apply (induct es arbitrary: es' e n rule: rev_induct)
  apply (case_tac n)
    apply force
    apply clarsimp
    apply (clarsimp dest!: allowed_insert_Some_deliver)

  apply clarsimp
  apply (case_tac aa)
    apply clarsimp
    apply (erule_tac x="(a, Broadcast, b) # es'" in meta_allE)
    apply clarsimp

  apply clarsimp
  apply (subgoal_tac "a=i")
  prefer 2
  apply (rule prefix_consistent, assumption, force)

  apply clarsimp
  apply (case_tac b)
  apply clarsimp
    apply (erule_tac x="[]" in meta_allE)
    apply (erule_tac x="a" in meta_allE)
    apply (erule_tac x="aa" in meta_allE)
    apply (erule_tac x="bb" in meta_allE)
    apply (erule_tac x="x12" in meta_allE)
    apply clarsimp
    apply (subgoal_tac "xs @ [(i, Deliver, Insert (a, aa, bb) x12)] prefix of i")
prefer 2
    apply (rule prefix_of_appendD)
    apply fastforce

    apply clarsimp

    apply (case_tac n)
    apply clarsimp
    using el_inserted apply force
    apply clarsimp
    apply (insert insert_no_failure)
    apply (erule_tac x="Some ad" in meta_allE)
    apply (erule_tac x="ys" in meta_allE)
    apply (erule_tac x="(ab, ac, ba)" in meta_allE)
    apply clarsimp
    apply (subgoal_tac "\<exists>v b. (ad, v, b) \<in> set ys")
    prefer 2


    
    


lemma (in rga) 
  assumes "fst e1 = fst e2"
          "(i, Broadcast, Insert e1 n1) \<in> set (carriers i)"
          "(j, Broadcast, Insert e2 n2) \<in> set (carriers j)"
  shows   "Insert e1 n1 = Insert e2 n2"
  using assms
  apply (subgoal_tac "e1 = e2")
  apply (metis surjective_pairing insert_id_unique)
  apply (cases e1, cases e2; clarsimp)
  by (metis insert_flag snd_conv insert_id_unique)


lemma (in rga) insert_id_unique_node:
  assumes "fst e1 = fst e2" 
          "(i, Broadcast, Insert e1 n1) \<in> set (carriers i)"
          "(j, Broadcast, Insert e2 n2) \<in> set (carriers j)"
  shows   "i = j"
  using assms broadcasts_unique insert_id_unique
  by (smt insert_flag prod.collapse)


lemma (in rga) insert_commute_assms:
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
by (smt delivery_has_a_cause rga.insert_flag rga_axioms insert_subset local_order_carrier_closed prod.sel(2))

lemma (in rga)
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
oops


lemma (in rga)
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
apply (smt delivery_has_a_cause rga.insert_flag rga_axioms insert_id_unique insert_subset local_order_carrier_closed prod.sel(2))
using insert_id_unique_node
by (smt delivery_has_a_cause insert_flag insert_id_unique insert_subset local_order_carrier_closed prod.sel(2))


lemma prefix_set_mem:
  assumes "xs@ys = zs"
          "x \<in> set ys"
  shows   "x \<in> set zs"
using assms by auto

lemma (in rga) apply_operations_singleton:
  assumes "es = apply_operations [oper]"
          "oper#ys = carriers i"
  shows   "\<exists>j e m. oper = (i, e, Insert j m) \<and> (e = Broadcast \<longrightarrow> es = []) \<and> (e = Deliver \<longrightarrow> es = [j])"
using assms
  apply(clarsimp simp add: apply_operations_def ordered_node_operations_def)
  apply(case_tac oper; clarsimp)
  apply(subgoal_tac "a=i")
  apply(case_tac b; clarsimp)
prefer 3
  using carriers_message_consistent apply (metis list.set_intros(1))
  apply(subgoal_tac "(i, Broadcast, c) \<in> set (carriers i)")
  apply(erule disjE[OF insert_or_delete])
  apply clarsimp
  apply(subgoal_tac "(i, Broadcast, Delete x) \<in> set (carriers i)")
  apply(drule allowed_delete)
  apply clarsimp
  using carriers_head_lt apply force
  apply (metis list.set_intros(1))
  apply force
  apply (metis list.set_intros(1))
  apply(subgoal_tac "(i, Deliver, c) \<in> set (carriers i)")
  apply(erule disjE[OF insert_or_delete])
  apply clarsimp
  apply(subgoal_tac "(i, Deliver, Delete x) \<in> set (carriers i)")
  apply(frule delivery_has_a_cause, erule exE)
  apply(drule broadcast_before_delivery[where j=i])
  apply(drule allowed_delete_deliver, clarsimp)
  using carriers_head_lt apply force
  apply (metis list.set_intros(1))
  apply clarsimp
  apply(rule_tac x=a in exI, rule_tac x=aa in exI, rule_tac x=b in exI)
  apply(rule conjI)
  apply force
  apply(subgoal_tac "y=None", clarsimp)
  apply(clarsimp simp add: Insert_def)
  apply(subgoal_tac "(i, Deliver, Insert (a, aa, b) y) \<in> set (carriers i)")
  apply(drule allowed_insert_deliver)
  apply(erule disjE, assumption)
  apply clarsimp
  using carriers_head_lt apply force  
  apply (metis list.set_intros(1))+
done

lemma (in rga) apply_operations_singleton_Broadcast:
  shows "apply_operations (xs @ [(i, Broadcast, f)]) = apply_operations xs"
by(clarsimp simp add: apply_operations_def ordered_node_operations_def)

lemma (in rga) apply_operations_singleton_Deliver:
  shows "apply_operations (xs @ [(i, Deliver, f)]) = f (apply_operations xs)"
  apply(clarsimp simp add: apply_operations_def ordered_node_operations_def)
done

lemma (in rga) insert_no_failure_lift:
  assumes "(es@es'@[(i, Deliver, Insert e m)]) prefix of i"
          "\<not> (\<exists>n' n'' v b. m = Some n' \<and> (i, Deliver, Insert (n', v, b) n'') \<in> set es')"
  shows   "m = None \<or> (\<exists>m'. m = Some m' \<and> m' \<in> fst ` set (apply_operations es))"
using assms
  apply -
  apply(induction es arbitrary: es' e m rule: rev_induct)
  apply clarsimp

  apply(case_tac m; clarsimp)
  apply(drule insert_no_failure_lift)
  apply clarsimp

  apply clarsimp
  apply(case_tac "aa"; clarsimp)
  apply(clarsimp simp add: apply_operations_singleton_Broadcast)
  apply(case_tac m; clarsimp)
  apply(erule_tac x="(a, Broadcast, b) # es'" in meta_allE)
  apply clarsimp
  apply(erule_tac x=ab in meta_allE)
  apply(erule_tac x=ac in meta_allE)
  apply(erule_tac x=ba in meta_allE)
  apply(erule_tac x="Some aa" in meta_allE)
  apply clarsimp
  apply(subgoal_tac "a=i")
  apply clarsimp
  apply(clarsimp simp add: apply_operations_singleton_Deliver)
  apply(frule_tac oper=b in prefix_opers_option')
  apply force
  apply(case_tac m; clarsimp)
  apply(erule disjE)
prefer 2
  apply clarsimp
  apply(erule_tac x="[]" in meta_allE)
  apply(erule_tac x="aa" in meta_allE)
  apply(erule_tac x="ad" in meta_allE)
  apply(erule_tac x="bb" in meta_allE)
  apply(erule_tac x="y" in meta_allE)
  apply clarsimp
  apply(subgoal_tac "xs @ [(i, Deliver, Insert (aa, ad, bb) y)] prefix of i")
  apply clarsimp
  apply(erule disjE)
  apply clarsimp
defer
  apply clarsimp
  apply(subst (asm) Insert_def) back back back
  apply(subgoal_tac "\<exists>ys. Ordered_List.insert (apply_operations xs) (aa, ad, bb) (Some ae) = Some ys")
prefer 2
  apply(rule insert_no_failure)
  apply force
  apply(frule insert_preserve_element)
  apply clarsimp
oops

lemma (in rga)
  shows "es @ es' @ [(i, Deliver, Insert e (Some m'))] prefix of i \<Longrightarrow> 
    (i, Deliver, Insert (m', v, b) n) \<in> set es \<Longrightarrow> m' \<in> fst ` set (apply_operations es)"
  apply(induction es arbitrary: es' rule: rev_induct)
  apply clarsimp
  apply clarsimp
  apply(erule_tac x="(a, aa, ba) # es'" in meta_allE)
  apply clarsimp
  apply(erule disjE)
  apply clarsimp
  apply(subst apply_operations_singleton_Deliver)
  apply(subst Insert_def)

lemma (in rga) ordered_node_operations_distinct:
  assumes "xs prefix of i"
  shows "distinct (ordered_node_operations xs)"
using assms
  apply (induct xs rule: rev_induct)
  apply simp
  apply (clarsimp simp add: ordered_nodes_opers_append)
  apply safe
  apply force
  apply (clarsimp simp: ordered_node_operations_def)
  apply clarsimp
  apply (frule prefix_distinct)
  apply clarsimp
  apply (subst (asm) ordered_node_operations_def) back back back
  apply clarsimp
  apply (case_tac aa; clarsimp)
  apply (subst (asm) ordered_node_operations_def) back
  apply clarsimp
  apply (case_tac ab; clarsimp)
  apply (subgoal_tac "a=i")
  apply (subgoal_tac "aa=i")
  apply clarsimp
  apply (rule_tac b=Deliver and c=ba in prefix_consistent)
  apply assumption
  apply force
  apply (rule_tac b=Deliver and c=ba in prefix_consistent)
  apply assumption
  apply force
done

lemma (in rga)
  assumes "\<exists>v b. (m, v, b) \<in> set (apply_operations xs)"
  shows "map fst (Delete m (apply_operations xs)) = map fst (apply_operations xs)"
using assms
  apply(induction xs rule: rev_induct)
  apply(clarsimp simp add: Delete_def apply_operations_def ordered_node_operations_def)
  apply clarsimp

  apply(unfold Delete_def)
oops

lemma (in rga) deliver_delete_neq_head:
  shows "carriers i \<noteq> (i, Deliver, Delete e)#ys"
  apply clarsimp
  apply(subgoal_tac "(i, Deliver, Delete e) \<in> set (carriers i)")
  apply(drule sym)
  apply(frule delivery_has_a_cause)
  apply clarsimp
  apply(drule allowed_delete)
  apply clarsimp
  apply(frule local_order_carrier_closed)
  apply clarsimp
  apply(drule delivery_has_a_cause) back
  apply clarsimp
  apply(frule no_message_lost[where j=i]) back
  apply(drule broadcast_causal[rotated, where j=i])
  apply force
  using carriers_head_lt apply blast
  apply force
done

lemma (in rga)
  "apply_operations (xs @ [(i, m, f)]) = apply_operations xs \<or> apply_operations (xs @ [(i, m, f)]) = f (apply_operations xs)"
  by (case_tac m) (auto simp: apply_operations_singleton_Broadcast apply_operations_singleton_Deliver)

lemma (in rga) [simp]: "apply_operations [] = []"
  by (auto simp: apply_operations_def)

lemma (in rga) 
  assumes "xs prefix of i"
  shows "(apply_operations xs) = [] \<longleftrightarrow> (xs = [] \<or> (\<forall>i m f. (i, m, f) \<in> set xs \<longrightarrow> m = Broadcast))"
  using assms apply -
  apply standard
  apply (induct xs rule: rev_induct)
  apply clarsimp
  apply clarsimp
  apply (case_tac aa)
  apply (clarsimp simp: apply_operations_singleton_Broadcast)
  apply force
  apply (clarsimp simp: apply_operations_singleton_Deliver)

  apply (subgoal_tac "(a, Deliver, b) \<in> set (xs @ [(a, Deliver, b)])")
  apply (frule prefix_events_option, assumption)
  apply clarsimp
  apply (rule conjI)
  apply clarsimp
  apply (erule disjE)
  apply clarsimp
oops

lemma (in rga)
  assumes "es@[(i, Deliver, Insert e n)] prefix of i"
          "xs = apply_operations es"
  shows   "\<exists>ys zs. Insert e n xs = ys@[e]@zs \<and> xs = ys@zs"
using assms
  apply(subst Insert_def)
  apply(subgoal_tac "\<exists>ys. insert xs e n = Some ys")
  apply(clarsimp)
  apply(drule insert_Some_split)
  apply clarsimp
  apply(rule insert_no_failure)
  apply(drule insert_no_failure_lift)
  apply(erule disjE, clarsimp)
  apply clarsimp

lemma (in rga)
  shows "es prefix of i \<Longrightarrow>
         distinct (map fst (apply_operations es))"
  apply(induction es rule: rev_induct)
  apply simp
  apply clarsimp
  apply(case_tac "aa"; clarsimp simp add: apply_operations_singleton_Broadcast)
  apply force
  apply(frule_tac oper="b" in prefix_opers_option')
  apply(subgoal_tac "a=i")
  apply clarsimp
  apply(rule prefix_consistent, assumption, force)
  apply(erule disjE; (erule exE)+; clarsimp)
defer
  apply(clarsimp simp add: apply_operations_singleton_Deliver)

lemma (in rga) delete_no_failure_technical:
  assumes "es @ es' @ [(i, Deliver, Delete n)] prefix of i" "\<forall>v b n'. (i, Deliver, Insert (n, v, b) n') \<notin> set es'"
  shows   "delete (apply_operations es) n = Some ys"
using assms
apply (induct es arbitrary: n ys es' rule: rev_induct)
apply clarsimp
defer
apply clarsimp
apply (case_tac aa)
apply (clarsimp simp: apply_operations_singleton_Broadcast)
apply (erule_tac x=n in meta_allE)
apply (erule_tac x=ys in meta_allE)
apply (erule_tac x="(a, Broadcast, b) # es'" in meta_allE)
apply clarsimp

apply clarsimp
apply (subgoal_tac "(a, Deliver, b) \<in> set (xs @ (a, Deliver, b) # es' @ [(i, Deliver, Delete n)])")
apply (frule prefix_events_option, assumption)
apply (erule disjE)
apply (erule exE)+
apply clarsimp

apply (clarsimp simp: apply_operations_singleton_Deliver)
apply (subst Delete_def)
apply (case_tac "(apply_operations xs)")
apply clarsimp
defer

apply simp

(*
apply (erule_tac x=ys in meta_allE)
apply (erule_tac x="(i, Deliver, Delete x) # es'" in meta_allE)
apply clarsimp
apply (subgoal_tac "\<forall>v b n'. Insert (n, v, b) n' \<noteq> Delete x")
apply (erule meta_impE)
using Insert_neq_Delete apply fastforce
apply (clarsimp simp: apply_operations_singleton_Deliver)
apply (clarsimp simp: Delete_def)
*)

oops

lemma (in rga) delete_no_failure:
  assumes "es @ [(i, Deliver, Delete n)] prefix of i"
  shows   "\<exists>ys. delete (apply_operations es) n = Some ys"
using assms delete_no_failure_technical[where es'="[]"] by force

lemma (in rga) insert_no_failure:
  assumes "es @ [(i, Deliver, Insert e n)] prefix of i"
  shows   "\<exists>ys. insert (apply_operations es) e n = Some ys"
oops

lemma (in rga) id_preserve_by_delete:
  assumes "xs @ [(i, Deliver, Delete n)] prefix of i"
  shows   "map fst (Delete n (apply_operations xs)) = map fst (apply_operations xs)"
  using assms
  apply (subst Delete_def)
  apply (drule delete_no_failure)
  apply clarsimp
  apply (drule delete_element_preserve)
  apply force
done

lemma (in rga) id_preserve_by_insert:
  assumes "xs @ [(i, Deliver, Insert e n)] prefix of i"
  shows   "set (map fst (Insert e n (apply_operations xs))) = set (map fst (apply_operations xs)) \<union> {fst e}"
  using assms
  apply (subst Insert_def)
  apply (rule insert_preserve_element)
  apply (rule insert_no_failure)
  
  
lemma (in rga)
  assumes "xs prefix of i" "x \<in> set (map fst (apply_operations xs))"
  shows   "x \<in> set (map fst (Insert e n (apply_operations xs)))"
using assms
  apply (clarsimp simp add: Insert_def)
  apply (subgoal_tac "\<exists>ys. insert (apply_operations xs) e n = Some ys")
  apply clarsimp
  apply (induct xs arbitrary: e n rule: rev_induct)
  apply clarsimp
  apply (case_tac xa)
  apply simp
  apply (case_tac ba)
  apply (force simp: apply_operations_singleton_Broadcast)
  apply simp
  apply (subgoal_tac "(a, Deliver, c) \<in> set (xs @ [(a, Deliver, c)])")
  apply (frule prefix_events_option, assumption)
  apply (erule disjE)
  apply (erule exE)+
  apply (simp add: apply_operations_singleton_Deliver)
  

  apply clarsimp
  thm prefix_opers_option



  apply clarsimp
  apply (case_tac "apply_operations xs")
  apply clarsimp
  apply clarsimp
  apply (cases n)
  apply clarsimp
  
oops

lemma (in rga)
  "es prefix of i \<Longrightarrow> Insert e n \<in> set (ordered_node_operations es) \<Longrightarrow> \<exists>v b. (fst e, v, b) \<in> set (apply_operations es)"
apply (induct es rule: rev_induct)
apply clarsimp
apply (clarsimp simp: ordered_nodes_opers_append)
apply (erule_tac disjE)
apply (case_tac aa)
apply clarsimp
apply force
apply clarsimp
find_theorems "apply_operations (?xs @ [(?a, ?aa, ?b)])"
oops

lemma (in rga)
  assumes "\<exists>ys. xs@(i, Deliver, Delete e)#ys = carriers i"
  shows   "\<exists>v b. (e, v, b) \<in> set (apply_operations xs)"
using assms
  apply -
  apply clarsimp
  apply(induction xs rule: rev_induct)
  apply clarsimp
  using deliver_delete_neq_head apply metis
  apply clarsimp
oops
(*
  apply(drule apply_operations_singleton[rotated], rule refl)  
  apply clarsimp
  using deliver_delete_neq_head
*)

lemma (in rga) Insert_Insert_commute:
  assumes "es prefix of i"
          "{Insert e n, Insert e' n'} \<subseteq> set (ordered_node_operations es)"
          "hb.concurrent (Insert e n) (Insert e' n')"
  shows   "(Insert e n \<circ> Insert e' n') = (Insert e' n' \<circ> Insert e n)"
using assms
apply (subst Insert_def)+
apply (rule ext)
apply clarsimp
apply (insert insert_commutes[of e e' _ n n'])
apply (erule_tac x=x in meta_allE)
apply (subgoal_tac "distinct (map fst (e # e' # x))")
apply (subgoal_tac "n = None \<or> n \<noteq> Some (fst e')")
apply (subgoal_tac "n' = None \<or> n' \<noteq> Some (fst e)")
apply clarsimp
apply (subgoal_tac "\<exists>ys. insert x e n = Some ys")
apply (subgoal_tac "\<exists>ys'. insert x e' n' = Some ys'")
apply clarsimp

defer
defer

apply(subgoal_tac "(i, Deliver, Insert e' n') \<in> set (carriers i)")
apply(subgoal_tac "(i, Deliver, Insert e n) \<in> set (carriers i)")
apply (rule insert_commute_assms)
apply clarsimp
apply (rule conjI)
apply assumption
apply assumption
apply clarsimp
apply simp
apply (rule prefix_opers_in_carrier)
apply assumption
apply simp
apply (rule prefix_opers_in_carrier)
apply assumption
apply simp

apply(subgoal_tac "(i, Deliver, Insert e' n') \<in> set (carriers i)")
apply(subgoal_tac "(i, Deliver, Insert e n) \<in> set (carriers i)")
apply (rule insert_commute_assms)
apply clarsimp
apply (rule conjI)
apply assumption+
apply clarsimp
apply simp
apply (rule prefix_opers_in_carrier)
apply assumption
apply simp
apply (rule prefix_opers_in_carrier)
apply assumption
apply simp

defer
oops

corollary (in rga) hb_consistent_prefix:
  assumes "xs prefix of i"
  shows   "hb.hb_consistent (ordered_node_operations xs)"
using assms
apply (clarsimp simp: prefix_of_carrier_def)
apply (rule_tac i=i in hb_consistent_technical)
apply (subst carriers_compatible)
apply(subgoal_tac "xs = [] \<or> (\<exists>c. xs = [c]) \<or> (length (xs) > 1)")
apply (erule disjE)
apply clarsimp
apply (erule disjE)
apply clarsimp
apply (drule horror_size3)
apply assumption
apply clarsimp
apply clarsimp
apply (rule_tac x=xsa in exI)
apply (rule_tac x=ysa in exI)
apply (rule_tac x="zs@ys" in exI)
apply (metis Cons_eq_appendI append_assoc)
apply force
done

lemma (in rga) Delete_Delete_commute:
  shows "Delete xa \<circ> Delete xb = Delete xb \<circ> Delete xa"
oops

lemma (in rga) Delete_Insert_commute:
  shows "Delete xa \<circ> Insert x ya = Insert x ya \<circ> Delete xa"
oops

lemma (in rga) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_elems_commute (ordered_node_operations xs)"
using assms
  apply (auto simp: hb.concurrent_elems_commute_def)
  apply (frule_tac i=i in prefix_opers_option[rotated])
  apply clarsimp
  apply (frule_tac i=i in prefix_opers_option[rotated]) back
  apply clarsimp
  apply safe
  using Delete_Delete_commute apply blast
  using Delete_Insert_commute apply blast
  using Delete_Insert_commute[symmetric] apply blast
  using Insert_Insert_commute apply blast
done

lemma (in rga)
  assumes "distinct (map fst xs)"
  shows   "distinct (map fst ((Delete n) xs)) \<or> xs = []"
using assms
apply -
apply (induct xs)
apply simp
apply clarsimp
apply (erule disjE)
defer
apply clarsimp



apply (clarsimp simp: Delete_def)
oops

corollary (in rga) main_result_of_paper:
  assumes "set (ordered_node_operations xs) = set (ordered_node_operations ys)"
          "xs prefix of i"
          "ys prefix of j"
  shows  "apply_operations xs = apply_operations ys"
using assms by (auto simp: apply_operations_def intro: hb.convergence_point concurrent_operations_commute ordered_node_operations_distinct hb_consistent_prefix)

end