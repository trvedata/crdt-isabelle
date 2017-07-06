(* Victor B. F. Gomes, University of Cambridge
   Martin Kleppmann, University of Cambridge
   Dominic P. Mulligan, University of Cambridge
   Alastair R. Beresford, University of Cambridge
*)

subsection\<open>Network\<close>

theory
  RGA
imports
  Network
  Ordered_List
  "~~/src/HOL/Library/Code_Target_Numeral"
begin
  
datatype ('id, 'v) operation =
  Insert "('id, 'v) elt" "'id option" |
  Delete "'id"

fun interpret_opers :: "('id::linorder, 'v) operation \<Rightarrow> ('id, 'v) elt list \<rightharpoonup> ('id, 'v) elt list" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_opers (Insert e n) xs  = insert xs e n" |
  "interpret_opers (Delete n)   xs  = delete xs n"

definition element_ids :: "('id, 'v) elt list \<Rightarrow> 'id set" where
 "element_ids list \<equiv> set (map fst list)"

definition valid_rga_msg :: "('id, 'v) elt list \<Rightarrow> 'id \<times> ('id::linorder, 'v) operation \<Rightarrow> bool" where
 "valid_rga_msg list msg \<equiv> case msg of
    (i, Insert e  None     ) \<Rightarrow> fst e = i |
    (i, Insert e (Some pos)) \<Rightarrow> fst e = i \<and> pos \<in> element_ids list |
    (i, Delete         pos ) \<Rightarrow> pos \<in> element_ids list"
 
export_code Insert interpret_opers valid_rga_msg in OCaml file "ocaml/rga.ml"

(* Replicated Growable Array Network *)
locale rga = network_with_constrained_ops _ interpret_opers "[]" valid_rga_msg
  
definition indices :: "('id \<times> ('id, 'v) operation) event list \<Rightarrow> 'id list" where
  "indices xs \<equiv>
     List.map_filter (\<lambda>x. case x of Deliver (i, Insert e n) \<Rightarrow> Some (fst e) | _ \<Rightarrow> None) xs"

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
  shows "indices [Deliver (i, Insert e n)] = [fst e]"
by(auto simp: indices_def map_filter_def)

lemma indices_Deliver_Delete [simp]:
  shows "indices [Deliver (i, Delete n)] = []"
by(auto simp: indices_def map_filter_def)

lemma (in rga) idx_in_elem_inserted [intro]:
  assumes "Deliver (i, Insert e n) \<in> set xs"
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
  apply(case_tac "b"; clarsimp)
  apply(auto split: bind_splits simp add: interp_msg_def)
  apply(metis (no_types, hide_lams) Un_insert_right image_eqI insert_iff insert_preserve_indices
        option.sel prefix_of_appendD prod.sel(1) sup_bot.comm_neutral)
  apply(metis Un_insert_right fst_conv insert_iff insert_preserve_indices option.sel)
  apply(metis (no_types, hide_lams) Un_insert_right insert_iff insert_preserve_indices' option.sel
        prefix_of_appendD sup_bot.comm_neutral)
  apply(metis delete_preserve_indices fst_conv image_eqI prefix_of_appendD)
  using delete_preserve_indices apply blast
done

lemma (in rga) delete_does_not_change_element_ids:
  assumes "es @ [Deliver (i, Delete n)] prefix of j"
  and "apply_operations es = Some xs1"
  and "apply_operations (es @ [Deliver (i, Delete n)]) = Some xs2"
  shows "element_ids xs1 = element_ids xs2"
proof -
  have "indices es = indices (es @ [Deliver (i, Delete n)])"
    by simp
  then show ?thesis
    by (metis (no_types) assms prefix_of_appendD rga.apply_opers_idx_elems rga_axioms)
qed

lemma (in rga) someone_inserted_id:
  assumes "es @ [Deliver (i, Insert (k, v, f) n)] prefix of j"
  and "apply_operations es = Some xs1"
  and "apply_operations (es @ [Deliver (i, Insert (k, v, f) n)]) = Some xs2"
  and "a \<in> element_ids xs2"
  and "a \<noteq> k"
  shows "a \<in> element_ids xs1"
using assms apply_opers_idx_elems by auto

lemma (in rga) deliver_insert_exists:
  assumes "es prefix of j"
      and "apply_operations es = Some xs"
      and "a \<in> element_ids xs"
    shows "\<exists>i v f n. Deliver (i, Insert (a, v, f) n) \<in> set es"
using assms unfolding element_ids_def
  apply(induction es arbitrary: xs rule: rev_induct; clarsimp)
  apply(case_tac x; clarsimp)
  apply(metis image_eqI prefix_of_appendD prod.sel(1))
  apply(case_tac "bb"; clarsimp)
  defer
  apply(drule prefix_of_appendD, clarsimp simp add: bind_eq_Some_conv interp_msg_def)
  apply(metis delete_preserve_indices image_eqI prod.sel(1))
  apply(case_tac "aba=a")
  apply blast
  apply(subgoal_tac "\<exists>xs'. apply_operations xsa = Some xs'")
  defer
  apply(meson bind_eq_Some_conv)
  apply(erule exE)
  apply(metis (no_types, lifting) someone_inserted_id apply_operations_Deliver element_ids_def
    image_eqI prefix_of_appendD prod.sel(1) set_map)
done

lemma (in rga) insert_in_apply_set:
  assumes "es @ [Deliver (i, Insert e (Some a))] prefix of j"
      and "Deliver (i', Insert e' n) \<in> set es"
      and "apply_operations es = Some s"
    shows "fst e' \<in> element_ids s"
using assms apply_opers_idx_elems idx_in_elem_inserted prefix_of_appendD by blast
  
lemma (in rga) insert_msg_id:
  assumes "Broadcast (i, Insert e n) \<in> set (history j)"
  shows "fst e = i"
  apply(subgoal_tac "\<exists>state. valid_rga_msg state (i, Insert e n)")
  defer
  using assms broadcast_is_valid apply blast
  apply(erule exE)
  apply(unfold valid_rga_msg_def)
  apply(clarsimp)
  apply(case_tac n)
  apply(simp, simp)
done

lemma (in rga) allowed_insert:
  assumes "Broadcast (i, Insert e n) \<in> set (history j)"
  shows "n = None \<or> (\<exists>i' e' n'. n = Some (fst e') \<and> Deliver (i', Insert e' n') \<sqsubset>\<^sup>j Broadcast (i, Insert e n))"
proof -
  obtain pre where 1: "pre @ [Broadcast (i, Insert e n)] prefix of j"
    using assms events_before_exist by blast
  from this obtain state where 2: "apply_operations pre = Some state" and 3: "valid_rga_msg state (i, Insert e n)"
    using broadcast_only_valid_msgs by blast
  show "n = None \<or> (\<exists>i' e' n'. n = Some (fst e') \<and> Deliver (i', Insert e' n') \<sqsubset>\<^sup>j Broadcast (i, Insert e n))"
  proof(cases n)
    fix a
    assume 4: "n = Some a"
    hence "a \<in> element_ids state" and 5: "fst e = i"
      using 3 by(clarsimp simp add: valid_rga_msg_def)+
    from this have "\<exists>i' v' f' n'. Deliver (i', Insert (a, v', f') n') \<in> set pre"
      using deliver_insert_exists 2 1 by blast
    thus "n = None \<or> (\<exists>i' e' n'. n = Some (fst e') \<and> Deliver (i', Insert e' n') \<sqsubset>\<^sup>j Broadcast (i, Insert e n))"
      using events_in_local_order 1 4 5 by(metis fst_conv)
  qed simp
qed
    
lemma (in rga) allowed_delete:
  assumes "Broadcast (i, Delete x) \<in> set (history j)"
  shows "\<exists>i' n' v b. Deliver (i', Insert (x, v, b) n') \<sqsubset>\<^sup>j Broadcast (i, Delete x)"
proof -
  obtain pre where 1: "pre @ [Broadcast (i, Delete x)] prefix of j"
    using assms events_before_exist by blast
  from this obtain state where 2: "apply_operations pre = Some state"
      and "valid_rga_msg state (i, Delete x)"
    using broadcast_only_valid_msgs by blast
  hence "x \<in> element_ids state"
    using apply_opers_idx_elems by(simp add: valid_rga_msg_def)
  hence "\<exists>i' v' f' n'. Deliver (i', Insert (x, v', f') n') \<in> set pre"
    using deliver_insert_exists 1 2 by blast
  thus "\<exists>i' n' v b. Deliver (i', Insert (x, v, b) n') \<sqsubset>\<^sup>j Broadcast (i, Delete x)"
    using events_in_local_order 1 by blast
qed

lemma (in rga) insert_id_unique:
  assumes "fst e1 = fst e2"
  and "Broadcast (i1, Insert e1 n1) \<in> set (history i)"
  and "Broadcast (i2, Insert e2 n2) \<in> set (history j)"
  shows "Insert e1 n1 = Insert e2 n2"
using assms insert_msg_id msg_id_unique Pair_inject fst_conv by metis

lemma (in rga) allowed_delete_deliver:
  assumes "Deliver (i, Delete x) \<in> set (history j)"
    shows "\<exists>i' n' v b. Deliver (i', Insert (x, v, b) n') \<sqsubset>\<^sup>j Deliver (i, Delete x)"
  using assms by (meson allowed_delete bot_least causal_broadcast delivery_has_a_cause insert_subset)

lemma (in rga) allowed_delete_deliver_in_set:
  assumes "(es@[Deliver (i, Delete m)]) prefix of j"
  shows   "\<exists>i' n v b. Deliver (i', Insert (m, v, b) n) \<in> set es"
by(metis (no_types, lifting) Un_insert_right insert_iff list.simps(15) assms
    local_order_prefix_closed_last rga.allowed_delete_deliver rga_axioms set_append subsetCE prefix_to_carriers)

lemma (in rga) allowed_insert_deliver:
  assumes "Deliver (i, Insert e n) \<in> set (history j)"
  shows   "n = None \<or> (\<exists>i' n' n'' v b. n = Some n' \<and> Deliver (i', Insert (n', v, b) n'') \<sqsubset>\<^sup>j Deliver (i, Insert e n))"
proof -
  obtain ja where 1: "Broadcast (i, Insert e n) \<in> set (history ja)"
    using assms delivery_has_a_cause by blast
  show "n = None \<or> (\<exists>i' n' n'' v b. n = Some n' \<and> Deliver (i', Insert (n', v, b) n'') \<sqsubset>\<^sup>j Deliver (i, Insert e n))"
  proof(cases n)
    fix a
    assume 3: "n = Some a"
    from this obtain i' e' n' where 4: "Some a = Some (fst e')" and
        2: "Deliver (i', Insert e' n') \<sqsubset>\<^sup>ja Broadcast (i, Insert e (Some a))"
      using allowed_insert 1 by blast
    hence "Deliver (i', Insert e' n') \<in> set (history ja)" and "Broadcast (i, Insert e (Some a)) \<in> set (history ja)"
      using local_order_carrier_closed by simp+
    from this obtain jaa where "Broadcast (i, Insert e (Some a)) \<in> set (history jaa)"
      using delivery_has_a_cause by simp
    have "\<exists>i' n' n'' v b. n = Some n' \<and> Deliver (i', Insert (n', v, b) n'') \<sqsubset>\<^sup>j Deliver (i, Insert e n)"
      using 2 3 4 by(metis assms causal_broadcast prod.collapse)
    thus "n = None \<or> (\<exists>i' n' n'' v b. n = Some n' \<and> Deliver (i', Insert (n', v, b) n'') \<sqsubset>\<^sup>j Deliver (i, Insert e n))"
      by auto
  qed simp
qed

lemma (in rga) allowed_insert_deliver_in_set:
  assumes "(es@[Deliver (i, Insert e m)]) prefix of j"
  shows   "m = None \<or> (\<exists>i' m' n v b. m = Some m' \<and> Deliver (i', Insert (m', v, b) n) \<in> set es)"
by(metis assms Un_insert_right insert_subset list.simps(15) set_append prefix_to_carriers
    allowed_insert_deliver local_order_prefix_closed_last)

lemma (in rga) Insert_no_failure:
  assumes "es @ [Deliver (i, Insert e n)] prefix of j" 
      and "apply_operations es = Some s"
    shows "\<exists>ys. insert s e n = Some ys"
by(metis (no_types, lifting) element_ids_def allowed_insert_deliver_in_set assms fst_conv
    insert_in_apply_set insert_no_failure set_map)

lemma (in rga) delete_no_failure:
  assumes "es @ [Deliver (i, Delete n)] prefix of j"
      and "apply_operations es = Some s"
    shows "\<exists>ys. delete s n = Some ys"
proof -
  obtain i' na v b where 1: "Deliver (i', Insert (n, v, b) na) \<in> set es"
    using assms allowed_delete_deliver_in_set by blast
  also have "fst (n, v, b) \<in> set (indices es)"
    using assms idx_in_elem_inserted calculation by blast
  from this assms and 1 show "\<exists>ys. delete s n = Some ys"
    apply -
    apply(rule delete_no_failure)
    apply(metis apply_opers_idx_elems element_ids_def prefix_of_appendD prod.sel(1) set_map)
    done
qed

lemma (in rga) Insert_equal:
  assumes "fst e1 = fst e2"
      and "Broadcast (i1, Insert e1 n1) \<in> set (history i)"
      and "Broadcast (i2, Insert e2 n2) \<in> set (history j)"
    shows "Insert e1 n1 = Insert e2 n2"
using insert_id_unique assms by simp

lemma (in rga) same_insert:
  assumes "fst e1 = fst e2"
      and "xs prefix of i"
      and "(i1, Insert e1 n1) \<in> set (node_deliver_messages xs)"
      and "(i2, Insert e2 n2) \<in> set (node_deliver_messages xs)"
    shows "Insert e1 n1 = Insert e2 n2"
proof -
  have "Deliver (i1, Insert e1 n1) \<in> set (history i)"
    using assms by(auto simp add: node_deliver_messages_def prefix_msg_in_history)
  from this obtain j where 1: "Broadcast (i1, Insert e1 n1) \<in> set (history j)"
    using delivery_has_a_cause by blast
  have "Deliver (i2, Insert e2 n2) \<in> set (history i)"
    using assms by(auto simp add: node_deliver_messages_def prefix_msg_in_history)
  from this obtain k where 2: "Broadcast (i2, Insert e2 n2) \<in> set (history k)"
    using delivery_has_a_cause by blast
  show "Insert e1 n1 = Insert e2 n2"
    by(rule Insert_equal; force simp add: assms intro: 1 2)
qed
  
lemma (in rga) insert_commute_assms:
  assumes "{Deliver (i, Insert e n), Deliver (i', Insert e' n')} \<subseteq> set (history j)"
      and "hb.concurrent (i, Insert e n) (i', Insert e' n')"
    shows "n = None \<or> n \<noteq> Some (fst e')"
using assms
  apply(clarsimp simp: hb.concurrent_def)
  apply(cases e')
  apply clarsimp
  apply(frule delivery_has_a_cause)
  apply(frule delivery_has_a_cause, clarsimp)
  apply(frule allowed_insert)
  apply clarsimp
  apply(metis Insert_equal delivery_has_a_cause fst_conv hb.intros(2) insert_subset
    local_order_carrier_closed insert_msg_id)
done

lemma subset_reorder:
  assumes "{a, b} \<subseteq> c"
  shows "{b, a} \<subseteq> c"
using assms by simp

lemma (in rga) Insert_Insert_concurrent:
  assumes "{Deliver (i, Insert e k), Deliver (i', Insert e' (Some m))} \<subseteq> set (history j)"
      and "hb.concurrent (i, Insert e k) (i', Insert e' (Some m))"
    shows "fst e \<noteq> m"
  by(metis assms subset_reorder hb.concurrent_comm insert_commute_assms option.simps(3))

lemma (in rga) insert_valid_assms:
 assumes "Deliver (i, Insert e n) \<in> set (history j)"
   shows "n = None \<or> n \<noteq> Some (fst e)"
  using assms by(meson allowed_insert_deliver hb.concurrent_def hb.less_asym insert_subset
      local_order_carrier_closed rga.insert_commute_assms rga_axioms)

lemma (in rga) Insert_Delete_concurrent:
  assumes "{Deliver (i, Insert e n), Deliver (i', Delete n')} \<subseteq> set (history j)"
      and "hb.concurrent (i, Insert e n) (i', Delete n')"
    shows "n' \<noteq> fst e"
by (metis assms Insert_equal allowed_delete delivery_has_a_cause fst_conv hb.concurrent_def
  hb.intros(2) insert_subset local_order_carrier_closed rga.insert_msg_id rga_axioms)

lemma (in rga) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(rule ext)
  apply(simp add: kleisli_def interp_msg_def)
  apply(case_tac b; case_tac ba)
  apply clarsimp
  apply(case_tac "ab = ad")
  apply(subgoal_tac "(ab, ac, bb) = (ad, ae, bc) \<and> x12a = x12")
  apply force
  defer
  apply(subgoal_tac "Ordered_List.insert x (ab, ac, bb) x12 \<bind> (\<lambda>x. Ordered_List.insert x (ad, ae, bc) x12a) = Ordered_List.insert x (ad, ae, bc) x12a \<bind> (\<lambda>x. Ordered_List.insert x (ab, ac, bb) x12)")
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
  apply(subgoal_tac "Ordered_List.insert x (ab, ac, bb) x12 \<bind> (\<lambda>x. Ordered_List.delete x x2) = delete x x2 \<bind> (\<lambda>x. Ordered_List.insert x (ab, ac, bb) x12)")
  apply(metis (no_types, lifting) Option.bind_cong interpret_opers.simps)
  apply(rule insert_delete_commute)
  apply(rule Insert_Delete_concurrent)
  apply clarsimp
  using prefix_msg_in_history apply blast
  apply(clarsimp)
  apply(clarsimp simp del: delete.simps)
  apply(subgoal_tac "delete x x2 \<bind> (\<lambda>x. insert x (ab, ac, bb) x12) = Ordered_List.insert x (ab, ac, bb) x12 \<bind> (\<lambda>x. delete x x2)")
  apply(metis (no_types, lifting) Option.bind_cong interpret_opers.simps)
  apply(rule insert_delete_commute[symmetric])
  apply(rule Insert_Delete_concurrent)
  using prefix_msg_in_history apply blast
  apply(subst (asm) hb.concurrent_comm)
  apply assumption
  apply(clarsimp simp del: delete.simps)
  apply(subgoal_tac "delete x x2 \<bind> (\<lambda>x. delete x x2a) = delete x x2a \<bind> (\<lambda>x. delete x x2)")
  apply(metis (mono_tags, lifting) Option.bind_cong interpret_opers.simps(2))
  apply(rule delete_commutes)
  using same_insert apply force
done

corollary (in rga) concurrent_operations_commute':
  shows "hb.concurrent_ops_commute (node_deliver_messages (history i))"
by (meson concurrent_operations_commute append.right_neutral prefix_of_node_history_def)

lemma (in rga) apply_operations_never_fails:
  assumes "xs prefix of i"
  shows "apply_operations xs \<noteq> None"
using assms proof(induction xs rule: rev_induct)
  show "apply_operations [] \<noteq> None"
    by clarsimp
next
  fix x xs
  assume 1: "xs prefix of i \<Longrightarrow> apply_operations xs \<noteq> None"
    and 2: "xs @ [x] prefix of i"
  hence 3: "xs prefix of i"
    by auto
  show "apply_operations (xs @ [x]) \<noteq> None"
  proof(cases x)
    fix b
    assume "x = Broadcast b"
    thus "apply_operations (xs @ [x]) \<noteq> None"
      using 1 3 by clarsimp
  next
    fix d
    assume 4: "x = Deliver d"
    thus "apply_operations (xs @ [x]) \<noteq> None"
    proof(cases d; clarify)
      fix a b
      assume 5: "x = Deliver (a, b)"
      show "\<exists>y. apply_operations (xs @ [Deliver (a, b)]) = Some y"
      proof(cases b; clarify)
        fix aa aaa ba x12
        assume 6: "b = Insert (aa, aaa, ba) x12"
        show "\<exists>y. apply_operations (xs @ [Deliver (a, Insert (aa, aaa, ba) x12)]) = Some y"
          apply(clarsimp simp add: 1 interp_msg_def split!: bind_splits)
           apply(simp add: "1" "3")
          apply(rule rga.Insert_no_failure, rule rga_axioms)
          using 4 5 6 2 apply force+
          done
      next
        fix x2
        assume 6: "b = Delete x2"
        show "\<exists>y. apply_operations (xs @ [Deliver (a, Delete x2)]) = Some y"
          apply(clarsimp simp add: interp_msg_def split!: bind_splits)
           apply(simp add: 1 3)
          apply(rule delete_no_failure)
          using 4 5 6 2 apply force+
          done
      qed
    qed
  qed
qed

lemma (in rga) apply_operations_never_fails':
  shows "apply_operations (history i) \<noteq> None"
by(meson apply_operations_never_fails append.right_neutral prefix_of_node_history_def)

corollary (in rga) rga_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
  using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext
      concurrent_operations_commute node_deliver_messages_distinct hb_consistent_prefix)

subsection\<open>Strong eventual consistency\<close>
              
context rga begin

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "[]"
proof(standard; clarsimp)
  fix xsa i
  assume "xsa prefix of i"
  thus "hb.hb_consistent (node_deliver_messages xsa)"
    by(auto simp add: hb_consistent_prefix)
next
  fix xsa i
  assume "xsa prefix of i"
  thus "distinct (node_deliver_messages xsa)"
    by(auto simp add: node_deliver_messages_distinct)
next
  fix xsa i
  assume "xsa prefix of i"
  thus "hb.concurrent_ops_commute (node_deliver_messages xsa)"
    by(auto simp add: concurrent_operations_commute)
next
  fix xs a b state xsa x
  assume "hb.apply_operations xs [] = Some state"
    and "node_deliver_messages xsa = xs @ [(a, b)]"
    and "xsa prefix of x"
  thus "\<exists>y. interp_msg (a, b) state = Some y"
   by(metis (no_types, lifting) apply_operations_def bind.bind_lunit not_None_eq
       hb.apply_operations_Snoc kleisli_def apply_operations_never_fails interp_msg_def)
next
  fix xs a b xsa x
  assume "node_deliver_messages xsa = xs @ [(a, b)]"
    and "xsa prefix of x"
  thus "\<exists>xsa. Ex (op prefix of xsa) \<and> node_deliver_messages xsa = xs"
    using drop_last_message by blast
qed

end
  
interpretation trivial_rga_implementation: rga "\<lambda>x. []"
  by(standard, auto simp add: trivial_node_histories.history_order_def
      trivial_node_histories.prefix_of_node_history_def)

end