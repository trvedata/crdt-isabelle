theory
  Network
imports
  Convergence
begin

section\<open>Model of the network\<close>

subsection\<open>Node histories\<close>

locale node_histories = 
  fixes history :: "nat \<Rightarrow> 'evt list"
  assumes histories_distinct [intro!, simp]: "distinct (history i)"

lemma (in node_histories) history_finite:
  shows "finite (set (history i))"
by auto
    
definition (in node_histories) history_order :: "'evt \<Rightarrow> nat \<Rightarrow> 'evt \<Rightarrow> bool" ("_/ \<sqsubset>\<^sup>_/ _" [50,1000,50]50) where
  "x \<sqsubset>\<^sup>i z \<equiv> \<exists>xs ys zs. xs@x#ys@z#zs = history i"

lemma (in node_histories) node_total_order_trans:
  assumes "e1 \<sqsubset>\<^sup>i e2"
      and "e2 \<sqsubset>\<^sup>i e3"
    shows "e1 \<sqsubset>\<^sup>i e3"
using assms unfolding history_order_def
  apply clarsimp
  apply(rule_tac x=xs in exI, rule_tac x="ys @ e2 # ysa" in exI, rule_tac x=zsa in exI)
  apply(subgoal_tac "xs @ e1 # ys = xsa \<and> zs = ysa @ e3 # zsa")
  apply clarsimp
  apply(rule_tac xs="history i" and ys="[e2]" in pre_suf_eq_distinct_list)
  apply auto
done

lemma (in node_histories) local_order_carrier_closed:
  assumes "e1 \<sqsubset>\<^sup>i e2"
    shows "{e1,e2} \<subseteq> set (history i)"
using assms by (clarsimp simp add: history_order_def)
  (metis in_set_conv_decomp Un_iff Un_subset_iff insert_subset list.simps(15) set_append set_subset_Cons)+

lemma (in node_histories) node_total_order_irrefl:
  shows "\<not> (e \<sqsubset>\<^sup>i e)"
by(clarsimp simp add: history_order_def)
  (metis Un_iff histories_distinct distinct_append distinct_set_notin list.set_intros(1) set_append)

lemma (in node_histories) node_total_order_antisym:
  assumes "e1 \<sqsubset>\<^sup>i e2"
      and "e2 \<sqsubset>\<^sup>i e1"
    shows "False"
  using assms node_total_order_irrefl node_total_order_trans by blast

lemma (in node_histories) node_order_is_total:
  assumes "e1 \<in> set (history i)"
      and "e2 \<in> set (history i)"
      and "e1 \<noteq> e2"
    shows "e1 \<sqsubset>\<^sup>i e2 \<or> e2 \<sqsubset>\<^sup>i e1"
  using assms unfolding history_order_def
  by (metis list_split_two_elems histories_distinct)

definition (in node_histories) prefix_of_node_history :: "'evt list \<Rightarrow> nat \<Rightarrow> bool" (infix "prefix of" 50) where
  "xs prefix of i \<equiv> \<exists>ys. xs@ys = history i"

lemma (in node_histories) carriers_head_lt:
  assumes "y#ys = history i"
  shows   "\<not>(x \<sqsubset>\<^sup>i y)"
using assms unfolding history_order_def
  apply -
  apply clarsimp
  apply (subgoal_tac "xs @ x # ysa = [] \<and> zs = ys")
  apply clarsimp
  apply (rule_tac xs="history i" and ys="[y]" in pre_suf_eq_distinct_list)
  apply auto
done

lemma (in node_histories) prefix_of_ConsD [dest]:
  assumes "x # xs prefix of i"
    shows "[x] prefix of i"
using assms by(auto simp: prefix_of_node_history_def)

lemma (in node_histories) prefix_of_appendD [dest]:
  assumes "xs @ ys prefix of i"
    shows "xs prefix of i"
using assms by(auto simp: prefix_of_node_history_def)

lemma (in node_histories) prefix_distinct:
  assumes "xs prefix of i"
    shows "distinct xs"
using assms by(clarsimp simp: prefix_of_node_history_def) (metis histories_distinct distinct_append)

lemma (in node_histories) prefix_to_carriers [intro]:
  assumes "xs prefix of i"
    shows "set xs \<subseteq> set (history i)"
using assms by(clarsimp simp: prefix_of_node_history_def) (metis Un_iff set_append)

lemma (in node_histories) local_order_prefix_closed:
  assumes "x \<sqsubset>\<^sup>i y"
      and "xs prefix of i"
      and "y \<in> set xs"
    shows "x \<in> set xs"
using assms
  apply -
  apply (frule prefix_distinct)
  apply (insert histories_distinct[where i=i])
  apply (clarsimp simp: history_order_def prefix_of_node_history_def)
  apply (frule split_list)
  apply clarsimp
  apply (subgoal_tac "ysb = xsa @ x # ysa \<and> zsa @ ys = zs")
  apply clarsimp
  apply (rule_tac xs="history i" and ys="[y]" in pre_suf_eq_distinct_list)
  apply auto
done

lemma (in node_histories) local_order_prefix_closed_last:
  assumes "x \<sqsubset>\<^sup>i y"
      and "xs@[y] prefix of i"
    shows "x \<in> set xs"
using assms
  apply -
  apply(frule local_order_prefix_closed, assumption, force)
  apply(auto simp add: node_total_order_irrefl prefix_to_carriers)
done

lemma (in node_histories) events_before_exist:
  assumes "x \<in> set (history i)"
  shows "\<exists>pre. pre @ [x] prefix of i"
  using assms unfolding prefix_of_node_history_def apply -
  apply(subgoal_tac "\<exists>idx. idx < length (history i) \<and> (history i) ! idx = x")
  apply(metis append_take_drop_id  take_Suc_conv_app_nth)
  apply(simp add: set_elem_nth)
done

lemma (in node_histories) events_in_local_order:
  assumes "pre @ [e2] prefix of i"
  and "e1 \<in> set pre"
  shows "e1 \<sqsubset>\<^sup>i e2"
using assms split_list unfolding history_order_def prefix_of_node_history_def by fastforce

subsection\<open>Networks\<close>

datatype 'msg event
  = Broadcast 'msg
  | Deliver 'msg

locale network = node_histories history for history :: "nat \<Rightarrow> 'msg event list" +
  fixes msg_id :: "'msg \<Rightarrow> 'msgid"
  (* Broadcast/Deliver interaction *)
  assumes delivery_has_a_cause: "Deliver m \<in> set (history i) \<Longrightarrow> \<exists>j. Broadcast m \<in> set (history j)"
      and deliver_locally: "Broadcast m \<in> set (history i) \<Longrightarrow> Broadcast m \<sqsubset>\<^sup>i Deliver m"
      and msg_id_unique: "Broadcast m1 \<in> set (history i) \<Longrightarrow> Broadcast m2 \<in> set (history j) \<Longrightarrow> msg_id m1 = msg_id m2 \<Longrightarrow> i = j \<and> m1 = m2"

lemma (in network) broadcast_before_delivery:
  assumes "Deliver m \<in> set (history i)"
  shows "\<exists>j. Broadcast m \<sqsubset>\<^sup>j Deliver m"
  using assms deliver_locally delivery_has_a_cause by blast

lemma (in network) broadcasts_unique:
  assumes "i \<noteq> j"
    and "Broadcast m \<in> set (history i)"
  shows "Broadcast m \<notin> set (history j)"
  using assms msg_id_unique by blast

inductive (in network) hb :: "'msg \<Rightarrow> 'msg \<Rightarrow> bool" where
  "\<lbrakk> Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<rbrakk> \<Longrightarrow> hb m1 m2" |
  "\<lbrakk> Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<rbrakk> \<Longrightarrow> hb m1 m2" |
  "\<lbrakk> hb m1 m2; hb m2 m3 \<rbrakk> \<Longrightarrow> hb m1 m3"
  
inductive_cases (in network) hb_elim: "hb x y"
        
definition (in network) weak_hb :: "'msg \<Rightarrow> 'msg \<Rightarrow> bool" where
  "weak_hb m1 m2 \<equiv> hb m1 m2 \<or> m1 = m2"

locale causal_network = network +
  assumes causal_delivery: "Deliver m2 \<in> set (history j) \<Longrightarrow> hb m1 m2 \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>j Deliver m2"

lemma (in causal_network) causal_broadcast:
  assumes "Deliver m2 \<in> set (history j)"
      and "Deliver m1 \<sqsubset>\<^sup>i Broadcast m2"
    shows "Deliver m1 \<sqsubset>\<^sup>j Deliver m2"
  using assms causal_delivery hb.intros(2) by blast

lemma (in network) hb_broadcast_exists1:
  assumes "hb m1 m2"
  shows "\<exists>i. Broadcast m1 \<in> set (history i)"
  using assms
  apply(induction rule: hb.induct)
  apply(meson insert_subset node_histories.local_order_carrier_closed node_histories_axioms)
  apply(meson delivery_has_a_cause insert_subset local_order_carrier_closed)
  by simp

lemma (in network) hb_broadcast_exists2:
  assumes "hb m1 m2"
  shows "\<exists>i. Broadcast m2 \<in> set (history i)"
  using assms
  apply(induction rule: hb.induct)
  apply(meson insert_subset node_histories.local_order_carrier_closed node_histories_axioms)
  apply(meson delivery_has_a_cause insert_subset local_order_carrier_closed)
  by simp

lemma (in causal_network) hb_has_a_reason:
  assumes "hb m1 m2"
    and "Broadcast m2 \<in> set (history i)"
  shows "Deliver m1 \<in> set (history i) \<or> Broadcast m1 \<in> set (history i)"
  using assms
  apply(induction rule: hb.induct)
  apply(metis insert_subset local_order_carrier_closed network.broadcasts_unique network_axioms)
  apply(metis insert_subset local_order_carrier_closed network.broadcasts_unique network_axioms)
  apply(case_tac "Deliver m2 \<in> set (history i)")
  apply(subgoal_tac "Deliver m1 \<in> set (history i)")
  apply blast
  using causal_delivery local_order_carrier_closed apply blast
  apply(subgoal_tac "Broadcast m2 \<in> set (history i)")
  apply blast+
done

lemma (in causal_network) hb_cross_node_delivery:
  assumes "hb m1 m2"
    and "Broadcast m1 \<in> set (history i)"
    and "Broadcast m2 \<in> set (history j)"
    and "i \<noteq> j"
  shows "Deliver m1 \<in> set (history j)"
  using assms
  apply(induction rule: hb.induct)
  apply(metis broadcasts_unique insert_subset local_order_carrier_closed)
  apply(metis insert_subset local_order_carrier_closed network.broadcasts_unique network_axioms)
  apply(case_tac "Deliver m2 \<in> set (history j)")
  apply(subgoal_tac "Deliver m1 \<in> set (history j)")
  apply blast
  using broadcasts_unique hb.intros(3) hb_has_a_reason apply blast
  apply(subgoal_tac "Broadcast m2 \<in> set (history j)")
  apply blast
  using hb_has_a_reason apply blast      
  done
    
lemma (in causal_network) hb_irrefl:
  assumes "hb m1 m2"
  shows "m1 \<noteq> m2"
  using assms
  apply(induction rule: hb.induct)
  using node_total_order_antisym apply auto[1]
  apply(meson causal_broadcast insert_subset local_order_carrier_closed
        node_total_order_irrefl)
  apply(subgoal_tac "\<exists>i. Broadcast m3 \<in> set (history i)")
  apply(subgoal_tac "\<exists>j. Broadcast m2 \<in> set (history j)")
  defer
  apply(simp add: hb_broadcast_exists2)
  apply(simp add: hb_broadcast_exists2)
  apply(clarsimp)
  apply(subgoal_tac "Deliver m2 \<in> set (history j) \<and> Deliver m3 \<in> set (history i)")
  apply(meson causal_delivery hb.intros(3) insert_subset local_order_carrier_closed
        network.broadcast_before_delivery network_axioms node_total_order_irrefl)
  apply(meson deliver_locally insert_subset local_order_carrier_closed)
  done

lemma (in causal_network) hb_broadcast_broadcast_order:
  assumes "hb m1 m2"
    and "Broadcast m1 \<in> set (history i)"
    and "Broadcast m2 \<in> set (history i)"
  shows "Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2"
  using assms
  apply(induction rule: hb.induct)
  apply(metis insertI1 local_order_carrier_closed network.broadcasts_unique
        network_axioms subsetCE)
  apply(metis broadcasts_unique insert_subset local_order_carrier_closed
        network.broadcast_before_delivery network_axioms node_total_order_trans)
  apply(case_tac "Broadcast m2 \<in> set (history i)")
  using node_total_order_trans apply blast
  apply(subgoal_tac "Deliver m2 \<in> set (history i)")
  defer
  using hb_has_a_reason apply blast
  apply(subgoal_tac "m1 \<noteq> m2 \<and> m2 \<noteq> m3")
  apply(metis event.inject(1) hb.intros(1) hb_irrefl network.hb.intros(3) network_axioms
        node_order_is_total hb_irrefl)
  apply blast
done

lemma (in causal_network) hb_antisym:
  assumes "hb x y"
      and "hb y x"
  shows   "False"
using assms proof(induction rule: hb.induct)
  fix m1 i m2  
  assume "hb m2 m1" and "Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2"
  thus False
    apply - proof(erule hb_elim)
    show "\<And>ia. Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Broadcast m2 \<sqsubset>\<^sup>ia Broadcast m1 \<Longrightarrow> False"
      by(metis broadcasts_unique insert_subset local_order_carrier_closed node_total_order_irrefl node_total_order_trans)
  next
    show "\<And>ia. Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Deliver m2 \<sqsubset>\<^sup>ia Broadcast m1 \<Longrightarrow> False"
      by(metis broadcast_before_delivery broadcasts_unique insert_subset local_order_carrier_closed node_total_order_irrefl node_total_order_trans)
  next
    show "\<And>m2a. Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> hb m2 m2a \<Longrightarrow> hb m2a m1 \<Longrightarrow> False"
      using assms(1) assms(2) hb.intros(3) hb_irrefl by blast
  qed
next
  fix m1 i m2
  assume "hb m2 m1"
     and "Deliver m1 \<sqsubset>\<^sup>i Broadcast m2"
  thus "False"
    apply - proof(erule hb_elim)
    show "\<And>ia. Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Broadcast m2 \<sqsubset>\<^sup>ia Broadcast m1 \<Longrightarrow> False"
      by (metis broadcast_before_delivery broadcasts_unique insert_subset local_order_carrier_closed node_total_order_irrefl node_total_order_trans)
  next
    show "\<And>ia. Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Deliver m2 \<sqsubset>\<^sup>ia Broadcast m1 \<Longrightarrow> False"
      by (meson causal_network.causal_delivery causal_network_axioms hb.intros(2) hb.intros(3) insert_subset local_order_carrier_closed node_total_order_irrefl)
  next
    show "\<And>m2a. Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> hb m2 m2a \<Longrightarrow> hb m2a m1 \<Longrightarrow> False"
      by (meson causal_delivery hb.intros(2) insert_subset local_order_carrier_closed network.hb.intros(3) network_axioms node_total_order_irrefl)
  qed
next
  fix m1 m2 m3
  assume "hb m1 m2" "hb m2 m3" "hb m3 m1"
     and "(hb m2 m1 \<Longrightarrow> False)" "(hb m3 m2 \<Longrightarrow> False)"
  thus "False"
    using hb.intros(3) by blast
qed

definition (in network) node_deliver_messages :: "'msg event list \<Rightarrow> 'msg list" where
  "node_deliver_messages cs \<equiv> List.map_filter (\<lambda>e. case e of Deliver m \<Rightarrow> Some m | _ \<Rightarrow> None) cs"

lemma (in network) node_deliver_messages_empty [simp]:
  shows "node_deliver_messages [] = []"
by(auto simp add: node_deliver_messages_def List.map_filter_simps)

lemma (in network) node_deliver_messages_append:
  shows "node_deliver_messages (xs@ys) = (node_deliver_messages xs)@(node_deliver_messages ys)"
by(auto simp add: node_deliver_messages_def map_filter_def)

lemma (in network) node_deliver_messages_Broadcast [simp]:
  shows "node_deliver_messages [Broadcast m] = []"
by(clarsimp simp: node_deliver_messages_def map_filter_def)

lemma (in network) node_deliver_messages_Deliver [simp]:
  shows "node_deliver_messages [Deliver m] = [m]"
by(clarsimp simp: node_deliver_messages_def map_filter_def)

lemma (in network) prefix_msg_in_history:
  assumes "es prefix of i"
      and "m \<in> set (node_deliver_messages es)"
    shows "Deliver m \<in> set (history i)"
using assms
  apply(auto simp: node_deliver_messages_def map_filter_def split: event.split_asm)
  using prefix_to_carriers apply auto
done

lemma (in network) prefix_contains_msg:
  assumes "es prefix of i"
      and "m \<in> set (node_deliver_messages es)"
    shows "Deliver m \<in> set es"
using assms
  apply(auto simp: node_deliver_messages_def map_filter_def split: event.split_asm)
done

lemma (in network) node_deliver_messages_distinct:
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

lemma (in network) drop_last_message:
  assumes "evts prefix of i"
  and "node_deliver_messages evts = msgs @ [last_msg]"
  shows "\<exists>pre. pre prefix of i \<and> node_deliver_messages pre = msgs"
using assms apply -
  apply(subgoal_tac "\<exists>pre suf. evts = pre @ (Deliver last_msg) # suf \<and> node_deliver_messages suf = []")
  apply(erule exE)+
  apply(simp)
  apply(rule_tac x=pre in exI)
  apply(rule conjI)
  using prefix_of_appendD apply blast
  apply(subgoal_tac "node_deliver_messages ([Deliver last_msg] @ suf) = [last_msg]")
  apply(simp add: node_deliver_messages_append)
  apply(metis append_Nil2 node_deliver_messages_append node_deliver_messages_Deliver)
  apply(subgoal_tac "Deliver last_msg \<in> set evts")
  defer
  apply(simp add: prefix_contains_msg)
  apply(subgoal_tac "\<exists>idx. idx < length evts \<and> evts ! idx = Deliver last_msg")
  apply(erule exE)
  apply(subgoal_tac "\<exists>pre suf. evts = pre @ (evts ! idx) # suf")
  defer
  using list_nth_split_technical id_take_nth_drop apply blast
  apply(simp add: set_elem_nth)
  apply(erule exE)+
  apply(rule_tac x=pre in exI, rule_tac x=suf in exI)
  apply(rule conjI, simp, simp)
  apply(subgoal_tac "node_deliver_messages (pre @ Deliver last_msg # suf) =
         (node_deliver_messages pre) @ (node_deliver_messages (Deliver last_msg # suf))")
  apply(subgoal_tac "node_deliver_messages ([Deliver last_msg] @ suf) = [last_msg] @ []")
  apply(metis node_deliver_messages_Deliver node_deliver_messages_append self_append_conv)
  apply(auto simp add: node_deliver_messages_append)
  apply(subgoal_tac "node_deliver_messages ([Deliver last_msg] @ suf) = [last_msg] @ []")
  apply(simp add: node_deliver_messages_append)
  apply(metis append_Cons node_deliver_messages_Deliver node_deliver_messages_append
    node_deliver_messages_distinct not_Cons_self2 pre_suf_eq_distinct_list self_append_conv2)
done

locale network_with_ops = causal_network history
  for history :: "nat \<Rightarrow> 'msg event list" +
  fixes interp :: "'msg \<Rightarrow> 'state \<rightharpoonup> 'state"
  and initial_state :: "'state"

context network_with_ops begin

sublocale hb: happens_before weak_hb hb
proof
  fix x y :: "'msg"
  show "hb x y = (weak_hb x y \<and> \<not> weak_hb y x)"
    unfolding weak_hb_def using hb_antisym by blast
next
  fix x
  show "weak_hb x x"
    using weak_hb_def by blast
next
  fix x y z
  assume "weak_hb x y" "weak_hb y z"
  thus "weak_hb x z"
    using weak_hb_def by (metis network.hb.intros(3) network_axioms)
qed

end

definition (in network_with_ops) apply_operations :: "'msg event list \<rightharpoonup> 'state" where
  "apply_operations es \<equiv> hb.apply_operations (node_deliver_messages es) initial_state"

lemma (in network_with_ops) apply_operations_empty [simp]:
  shows "apply_operations [] = Some initial_state"
by(auto simp add: apply_operations_def)

lemma (in network_with_ops) apply_operations_Broadcast [simp]:
  shows "apply_operations (xs @ [Broadcast m]) = apply_operations xs"
by(auto simp add: apply_operations_def node_deliver_messages_def map_filter_def)

lemma (in network_with_ops) apply_operations_Deliver [simp]:
  shows "apply_operations (xs @ [Deliver m]) = (apply_operations xs \<bind> interp m)"
by(auto simp add: apply_operations_def node_deliver_messages_def map_filter_def kleisli_def)

lemma (in network_with_ops) hb_consistent_technical:
  assumes "\<And>m n. m < length cs \<Longrightarrow> n < m \<Longrightarrow> cs ! n \<sqsubset>\<^sup>i cs ! m"
  shows   "hb.hb_consistent (node_deliver_messages cs)"
using assms
  apply -
  apply(induction cs rule: rev_induct)
  apply(unfold node_deliver_messages_def)
  apply(simp add: hb.hb_consistent.intros(1) map_filter_simps(2))
  apply(case_tac x; clarify)
  apply(simp add: List.map_filter_def)
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(smt Suc_less_eq less_SucI less_trans_Suc nth_append)
  apply(subst map_filter_append)
  apply(clarsimp simp add: map_filter_def)
  apply(rule hb.hb_consistent.intros)
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(smt Suc_less_eq less_SucI less_trans_Suc nth_append)
  apply clarsimp
  apply(case_tac x; clarsimp)
  apply(drule set_elem_nth, erule exE, erule conjE)
  apply(erule_tac x="length xs" in meta_allE, erule_tac x=m in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)
  apply(meson causal_network.causal_delivery causal_network_axioms insert_subset node_histories.local_order_carrier_closed node_histories_axioms node_total_order_irrefl node_total_order_trans)
done

corollary (in network_with_ops)
  shows "hb.hb_consistent (node_deliver_messages (history i))"
  apply(subgoal_tac "history i = [] \<or> (\<exists>c. history i = [c]) \<or> (length (history i) \<ge> 2)")
  apply(erule disjE, clarsimp simp add: node_deliver_messages_def map_filter_def)
  apply(erule disjE, clarsimp simp add: node_deliver_messages_def map_filter_def)
  apply blast
  apply(cases "history i"; clarsimp; case_tac "list"; clarsimp)
  apply(rule hb_consistent_technical[where i=i])                                         
  apply(subst history_order_def, clarsimp)
  apply(metis list_nth_split One_nat_def Suc_le_mono cancel_comm_monoid_add_class.diff_cancel
          le_imp_less_Suc length_Cons less_Suc_eq_le less_imp_diff_less neq0_conv nth_Cons_pos)
  apply(cases "history i"; clarsimp; case_tac "list"; clarsimp)
done

lemma (in network_with_ops) hb_consistent_prefix:
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

locale network_with_constrained_ops = network_with_ops +
  fixes valid_op :: "'c \<Rightarrow> 'a \<Rightarrow> bool"
  assumes broadcast_only_valid_ops: "pre @ [Broadcast m] prefix of i \<Longrightarrow>
             \<exists>state. apply_operations pre = Some state \<and> valid_op state m"

lemma (in network_with_constrained_ops) broadcast_is_valid:
  assumes "Broadcast m \<in> set (history i)"
  shows "\<exists>state. valid_op state m"
  using assms
  apply(subgoal_tac "\<exists>pre. pre @ [Broadcast m] prefix of i")
  using broadcast_only_valid_ops apply blast
  using events_before_exist apply blast
done

section\<open>Example instantiations and interpretations\<close>

interpretation trivial_node_histories: node_histories "\<lambda>m. []"
  by standard auto

interpretation trivial_network: network "\<lambda>m. []" id
  by standard auto
    
interpretation trivial_causal_network: causal_network "\<lambda>m. []" id
  by standard auto
    
interpretation trivial_network_with_ops: network_with_ops "(\<lambda>x::nat \<Rightarrow> nat option. (0::nat))" "\<lambda>m. []" id 0
  by standard auto
    
end
