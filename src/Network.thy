theory
  Network
imports
  Convergence
begin

section\<open>Model of the network\<close>

subsection\<open>Node histories\<close>

locale node_histories = 
  fixes history :: "nat \<Rightarrow> 'a list"
  assumes histories_distinct [intro!, simp]: "distinct (history i)"

definition (in node_histories) history_order :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" ("_\<sqsubset>\<^sup>__" [50,1000,50]50) where
  "x \<sqsubset>\<^sup>i z \<equiv> \<exists>xs ys zs. xs@x#ys@z#zs = history i"

lemma (in node_histories) node_total_order_trans:
  assumes "e1 \<sqsubset>\<^sup>i e2"
      and "e2 \<sqsubset>\<^sup>i e3"
    shows "e1 \<sqsubset>\<^sup>i e3"
using assms
  apply (clarsimp simp add: history_order_def)
  apply (rule_tac x=xs in exI, rule_tac x="ys @ e2 # ysa" in exI, rule_tac x=zsa in exI)
  apply (subgoal_tac "xs @ e1 # ys = xsa \<and> zs = ysa @ e3 # zsa")
  apply clarsimp
  apply (rule_tac xs="history i" and ys="[e2]" in pre_suf_eq_distinct_list)
  using histories_distinct apply auto
done

lemma (in node_histories) local_order_carrier_closed:
  assumes "e1 \<sqsubset>\<^sup>i e2"
    shows "{e1,e2} \<subseteq> set (history i)"
using assms by (clarsimp simp add: history_order_def)
  (metis in_set_conv_decomp Un_iff Un_subset_iff insert_subset list.simps(15) set_append set_subset_Cons)+

lemma (in node_histories) node_total_order_irrefl:
  shows "\<not> (e \<sqsubset>\<^sup>i e)"
by(clarsimp simp add: history_order_def) (metis Un_iff histories_distinct distinct_append distinct_set_notin list.set_intros(1) set_append)

definition (in node_histories) prefix_of_node_history :: "'a list \<Rightarrow> nat \<Rightarrow> bool" (infix "prefix of" 50) where
  "xs prefix of i \<equiv> \<exists>ys. xs@ys = history i"

lemma (in node_histories) carriers_head_lt:
  assumes "y#ys = history i"
  shows   "\<not>(x \<sqsubset>\<^sup>i y)"
using assms
  apply -
  apply clarsimp
  apply(subst (asm) history_order_def)
  apply clarsimp
  apply (subgoal_tac "xs @ x # ysa = [] \<and> zs = ys")
  apply clarsimp
  apply (rule_tac xs="history i" and ys="[y]" in pre_suf_eq_distinct_list)
  using histories_distinct apply auto
done

lemma (in node_histories) prefix_of_ConsD [dest]: "x # xs prefix of i \<Longrightarrow> [x] prefix of i"
  by (auto simp: prefix_of_node_history_def)

lemma (in node_histories) prefix_of_appendD [dest]: "xs @ ys prefix of i \<Longrightarrow> xs prefix of i"
  by (auto simp: prefix_of_node_history_def)

lemma (in node_histories) prefix_distinct: "xs prefix of i \<Longrightarrow> distinct xs"
  apply (clarsimp simp: prefix_of_node_history_def)
  by (metis histories_distinct distinct_append)

lemma (in node_histories) prefix_to_carriers [intro]: "xs prefix of i \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set (history i)"
  apply (clarsimp simp: prefix_of_node_history_def)
  by (metis Un_iff set_append)

lemma (in node_histories) local_order_prefix_closed:
  "x \<sqsubset>\<^sup>i y \<Longrightarrow> xs prefix of i \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<in> set xs"
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
          "xs@[y] prefix of i"
  shows   "x \<in> set xs"
using assms
  apply -
  apply(frule local_order_prefix_closed, assumption, force)
  apply(auto simp add: node_total_order_irrefl prefix_to_carriers)
done

subsection\<open>Global order\<close>

locale global_order = node_histories history for history :: "nat \<Rightarrow> 'a list" +
  fixes global_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>\<^sup>G" 50)
  assumes global_order_trans: "e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e2 \<sqsubset>\<^sup>G e3 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e3"
   and local_order_to_global: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2"
   and global_order_to_local: "{e1, e2} \<subseteq> set (history i) \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e2"

subsection\<open>Networks\<close>

datatype 'a event
  = Broadcast 'a
  | Deliver 'a

locale network = global_order history global_order for global_order :: "'a event \<Rightarrow> 'a event \<Rightarrow> bool" and history :: "nat \<Rightarrow> 'a event list" +
  (* Broadcast/Deliver interaction *)
  assumes broadcast_before_delivery: "Broadcast m \<in> set (history i) \<Longrightarrow> (Broadcast m) \<sqsubset>\<^sup>G (Deliver m)"
   and no_message_lost: "Broadcast m \<in> set (history i) \<Longrightarrow> Deliver m \<in> set (history j)"
   and delivery_has_a_cause: "Deliver m \<in> set (history i) \<Longrightarrow> \<exists>j. Broadcast m \<in> set (history j)"
   and broadcasts_unique: "i \<noteq> j \<Longrightarrow> Broadcast m \<in> set (history i) \<Longrightarrow> \<not> Broadcast m \<in> set (history j)"

locale fifo_network = network +
  assumes delivery_fifo_order: "{Deliver m1, Deliver m2} \<subseteq> set (history j) \<Longrightarrow> Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>j Deliver m2"
   and broadcast_fifo_order: "{Broadcast m1, Broadcast m2} \<subseteq> set (history i) \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>j Deliver m2 \<Longrightarrow> Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2"

locale causal_network = fifo_network +
   assumes broadcast_causal: "{Deliver m1, Deliver m2} \<subseteq> set (history j) \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>j Deliver m2"

definition (in network) node_deliver_messages :: "'a event list \<Rightarrow> 'a list" where
  "node_deliver_messages cs \<equiv> List.map_filter (\<lambda>e. case e of Deliver m \<Rightarrow> Some m | _ \<Rightarrow> None) cs"

lemma (in network) node_deliver_messages_empty [simp]: "node_deliver_messages [] = []"
  by(auto simp add: node_deliver_messages_def List.map_filter_simps)

lemma (in network) node_deliver_messages_append: "node_deliver_messages (xs@ys) = (node_deliver_messages xs)@(node_deliver_messages ys)"
  by(auto simp add: node_deliver_messages_def map_filter_def)

lemma (in network) node_deliver_messages_Broadcast [simp]: "node_deliver_messages [Broadcast m] = []"
  by (clarsimp simp: node_deliver_messages_def map_filter_def)

lemma (in network) node_deliver_messages_Deliver [simp]: "node_deliver_messages [Deliver m] = [m]"
  by (clarsimp simp: node_deliver_messages_def map_filter_def)

lemma (in network) prefix_msg_in_history:
  shows "es prefix of i \<Longrightarrow> m \<in> set (node_deliver_messages es) \<Longrightarrow> Deliver m \<in> set (history i)"
  by (auto simp: node_deliver_messages_def map_filter_def split: event.split_asm)

subsection\<open>Causal Network\<close>

locale network = finite_event_structure +
  (* Broadcast/Deliver interaction *)
  assumes broadcast_before_delivery: "(i, Broadcast, m) \<in> set (carriers i) \<Longrightarrow> (i, Broadcast, m) \<sqsubset>\<^sup>G (j, Deliver, m)"
  assumes no_message_lost: "(i, Broadcast, m) \<in> set (carriers i) \<Longrightarrow> (j, Deliver, m) \<in> set (carriers j)"
  assumes delivery_has_a_cause: "(i, Deliver, m) \<in> set (carriers i) \<Longrightarrow> \<exists>j. (j, Broadcast, m) \<in> set (carriers j)"
  assumes delivery_fifo_order: "{(j, Deliver, m1), (j, Deliver, m2)} \<subseteq> set (carriers j) \<Longrightarrow> (i, Broadcast, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2)"
  assumes broadcast_fifo_order: "{(i, Broadcast, m1), (i, Broadcast, m2)} \<subseteq> set (carriers i) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2) \<Longrightarrow> (i, Broadcast, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2)" 
  assumes broadcast_causal: "{(j, Deliver, m1), (j, Deliver, m2)} \<subseteq> set (carriers j) \<Longrightarrow> (i, Deliver, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2)"
  assumes broadcasts_unique: "i \<noteq> j \<Longrightarrow> (i, Broadcast, m) \<in> set (carriers i) \<Longrightarrow> \<not> (j, Broadcast, m) \<in> set (carriers j)"

subsection\<open>Trivial models\<close>

interpretation trivial_model: network "\<lambda>m. []" "\<lambda>e1 m e2. False" "\<lambda>e1 e2. False"
  by standard auto

interpretation non_trivial_model: network
  "\<lambda>m. if m = 0 then [(0, Broadcast, id), (0, Deliver, id)] else [(m, Deliver, id)]"
  "\<lambda>e1 m e2. m = 0 \<and> e1 = (0, Broadcast, id) \<and> e2 = (0, Deliver, id)"
  "\<lambda>e1 e2. (\<exists>m. e1 = (0, Broadcast, id) \<and> e2 = (m, Deliver, id))"
  apply standard
  apply force
  apply (case_tac "i=0"; clarsimp)
  apply force
  apply (rule iffI)
  apply clarsimp
  apply (rule_tac x="[]" in exI; force)
  apply clarsimp
  apply(case_tac xs; case_tac ys; case_tac zs; clarsimp)
  by standard (case_tac "i = 0"; force)+

subsection\<open>Connecting network with happens before locale.\<close>

locale network_with_ops = network carriers
  for carriers :: "nat \<Rightarrow> (nat \<times> event_type \<times> 'a) list" +
  fixes interp :: "'a \<Rightarrow> 'b \<rightharpoonup> 'b"

context network_with_ops begin

definition hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "hb m1 m2 \<equiv> (\<exists>i. ((i, Broadcast, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<or>
                  (i, Deliver, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2)))"

definition weak_hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "weak_hb m1 m2 \<equiv> hb m1 m2 \<or> m1 = m2"

sublocale hb: happens_before weak_hb hb
proof
  fix x y
  show "hb x y = (weak_hb x y \<and> \<not> weak_hb y x)"
  unfolding hb_def weak_hb_def
    apply standard
    apply(erule exE)
    apply(erule disjE)
    apply(rule conjI)
    apply(rule disjI1)
    apply(rule_tac x=i in exI, simp)
    apply(rule notI)
    apply(erule disjE)
    apply(erule exE)
    apply(erule disjE)
    apply(case_tac "i=ia")
    apply clarsimp
    using node_total_order_irrefl node_total_order_trans
      local_order_carrier_closed insert_subset apply blast
    using broadcasts_unique apply(meson insert_subset local_order_carrier_closed)
    apply(case_tac "i=ia")
    apply clarsimp
    using broadcast_before_delivery local_order_carrier_closed node_total_order_trans apply(smt finite_event_structure.global_order_to_local finite_event_structure_axioms insert_subset node_total_order_irrefl)
    apply(drule local_order_carrier_closed)+
    using broadcasts_unique apply(meson insert_subset)
    apply(frule local_order_carrier_closed)
    using node_total_order_irrefl apply simp
    apply(frule local_order_carrier_closed; clarsimp)
    apply(frule delivery_has_a_cause)
    apply(frule broadcast_causal[rotated], clarsimp)
    apply(rule conjI, assumption)
    apply(rule no_message_lost, assumption)
    apply(rule conjI)
    apply(erule exE)
    apply force
    apply(erule exE)
    apply(rule conjI)
    apply clarsimp
    apply(rule conjI)
    apply(rule notI)
    apply(frule local_order_carrier_closed)
    apply(frule local_order_carrier_closed) back
    apply(drule delivery_fifo_order[rotated], clarsimp)
    apply(rule conjI, assumption, assumption)
    using node_total_order_irrefl apply (meson insert_subset node_total_order_trans)
    apply(rule notI)
    using broadcast_before_delivery apply (meson global_order_to_local global_order_trans insert_subset local_order_carrier_closed local_order_to_global node_total_order_irrefl)
    apply clarsimp
    using node_total_order_irrefl apply blast
    apply(erule conjE)
    apply(erule disjE)
    apply(erule exE)
    apply clarsimp
    apply(erule disjE)
    apply force
    apply force
    apply clarsimp
  done
next
  fix x
  show "weak_hb x x"
  unfolding weak_hb_def by force
next
  fix x y z
  assume "weak_hb x y" "weak_hb y z"
  thus "weak_hb x z"
  unfolding weak_hb_def hb_def
    apply -
    apply safe
    apply (metis (mono_tags, hide_lams) broadcasts_unique insert_subset local_order_carrier_closed node_total_order_trans)
    apply (meson delivery_fifo_order insert_subset local_order_carrier_closed no_message_lost node_total_order_trans)
    apply (metis (no_types, lifting) broadcasts_unique insert_subset local_order_carrier_closed node_total_order_trans)
    apply (meson broadcast_causal delivery_has_a_cause insert_subset local_order_carrier_closed no_message_lost node_total_order_trans)
    apply blast
    apply blast
  done
qed

end

end