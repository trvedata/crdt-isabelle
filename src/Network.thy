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

definition (in node_histories) prefix_of_node_history :: "'a list \<Rightarrow> nat \<Rightarrow> bool" (infix "prefix of" 50) where
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

subsection\<open>Global order\<close>

locale global_order = node_histories history for history :: "nat \<Rightarrow> 'a list" +
  fixes global_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
  assumes global_order_trans: "e1 \<sqsubset> e2 \<Longrightarrow> e2 \<sqsubset> e3 \<Longrightarrow> e1 \<sqsubset> e3"
   and local_order_to_global: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e1 \<sqsubset> e2"
   and global_order_to_local: "{e1, e2} \<subseteq> set (history i) \<Longrightarrow> e1 \<sqsubset> e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e2"

subsection\<open>Networks\<close>

datatype 'a event
  = Broadcast 'a
  | Deliver 'a

locale network = global_order history global_order
    for global_order :: "'a event \<Rightarrow> 'a event \<Rightarrow> bool" (infix "\<sqsubset>" 50) and history :: "nat \<Rightarrow> 'a event list" +
  (* Broadcast/Deliver interaction *)
  assumes broadcast_before_delivery: "Broadcast m \<in> set (history i) \<Longrightarrow> (Broadcast m) \<sqsubset> (Deliver m)"
      and no_message_lost: "Broadcast m \<in> set (history i) \<Longrightarrow> Deliver m \<in> set (history j)"
      and delivery_has_a_cause: "Deliver m \<in> set (history i) \<Longrightarrow> \<exists>j. Broadcast m \<in> set (history j)"
      and broadcasts_unique: "i \<noteq> j \<Longrightarrow> Broadcast m \<in> set (history i) \<Longrightarrow> Broadcast m \<notin> set (history j)"

locale fifo_network = network +
  assumes delivery_fifo_order: "{Deliver m1, Deliver m2} \<subseteq> set (history j) \<Longrightarrow>
      Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>j Deliver m2"
   and broadcast_fifo_order: "{Broadcast m1, Broadcast m2} \<subseteq> set (history i) \<Longrightarrow>
      Deliver m1 \<sqsubset>\<^sup>j Deliver m2 \<Longrightarrow> Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2"

locale causal_network = fifo_network +
  assumes broadcast_causal: "{Deliver m1, Deliver m2} \<subseteq> set (history j) \<Longrightarrow>
    Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>j Deliver m2"

definition (in network) node_deliver_messages :: "'a event list \<Rightarrow> 'a list" where
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

definition (in network) hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "hb m1 m2 \<equiv> (\<exists>i. Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<or> Deliver m1 \<sqsubset>\<^sup>i Broadcast m2)"

definition (in network) weak_hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "weak_hb m1 m2 \<equiv> hb m1 m2 \<or> m1 = m2"

locale network_with_ops = causal_network _ history
  for history :: "nat \<Rightarrow> 'a event list" +
  fixes interp :: "'a \<Rightarrow> 'b \<rightharpoonup> 'b"

context network_with_ops begin

sublocale hb: happens_before weak_hb hb
proof
  fix x y :: "'a"
  show "hb x y = (weak_hb x y \<and> \<not> weak_hb y x)"
  proof(rule iffI; unfold hb_def weak_hb_def; clarsimp)
    fix i :: "nat"
    assume "Broadcast x \<sqsubset>\<^sup>i Broadcast y \<or> Deliver x \<sqsubset>\<^sup>i Broadcast y"
    thus "(\<forall>i. \<not> Broadcast y \<sqsubset>\<^sup>i Broadcast x \<and> \<not> Deliver y \<sqsubset>\<^sup>i Broadcast x) \<and> y \<noteq> x"
    proof
      assume "Broadcast x \<sqsubset>\<^sup>i Broadcast y"
      thus "(\<forall>i. \<not> Broadcast y \<sqsubset>\<^sup>i Broadcast x \<and> \<not> Deliver y \<sqsubset>\<^sup>i Broadcast x) \<and> y \<noteq> x"
        by(metis global_order.global_order_trans global_order_axioms global_order_to_local
            insert_subset local_order_carrier_closed local_order_to_global
            network.broadcast_before_delivery network_axioms node_total_order_irrefl)
    next
      assume "Deliver x \<sqsubset>\<^sup>i Broadcast y"
      thus "(\<forall>i. \<not> Broadcast y \<sqsubset>\<^sup>i Broadcast x \<and> \<not> Deliver y \<sqsubset>\<^sup>i Broadcast x) \<and> y \<noteq> x"  
        by(meson broadcast_before_delivery global_order_to_local global_order_trans insert_subset
            local_order_carrier_closed local_order_to_global node_total_order_irrefl)
    qed
  qed
next
  fix x :: "'a"
  show "weak_hb x x"
    by(simp add: weak_hb_def)
next
  fix x y z :: "'a"
  assume "weak_hb x y"
     and "weak_hb y z"
    thus "weak_hb x z"
  proof(unfold weak_hb_def hb_def)
    assume 1: "(\<exists>i. Broadcast x \<sqsubset>\<^sup>i Broadcast y \<or> Deliver x \<sqsubset>\<^sup>i Broadcast y) \<or> x = y"
       and 2: "(\<exists>i. Broadcast y \<sqsubset>\<^sup>i Broadcast z \<or> Deliver y \<sqsubset>\<^sup>i Broadcast z) \<or> y = z"
      show "(\<exists>i. Broadcast x \<sqsubset>\<^sup>i Broadcast z \<or> Deliver x \<sqsubset>\<^sup>i Broadcast z) \<or> x = z"
    proof(rule disjE[OF 1]; rule disjE[OF 2]; clarsimp)
      fix i j :: "nat"
      assume "Broadcast x \<sqsubset>\<^sup>i Broadcast y \<or> Deliver x \<sqsubset>\<^sup>i Broadcast y"
         and "Broadcast y \<sqsubset>\<^sup>j Broadcast z \<or> Deliver y \<sqsubset>\<^sup>j Broadcast z"
         and "x \<noteq> z"
       thus "\<exists>i. Broadcast x \<sqsubset>\<^sup>i Broadcast z \<or> Deliver x \<sqsubset>\<^sup>i Broadcast z" 
         by(smt broadcasts_unique delivery_fifo_order delivery_has_a_cause global_order_to_local
              insert_subset local_order_carrier_closed local_order_to_global
              network.broadcast_before_delivery network_axioms no_message_lost node_total_order_trans)
    qed
  qed
qed

end

section\<open>Example instantiations and interpretations\<close>

interpretation trivial_node_histories: node_histories "\<lambda>m. []"
  by standard auto

interpretation trivial_global_order: global_order "\<lambda>m. []" "\<lambda>e1 e2. False"
  by standard (auto simp add: trivial_node_histories.history_order_def)

interpretation trivial_network: network "\<lambda>e1 e2. False" "\<lambda>m. []"
  by standard auto

interpretation non_trivial_node_histories: node_histories "\<lambda>m. if m = 0 then [Broadcast id, Deliver id] else [Deliver id]"
  by standard auto

interpretation non_trivial_global_order: global_order "\<lambda>m. if m = 0 then [Broadcast id, Deliver id] else [Deliver id]"
                                                      "\<lambda>e1 e2. e1 = Broadcast id \<and> e2 = Deliver id"
  apply standard
  apply(auto simp add: non_trivial_node_histories.history_order_def)
  apply(metis (no_types, lifting) append_is_Nil_conv butlast.simps(2) butlast_append append_Cons neq_Nil_conv append_Nil last_snoc)
  apply(metis (no_types, lifting) append_is_Nil_conv butlast.simps(2) butlast_append append_Cons neq_Nil_conv append_Nil last_snoc)
  apply(simp add: append_eq_Cons_conv)
  using distinct_set_notin apply fastforce
done

interpretation non_trivial_network: network "\<lambda>e1 e2. e1 = Broadcast id \<and> e2 = Deliver id"
                                            "\<lambda>m. if m = 0 then [Broadcast id, Deliver id] else [Deliver id]"
  by standard (auto split: split_if_asm)

end
  