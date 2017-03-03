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

definition (in node_histories) history_order :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" ("_/ \<sqsubset>\<^sup>_/ _" [50,1000,50]50) where
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

subsection\<open>Networks\<close>

datatype 'a event
  = Broadcast 'a
  | Deliver 'a

locale network = node_histories history for history :: "nat \<Rightarrow> 'a event list" +
  (* Broadcast/Deliver interaction *)
  assumes broadcast_before_delivery: "Deliver m \<in> set (history i) \<Longrightarrow> \<exists>j. Broadcast m \<sqsubset>\<^sup>j Deliver m"
      and no_message_lost: "Broadcast m \<in> set (history i) \<Longrightarrow> Deliver m \<in> set (history j)"
      and broadcasts_unique: "i \<noteq> j \<Longrightarrow> Broadcast m \<in> set (history i) \<Longrightarrow> Broadcast m \<notin> set (history j)"
      
lemma (in network) delivery_has_a_cause:
  assumes "Deliver m \<in> set (history i)"
  shows "\<exists>j. Broadcast m \<in> set (history j)"
  by (meson assms broadcast_before_delivery insert_subset local_order_carrier_closed)
      
inductive (in network) hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "\<lbrakk> Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<rbrakk> \<Longrightarrow> hb m1 m2" |
  "\<lbrakk> Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<rbrakk> \<Longrightarrow> hb m1 m2" |
  "\<lbrakk> hb m1 m2; hb m2 m3 \<rbrakk> \<Longrightarrow> hb m1 m3"
  
inductive_cases (in network) hb_elim: "hb x y"
        
definition (in network) weak_hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "weak_hb m1 m2 \<equiv> hb m1 m2 \<or> m1 = m2"

locale causal_network = network +
  assumes broadcast_causal: "{Deliver m1, Deliver m2} \<subseteq> set (history j) \<Longrightarrow>
    hb m1 m2 \<Longrightarrow> Deliver m1 \<sqsubset>\<^sup>j Deliver m2"
    
lemma (in causal_network) broadcast_causal':
  assumes "{Deliver m1, Deliver m2} \<subseteq> set (history j)"
      and "Deliver m1 \<sqsubset>\<^sup>i Broadcast m2"
    shows "Deliver m1 \<sqsubset>\<^sup>j Deliver m2"
  using assms by (meson causal_network.broadcast_causal causal_network_axioms hb.intros(2))
    
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
    show "\<And>m1 i m2 ia. Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> Broadcast m2 \<sqsubset>\<^sup>ia Broadcast m1 \<Longrightarrow> False"
      by(metis broadcast_before_delivery broadcasts_unique insert_subset local_order_carrier_closed node_total_order_irrefl node_total_order_trans)
  next
    show "\<And>m2a. Broadcast m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> hb m2 m2a \<Longrightarrow> hb m2a m1 \<Longrightarrow> False"
      by (meson causal_network.broadcast_causal causal_network_axioms hb.intros(1) hb.intros(3) insert_subset local_order_carrier_closed no_message_lost node_histories.node_total_order_irrefl node_histories_axioms)
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
      by (meson causal_network.broadcast_causal causal_network_axioms hb.intros(2) hb.intros(3) insert_subset local_order_carrier_closed node_total_order_irrefl)
  next
    show "\<And>m2a. Deliver m1 \<sqsubset>\<^sup>i Broadcast m2 \<Longrightarrow> hb m2 m2a \<Longrightarrow> hb m2a m1 \<Longrightarrow> False"
      by (meson broadcast_causal hb.intros(2) insert_subset local_order_carrier_closed network.hb.intros(3) network_axioms node_total_order_irrefl)
  qed
next
  fix m1 m2 m3
  assume "hb m1 m2" "hb m2 m3" "hb m3 m1"
     and "(hb m2 m1 \<Longrightarrow> False)" "(hb m3 m2 \<Longrightarrow> False)"
  thus "False"
    using hb.intros(3) by blast
qed

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

locale network_with_ops = causal_network history
  for history :: "nat \<Rightarrow> 'a event list" +
  fixes interp :: "'a \<Rightarrow> 'b \<rightharpoonup> 'b"

context network_with_ops begin

sublocale hb: happens_before weak_hb hb
proof
  fix x y :: "'a"
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

section\<open>Example instantiations and interpretations\<close>

interpretation trivial_node_histories: node_histories "\<lambda>m. []"
  by standard auto

interpretation trivial_network: network "\<lambda>m. []"
  by standard auto

interpretation non_trivial_node_histories: node_histories "\<lambda>m. if m = 0 then [Broadcast id, Deliver id] else [Deliver id]"
  by standard auto

interpretation non_trivial_network: network "\<lambda>m. if m = 0 then [Broadcast id, Deliver id] else [Deliver id]"
  apply standard
    apply(auto split: if_split_asm)
    apply(rule_tac x=0 in exI)
   apply (metis append.left_neutral non_trivial_node_histories.history_order_def)
    apply(rule_tac x=0 in exI)
  apply (metis append.left_neutral non_trivial_node_histories.history_order_def)
    done
end
  