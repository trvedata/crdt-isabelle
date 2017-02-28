theory
  Network
imports
  Convergence
begin

section\<open>Model of the network\<close>

subsection\<open>Finite Event Structure\<close>

datatype event_type
  = Broadcast
  | Deliver

type_synonym 'a event = "nat \<times> event_type \<times> 'a"

locale finite_event_structure =
  fixes carriers :: "nat \<Rightarrow> 'a event list"
  fixes node_total_order :: "'a event \<Rightarrow> nat \<Rightarrow> 'a event \<Rightarrow> bool" (infix "\<sqsubset>\<^sup>_" 50)
  fixes global_order :: "'a event \<Rightarrow> 'a event \<Rightarrow> bool" (infix "\<sqsubset>\<^sup>G" 50 )
  (* Isolated node *)
  assumes carriers_distinct: "distinct (carriers i)"
  assumes carriers_message_consistent: "(j, bt, m) \<in> set (carriers i) \<Longrightarrow> i = j"
  assumes carriers_compatible: "(x \<sqsubset>\<^sup>i z) \<longleftrightarrow> (\<exists>xs ys zs. xs@x#ys@z#zs = carriers i)"
  (* Global order *)
  assumes global_order_trans: "e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e2 \<sqsubset>\<^sup>G e3 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e3"
  assumes global_order_irrefl: "e1 \<in> (\<Union>i. set (carriers i)) \<Longrightarrow> \<not> (e1 \<sqsubset>\<^sup>G e1)"
  assumes local_order_to_global: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2"
  assumes global_order_to_local: "{e1, e2} \<subseteq> set (carriers i) \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e2"
  assumes global_order_carrier_closed: "e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> {e1, e2} \<subseteq> (\<Union>i. set (carriers i))"

lemma (in finite_event_structure) node_total_order_trans: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e2 \<sqsubset>\<^sup>i e3 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e3"
  apply (clarsimp simp add: carriers_compatible)
  apply (rule_tac x=xs in exI, rule_tac x="ys @ e2 # ysa" in exI, rule_tac x=zsa in exI)
  apply (subgoal_tac "xs @ e1 # ys = xsa \<and> zs = ysa @ e3 # zsa")
  apply clarsimp
  apply (rule_tac xs="carriers i" and ys="[e2]" in pre_suf_eq_distinct_list)
  using carriers_distinct apply simp
  apply auto
done

lemma (in finite_event_structure) local_order_carrier_closed: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> {e1,e2} \<subseteq> set (carriers i)"
  apply (clarsimp simp add: carriers_compatible)
  apply safe
  apply (metis in_set_conv_decomp)
  apply (metis Un_iff Un_subset_iff insert_subset list.simps(15) set_append set_subset_Cons)
done

lemma (in finite_event_structure) node_total_order_irrefl: "e1 \<in> set (carriers i) \<Longrightarrow> \<not> (e1 \<sqsubset>\<^sup>i e1)"
  apply (clarsimp simp add: carriers_compatible)
  apply (metis Un_iff carriers_distinct distinct_append distinct_set_notin list.set_intros(1) set_append)
done

definition (in finite_event_structure) prefix_of_carrier :: "'a event list \<Rightarrow> nat \<Rightarrow> bool" (infix "prefix of" 50) where
  "xs prefix of i \<equiv> \<exists>ys. xs@ys = carriers i"

definition (in finite_event_structure) node_deliver_messages :: "'a event list \<Rightarrow> 'a list" where
  "node_deliver_messages cs \<equiv>
    map (snd o snd) (List.filter (\<lambda>e. case e of (_, Broadcast, _) \<Rightarrow> False | _ \<Rightarrow> True) cs)"

lemma (in finite_event_structure) node_deliver_messages_empty [simp]: "node_deliver_messages [] = []"
  by (clarsimp simp: node_deliver_messages_def)

lemma (in finite_event_structure) node_deliver_messages_append: "node_deliver_messages (xs@ys) = (node_deliver_messages xs)@(node_deliver_messages ys)"
  by (clarsimp simp: node_deliver_messages_def)

lemma (in finite_event_structure) node_deliver_messages_Broadcast [simp]: "node_deliver_messages ([(a, Broadcast, b)]) = []"
  by (clarsimp simp: node_deliver_messages_def)

lemma (in finite_event_structure) node_deliver_messages_Deliver [simp]: "node_deliver_messages ([(a, Deliver, b)]) = [b]"
  by (clarsimp simp: node_deliver_messages_def)

lemma (in finite_event_structure) carriers_head_lt:
  assumes "y#ys = carriers i"
  shows   "\<not>(x \<sqsubset>\<^sup>i y)"
using assms
  apply -
  apply clarsimp
  apply(subst (asm) carriers_compatible)
  apply clarsimp
  apply (subgoal_tac "xs @ x # ysa = [] \<and> zs = ys")
  apply clarsimp
  apply (rule_tac xs="carriers i" and ys="[y]" in pre_suf_eq_distinct_list)
  using carriers_distinct apply auto
done

lemma (in finite_event_structure) prefix_of_ConsD [dest]: "x # xs prefix of i \<Longrightarrow> [x] prefix of i"
  by (auto simp: prefix_of_carrier_def)

lemma (in finite_event_structure) prefix_of_appendD [dest]: "xs @ ys prefix of i \<Longrightarrow> xs prefix of i"
  by (auto simp: prefix_of_carrier_def)

lemma (in finite_event_structure) prefix_distinct: "xs prefix of i \<Longrightarrow> distinct xs"
  apply (clarsimp simp: prefix_of_carrier_def)
  by (metis carriers_distinct distinct_append)

lemma (in finite_event_structure) prefix_consistent: "xs prefix of i \<Longrightarrow> (a, b, c) \<in> set xs \<Longrightarrow> a = i"
  apply (clarsimp simp: prefix_of_carrier_def)
  by (metis Un_iff carriers_message_consistent set_append)

lemma (in finite_event_structure) prefix_to_carriers [intro]: "xs prefix of i \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set (carriers i)"
  apply (clarsimp simp: prefix_of_carrier_def)
  by (metis Un_iff set_append)

lemma (in finite_event_structure) prefix_msg_in_carrier:
  shows "es prefix of i \<Longrightarrow> m \<in> set (node_deliver_messages es) \<Longrightarrow> (i, Deliver, m) \<in> set (carriers i)"
  apply (clarsimp simp: node_deliver_messages_def)
  apply (case_tac aa; clarsimp)
  apply (subgoal_tac "a=i", clarsimp)
  apply force
  using prefix_consistent apply simp
done

lemma (in finite_event_structure) local_order_prefix_closed:
  "x \<sqsubset>\<^sup>i y \<Longrightarrow> xs prefix of i \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<in> set xs"
  apply (frule prefix_distinct)
  apply (insert carriers_distinct[where i=i])
  apply (clarsimp simp: carriers_compatible prefix_of_carrier_def)
  apply (frule split_list)
  apply clarsimp
  apply (subgoal_tac "ysb = xsa @ x # ysa \<and> zsa @ ys = zs")
  apply clarsimp
  apply (rule_tac xs="carriers i" and ys="[y]" in pre_suf_eq_distinct_list)
  apply clarsimp
  apply clarsimp
  apply clarsimp
  apply clarsimp
done

lemma (in finite_event_structure) local_order_prefix_closed_last:
  assumes "x \<sqsubset>\<^sup>i y"
          "xs@[y] prefix of i"
  shows   "x \<in> set xs"
using assms
  apply -
  apply(frule local_order_prefix_closed, assumption, force)
  apply clarsimp
  apply(simp add: node_total_order_irrefl prefix_to_carriers)
done

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