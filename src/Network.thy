theory
  Network
imports
  Main
begin

datatype event_type
  = Broadcast
  | Deliver

type_synonym 'a event = "nat \<times> event_type \<times> 'a"

locale infinite_event_structure =
  fixes carriers :: "nat \<Rightarrow> 'a event set"
  fixes node_total_order :: "'a event \<Rightarrow> nat \<Rightarrow> 'a event \<Rightarrow> bool" (infix "\<sqsubset>\<^sup>_" 50)
  fixes global_order :: "'a event \<Rightarrow> 'a event \<Rightarrow> bool" (infix "\<sqsubset>\<^sup>G" 50 )
  assumes global_order_trans: "{e1, e2, e3} \<subseteq> (\<Union>i. carriers i) \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e2 \<sqsubset>\<^sup>G e3 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e3"
  assumes global_order_irrefl: "e1 \<in> (\<Union>i. carriers i) \<Longrightarrow> \<not> (e1 \<sqsubset>\<^sup>G e1)"
  assumes node_total_order_trans: "{e1, e2, e3} \<subseteq> carriers i \<Longrightarrow> e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e2 \<sqsubset>\<^sup>i e3 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e3"
  assumes node_total_order_total: "{e1, e2} \<subseteq> carriers i \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> (e1 \<sqsubset>\<^sup>i e2) \<or> (e2 \<sqsubset>\<^sup>i e1)"
  assumes node_total_order_irrefl: "e1 \<in> carriers i \<Longrightarrow> \<not> (e1 \<sqsubset>\<^sup>i e1)"
  assumes local_order_to_global: "{e1, e2} \<subseteq> carriers i \<Longrightarrow> e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2"
  assumes global_order_to_local: "{e1, e2} \<subseteq> carriers i \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e2"
  assumes local_order_carrier_closed: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> {e1,e2} \<subseteq> carriers i"
  assumes global_order_carrier_closed: "e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> {e1, e2} \<subseteq> (\<Union>i. carriers i)"
  assumes broadcast_before_delivery: "(i, Broadcast, m) \<in> carriers i \<Longrightarrow> (i, Broadcast, m) \<sqsubset>\<^sup>G (j, Deliver, m)"
  assumes no_message_lost: "(i, Broadcast, m) \<in> carriers i \<Longrightarrow> (j, Deliver, m) \<in> carriers j"
  assumes delivery_has_a_cause: "(i, Deliver, m) \<in> carriers i \<Longrightarrow> \<exists>j. (j, Broadcast, m) \<in> carriers j"
  assumes carriers_message_consistent: "(j, bt, m) \<in> carriers i \<Longrightarrow> i = j"
  assumes broadcast_fifo_order: "{(j, Deliver, m1), (j, Deliver, m2)} \<subseteq> carriers j \<Longrightarrow> (i, Broadcast, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2)"
  assumes broadcast_causal: "{(j, Deliver, m1), (j, Deliver, m2)} \<subseteq> carriers j \<Longrightarrow> (i, Deliver, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2)"

interpretation trivial_model: infinite_event_structure "\<lambda>m. {}" "\<lambda>e1 m e2. False" "\<lambda>e1 e2. False"
  by standard simp_all

interpretation non_trivial_model: infinite_event_structure
  "\<lambda>m. if m = 0 then {(0, Broadcast, 0), (0, Deliver, 0)} else {(m, Deliver, 0)}"
  "\<lambda>e1 m e2. m = 0 \<and> e1 = (0, Broadcast, 0) \<and> e2 = (0, Deliver, 0)"
  "\<lambda>e1 e2. (\<exists>m. e1 = (0, Broadcast, 0) \<and> e2 = (m, Deliver, 0))"
  by standard (case_tac "i = 0"; force)+

locale finite_event_structure = infinite_event_structure +
  assumes finite_carriers: "finite (carriers i)"

definition (in finite_event_structure) ordered_node_events :: "nat \<Rightarrow> 'a event list" where
  "ordered_node_events i \<equiv>
     let events = carriers i in
       linorder.sorted_list_of_set (\<lambda>e1 e2. e1 \<sqsubset>\<^sup>i e2)
         (Set.filter (\<lambda>e.
            case e of (_, Broadcast, _) \<Rightarrow> HOL.False | (_, Delivery, _) \<Rightarrow> HOL.True) events)"

end