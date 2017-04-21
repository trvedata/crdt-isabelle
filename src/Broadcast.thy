section\<open>Implementation of Causal Broadcast Protocol\<close>

theory
  Broadcast
imports
  Execution
  Network
  Util
begin

subsection\<open>Causal broadcasts using vector timestamps\<close>

type_synonym 'nodeid msgid = "'nodeid \<times> nat"

record ('nodeid, 'op) message =
  msg_id   :: "'nodeid msgid"
  msg_deps :: "'nodeid \<Rightarrow> nat"
  msg_op   :: "'op"

type_synonym ('nodeid, 'op) node_state = "(('nodeid, 'op) message event, unit) node"

definition broadcasts :: "('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message list" where
  "broadcasts state \<equiv> List.map_filter (\<lambda>e. case e of Broadcast m \<Rightarrow> Some m | _ \<Rightarrow> None) (fst state)"

definition deliveries :: "('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message list" where
  "deliveries state \<equiv> List.map_filter (\<lambda>e. case e of Deliver m \<Rightarrow> Some m | _ \<Rightarrow> None) (fst state)"

definition causal_deps :: "('nodeid, 'op) node_state \<Rightarrow> 'nodeid \<Rightarrow> nat" where
  "causal_deps state \<equiv> foldl
    (\<lambda>map msg. case msg_id msg of (node, seq) \<Rightarrow> map(node := seq))
    (\<lambda>n. 0) (deliveries state)"

definition deps_leq :: "('nodeid \<Rightarrow> nat) \<Rightarrow> ('nodeid \<Rightarrow> nat) \<Rightarrow> bool" where
  "deps_leq left right \<equiv> \<forall>node::'nodeid. left node \<le> right node"

definition causally_ready :: "('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message \<Rightarrow> bool" where
  "causally_ready state msg \<equiv>
     deps_leq (msg_deps msg) (causal_deps state) \<and>
     (case msg_id msg of (sender, seq) \<Rightarrow> seq = Suc(causal_deps state sender))"

definition next_msgid :: "'nodeid \<Rightarrow> ('nodeid, 'op) node_state \<Rightarrow> 'nodeid msgid" where
  "next_msgid sender state \<equiv> (sender, Suc (length (broadcasts state)))"

definition valid_msgs :: "(('nodeid, 'op) node_state \<Rightarrow> 'op set) \<Rightarrow> 'nodeid \<Rightarrow> ('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message set" where
  "valid_msgs valid_ops sender state \<equiv>
     (\<lambda>oper. \<lparr>msg_id   = next_msgid sender state,
              msg_deps = causal_deps state,
              msg_op   = oper\<rparr>
     ) ` valid_ops state"

definition protocol_send ::
  "'nodeid \<Rightarrow> ('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message \<Rightarrow> ('nodeid, 'op) node_state" where
  "protocol_send sender state msg \<equiv> ([Broadcast msg, Deliver msg], ())"

definition protocol_recv ::
  "'nodeid \<Rightarrow> ('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message \<Rightarrow> ('nodeid, 'op) node_state" where
  "protocol_recv recipient state msg \<equiv>
     if causally_ready state msg then ([Deliver msg], ()) else ([], ())"

locale cbcast_protocol_base = executions "\<lambda>n. ()" valid_msg protocol_send protocol_recv
  for valid_msg :: "nat \<Rightarrow> (nat, 'op) message event list \<times> unit \<Rightarrow> (nat, 'op) message set" +
  fixes valid_ops :: "(nat, 'op) node_state \<Rightarrow> 'op set"

locale cbcast_protocol = cbcast_protocol_base "valid_msgs valid_ops" valid_ops
  for valid_ops :: "(nat, 'op) message event list \<times> unit \<Rightarrow> 'op set" +
  fixes config :: "(nat, (nat, 'op) message, (nat, 'op) message event, unit) system"
  assumes valid_execution: "execution config"

definition (in cbcast_protocol) history :: "nat \<Rightarrow> (nat, 'op) message event list" where
  "history i \<equiv> fst (snd config i)"

definition (in cbcast_protocol) all_messages :: "(nat, 'op) message set" where
  "all_messages \<equiv> fst config"

definition (in cbcast_protocol) broadcasts :: "nat \<Rightarrow> (nat, 'op) message list" where
  "broadcasts i \<equiv> List.map_filter (\<lambda>e. case e of Broadcast m \<Rightarrow> Some m | _ \<Rightarrow> None) (history i)"

definition (in cbcast_protocol) deliveries :: "nat \<Rightarrow> (nat, 'op) message list" where
  "deliveries i \<equiv> List.map_filter (\<lambda>e. case e of Deliver m \<Rightarrow> Some m | _ \<Rightarrow> None) (history i)"


subsection\<open>Proof that this protocol satisfies the causal network assumptions\<close>

lemma (in cbcast_protocol) broadcast_node_id:
  assumes "Broadcast msg \<in> set (history i)"
    and "msg_id msg = (j, seq)"
  shows "i = j"
  using assms valid_execution apply(simp add: history_def)
  apply(drule event_origin, simp)
  apply((erule exE)+, (erule conjE)+)
  apply(subgoal_tac "msg_id msg = next_msgid i (snd before i)")
  apply(simp add: next_msgid_def)
  apply(erule disjE)
  apply(simp add: send_step_def case_prod_beta)
  apply(erule unpack_let)+
  apply(simp add: case_prod_beta protocol_send_def split: if_split_asm)
  apply(erule unpack_let)
  apply(subgoal_tac "sender=i") prefer 2 apply force
  apply(subgoal_tac "fst (snd after i) = fst (snd before i) @ [Broadcast msga, Deliver msga]")
  prefer 2 apply force
  apply(subgoal_tac "msga=msg") prefer 2 apply simp
  apply(subgoal_tac "msg \<in> valid_msgs valid_ops i (snd before i)")
  prefer 2 apply(simp add: some_set_memb)
  apply(simp add: valid_msgs_def, force)
  apply(simp add: recv_step_def protocol_recv_def case_prod_beta split: if_split_asm)
  apply(erule unpack_let)+
  apply(subgoal_tac "recipient=i")
  apply force+
done


lemma (in cbcast_protocol) broadcast_msg_id:
  assumes "broadcasts i = pre @ [msg] @ suf"
    shows "msg_id msg = (i, Suc (length pre))"
  oops

context cbcast_protocol begin
sublocale causal: causal_network history msg_id
  apply standard
  oops

end

end