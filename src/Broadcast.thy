theory
  Broadcast
imports
  Network
begin

section\<open>Implementation of Causal Broadcast Protocol\<close>

subsection\<open>Non-determinism of users and networks\<close>

locale executions =
  fixes initial   :: "'nodeid \<Rightarrow> 'state"
    and valid_msg :: "'state \<Rightarrow> 'msg set"
    and send_msg  :: "'msg \<Rightarrow> 'state \<Rightarrow> 'state"
    and recv_msg  :: "'msg \<Rightarrow> 'state \<Rightarrow> 'state"

definition (in executions) user_step :: "('nodeid \<Rightarrow> 'state \<times> 'msg set) \<Rightarrow> ('nodeid \<Rightarrow> 'state \<times> 'msg set)" where
  "user_step conf \<equiv>
     let sender = SOME node::'nodeid. True in
     let (state, msgs) = conf sender in
     let msg = SOME msg. msg \<in> valid_msg state in
     conf(sender := (send_msg msg state, insert msg msgs))"

definition (in executions) network_step :: "('nodeid \<Rightarrow> 'state \<times> 'msg set) \<Rightarrow> ('nodeid \<Rightarrow> 'state \<times> 'msg set)" where
  "network_step conf \<equiv>
     let sender = SOME node::'nodeid. True in
     let recipt = SOME node::'nodeid. True in
     let msg = SOME msg. msg \<in> snd (conf sender) in
     let (state, msgs) = conf recipt in
     conf(recipt := (recv_msg msg state, msgs))"

inductive (in executions) execution :: "('nodeid \<Rightarrow> 'state \<times> 'msg set) \<Rightarrow> bool" where
  "execution (\<lambda>n. (initial n, {}))" |
  "\<lbrakk> execution conf; user_step    conf = conf' \<rbrakk> \<Longrightarrow> execution conf'" |
  "\<lbrakk> execution conf; network_step conf = conf' \<rbrakk> \<Longrightarrow> execution conf'"

(* I think this definition is equivalent, but makes the non-deterministic choices less explicit:
inductive (in executions) execution :: "('nodeid \<Rightarrow> 'state \<times> 'msg set) \<Rightarrow> bool" where
  "execution (\<lambda>n. (initial n, {}))" |
  "\<lbrakk> execution conf; conf sender = (state, msgs); msg \<in> valid_msg state; state' = send_msg msg state \<rbrakk>
       \<Longrightarrow> execution (conf(sender := (state', insert msg msgs)))" |
  "\<lbrakk> execution conf; conf recver = (state, msgs); msg \<in> snd (conf sender); state' = recv_msg msg state \<rbrakk>
       \<Longrightarrow> execution (conf(recver := (state', msgs)))"
*)

subsection\<open>Causal broadcasts using vector timestamps\<close>

type_synonym 'nodeid msgid = "'nodeid \<times> nat"

record ('nodeid, 'op) message =
  msg_id   :: "'nodeid msgid"
  msg_deps :: "'nodeid \<Rightarrow> nat"
  msg_op   :: "'op"

record ('nodeid, 'op) node_state =
  state_id   :: "'nodeid"
  state_hist :: "('nodeid, 'op) message event list"

definition initial_node_state :: "'nodeid \<Rightarrow> ('nodeid, 'op) node_state" where
  "initial_node_state node \<equiv> \<lparr>state_id = node, state_hist = []\<rparr>"

definition broadcasts :: "('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message list" where
  "broadcasts state \<equiv> List.map_filter (\<lambda>e. case e of Broadcast m \<Rightarrow> Some m | _ \<Rightarrow> None) (state_hist state)"

definition deliveries :: "('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message list" where
  "deliveries state \<equiv> List.map_filter (\<lambda>e. case e of Deliver m \<Rightarrow> Some m | _ \<Rightarrow> None) (state_hist state)"

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

definition next_msgid :: "('nodeid, 'op) node_state \<Rightarrow> 'nodeid msgid" where
  "next_msgid state \<equiv> (state_id state, Suc (length (broadcasts state)))"

definition valid_msgs :: "(('nodeid, 'op) node_state \<Rightarrow> 'op set) \<Rightarrow> ('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) message set" where
  "valid_msgs valid_ops state \<equiv>
     (\<lambda>oper. \<lparr>msg_id = next_msgid state, msg_deps = causal_deps state, msg_op = oper\<rparr>) ` valid_ops state"

definition protocol_send :: "('nodeid, 'op) message \<Rightarrow> ('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) node_state" where
  "protocol_send msg state \<equiv>
     state \<lparr>state_hist := state_hist state @ [Broadcast msg, Deliver msg]\<rparr>"

definition protocol_recv :: "('nodeid, 'op) message \<Rightarrow> ('nodeid, 'op) node_state \<Rightarrow> ('nodeid, 'op) node_state" where
  "protocol_recv msg state \<equiv>
     if causally_ready state msg then state \<lparr>state_hist := state_hist state @ [Deliver msg]\<rparr> else state"

locale cbcast_protocol_base = executions initial_node_state _ protocol_send protocol_recv +
  fixes valid_ops :: "(nat, 'op) node_state \<Rightarrow> 'op set"

locale cbcast_protocol = cbcast_protocol_base "valid_msgs valid_ops"

definition (in cbcast_protocol) history :: "nat \<Rightarrow> (nat, 'a) message event list" where
  "history \<equiv> state_hist \<circ> fst \<circ> (SOME conf. execution conf)"


subsection\<open>Proof that this protocol satisfies the causal broadcast axioms\<close>

context cbcast_protocol begin
sublocale causal: causal_network history msg_id
  apply standard
  oops

end

end