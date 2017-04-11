theory
  Broadcast
imports
  Network
  Util
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
     if valid_msg state \<noteq> {} then
       let msg = SOME msg. msg \<in> valid_msg state in
         conf(sender := (send_msg msg state, insert msg msgs))
     else conf"

definition (in executions) network_step :: "('nodeid \<Rightarrow> 'state \<times> 'msg set) \<Rightarrow> ('nodeid \<Rightarrow> 'state \<times> 'msg set)" where
  "network_step conf \<equiv>
     let sender = SOME node::'nodeid. True in
     let recipient = SOME node::'nodeid. node \<noteq> sender in
     if snd (conf sender) \<noteq> {} then
       let msg = SOME msg. msg \<in> snd (conf sender) in
       let (state, msgs) = conf recipient in
         conf(recipient := (recv_msg msg state, msgs))
     else conf"

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

type_synonym 'op configuration = "nat \<Rightarrow> (nat, 'op) node_state \<times> (nat, 'op) message set"

locale cbcast_protocol_base = executions initial_node_state _ protocol_send protocol_recv +
  fixes valid_ops :: "(nat, 'op) node_state \<Rightarrow> 'op set"

locale cbcast_protocol = cbcast_protocol_base "valid_msgs valid_ops" +
  fixes config :: "'a configuration"
  assumes valid_execution: "execution config"

definition (in cbcast_protocol) history :: "nat \<Rightarrow> (nat, 'a) message event list" where
  "history \<equiv> state_hist \<circ> fst \<circ> config"


subsection\<open>Proof that this protocol satisfies the causal broadcast axioms\<close>

lemma (in cbcast_protocol) history_to_exec:
  shows "history i = state_hist (fst (config i))"
by(simp add: history_def)

definition (in cbcast_protocol) config_evolution :: "'a configuration \<Rightarrow> 'a configuration list \<Rightarrow> bool" where
  "config_evolution c cs \<equiv>
     cs \<noteq> [] \<and>
     hd cs = (\<lambda>n. (initial_node_state n, {})) \<and>
     last cs = c \<and>
     (\<forall>x \<in> set cs. execution x) \<and>
     (\<forall>pre x y suf. cs = pre@x#y#suf \<longrightarrow> user_step x = y \<or> network_step x = y)"

definition (in cbcast_protocol) forall_execs :: "('a configuration \<Rightarrow> 'a configuration \<Rightarrow> bool) \<Rightarrow> bool" where
  "forall_execs P \<equiv> \<exists>cs. config_evolution config cs \<and>
     (\<forall>pre x y suf. cs = pre@x#y#suf \<longrightarrow> P x y)"

lemma (in cbcast_protocol) config_evolution_drop_last:
  assumes "config_evolution c2 (confs@[c1,c2])"
  shows "config_evolution c1 (confs@[c1])"
  using assms apply(simp add: config_evolution_def)
  apply(erule conjE)+
  apply(rule conjI)
  apply(simp add: list_head_unaffected)
  apply(metis (no_types, lifting) append.assoc append.simps(2) self_append_conv2)
done

lemma (in cbcast_protocol) config_evolution_drop_last2:
  assumes "config_evolution (last cs) cs"
    and "length cs > 1"
  shows "config_evolution (last (butlast cs)) (butlast cs)"
  using assms apply -
  apply(subgoal_tac "\<exists>c1 c2 confs. cs = confs@[c1,c2]")
  apply(erule exE)+
  apply(simp add: butlast_append config_evolution_drop_last)
  using list_two_at_end apply blast
done

lemma (in cbcast_protocol) config_evolution_exists:
  assumes "execution conf"
  shows "\<exists>confs. config_evolution conf confs"
  using assms unfolding config_evolution_def
  apply(induction rule: execution.induct)
  apply(rule_tac x="[\<lambda>a. (initial_node_state a, {})]" in exI)
  apply(simp add: execution.intros(1))
  apply(erule exE)
  apply(rule_tac x="confs@[conf']" in exI, clarsimp)
  apply(rule conjI)
  using execution.intros(2) last_in_set apply blast
  apply(rule allI)+
  apply(clarsimp)
  apply(case_tac suf, force)
  apply(metis (no_types, lifting) butlast.simps(2) butlast_append butlast_snoc list.simps(3))
  apply(erule exE)
  apply(rule_tac x="confs@[conf']" in exI, clarsimp)
  apply(rule conjI)
  using execution.intros(3) last_in_set apply blast
  apply(rule allI)+
  apply(clarsimp)
  apply(case_tac suf, force)
  apply(metis (no_types, lifting) butlast.simps(2) butlast_append butlast_snoc list.simps(3))
done

lemma unpack_let:
  assumes "(let x = y in f x) = z"
  and "\<And>x. (x = y \<and> f x = z) \<Longrightarrow> R"
  shows R
using assms by auto

lemma some_set_memb:
  assumes "y \<noteq> {}"
  shows "(SOME x. x \<in> y) \<in> y"
by (rule someI_ex, simp add: assms ex_in_conv)

lemma (in cbcast_protocol) user_step_effect:
  assumes "user_step before = after"
    and "before \<noteq> after"
  shows "\<exists>i es msg msgs. msgs = valid_msgs valid_ops (fst (before i)) \<and> msgs \<noteq> {} \<and> msg \<in> msgs \<and>
           after = before(i := (protocol_send msg (fst (before i)), insert msg (snd (before i))))"
  using assms
  apply(simp add: user_step_def)
  apply(erule unpack_let, erule conjE)
  apply(simp add: case_prod_beta split: if_split_asm)
  apply(erule unpack_let, erule conjE)
  apply(rule_tac x=sender in exI)
  apply(rule conjI, simp)
  apply(rule_tac x=msg in exI)
  apply(rule conjI, simp add: some_set_memb, simp)
done

lemma (in cbcast_protocol) network_step_effect:
  assumes "network_step before = after"
    and "before \<noteq> after"
  shows "\<exists>sender recipient es msg msgs. msgs = snd (before sender) \<and> msgs \<noteq> {} \<and> msg \<in> msgs \<and>
    after = before(recipient := (protocol_recv msg (fst (before recipient)), snd (before recipient)))"
  using assms
  apply(simp add: network_step_def)
  apply(erule unpack_let, erule conjE)
  apply(erule unpack_let, erule conjE)
  apply(simp add: case_prod_beta split: if_split_asm)
  apply(subgoal_tac "\<exists>msg. msg = (SOME msg. msg \<in> snd (before sender))", erule exE)
  apply(rule_tac x=sender in exI, simp)
  apply(rule_tac x=recipient in exI, rule_tac x=msg in exI, simp)
  apply(meson ex_in_conv some_eq_ex)
  using some_set_memb apply blast
done

lemma (in cbcast_protocol) history_append:
  shows "forall_execs (\<lambda>x y.
      (\<exists>i es. state_hist (fst (x i)) @ es = state_hist (fst (y i)) \<and>
         (\<forall>j::nat. i\<noteq>j \<longrightarrow> state_hist (fst (x j)) = state_hist (fst (y j)))))"
  apply(unfold forall_execs_def)
  apply(insert valid_execution)
  apply(drule config_evolution_exists, erule exE)
  apply(simp add: config_evolution_def)
  apply(rule_tac x=confs in exI, simp)
  apply(rule allI)+
  apply(erule conjE)+
  apply(erule_tac x=pre in allE, erule_tac x=x in allE, erule_tac x=y in allE)
  apply(subgoal_tac "user_step x = y \<or> network_step x = y \<Longrightarrow>
       \<exists>i. (\<exists>es. state_hist (fst (x i)) @ es = state_hist (fst (y i))) \<and>
            (\<forall>j. i \<noteq> j \<longrightarrow> state_hist (fst (x j)) = state_hist (fst (y j)))")
  apply simp+
  apply(case_tac "x=y")
  apply(rule_tac x=0 in exI, simp)
  apply(erule disjE)
  apply(drule user_step_effect, assumption)
  apply(clarsimp simp: protocol_send_def)
  apply(drule network_step_effect, assumption)
  apply(clarsimp simp: protocol_recv_def)
done

lemma (in cbcast_protocol) history_nonempty:
  assumes "execution conf"
  and "evt \<in> set (state_hist (fst (conf i)))"
  shows "\<exists>confs. config_evolution conf confs \<and> length confs > 1"
  using assms apply -
  apply(drule config_evolution_exists, erule exE)
  apply(rule_tac x=confs in exI, clarsimp)
  apply(simp add: config_evolution_def)
  apply(erule conjE)+
  apply(subgoal_tac "length confs \<le> 1 \<Longrightarrow> False", fastforce)
  apply(subgoal_tac "confs = [\<lambda>n. (initial_node_state n, {})]")
  apply(metis empty_iff empty_set fst_conv initial_node_state_def last_ConsL node_state.select_convs(2))
  apply(subgoal_tac "\<exists>xs. confs = (\<lambda>n. (initial_node_state n, {})) # xs")
  apply(metis (no_types, lifting) One_nat_def Suc_le_mono add.right_neutral add_Suc_right length_greater_0_conv list.size(4) not_less)
  apply(subgoal_tac "length confs = 1")
  apply(rule_tac x="[]" in exI)
  using list_head_length_one apply fastforce
  apply(subgoal_tac "length confs < 1 \<Longrightarrow> False")
  apply(simp add: le_less)
  apply(subgoal_tac "length confs = 0 \<Longrightarrow> False")
  apply blast+
done

lemma (in cbcast_protocol) history_nonempty2:
  assumes "execution conf"
  and "config_evolution conf confs"
  and "evt \<in> set (state_hist (fst (conf i)))"
  shows "\<exists>pre c. confs = pre @ [c, conf]"
  using assms apply(simp add: config_evolution_def)
  apply(erule conjE)+
  apply(subgoal_tac "butlast confs \<noteq> []")
  apply(rule_tac x="butlast (butlast confs)" in exI)
  apply(rule_tac x="last (butlast confs)" in exI)
  apply(metis append_assoc append_butlast_last_id butlast.simps(2) last.simps list.simps(3))
  apply(subgoal_tac "butlast confs = [] \<Longrightarrow> False", fastforce)
  apply(subgoal_tac "confs = [\<lambda>n. (initial_node_state n, {})]")
  apply(metis empty_iff empty_set fst_conv initial_node_state_def last_ConsL node_state.select_convs(2))
  apply(metis append_butlast_last_id append_self_conv2 list.sel(1))
done

lemma (in cbcast_protocol) history_append_simp:
  assumes "conf' = conf(i := (
               fst (conf i) \<lparr>state_hist := state_hist (fst (conf i)) @ xs\<rparr>,
               insert msg (snd (conf i))))"
  shows "state_hist (fst (conf i)) @ xs = state_hist (fst (conf' i))"
using assms by simp

lemma (in cbcast_protocol) event_creation:
  assumes "execution conf"
    and "evt \<in> set (state_hist (fst (conf i)))"
  shows "\<exists>before after es. evt \<in> set es \<and> before \<noteq> after \<and>
    (user_step before = after \<or> network_step before = after) \<and>
    state_hist (fst (before i)) @ es = state_hist (fst (after i))"
  using assms
  apply(induction rule: execution.induct)
  apply(simp add: initial_node_state_def)
  apply(case_tac "conf=conf'", simp)
  apply(frule user_step_effect, assumption, (erule exE)+, (erule conjE)+)
  apply(subst (asm) protocol_send_def)
  apply(case_tac "i=ia")
  apply(case_tac "evt \<in> {Broadcast msg, Deliver msg}")
  apply(rule_tac x=conf in exI, rule_tac x=conf' in exI)
  apply(rule_tac x="[Broadcast msg, Deliver msg]" in exI, simp)
  apply(subgoal_tac "evt \<in> set (state_hist (fst (conf i)))", simp)
  apply(subgoal_tac "state_hist (fst (conf ia)) @ [Broadcast msg, Deliver msg] = state_hist (fst (conf' ia))")
  apply(metis UnE empty_set list.simps(15) set_append, simp, simp)
  apply(case_tac "conf=conf'", simp)
  apply(frule network_step_effect, assumption, (erule exE)+, (erule conjE)+)
  apply(subst (asm) protocol_recv_def)
  apply(case_tac "i = recipient")
  apply(case_tac "causally_ready (fst (conf recipient)) msg")
  apply(case_tac "evt = Deliver msg")
  apply(rule_tac x=conf in exI, rule_tac x=conf' in exI)
  apply(rule_tac x="[Deliver msg]" in exI, simp)
  apply(subgoal_tac "evt \<in> set (state_hist (fst (conf i)))", simp)
  apply(subgoal_tac "state_hist (fst (conf recipient)) @ [Deliver msg] = state_hist (fst (conf' recipient))")
  apply(metis UnE empty_iff empty_set set_ConsD set_append)
  apply simp+
done

lemma (in cbcast_protocol) broadcast_node_id:
  assumes "Broadcast msg \<in> set (history i)"
    and "msg_id msg = (j, seq)"
  shows "i = j"
  using assms valid_execution apply(simp add: history_def)
  apply(frule config_evolution_exists, erule exE)
  apply(drule event_creation, simp)
  apply((erule exE)+, (erule conjE)+, erule disjE)
  apply(frule user_step_effect, simp)
  apply(simp add: protocol_send_def, erule exE, erule conjE, erule exE, erule conjE)
  apply(subgoal_tac "msg = msga", subgoal_tac "i = ia")
  apply(subst (asm) valid_msgs_def)
  apply(subst (asm) next_msgid_def)
  apply(subgoal_tac "es = [Broadcast msga, Deliver msga]")
  oops


context cbcast_protocol begin
sublocale causal: causal_network history msg_id
  apply standard
  oops

end

end