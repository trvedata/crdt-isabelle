section\<open>Model of a distributed system executing some algorithm\<close>

theory
  Execution
imports
  Util
begin

subsection\<open>Non-determinism of users and networks\<close>

type_synonym ('evt, 'state) node = "'evt list \<times> 'state"
type_synonym ('nodeid, 'msg, 'evt, 'state) system = "'msg set \<times> ('nodeid \<Rightarrow> ('evt, 'state) node)"

locale executions =
  fixes initial   :: "'nodeid \<Rightarrow> 'state"
    and valid_msg :: "'nodeid \<Rightarrow> ('evt, 'state) node \<Rightarrow> 'msg set"
    and send_msg  :: "'nodeid \<Rightarrow> ('evt, 'state) node \<Rightarrow> 'msg \<Rightarrow> 'evt list \<times> 'state"
    and recv_msg  :: "'nodeid \<Rightarrow> ('evt, 'state) node \<Rightarrow> 'msg \<Rightarrow> 'evt list \<times> 'state"
  assumes node_exists: "\<exists>node::'nodeid. True"

definition (in executions) send_step ::
  "('nodeid, 'msg, 'evt, 'state) system \<Rightarrow> ('nodeid, 'msg, 'evt, 'state) system" where
  "send_step sys \<equiv>
     let (msgs, nodes) = sys;
         sender = SOME node::'nodeid. True;
         (evts, state) = nodes sender;
         valid = valid_msg sender (nodes sender) in
     if valid \<noteq> {} then
       let msg = SOME msg. msg \<in> valid;
           (evts', state') = send_msg sender (nodes sender) msg in
       (insert msg msgs, nodes(sender := (evts @ evts', state')))
     else sys"

definition (in executions) recv_step ::
  "('nodeid, 'msg, 'evt, 'state) system \<Rightarrow> ('nodeid, 'msg, 'evt, 'state) system" where
  "recv_step sys \<equiv>
     let (msgs, nodes) = sys in
     if msgs \<noteq> {} then
       let msg = SOME msg. msg \<in> msgs;
           recipient = SOME node::'nodeid. True;
           (evts, state) = nodes recipient;
           (evts', state') = recv_msg recipient (nodes recipient) msg in
       (msgs, nodes(recipient := (evts @ evts', state')))
     else sys"

definition (in executions) take_step ::
  "('nodeid, 'msg, 'evt, 'state) system \<Rightarrow> ('nodeid, 'msg, 'evt, 'state) system" where
  "take_step \<equiv> SOME step. step \<in> {send_step, recv_step}"

definition (in executions) initial_conf :: "('nodeid, 'msg, 'evt, 'state) system" where
  "initial_conf \<equiv> ({}, \<lambda>n. ([], initial n))"

inductive (in executions) execution :: "('nodeid, 'msg, 'evt, 'state) system \<Rightarrow> bool" where
  "execution initial_conf" |
  "\<lbrakk> execution conf; take_step conf = conf' \<rbrakk> \<Longrightarrow> execution conf'"

definition (in executions) config_evolution ::
  "('nodeid, 'msg, 'evt, 'state) system \<Rightarrow> ('nodeid, 'msg, 'evt, 'state) system list \<Rightarrow> bool" where
  "config_evolution c cs \<equiv>
     cs \<noteq> [] \<and>
     hd cs = initial_conf \<and>
     last cs = c \<and>
     (\<forall>x \<in> set cs. execution x) \<and>
     (\<forall>pre x y suf. cs = pre@x#y#suf \<longrightarrow> send_step x = y \<or> recv_step x = y)"

lemma (in executions) config_evolution_drop_last:
  assumes "config_evolution c2 (confs@[c1,c2])"
  shows "config_evolution c1 (confs@[c1])"
  using assms apply(simp add: config_evolution_def)
  apply(erule conjE)+
  apply(rule conjI)
  apply(simp add: list_head_unaffected)
  apply(metis (no_types, lifting) append.assoc append.simps(2) self_append_conv2)
done

lemma (in executions) config_evolution_drop_last2:
  assumes "config_evolution (last cs) cs"
    and "length cs > 1"
  shows "config_evolution (last (butlast cs)) (butlast cs)"
  using assms apply -
  apply(subgoal_tac "\<exists>c1 c2 confs. cs = confs@[c1,c2]")
  apply(erule exE)+
  apply(simp add: butlast_append config_evolution_drop_last)
  using list_two_at_end apply blast
done

lemma (in executions) config_evolution_exists:
  assumes "execution conf"
  shows "\<exists>confs. config_evolution conf confs"
  using assms unfolding config_evolution_def
  apply(induction rule: execution.induct)
  apply(rule_tac x="[initial_conf]" in exI)
  apply(simp add: execution.intros(1))
  apply(erule exE)
  apply(rule_tac x="confs@[conf']" in exI, clarsimp)
  apply(rule conjI)
  using execution.intros(2) last_in_set apply blast
  apply(rule allI)+
  apply(subgoal_tac "take_step \<in> {send_step, recv_step}") defer
  apply(rule choose_set_memb, simp, simp add: take_step_def)
  apply(simp, erule disjE, clarsimp)
  apply(case_tac suf, force)
  apply(metis (no_types, lifting) butlast.simps(2) butlast_append butlast_snoc list.simps(3))
  apply(clarsimp, case_tac suf, force)
  apply(metis (no_types, lifting) butlast.simps(2) butlast_append butlast_snoc list.simps(3))
done

lemma (in executions) config_evolution_fold:
  assumes "execution conf"
  shows "\<exists>steps. conf = fold (op \<circ>) steps id initial_conf"
  using assms unfolding config_evolution_def
  apply(induction rule: execution.induct)
  apply(rule_tac x="[]" in exI, simp)
  apply(erule exE)
  apply(rule_tac x="steps@[take_step]" in exI, simp)
done

lemma (in executions) config_evolution_butlast:
  assumes "config_evolution conf (confs@[conf])"
    and "conf \<noteq> initial_conf"
  shows "config_evolution (last confs) confs"
  using assms unfolding config_evolution_def apply clarsimp
  apply(rule conjI, force)
  apply(rule conjI)
  apply(metis (mono_tags, lifting) hd_append list.sel(1))
  apply(clarsimp, blast)
done

lemma (in executions) history_append:
  assumes "config_evolution conf confs"
  and "\<exists>suf. pre@x#y#suf = confs"
  shows "(send_step x = y \<or> recv_step x = y) \<and>
      (\<exists>i es. fst (snd x i) @ es = fst (snd y i) \<and> (\<forall>j. i\<noteq>j \<longrightarrow> fst (snd x j) = fst (snd y j)))"
  using assms apply(simp add: config_evolution_def)
  apply(erule conjE)+
  apply(erule_tac x="pre" in allE)
  apply(erule_tac x="fst x" in allE, erule_tac x="snd x" in allE)
  apply(erule_tac x="fst y" in allE, erule_tac x="snd y" in allE)
  apply(subgoal_tac "send_step x = y \<or> recv_step x = y \<Longrightarrow>
       \<exists>i. (\<exists>es. fst (snd x i) @ es = fst (snd y i)) \<and> (\<forall>j. i \<noteq> j \<longrightarrow> fst (snd x j) = fst (snd y j))")
  apply force
  apply(case_tac "x=y")
  apply(insert node_exists, (erule exE)+, rule_tac x=node in exI, simp)
  apply(erule disjE)
  apply(simp add: send_step_def case_prod_beta)
  apply(erule unpack_let)+
  apply(simp add: case_prod_beta split: if_split_asm)
  apply(erule unpack_let)
  apply(rule_tac x=sender in exI, rule conjI)
  apply(rule_tac x="fst (send_msg sender (snd x sender) msg)" in exI, force, force)
  apply(simp add: recv_step_def case_prod_beta split: if_split_asm)
  apply(erule unpack_let)+
  apply(rule_tac x=recipient in exI, rule conjI)
  apply(rule_tac x="fst (recv_msg recipient (snd x recipient) msg)" in exI, auto)
done

lemma (in executions) history_nonempty:
  assumes "execution conf"
  and "evt \<in> set (fst (snd conf i))"
  shows "\<exists>confs. config_evolution conf confs \<and> length confs > 1"
  using assms apply -
  apply(drule config_evolution_exists, erule exE)
  apply(rule_tac x=confs in exI, clarsimp)
  apply(simp add: config_evolution_def)
  apply(erule conjE)+
  apply(subgoal_tac "length confs \<le> 1 \<Longrightarrow> False", fastforce)
  apply(subgoal_tac "confs = [initial_conf]")
  using initial_conf_def apply fastforce
  apply(metis le_less length_0_conv less_one list_head_length_one)
done

lemma (in executions) history_nonempty2:
  assumes "execution conf"
  and "config_evolution conf confs"
  and "evt \<in> set (fst (snd conf i))"
  shows "\<exists>pre c. confs = pre @ [c, conf]"
  using assms apply(simp add: config_evolution_def)
  apply(erule conjE)+
  apply(subgoal_tac "butlast confs \<noteq> []")
  apply(rule_tac x="butlast (butlast confs)" in exI)
  apply(rule_tac x="fst (last (butlast confs))" in exI)
  apply(rule_tac x="snd (last (butlast confs))" in exI)
  apply(metis append_butlast_last_id append_eq_appendI butlast.simps(2) last_ConsL
    last_ConsR list.distinct(1) prod.collapse)
  apply(subgoal_tac "butlast confs = [] \<Longrightarrow> False", fastforce)
  apply(subgoal_tac "confs = [initial_conf]")
  using initial_conf_def apply fastforce
  apply(metis append_butlast_last_id append_self_conv2 list.sel(1))
done

lemma (in executions) history_append_simp:
  assumes "conf' = conf(i := (fst (conf i) @ xs, insert msg (snd (conf i))))"
  shows "fst (conf i) @ xs = fst (conf' i)"
using assms by simp

lemma (in executions) event_origin:
  assumes "execution conf"
    and "evt \<in> set (fst (snd conf i))"
  shows "\<exists>before after es. evt \<in> set es \<and> before \<noteq> after \<and>
    (send_step before = after \<or> recv_step before = after) \<and>
    fst (snd before i) @ es = fst (snd after i)"
  using assms
  apply(induction rule: execution.induct, simp add: initial_conf_def)
  apply(case_tac "conf=conf'", simp)
  apply(subgoal_tac "take_step \<in> {send_step, recv_step}") defer
  apply(rule choose_set_memb, simp, simp add: take_step_def)
  apply(simp, erule disjE, simp)
  apply(insert send_step_def, erule_tac x=conf in meta_allE)[1]
  apply(simp add: case_prod_beta)
  apply(erule unpack_let)+
  apply(simp add: case_prod_beta split: if_split_asm)
  apply(erule unpack_let)
  apply(case_tac "i=sender")
  apply(case_tac "evt \<in> set (fst (send_msg i (snd conf i) msg))")
  apply(rule_tac x="fst conf" in exI, rule_tac x="snd conf" in exI)
  apply(rule_tac x="fst conf'" in exI, rule_tac x="snd conf'" in exI)
  apply(rule_tac x="fst (send_msg i (snd conf i) msg)" in exI, force)
  apply(subgoal_tac "evt \<in> set (fst (snd conf i))", simp)
  apply(subgoal_tac "fst (snd conf i) @ fst (send_msg i (snd conf i) msg) = fst (snd conf' i)")
  apply(force, force, force)
  apply(insert recv_step_def, erule_tac x=conf in meta_allE)
  apply(simp add: case_prod_beta split: if_split_asm)
  apply(erule unpack_let)+
  apply(case_tac "i = recipient")
  apply(case_tac "evt \<in> set (fst (recv_msg i (snd conf i) msg))")
  apply(rule_tac x="fst conf" in exI, rule_tac x="snd conf" in exI)
  apply(rule_tac x="fst conf'" in exI, rule_tac x="snd conf'" in exI)
  apply(rule_tac x="fst (recv_msg i (snd conf i) msg)" in exI)
  apply force+
done

lemma (in executions) config_evolution_append:
  assumes "config_evolution conf (cs1 @ step # cs2)"
  shows "\<exists>suf. fst (snd step i) @ suf = fst (snd conf i)"
  using assms apply -
  apply(induction cs2 arbitrary: conf rule: rev_induct)
  apply(rule_tac x="[]" in exI)
  apply(metis (mono_tags, lifting) config_evolution_def last_snoc self_append_conv)
  apply(subgoal_tac "x=conf") defer
  apply(metis (mono_tags, lifting) config_evolution_def last.simps last_append
    list.distinct(1) snoc_eq_iff_butlast)
  apply(insert config_evolution_drop_last2)
  apply(erule_tac x="cs1 @ step # xs @ [conf]" in meta_allE)
  apply(erule_tac x="last (step # xs)" in meta_allE)
  apply(simp add: butlast_append)
  apply(case_tac "xs=[]")
  apply(insert history_append)
  apply(erule_tac x=conf in meta_allE)
  apply(erule_tac x="cs1 @ [step, conf]" in meta_allE)
  apply(erule_tac x=cs1 in meta_allE)
  apply(erule_tac x=step in meta_allE)
  apply(erule_tac x=conf in meta_allE)
  apply(subgoal_tac "\<exists>i es. fst (snd step i) @ es = fst (snd conf i) \<and>
                (\<forall>j. i \<noteq> j \<longrightarrow> fst (snd step j) = fst (snd conf j))")
  apply(erule exE)+
  apply(case_tac "i=ia")
  apply(rule_tac x="es" in exI, simp)
  apply(rule_tac x="[]" in exI, simp, simp)
  apply(erule_tac x="conf" in meta_allE)
  apply(erule_tac x="cs1 @ step # xs @ [conf]" in meta_allE)
  apply(erule_tac x="cs1 @ step # butlast xs" in meta_allE)
  apply(erule_tac x="last xs" in meta_allE)
  apply(erule_tac x="conf" in meta_allE)
  apply(subgoal_tac "\<exists>suf. cs1 @ step # butlast xs @ last xs # conf # suf = cs1 @ step # xs @ [conf]")
  apply(clarsimp)
  apply(case_tac "i=ia")
  apply(rule_tac x="suf@es" in exI, metis append.assoc)
  apply(rule_tac x="suf" in exI, simp)
  apply(rule_tac x="[]" in exI, simp)
done

lemma (in executions) message_origin:
  assumes "config_evolution conf confs"
    and "msg \<in> fst conf"
  shows "\<exists>before after sender valid evts state.
           valid = valid_msg sender (snd before sender) \<and> valid \<noteq> {} \<and> msg \<in> valid \<and>
           (evts, state) = send_msg sender (snd before sender) msg \<and>
           after = (insert msg (fst before),
             (snd before)(sender := (fst (snd before sender) @ evts, state)))"
  using assms apply -
  apply(induction confs arbitrary: conf rule: rev_induct)
  apply(simp add: config_evolution_def)
  apply(case_tac "xs=[]")
  using config_evolution_def initial_conf_def apply fastforce
  apply(erule_tac x="last xs" in meta_allE)
  apply(simp)
  apply(insert config_evolution_def)
  apply(erule_tac x=conf in meta_allE, erule_tac x="xs@[x]" in meta_allE)
  apply(simp, (erule conjE)+)
  apply(erule_tac x="butlast xs" in allE)
  apply(erule_tac x="fst (last xs)" in allE)
  apply(erule_tac x="snd (last xs)" in allE)
  apply(erule_tac x="fst conf" in allE)
  apply(erule_tac x="snd conf" in allE)
  apply(subgoal_tac "\<exists>suf. xs @ [conf] = butlast xs @ last xs # conf # suf") defer
  apply(metis (no_types, lifting) append_butlast_last_id append_eq_append_conv2
    butlast.simps(2) last_ConsL last_ConsR list.simps(3))
  apply(simp, erule disjE)
  apply(insert send_step_def, erule_tac x="last xs" in meta_allE)[1]
  apply(simp add: case_prod_beta)
  apply(erule unpack_let)+
  apply(simp add: case_prod_beta split: if_split_asm)
  apply(erule unpack_let)
  apply(case_tac "msga=msg")
  apply(rule_tac x="fst (last xs)" in exI)
  apply(rule_tac x="snd (last xs)" in exI)
  apply(rule_tac x="fst conf" in exI)
  apply(rule_tac x="snd conf" in exI)
  apply(rule_tac x="sender" in exI)
  apply(rule conjI, simp)
  apply(rule conjI, simp add: some_set_memb)
  apply(rule_tac x="fst (send_msg sender (snd (last xs) sender) msga)" in exI)
  apply(rule_tac x="snd (send_msg sender (snd (last xs) sender) msga)" in exI)
  apply(rule conjI, simp)
  apply(rule conjI, force, force)
  apply(subgoal_tac "config_evolution (last xs) xs", simp)
  apply(subgoal_tac "msg \<in> fst (last xs)", simp, force)
  apply(metis config_evolution_butlast empty_iff fst_conv initial_conf_def)
  apply(metis config_evolution_butlast empty_iff fst_conv initial_conf_def)
  apply(insert recv_step_def, erule_tac x="last xs" in meta_allE)
  apply(simp add: case_prod_beta split: if_split_asm)
  apply(erule unpack_let)+
  apply(metis config_evolution_butlast fst_conv initial_conf_def)
done

end