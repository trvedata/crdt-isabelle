theory
  Causal_CRDT
imports
  Network
  Ordered_List
  Convergence
begin

lemma filter_empty:
  shows "Set.filter p {} = {}"
by auto

lemma set_filter_Un:
  shows "Set.filter p (xs \<union> ys) = Set.filter p xs \<union> Set.filter p ys"
by auto

corollary set_filter_insert:
  shows "Set.filter p (Set.insert x xs) = (if p x then Set.insert x (Set.filter p xs) else Set.filter p xs)"
using set_filter_Un by(auto split: split_if)

lemma finite_filter:
  assumes "finite A"
  shows   "finite (Set.filter p A)"
using assms
  apply(induction rule: finite.induct)
  apply(auto simp add: filter_empty)
  apply(simp add: set_filter_insert)
done

lemma set_filter_pred:
  assumes "x \<in> Set.filter p xs"
  shows   "p x"
using assms by simp

lemma list_filter_pred:
  assumes "x \<in> set (List.filter p xs)"
  shows   "p x"
using assms by simp

lemma set_elem_nth:
  assumes "x \<in> set xs"
  shows   "\<exists>m. m < length xs \<and> xs ! m = x"
using assms
  apply(induction xs, auto)
  apply(rule_tac x="m+1" in exI)
  apply auto
done

(*
lemma (in finite_event_structure) hb_consistent_lt_hb:
  assumes "hb.hb_consistent cs"
          "i < j" "j < length cs"
  shows   "hb (cs ! i) (cs ! j) \<or> \<not> hb (cs ! j) (cs ! i)"
using assms
  apply(induction rule: hb.hb_consistent.induct)
  apply force
  apply(subgoal_tac "j < length xs \<or> j = length xs")
  apply(erule disjE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)+
  apply clarsimp
prefer 2
  apply force
  apply(clarsimp simp add: hb_def)
  apply(subst (asm) nth_append, simp)+
done
*)

lemma (in finite_event_structure) hb_consistent_technical:
  assumes "\<And>m n. m < length cs \<Longrightarrow> n < m \<Longrightarrow> cs ! n \<sqsubset>\<^sup>i cs ! m"
  shows   "hb.hb_consistent (map (snd \<circ> snd) (ordered_node_events cs))"
using assms
  apply -
  apply(induction cs rule: rev_induct)
  apply(unfold ordered_node_events_def)
  apply force
  apply clarsimp
  apply(case_tac aa; clarsimp)
defer
  apply(rule hb.hb_consistent.intros)
prefer 2
  apply clarsimp
  apply(case_tac "ab"; clarsimp)
  apply(unfold hb_def)
  apply clarsimp
  apply(erule disjE)
  apply(subgoal_tac "(i, Deliver, ba) \<sqsubset>\<^sup>i (i, Deliver, b)")
  apply(frule local_order_carrier_closed) back
  apply(drule delivery_fifo_order[rotated], force)
  using node_total_order_irrefl node_total_order_trans apply (meson insert_subset)
defer
  apply(subgoal_tac "(i, Deliver, ba) \<sqsubset>\<^sup>i (i, Deliver, b)")
  apply(erule_tac x=i in allE)
  apply(frule local_order_carrier_closed) back
  apply(drule broadcast_causal[rotated], force)
  using node_total_order_irrefl node_total_order_trans apply (meson insert_subset)
  apply(drule set_elem_nth)
  apply(erule exE, erule conjE)
  apply(erule_tac x="length xs" in meta_allE)
  apply(erule_tac x="m" in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)
  apply(frule local_order_carrier_closed) back
  apply clarsimp
  apply(drule carriers_message_consistent)+
  apply clarsimp
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(erule_tac x=m in meta_allE)
  apply(erule_tac x=n in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)+
  apply(subgoal_tac "(\<And>m n. m < length xs \<Longrightarrow> n < m \<Longrightarrow> xs ! n \<sqsubset>\<^sup>i xs ! m)")
  apply clarsimp
  apply(erule_tac x=m in meta_allE)
  apply(erule_tac x=n in meta_allE)
  apply clarsimp
  apply(subst (asm) nth_append, simp)+
  apply(drule set_elem_nth)
  apply(erule exE, erule conjE)
  apply(erule_tac x="length xs" in meta_allE)
  apply(erule_tac x="m" in meta_allE)
  apply clarsimp
  apply(frule local_order_carrier_closed) back
  apply clarsimp
  apply(drule carriers_message_consistent)+
  apply clarsimp
done

lemma take_drop_horror:
  assumes "m < length cs"
          "n < m"
          "length cs \<ge> 2"
  shows   "take n cs @ cs ! n # drop (Suc n) (take m cs) @ cs ! m # drop (Suc m) cs = cs"
using assms
sorry

lemma nth_append_technical:
  assumes "m < length cs"
          "n < m"
          "length cs \<ge> 2"
  shows "\<exists>xs ys zs. xs @ [cs ! n] @ ys @ [cs ! m] @ zs = cs"
using assms
  apply(rule_tac x="take n cs" in exI)
  apply(rule_tac x="drop (Suc n) (take m cs)" in exI)
  apply(rule_tac x="drop (Suc m) cs" in exI)
  apply clarsimp
  apply(rule take_drop_horror; simp)
done

corollary (in finite_event_structure)
  shows "hb.hb_consistent (map (snd \<circ> snd) (ordered_node_events (carriers i)))"
  apply(subgoal_tac "carriers i = [] \<or> (\<exists>c. carriers i = [c]) \<or> (length (carriers i) \<ge> 2)")
  apply(erule disjE, clarsimp simp add: ordered_node_events_def)
  apply(erule disjE, clarsimp simp add: ordered_node_events_def)
  apply(case_tac aa; clarsimp)
defer
  apply(cases "carriers i"; clarsimp; case_tac "list"; clarsimp)
  apply(rule hb_consistent_technical[where i=i])
  apply(subst carriers_compatible[symmetric])
  apply(rule nth_append_technical, simp, simp, simp)
done

type_synonym lamport = "nat \<times> nat"

datatype 'v operation
  = Insert "lamport" "'v" "lamport option"

locale network = finite_event_structure carriers
    for carriers :: "nat \<Rightarrow> 'v operation event set" +
  fixes event_id :: "'v operation event \<Rightarrow> lamport"
  assumes event_id_unique: "event_id e1 = event_id e2 \<longleftrightarrow> e1 = e2"

definition (in network) interpret_delivery :: "'v operation event \<Rightarrow> (lamport, 'v) elt list \<rightharpoonup> (lamport, 'v) elt list" where
  "interpret_delivery oper_evt xs \<equiv>
     case oper_evt of
       (_, Deliver, Insert i v pos) \<Rightarrow> insert xs (i, v) pos
     | (_, Broadcast, m) \<Rightarrow> Some xs"

fun option_foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b option" where
  "option_foldr f []     e = Some e" |
  "option_foldr f (x#xs) e =
     (case f x e of
        None \<Rightarrow> None
      | Some h \<Rightarrow> option_foldr f xs h)"

lemma (in network) lengths_same:
  assumes "{ m. (i, Deliver, m) \<in> carriers i } = { m. (j, Deliver, m) \<in> carriers j }"
  shows   "length (ordered_node_events i) = length (ordered_node_events j)"
using assms
  apply(simp add: ordered_node_events_def)
  apply(rule finite.induct)
  using finite_carriers sorry

theorem (in network) foo:
  assumes "{ m. (i, Deliver, m) \<in> carriers i } = { m. (j, Deliver, m) \<in> carriers j }"
          "\<And>j lamp v pos. (j, Broadcast, Insert lamp v pos) \<in> carriers j \<Longrightarrow> pos = None \<or> (\<exists>k k' k''. pos = Some k \<and> (j, Deliver, Insert k k' k'') \<in> carriers j)"
          "xs = ordered_node_events i"
          "ys = ordered_node_events j"
  shows   "option_foldr interpret_delivery xs [] =
             option_foldr interpret_delivery ys []"
using assms
  apply(induction xs)
  apply(drule lengths_same)
  apply(simp add: ordered_node_events_def)
  apply(frule lengths_same, clarsimp)
  apply(erule_tac x="i" in meta_allE)
sorry

definition next_lamport :: "(lamport, 'v) elt list \<Rightarrow> nat \<Rightarrow> lamport" where
  "next_lamport xs node_name \<equiv>
     let ss = fst ` fst ` set xs in
       if ss = {} then
         (node_name, 0)
       else
         (node_name, Suc (Max ss))"

inductive possible_broadcasts :: "(lamport, 'v) elt list \<Rightarrow> nat \<Rightarrow> 'v operation event \<Rightarrow> bool" where
  possible_broadcasts_Nil [intro!]: "\<lbrakk> next_lamport ([]::(lamport,'v) elt list) node_name = next \<rbrakk> \<Longrightarrow> possible_broadcasts [] node_name (node_name, Broadcast, (Insert next v None))" |
  possible_broadcasts_Cons_tail [intro!]: "\<lbrakk> possible_broadcasts xs node_name tail \<rbrakk> \<Longrightarrow> possible_broadcasts (x#xs) node_name tail" |
  possible_broadcasts_Cons_head [intro!]: "\<lbrakk> next_lamport xs node_name = next; (node_name, Broadcast, Insert next v (Some i)) = oper \<rbrakk> \<Longrightarrow> possible_broadcasts ((i,_)#xs) node_name oper"



inductive node_state_evolution :: "(lamport, 'a) elt list \<Rightarrow> nat \<Rightarrow> 'a operation event \<Rightarrow> (lamport, 'a) elt list \<Rightarrow> bool" where
  "\<lbrakk> interpret_delivery xs oper = Some ys \<rbrakk> \<Longrightarrow> node_state_evolution xs node_name (node_name, Deliver, oper) ys" |
  "\<lbrakk> possible_broadcasts xs node_name ev \<rbrakk> \<Longrightarrow> node_state_evolution xs node_name ev xs"

inductive (in node_state_evolution' :: "(lamport, 'a) elt list \<Rightarrow> 'a operation event set \<Rightarrow> (lamport, 'a) elt list \<Rightarrow> bool" where
  "node_state_evolution' [] {} []" |
  "\<lbrakk> node_state_evolution' xs es ys"

locale infinite_stateful_network = infinite_event_structure +
  fixes states :: "nat \<Rightarrow> (lamport, 'a) elt list"
  

end