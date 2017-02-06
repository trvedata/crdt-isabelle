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

lemma (in finite_event_structure) ordered_node_events_Deliver:
  assumes "(e, m, f) \<in> set (ordered_node_events i)"
  shows   "m = Deliver"
sorry

lemma (in finite_event_structure) ordered_node_events_rev_elim:
  assumes "xs@[(x,y,z)] = ordered_node_events i"
  shows   "\<forall>e \<in> set xs. e \<sqsubset>\<^sup>i (x,y,z)"
sorry

lemma (in finite_event_structure)
  shows "hb.hb_consistent (map (snd o snd) (ordered_node_events i))"
  apply -
  apply(induction "ordered_node_events i" rule: rev_induct)
  apply(force)
  apply(case_tac x; clarify)
  apply(frule_tac ordered_node_events_rev_elim)
  apply(subgoal_tac "hb.hb_consistent (map (snd \<circ> snd) (xs @ [(ab, ba, c)]))")
  apply(simp)
  apply(subst map_append)
  apply simp
  apply(rule hb.hb_consistent.intros)
  apply auto
prefer 2
  apply(unfold hb_def)
  apply(rule_tac x=i in exI)
  apply(rule disjI1)
  apply(erule_tac x="(a, aa, b)" in ballE)
  apply(frule local_order_carrier_closed)
  apply clarsimp
  apply(frule carriers_message_consistent)
  apply(frule carriers_message_consistent) back
  apply clarsimp
  sorry
  

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