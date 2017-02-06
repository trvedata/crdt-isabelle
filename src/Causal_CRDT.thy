theory
  Causal_CRDT
imports
  Network
  Ordered_List
  Convergence
begin

context finite_event_structure begin

definition hb :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "hb m1 m2 \<equiv> (\<exists>i. ((i, Broadcast, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<or>
                  (i, Deliver, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2)))"

definition weak_hb :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
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
    using broadcast_before_delivery local_order_carrier_closed node_total_order_trans apply(smt infinite_event_structure.global_order_to_local infinite_event_structure_axioms insert_subset node_total_order_irrefl)
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
    apply(drule broadcast_fifo_order[rotated], clarsimp)
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
    apply (meson broadcast_fifo_order insert_subset local_order_carrier_closed no_message_lost node_total_order_trans)
    apply (metis (no_types, lifting) broadcasts_unique insert_subset local_order_carrier_closed node_total_order_trans)
    apply (meson broadcast_causal delivery_has_a_cause insert_subset local_order_carrier_closed no_message_lost node_total_order_trans)
    apply blast
    apply blast
  done
qed

lemma linorder_local_order:
  shows "class.linorder (\<lambda>x y. x \<sqsubset>\<^sup>i y \<or> x = y) (\<lambda>x y. x \<sqsubset>\<^sup>i y)"
  apply(unfold class.linorder_def class.linorder_axioms_def class.order_def class.preorder_def
          class.order_axioms_def)
  apply(meson insert_subset local_order_carrier_closed node_total_order_irrefl node_total_order_trans)
  apply(drule node_total_order_total[rotated])
defer
  apply(erule disjE)
  apply(rule notE, assumption, assumption, assumption)

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

lemma sorted_list_of_set_singleton:
  shows "sorted_list_of_set {x} = [x]"
by simp

lemma sorted_list_of_set_insert_elem:
  assumes "finite ys"
  assumes "x \<in> set (linorder.sorted_list_of_set p (Set.insert y ys))"
  shows   "x = y \<or> x \<in> set (linorder.sorted_list_of_set p ys)"
using assms
sorry

lemma ordered_node_events_Broadcast [rule_format]:
  shows "(e, m, f) \<in> set (ordered_node_events i) \<longrightarrow> m = Deliver"
  apply(unfold ordered_node_events_def)
  apply(simp only: Let_def)
  apply(rule_tac x="carriers i" in finite.induct)
  apply(force simp add: finite_carriers)
  apply(subst filter_empty)
  apply(insert "linorder.sorted_list_of_set_empty")
  apply(erule_tac x="(\<lambda>x y. x \<sqsubset>\<^sup>i y \<or> x = y)" in meta_allE)
  apply(erule_tac x="(\<lambda>x y. x \<sqsubset>\<^sup>i y)" in meta_allE)
  apply(erule meta_impE, rule linorder_local_order, simp)
  apply clarsimp
  apply(case_tac aa; clarsimp)
  apply(clarsimp simp add: set_filter_insert)+
  apply(subgoal_tac "finite (Set.filter (\<lambda>(x, a, xa). case a of Broadcast \<Rightarrow> False | Deliver \<Rightarrow> True) A)")
  apply(drule sorted_list_of_set_insert_elem) back
  apply assumption
  apply(auto simp add: finite_filter)
done

lemma
  shows "hb.hb_consistent (map (snd o snd) (ordered_node_events i))"
  apply -
  apply(unfold ordered_node_events_def)
  apply(rule_tac x="carriers i" in finite.induct)
  apply(clarsimp simp add: finite_carriers)
  apply clarsimp
  apply(subst filter_empty)
  apply(subst linorder.sorted_list_of_set_empty)
  apply(rule linorder_local_order)
  apply force
  apply clarsimp
  apply(case_tac aa; clarsimp)
  apply(subst set_filter_insert, clarsimp)+

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