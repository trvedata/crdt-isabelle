theory
  Network
imports
  Convergence
begin

datatype event_type
  = Broadcast
  | Deliver

type_synonym 'a event = "nat \<times> event_type \<times> ('a \<Rightarrow> 'a)"

locale finite_event_structure =
  fixes carriers :: "nat \<Rightarrow> 'a event list"
  fixes node_total_order :: "'a event \<Rightarrow> nat \<Rightarrow> 'a event \<Rightarrow> bool" (infix "\<sqsubset>\<^sup>_" 50)
  fixes global_order :: "'a event \<Rightarrow> 'a event \<Rightarrow> bool" (infix "\<sqsubset>\<^sup>G" 50 )
  assumes carriers_compatible: "(\<exists>xs ys zs. xs@x#ys@z#zs = carriers i) \<longleftrightarrow> (x \<sqsubset>\<^sup>i z)"
  assumes global_order_trans: "e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e2 \<sqsubset>\<^sup>G e3 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e3"
  assumes global_order_irrefl: "e1 \<in> (\<Union>i. set (carriers i)) \<Longrightarrow> \<not> (e1 \<sqsubset>\<^sup>G e1)"
  assumes node_total_order_trans: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e2 \<sqsubset>\<^sup>i e3 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e3"
  assumes node_total_order_total: "{e1, e2} \<subseteq> set (carriers i) \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> (e1 \<sqsubset>\<^sup>i e2) \<or> (e2 \<sqsubset>\<^sup>i e1)"
  assumes node_total_order_irrefl: "e1 \<in> set (carriers i) \<Longrightarrow> \<not> (e1 \<sqsubset>\<^sup>i e1)"
  assumes local_order_to_global: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2"
  assumes global_order_to_local: "{e1, e2} \<subseteq> set (carriers i) \<Longrightarrow> e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> e1 \<sqsubset>\<^sup>i e2"
  assumes local_order_carrier_closed: "e1 \<sqsubset>\<^sup>i e2 \<Longrightarrow> {e1,e2} \<subseteq> set (carriers i)"
  assumes global_order_carrier_closed: "e1 \<sqsubset>\<^sup>G e2 \<Longrightarrow> {e1, e2} \<subseteq> (\<Union>i. set (carriers i))"
  assumes broadcast_before_delivery: "(i, Broadcast, m) \<in> set (carriers i) \<Longrightarrow> (i, Broadcast, m) \<sqsubset>\<^sup>G (j, Deliver, m)"
  assumes no_message_lost: "(i, Broadcast, m) \<in> set (carriers i) \<Longrightarrow> (j, Deliver, m) \<in> set (carriers j)"
  assumes delivery_has_a_cause: "(i, Deliver, m) \<in> set (carriers i) \<Longrightarrow> \<exists>j. (j, Broadcast, m) \<in> set (carriers j)"
  assumes carriers_message_consistent: "(j, bt, m) \<in> set (carriers i) \<Longrightarrow> i = j"
  assumes delivery_fifo_order: "{(j, Deliver, m1), (j, Deliver, m2)} \<subseteq> set (carriers j) \<Longrightarrow> (i, Broadcast, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2)"
  assumes broadcast_fifo_order: "{(i, Broadcast, m1), (i, Broadcast, m2)} \<subseteq> set (carriers i) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2) \<Longrightarrow> (i, Broadcast, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2)" 
  assumes broadcast_causal: "{(j, Deliver, m1), (j, Deliver, m2)} \<subseteq> set (carriers j) \<Longrightarrow> (i, Deliver, m1) \<sqsubset>\<^sup>i (i, Broadcast, m2) \<Longrightarrow> (j, Deliver, m1) \<sqsubset>\<^sup>j (j, Deliver, m2)"
  assumes broadcasts_unique: "i \<noteq> j \<Longrightarrow> (i, Broadcast, m) \<in> set (carriers i) \<Longrightarrow> \<not> (j, Broadcast, m) \<in> set (carriers j)"

interpretation trivial_model: finite_event_structure "\<lambda>m. []" "\<lambda>e1 m e2. False" "\<lambda>e1 e2. False"
  by standard auto

interpretation non_trivial_model: finite_event_structure
  "\<lambda>m. if m = 0 then [(0, Broadcast, id), (0, Deliver, id)] else [(m, Deliver, id)]"
  "\<lambda>e1 m e2. m = 0 \<and> e1 = (0, Broadcast, id) \<and> e2 = (0, Deliver, id)"
  "\<lambda>e1 e2. (\<exists>m. e1 = (0, Broadcast, id) \<and> e2 = (m, Deliver, id))"
  apply standard
  apply (case_tac "i=0")
  apply(rule iffI, (erule exE)+)
  apply clarsimp
  apply(case_tac xs; case_tac ys; case_tac zs; clarsimp)
  apply clarsimp
  apply(rule_tac x="[]" in exI)+
  apply force
  by standard (case_tac "i = 0"; force)+

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

fun merge :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge cmp []     ys     = ys" |
  "merge cmp xs     []     = xs" |
  "merge cmp (x#xs) (y#ys) =
     (if cmp x y then
        x#merge cmp xs (y#ys)
      else
        y#merge cmp (x#xs) ys)"

function (sequential) qsort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "qsort cmp []      = []" |
  "qsort cmp [x]     = [x]" |
  "qsort cmp (x#xs)  =
     (let ls = List.filter (\<lambda>y. cmp x y) xs;
          rs = List.filter (\<lambda>y. cmp y x) xs
      in (qsort cmp ls) @ [x] @ (qsort cmp rs))"
by pat_completeness auto

termination qsort
  apply(relation "measure (\<lambda>(cmp, xs). size xs)")
  apply auto
  apply(simp_all add: le_imp_less_Suc)
  using le_imp_less_Suc less_Suc_eq apply auto
done

lemma qsort_set_mem_preserve:
  shows "(\<forall>x \<in> set xs. \<forall>y \<in> set xs. cmp x y \<or> cmp y x) \<longrightarrow> set xs = set (qsort cmp xs)"
  apply(induction rule: qsort.induct[where P="\<lambda>cmp xs. (\<forall>x \<in> set xs. \<forall>y \<in> set xs. cmp x y \<or> cmp y x) \<longrightarrow> set xs = set (qsort cmp xs)"])
  apply auto
done
  
definition (in finite_event_structure) ordered_node_operations :: "'a event list \<Rightarrow> ('a \<Rightarrow> 'a) list" where
  "ordered_node_operations cs \<equiv>
    map (snd o snd) (
     List.filter (\<lambda>e. case e of (_, Broadcast, _) \<Rightarrow> False | _ \<Rightarrow> True) cs)"

end