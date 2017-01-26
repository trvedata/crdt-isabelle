theory
  Fresh_Start
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Product_Lexorder"
begin

section\<open>A commutative operation (insert)\<close>

type_synonym ('id, 'v) elt = "'id \<times> 'v"

hide_const insert

fun insert_body :: "('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt \<Rightarrow> ('id, 'v) elt list" where
  "insert_body []     e = [e]" |
  "insert_body (x#xs) e =
     (if fst x < fst e then
        e#x#xs
      else x#insert_body xs e)"

fun insert :: "('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt \<Rightarrow> 'id option \<rightharpoonup> ('id, 'v) elt list" where
  "insert xs     e None     = Some (insert_body xs e)" |
  "insert []     e (Some i) = None" |
  "insert (x#xs) e (Some i) =
     (if fst x = i then
        Some (x#insert_body xs e)
      else
        do { t \<leftarrow> insert xs e (Some i)
           ; Some (x#t)
           })"

lemma insert_body_commutes:
  assumes "distinct (map fst (e1#e2#xs))"
  shows   "insert_body (insert_body xs e1) e2 = insert_body (insert_body xs e2) e1"
using assms
  apply(induction xs)
    apply force
    apply clarsimp
    apply(case_tac "fst e1 < fst e2")
      apply force+
done

lemma insert_insert_body:
  assumes "distinct (map fst (e1#e2#xs))" "i2 \<noteq> Some (fst e1)"
  shows   "insert (insert_body xs e1) e2 i2 = do { ys \<leftarrow> insert xs e2 i2; Some (insert_body ys e1) }"
using assms
  apply(induction xs)
    apply(case_tac "i2")
      apply force
      apply clarsimp
    apply clarsimp
    apply(case_tac "a < fst e1")
      apply clarsimp
      apply(case_tac "i2")
        apply clarsimp
        apply(case_tac "fst e2 < fst e1")
          apply force+
        apply clarsimp
      apply clarsimp
      apply(case_tac "i2")
        apply force
        apply clarsimp
        apply(case_tac "aa < fst e1")
          apply clarsimp
          apply clarsimp
          apply(force simp add: insert_body_commutes)
  done

lemma insert_Nil_None:
  assumes "fst e1 \<noteq> fst e2" "i \<noteq> fst e2" "i2 \<noteq> Some (fst e1)"
  shows   "insert [] e2 i2 \<bind> (\<lambda>ys. insert ys e1 (Some i)) = None"
using assms by (cases "i2") clarsimp+

lemma insert_insert_body_commute:
  assumes "a \<noteq> aa"
          "aa \<noteq> fst e2"
          "aa \<notin> fst ` set xs"
          "fst e2 \<notin> fst ` set xs"
          "distinct (map fst xs)"
  shows   "insert (insert_body xs (aa, ba)) e2 (Some a) =
             insert xs e2 (Some a) \<bind> (\<lambda>y. Some (insert_body y (aa, ba)))"
using assms
  apply(induction xs)
    apply clarsimp
    apply clarsimp
    apply(force simp add: insert_body_commutes)
  done

lemma insert_commutes:
  assumes "distinct (map fst (e1#e2#xs))"
          "i1 = None \<or> i1 \<noteq> Some (fst e2)"
          "i2 = None \<or> i2 \<noteq> Some (fst e1)"
  shows   "do { ys \<leftarrow> insert xs e1 i1; insert ys e2 i2 } =
             do { ys \<leftarrow> insert xs e2 i2; insert ys e1 i1 }"
using assms
  apply(induction rule: insert.induct)
    apply clarsimp
    apply(erule disjE)
      apply clarsimp
      apply(force simp add: insert_body_commutes)
      apply(rule insert_insert_body, simp, simp, simp)
    apply(erule disjE)
      apply simp
      apply clarsimp
      apply(rule insert_Nil_None[symmetric], simp, simp, simp)
    apply(erule disjE)
      apply clarsimp
      apply clarsimp
      apply(case_tac "a = i")
        apply clarsimp
        apply(case_tac "i2")
          apply clarsimp
          apply(force simp add: insert_body_commutes)
        apply clarsimp
      apply(case_tac "a = i")
        apply clarsimp
        apply(force simp add: insert_body_commutes)
        apply clarsimp
        apply(force simp add: insert_insert_body_commute)
        apply clarsimp
        apply(case_tac i2)
          apply(force cong: Option.bind_cong simp add: insert_insert_body)
          apply clarsimp
          apply(case_tac "ab = i")
            apply clarsimp
            apply(metis bind_assoc)
            apply clarsimp
            apply(case_tac "a = ab")
              apply clarsimp
              apply(force cong: Option.bind_cong simp add: insert_insert_body)
              apply clarsimp
              apply(metis bind_assoc)
  done

fun insert' :: "('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt \<Rightarrow> 'id option \<rightharpoonup> ('id::{linorder}, 'v) elt list" where
  "insert' [] e     None     = Some [e]" |
  "insert' [] e     (Some i) = None" |
  "insert' (x#xs) e None     =
     (if fst x < fst e then
        Some (e#x#xs)
      else
        case insert' xs e None of
          None   \<Rightarrow> None
        | Some t \<Rightarrow> Some (x#t))" |
  "insert' (x#xs) e (Some i) =
     (if fst x = i then
        case insert' xs e None of
          None   \<Rightarrow> None
        | Some t \<Rightarrow> Some (x#t)
      else
        case insert' xs e (Some i) of
          None   \<Rightarrow> None
        | Some t \<Rightarrow> Some (x#t))"

lemma insert'_None_condition2 [elim!, dest]:
  assumes "insert' xs e None = None"
  shows   "False"
using assms
  by (induction xs, auto, case_tac "a < fst e"; clarsimp) (case_tac "insert' xsa e None"; clarsimp)

lemma insert_body_insert':
  shows "insert' list (a, b) None = Some (insert_body list (a, b))"
  apply(induction list)
    apply clarsimp+
  done

lemma insert_insert':
  shows "insert = insert'"
  apply(rule ext)+
  apply(induct_tac x)
    apply(case_tac "xb")
      apply simp+
    apply clarsimp
    apply(case_tac "xb")
      apply simp
      apply(rule impI)
      apply(case_tac "insert' list (a, b) None")
        apply clarsimp+
      apply safe
      apply(case_tac "insert' list (a, b) None")
        apply force
        apply(force simp add: insert_body_insert')
    apply(case_tac "insert' list (a, b) (Some ab)")
      apply clarsimp
      apply clarsimp
  done

section\<open>Modal logic of networks\<close>

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

datatype 'a formula
  = True   ("\<top>" 65)
  | False  ("\<bottom>" 65)
  | Event  "'a event"
  | Conjunction "'a formula" "'a formula" ("_/ and/ _"  [75,75]75)
  | Implication "'a formula" "'a formula" ("_/ \<rightarrow>/ _"    [66,65]65)
  | GlobalB     "'a formula"              ("\<box>\<^sup>G_"         [100]100)
  | LocalB      "nat" "'a formula"        ("\<box>\<^sup>__"         [100,100]100)
  | LabolgB     "'a formula"              ("\<box>\<^sup>-\<^sup>1\<^sup>,\<^sup>G_"       [100]100)
  | LacolB      "nat" "'a formula"        ("\<box>\<^sup>-\<^sup>1\<^sup>,\<^sup>__"       [100,100]100)
  | ExistsNode  "nat \<Rightarrow> 'a formula"       (binder "ExNode" 65)

function (in infinite_event_structure) satisfaction :: "'a event \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
  "e \<Turnstile> \<top> = HOL.True" |
  "e \<Turnstile> \<bottom> = HOL.False" |
  "e \<Turnstile> Event e' = (e = e')" |
  "e \<Turnstile> (\<phi> and \<psi>) = ((e \<Turnstile> \<phi>) \<and> (e \<Turnstile> \<psi>))" |
  "e \<Turnstile> (\<phi> \<rightarrow> \<psi>) = ((e \<Turnstile> \<phi>) \<longrightarrow> (e \<Turnstile> \<psi>))" |
  "e \<Turnstile> \<box>\<^sup>G \<phi> = (\<forall>e'. e \<sqsubset>\<^sup>G e' \<longrightarrow> e' \<Turnstile> \<phi>)" |
  "e \<Turnstile> \<box>\<^sup>i \<phi> = (\<forall>e'. e \<sqsubset>\<^sup>i e' \<longrightarrow> e' \<Turnstile> \<phi>)" |
  "e \<Turnstile> \<box>\<^sup>-\<^sup>1\<^sup>,\<^sup>G \<phi> = (\<forall>e'. e' \<sqsubset>\<^sup>G e \<longrightarrow> e' \<Turnstile> \<phi>)" |
  "e \<Turnstile> \<box>\<^sup>-\<^sup>1\<^sup>,\<^sup>i \<phi> = (\<forall>e'. e' \<sqsubset>\<^sup>i e \<longrightarrow> e' \<Turnstile> \<phi>)" |
  "e \<Turnstile> ExistsNode \<phi> = (\<exists>node. e \<Turnstile> \<phi> node)"
by pat_completeness auto

termination (in infinite_event_structure) satisfaction
  sorry

definition negation :: "'a formula \<Rightarrow> 'a formula" ("not/_" [100]100) where
  "not \<phi> \<equiv> \<phi> \<rightarrow> \<bottom>"

definition disjunction :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" (infixr "or" 75) where
  "\<phi> or \<psi> \<equiv> not ((not \<phi>) and (not \<psi>))"

definition globalD :: "'a formula \<Rightarrow> 'a formula" ("\<diamondop>\<^sup>G_" [100]100) where
  "\<diamondop>\<^sup>G \<phi> \<equiv> not (\<box>\<^sup>G (not \<phi>))"

definition localD :: "nat \<Rightarrow> 'a formula \<Rightarrow> 'a formula" ("\<diamondop>\<^sup>__" [100,100]100) where
  "\<diamondop>\<^sup>i \<phi> \<equiv> not (\<box>\<^sup>i (not \<phi>))"

definition globalD_inv :: "'a formula \<Rightarrow> 'a formula" ("\<diamondop>\<^sup>-\<^sup>1\<^sup>,\<^sup>G_" [100]100) where
  "\<diamondop>\<^sup>-\<^sup>1\<^sup>,\<^sup>G \<phi> \<equiv> not (\<box>\<^sup>-\<^sup>1\<^sup>,\<^sup>G (not \<phi>))"

definition localD_inv :: "nat \<Rightarrow> 'a formula \<Rightarrow> 'a formula" ("\<diamondop>\<^sup>-\<^sup>1\<^sup>,\<^sup>__" [100,100]100) where
  "\<diamondop>\<^sup>-\<^sup>1\<^sup>,\<^sup>i \<phi> \<equiv> not (\<box>\<^sup>-\<^sup>1\<^sup>,\<^sup>i (not \<phi>))"

definition all_node :: "(nat \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" (binder "AllNode" 65) where
  "AllNode x. P x \<equiv> not (ExNode x. not (P x))"

lemma (in infinite_event_structure) negation_satisfaction:
  shows "(e \<Turnstile> not \<phi>) = (\<not> (e \<Turnstile> \<phi>))"
by(simp add: negation_def)

definition (in infinite_event_structure) validity :: "'a formula \<Rightarrow> bool" ("\<Turnstile>/_" [55]55) where
  "\<Turnstile> \<phi> \<equiv> \<forall>e \<in> (\<Union>i. carriers i). e \<Turnstile> \<phi>"

lemma (in infinite_event_structure) S4_global_transitivity:
  shows "\<Turnstile> \<box>\<^sup>G \<phi> \<rightarrow> \<box>\<^sup>G \<box>\<^sup>G \<phi>"
unfolding validity_def
sorry

lemma (in infinite_event_structure) S4_global_reflexivity:
  shows "\<Turnstile> \<box>\<^sup>G \<phi> \<rightarrow> \<phi>"
unfolding validity_def sorry

lemma (in infinite_event_structure) global_distribution:
  shows "\<Turnstile> \<box>\<^sup>G (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<box>\<^sup>G \<phi>) \<rightarrow> (\<box>\<^sup>G \<psi>)"
unfolding validity_def
sorry

lemma (in infinite_event_structure) global_necessitation:
  assumes "\<Turnstile> \<phi>"
  shows   "\<Turnstile> \<box>\<^sup>G \<phi>"
sorry

lemma (in infinite_event_structure) all_messages_delivered:
  shows "\<Turnstile> Event (i, Broadcast, m) \<rightarrow> \<diamondop>\<^sup>G Event (i, Deliver, m)"
unfolding validity_def globalD_def negation_def
  apply standard+
  apply clarsimp
  apply(rule broadcast_before_delivery)
  apply(frule carriers_message_consistent)
  apply auto
done

lemma (in infinite_event_structure) messages_delivered_once:
  shows "\<Turnstile> Event (i, Deliver, m) \<rightarrow> \<box>\<^sup>i not (Event (i, Deliver, m))"
unfolding validity_def negation_def
  apply standard+
  apply clarsimp
  apply(rule notE[OF node_total_order_irrefl], assumption)
  apply(frule carriers_message_consistent)
  apply auto
done

lemma (in infinite_event_structure) no_out_of_thin_air:
  shows "\<Turnstile> Event (i, Deliver, m) \<rightarrow> ExNode q. (\<diamondop>\<^sup>-\<^sup>1\<^sup>,\<^sup>G (Event (q, Broadcast, m)))"
unfolding validity_def
  apply standard+
  apply(clarsimp simp add: globalD_inv_def negation_def)
  apply(frule carriers_message_consistent, clarsimp) 
  apply(drule delivery_has_a_cause)
  apply clarsimp
  apply(rule_tac x=j in exI)
  apply(rule broadcast_before_delivery, assumption)
done

lemma (in infinite_event_structure) reliable_delivery:
  shows "\<Turnstile> Event (i, Broadcast, m) \<rightarrow> AllNode q. \<diamondop>\<^sup>G (Event (q, Deliver, m))"
unfolding validity_def
  apply standard+
  apply(clarsimp simp add: all_node_def negation_def globalD_inv_def globalD_def disjunction_def)
  apply(frule carriers_message_consistent, clarsimp)
  apply(simp add: broadcast_before_delivery)
done

lemma (in infinite_event_structure) global_order_carriers_closed_split1:
  assumes "(i1, t1, m1) \<sqsubset>\<^sup>G (i2, t2, m2)"
  shows   "(i1, t1, m1) \<in> carriers i1"
using assms
  apply -
  apply(drule global_order_carrier_closed, clarsimp, frule carriers_message_consistent, force)
done

lemma (in infinite_event_structure) global_order_carriers_closed_split2:
  assumes "(i1, t1, m1) \<sqsubset>\<^sup>G (i2, t2, m2)"
  shows   "(i2, t2, m2) \<in> carriers i2"
using assms
  apply -
  apply(drule global_order_carrier_closed, clarsimp, frule carriers_message_consistent, force)
done

lemma (in infinite_event_structure) fifo_broadcast_order:
  shows "\<Turnstile> (Event (i, Broadcast, m1) and \<diamondop>\<^sup>i Event (i, Broadcast, m2)) \<rightarrow>
          \<box>\<^sup>G(Event (j, Deliver, m2) \<rightarrow> \<diamondop>\<^sup>-\<^sup>1\<^sup>,\<^sup>j Event (j, Deliver, m1))"
using assms unfolding validity_def
  apply(clarsimp simp add: negation_def localD_inv_def localD_def globalD_def)
  apply(frule carriers_message_consistent, clarsimp)
  apply(rule broadcast_fifo_order[rotated])
  apply assumption
  apply(drule global_order_carriers_closed_split2)
  apply (drule no_message_lost)
  apply force
done

lemma (in infinite_event_structure) causal_broadcast_order:
  shows "\<Turnstile> (Event (i, Deliver, m1) and \<diamondop>\<^sup>i Event (i, Broadcast, m2)) \<rightarrow>
          \<box>\<^sup>G(Event (j, Deliver, m2) \<rightarrow> \<diamondop>\<^sup>-\<^sup>1\<^sup>,\<^sup>j Event (j, Deliver, m1))"
using assms unfolding validity_def
  apply(clarsimp simp add: negation_def localD_inv_def localD_def globalD_def)
  apply(frule carriers_message_consistent, clarsimp)
  apply(rule broadcast_causal[rotated])
  apply assumption
  apply(drule global_order_carriers_closed_split2)
  apply(drule delivery_has_a_cause)
  apply clarsimp
  apply (drule no_message_lost)
  apply force
done

locale finite_event_structure = infinite_event_structure +
  assumes finite_carriers: "finite (carriers i)"

definition (in finite_event_structure) ordered_node_events :: "nat \<Rightarrow> 'a event list" where
  "ordered_node_events i \<equiv>
     let events = carriers i in
       linorder.sorted_list_of_set (\<lambda>e1 e2. e1 \<sqsubset>\<^sup>i e2)
         (Set.filter (\<lambda>e.
            case e of (_, Broadcast, _) \<Rightarrow> HOL.False | (_, Delivery, _) \<Rightarrow> HOL.True) events)"

section\<open>Network events to...\<close>

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

section\<open>Modal logic of networks\<close>

datatype 'a action
  = Broadcast "'a"
  | Deliver   "'a"

datatype 'a formula
  = True   ("\<top>" 65)
  | False  ("\<bottom>" 65)
  | Conjunction "'a formula" "'a formula" ("_/ &/  _" [75,75]75)
  | Implication "'a formula" "'a formula" ("_/ \<rightarrow>/ _" [65,65]65)
  | Atomic "nat" "'a action"
  | Diamond "'a formula"                  ("\<diamondop>/ _" [85]85)
  | Dnomaid "'a formula"                 ("\<diamondop>\<^sup>-\<^sup>1/ _" [85]85)
  | Box "'a formula"                      ("\<box>/ _" [85]85)
  | Xob "'a formula"                     ("\<box>\<^sup>-\<^sup>1/ _" [85]85)

syntax
  Broadcast_syntax :: "nat \<Rightarrow> 'a \<Rightarrow> 'a formula" ("\<B>/_/_" [85,85]85)
  Deliver_syntax   :: "nat \<Rightarrow> 'a \<Rightarrow> 'a formula" ("\<D>/_/_" [85,85]85)

translations
  "\<B> node msg" \<rightleftharpoons> "CONST Atomic node (CONST Broadcast msg)"
  "\<D> node msg" \<rightleftharpoons> "CONST Atomic node (CONST Deliver msg)"

fun quantN :: "nat \<Rightarrow> (nat \<Rightarrow> 'a formula) \<Rightarrow> ('a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula) \<Rightarrow> 'a formula \<Rightarrow> 'a formula" where
  "quantN 0       f j e = e" |
  "quantN (Suc m) f j e = j (f m) (quantN m f j e)"

fun satisfaction :: "(nat \<Rightarrow> 'a action \<times> nat) \<times> nat \<Rightarrow> 'a formula \<Rightarrow> bool" ("_/ \<Turnstile>/ _" [65,65]65) where
  "(\<M>, a) \<Turnstile> \<top>      = HOL.True" |
  "(\<M>, a) \<Turnstile> \<bottom>     = HOL.False" |
  "(\<M>, a) \<Turnstile> \<phi> & \<psi> = ((\<M>, a) \<Turnstile> \<phi> \<and> (\<M>, a) \<Turnstile> \<psi>)" |
  "(\<M>, a) \<Turnstile> \<phi> \<rightarrow> \<psi> = ((\<M>, a) \<Turnstile> \<phi> \<longrightarrow> (\<M>, a) \<Turnstile> \<psi>)" |
  "(\<M>, a) \<Turnstile> \<diamondop> \<phi> = (\<exists>a'. a < a' \<and> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> \<box> \<phi> = (\<forall>a'. a < a' \<longrightarrow> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> \<diamondop>\<^sup>-\<^sup>1 \<phi> = (\<exists>a'. a' < a \<and> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> \<box>\<^sup>-\<^sup>1 \<phi> = (\<forall>a'. a' < a \<longrightarrow> (\<M>, a') \<Turnstile> \<phi>)" |
  "(\<M>, a) \<Turnstile> Atomic node action = (\<M> a = (action, node))"

definition Negation :: "'a formula \<Rightarrow> 'a formula" ("not/ _" [85]85) where
  "Negation \<phi> \<equiv> \<phi> \<rightarrow> \<bottom>"

definition Disjunction :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" ("_/ orelse/ _" [75,75]75) where
  "\<phi> orelse \<psi> \<equiv> not ((not \<phi>) & (not \<psi>))"

lemma Negation_satisfaction:
  shows "\<M> \<Turnstile> not \<phi> = (\<not> (\<M> \<Turnstile> \<phi>))"
unfolding Negation_def by (cases "\<M>", simp)

lemma Diamond_Box_deMorgan1:
  shows "\<M> \<Turnstile> not \<diamondop> \<phi> = \<M> \<Turnstile> \<box> not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Diamond_Box_deMorgan2:
  shows "\<M> \<Turnstile> not \<box> \<phi> = \<M> \<Turnstile> \<diamondop> not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Dnomaid_Xob_deMorgan1:
  shows "\<M> \<Turnstile> not \<diamondop>\<^sup>-\<^sup>1 \<phi> = \<M> \<Turnstile> \<box>\<^sup>-\<^sup>1 not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Dnomaid_Xob_deMorgan2:
  shows "\<M> \<Turnstile> not \<box>\<^sup>-\<^sup>1 \<phi> = \<M> \<Turnstile> \<diamondop>\<^sup>-\<^sup>1 not \<phi>"
unfolding Negation_def by (cases "\<M>", simp)

lemma Disjunction_Conjunction_deMorgan1:
  shows "\<M> \<Turnstile> not (\<phi> orelse \<psi>) = \<M> \<Turnstile> (not \<phi>) & (not \<psi>)"
unfolding Disjunction_def Negation_def by (cases "\<M>", simp)

lemma Disjunction_Conjunction_deMorgan2:
  shows "\<M> \<Turnstile> not (\<phi> & \<psi>) = \<M> \<Turnstile> (not \<phi>) orelse (not \<psi>)"
unfolding Disjunction_def Negation_def by (cases "\<M>", simp)

definition valid :: "'a formula \<Rightarrow> bool" ("\<Turnstile>/ _" [50]50) where
  "\<Turnstile> \<phi> \<equiv> \<forall>\<M>. \<M> \<Turnstile> \<phi>"

locale fixed_nodes =
  fixes node_count :: "nat"

definition (in fixed_nodes) exists :: "(nat \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" (binder "Ex" 55) where
  "exists f \<equiv> quantN node_count f Disjunction False"

definition (in fixed_nodes) forall :: "(nat \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" (binder "All" 55) where
  "forall f \<equiv> quantN node_count f Conjunction True"

locale network = fixed_nodes +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes all_messages_delivered: "\<And>p::nat. \<And>m::'a. \<Turnstile> (\<B> p m) \<rightarrow> \<diamondop> (\<D> p m)"
  and messages_are_unique: "\<And>p::nat. \<And>m::'a. \<Turnstile> (\<D> p m) \<rightarrow> \<box> not (\<D> p m)"
  and no_out_thin_air: "\<And>p::nat. \<And>m::'a. \<Turnstile> \<D> p m \<rightarrow> (Ex q. (\<diamondop>\<^sup>-\<^sup>1 (\<B> q m)))"
  and no_message_lost: "\<And>p::nat. \<And>m::'a. \<Turnstile> (\<D> p m) \<rightarrow> (All q. ((\<diamondop> (\<D> q m)) orelse (\<diamondop>\<^sup>-\<^sup>1 (\<D> q m))))"
  and causal_delivery: "\<And>p::nat. \<And>m1 m2::'a. R m1 m2 \<Longrightarrow> \<Turnstile> (\<D> p m2) \<rightarrow> \<diamondop>\<^sup>-\<^sup>1 (\<D> p m1)"

lemma (in network) All_elim:
  assumes "\<Turnstile> All p. f p"
  shows   "\<And>p. p < node_count \<Longrightarrow> \<Turnstile> f p"
using assms unfolding forall_def valid_def
  apply clarsimp
  apply(induction node_count; clarsimp)
  apply(subgoal_tac "p = node_count \<or> p < node_count")
  apply force+
done

lemma (in network) All_intro:
  assumes "\<And>p. p < node_count \<Longrightarrow> \<Turnstile> f p"
  shows   "\<Turnstile> All p. f p"
using assms unfolding forall_def valid_def
  apply clarsimp
  apply(induction node_count; clarsimp)
done

lemma (in network) Implication_intro:
  assumes "\<Turnstile> p \<Longrightarrow> \<Turnstile> q"
  shows   "\<Turnstile> p \<rightarrow> q"
using assms unfolding valid_def
  apply simp
  apply standard+
  

lemma (in network)
  shows "\<Turnstile> \<B> p m \<rightarrow> (All q. \<diamondop> (D q m))"
unfolding valid_def
  apply standard+
  

section\<open>Modelling the network\<close>

locale network =
  fixes node_count :: "nat"