theory
  Modal_Logic
imports
  Network
  "~~/src/HOL/Library/Product_Lexorder"
begin

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

end