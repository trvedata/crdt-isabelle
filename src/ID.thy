theory
  ID
imports
  RGA
  "~~/src/HOL/Library/Product_Lexorder"
begin
  
locale lamport_rga = rga history for history :: "nat \<Rightarrow> (nat \<times> nat, 'b) operation event list" +
  assumes lamport_spec: "hb (Insert e n') (Insert f n) \<Longrightarrow> fst (fst e) < fst (fst f)"

(* What the fuck... *)
lemma finite_deliveries:
  shows "finite {(e, n). Deliver (Insert e n) \<in> set xs}"
  apply(induction xs, clarsimp)
  apply clarsimp
  apply(auto split: prod.split_sel prod.split_sel_asm)
  apply(case_tac a; clarsimp; case_tac x2; clarsimp; case_tac x12; clarsimp)
   apply(subgoal_tac "{x. fst x = (a, aa, b) \<and> snd x = None} = {} \<or> {x. fst x = (a, aa, b) \<and> snd x = None} = {((a, aa, b), None)}")
    apply(erule disjE, clarsimp, force)
    apply (smt Collect_cong finite.simps not_finite_existsD prod_eq_iff singleton_conv2)
    apply force
  apply(subgoal_tac "{x. fst x = (a, aa, b) \<and> snd x = Some ab} = {} \<or> {x. fst x = (a, aa, b) \<and> snd x = Some ab} = {((a, aa, b), Some ab)}")
   apply(erule disjE, clarsimp, force)
  apply auto
  done
    
sublocale lamport_rga < id_consistent_rga_network
  apply standard
  apply(frule lamport_spec)
  apply(auto split: prod.split_asm prod.split)
  done
    
lemma fst_prod_less:
  assumes "fst x < fst y"
  shows "x < y"
  using assms by(simp add: prod_less_def)
    (*
(* Not needed, now? *)
lemma (in lamport_rga) Insert_between_elements:
  assumes "xs@[Broadcast (Insert e (Some (fst ref)))] prefix of j"
      and "apply_operations xs = Some (pre@ref#suf)"
    shows "insert (pre@ref#suf) e (Some (fst ref)) = Some (pre@ref#e#suf)"
  using assms
  apply -
  apply(rule insert_between_elements, force)
  using apply_operations_distinct apply blast
   apply(subgoal_tac "\<exists>j::(nat \<times> nat, 'b) elt. i' = fst j", erule exE)
    apply(subgoal_tac "fst ja < fst e", force)
   apply(rule fst_prod_less)
   apply(subgoal_tac "Broadcast (Insert e (Some (fst ref))) \<in> set (history j)")
    apply(drule allowed_insert)
    apply(erule disjE, force)
    apply(erule exE)+
    apply(erule conjE)
    apply(rule_tac n'="n''" in lamport_spec[where n="Some (fst ref)"])
    apply(rule_tac i=j in hb.intros(2))
    apply(subgoal_tac "Deliver (Insert ja n'') \<sqsubset>\<^sup>j Deliver (Insert (n', v, b) n'')")
      using node_total_order_trans apply blast
     apply(frule apply_opers_idx_elems[rotated], force)
        apply(subgoal_tac "i' \<in> set (indices xs)")
         apply(subgoal_tac "\<exists>n. Deliver (Insert ja n) \<in> set (history j)")
          apply(erule exE)
        apply(subgoal_tac "n=n''", clarify)
oops
*)
end
    
  
  