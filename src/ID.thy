theory
  ID
imports
  RGA
  "~~/src/HOL/Library/Product_Lexorder"
begin
  
locale lamport_rga = rga history for history :: "nat \<Rightarrow> (nat \<times> nat, 'b) operation event list" +
  assumes lamport_spec: "Broadcast (Insert e n) \<in> set (history i) \<Longrightarrow>
    (\<forall>e' n'. hb (Insert e' n') (Insert e n) \<longrightarrow> fst (fst e') < counter) \<Longrightarrow> fst e = (counter, i)"

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
proof
  fix e2 e1 n2 n1
  define next_id :: _ where "next_id \<equiv> \<lambda>j. (Suc (Max (fst ` fst ` fst ` { (e, n). Deliver (Insert e n) \<sqsubset>\<^sup>j Deliver (Insert e1 n1) })), j)"  
  assume A: "hb (Insert e2 n2) (Insert e1 n1)"
  from this obtain j where B: "Broadcast (Insert e1 n1) \<in> set (history j)" and "Deliver (Insert e1 n1) \<in> set (history j)"
    using hb_broadcast_exists2 by (meson deliver_locally insert_subset local_order_carrier_closed)
  hence "Deliver (Insert e2 n2) \<sqsubset>\<^sup>j Deliver (Insert e1 n1)"
    using causal_delivery \<open>hb (Insert e2 n2) (Insert e1 n1)\<close> by blast
  have C: "\<forall>e' n'. hb (Insert e' n') (Insert e1 n1) \<longrightarrow> fst (fst e') < fst (next_id j)"
  proof(standard+)
    fix e' n'
    assume "hb (Insert e' n') (Insert e1 n1)"
    hence "Deliver (Insert e' n') \<sqsubset>\<^sup>j Deliver (Insert e1 n1)"
      using \<open>Deliver (Insert e1 n1) \<in> set (history j)\<close> causal_delivery by blast
    hence D: "fst (fst e') \<in> fst ` fst ` fst ` { (e, n). Deliver (Insert e n) \<sqsubset>\<^sup>j Deliver (Insert e1 n1) }"
      by (metis (no_types, lifting) case_prod_conv fst_conv imageI mem_Collect_eq)
    also have "finite (fst ` fst ` fst ` { (e, n). Deliver (Insert e n) \<sqsubset>\<^sup>j Deliver (Insert e1 n1) })"
      apply -
      apply(rule finite_imageI, rule finite_imageI, rule finite_imageI)
      apply(subgoal_tac "{(e, n). Deliver (Insert e n) \<sqsubset>\<^sup>j Deliver (Insert e1 n1)} \<subseteq> {(e, n). Deliver (Insert e n) \<in> set (history j)}")
       apply(subgoal_tac "finite {(e, n). Deliver (Insert e n) \<in> set (history j)}")
      using infinite_super apply blast
      using finite_deliveries apply force
      apply(rule subsetI, drule CollectD, rule CollectI)
      apply(simp split: prod.split_asm)
      apply(metis history_order_def in_set_conv_decomp)
      done (* What is happening here?  This should be easy... *)
    hence "fst (fst e') \<le> Max (fst ` fst ` fst ` { (e, n). Deliver (Insert e n) \<sqsubset>\<^sup>j Deliver (Insert e1 n1) })"
      using D Max_ge by simp
    thus "fst (fst e') < fst (next_id j)"
      using D Max_ge next_id_def by simp
  qed
  thus "fst e2 < fst e1"
    using A lamport_spec[OF B, where counter="fst (next_id j)"] C less_prod_def' by(metis (no_types, lifting) fst_conv)
qed

end
    
  
  