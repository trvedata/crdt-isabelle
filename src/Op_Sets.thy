theory
  Op_Sets
imports
  Util
begin

datatype ('objId, 'elemId) operation =
  MakeList 'objId |
  Insert 'objId "'elemId option" "'elemId"

definition have_list :: "('objId, 'elemId) operation set \<Rightarrow> 'objId \<Rightarrow> bool" where
  "have_list opers listId \<equiv> MakeList listId \<in> opers"

definition have_list_elem :: "('objId, 'elemId) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "have_list_elem opers listId elemId \<equiv> \<exists>prev. Insert listId prev elemId \<in> opers"

definition child :: "('objId, 'elemId) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId option \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "child opers listId parentId childId \<equiv> Insert listId parentId childId \<in> opers"

definition first_child :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId option \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "first_child opers listId parentId childId \<equiv>
     child opers listId parentId childId \<and>
     (\<nexists>other. child opers listId parentId other \<and> childId < other)"

definition first_elem :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "first_elem opers listId elemId \<equiv> first_child opers listId None elemId"

definition sibling :: "('objId, 'elemId) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "sibling opers listId child1 child2 \<equiv>
     \<exists>parent. child opers listId parent child1 \<and> child opers listId parent child2"

definition next_sibling :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "next_sibling opers listId prevId nextId \<equiv>
     sibling opers listId prevId nextId \<and>
     nextId < prevId \<and>
     (\<nexists>other. sibling opers listId prevId other \<and> nextId < other \<and> other < prevId)"

definition next_elem_sibling :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "next_elem_sibling opers listId prevId nextId \<equiv>
     (\<nexists>child. first_child opers listId (Some prevId) child) \<and>
     next_sibling opers listId prevId nextId"

definition next_elem_aunt :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "next_elem_aunt opers listId prevId nextId \<equiv>
     (\<nexists>child. first_child opers listId (Some prevId) child) \<and>
     (\<nexists>sibling. next_sibling opers listId prevId sibling) \<and>
     (\<exists>parent. child opers listId (Some parent) prevId \<and> next_sibling opers listId parent nextId)"

definition next_elem :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "next_elem opers listId prevId nextId \<equiv>
     first_child opers listId (Some prevId) nextId \<or>
     next_elem_sibling opers listId prevId nextId \<or>
     next_elem_aunt opers listId prevId nextId"

fun valid_op :: "('objId, 'elemId) operation set \<Rightarrow> ('objId, 'elemId) operation \<Rightarrow> bool" where
  "valid_op opers (MakeList listId) = (\<not> have_list opers listId)" |
  "valid_op opers (Insert listId ref elem) = (
     have_list opers listId \<and>
     (case ref of None \<Rightarrow> True | Some refId \<Rightarrow> have_list_elem opers listId refId) \<and>
     \<not> have_list_elem opers listId elem)"

fun apply_op :: "('objId, 'elemId) operation set \<Rightarrow> ('objId, 'elemId) operation \<rightharpoonup> ('objId, 'elemId) operation set" where
  "apply_op opers oper = (if valid_op opers oper then Some (insert oper opers) else None)"

inductive valid_ops :: "('objId, 'elemId) operation set \<Rightarrow> bool" where
  "valid_ops {}" |
  "\<lbrakk> valid_ops opers; apply_op opers oper = Some newOpers \<rbrakk> \<Longrightarrow> valid_ops newOpers"

inductive list_elem_set :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId set \<Rightarrow> bool" where
  "\<lbrakk> valid_ops opers; first_elem opers listId elemId \<rbrakk> \<Longrightarrow> list_elem_set opers listId {elemId}" |
  "\<lbrakk> listElems opers listId elems; prevId \<in> elems; next_elem opers listId elem nextId \<rbrakk>
     \<Longrightarrow> list_elem_set opers listId (insert nextId elems)"

lemma first_child_subset:
  shows "{childId. first_child opers listId parentId childId}
       \<subseteq> {childId. child opers listId parentId childId}"
by(simp add: Collect_mono first_child_def)

lemma next_elem_exclusive_child:
  assumes "{nextId. first_child opers listId (Some prevId) nextId} \<noteq> {}"
  shows "{nextId. next_elem_sibling opers listId prevId nextId} = {}"
    and "{nextId. next_elem_aunt opers listId prevId nextId} = {}"
using assms apply(simp add: next_elem_sibling_def)
using assms next_elem_aunt_def by force

lemma next_elem_exclusive_sibling:
  assumes "{nextId. next_elem_sibling opers listId prevId nextId} \<noteq> {}"
  shows "{nextId. first_child opers listId (Some prevId) nextId} = {}"
    and "{nextId. next_elem_aunt opers listId prevId nextId} = {}"
using assms by (simp add: next_elem_aunt_def next_elem_sibling_def)+

lemma set_pick_2:
  assumes "card S > 1"
  shows "\<exists>x y. x \<noteq> y \<and> {x, y} \<subseteq> S"
  using assms
  apply(subgoal_tac "\<exists>x. x \<in> S") defer
  using card_gt_0_iff apply fastforce
  apply(erule exE, rule_tac x=x in exI)
  apply(subgoal_tac "card (S - {x}) > 0")
  apply(metis Diff_eq_empty_iff Diff_idemp card_gt_0_iff insertCI insert_subsetI subsetI)
  apply(metis One_nat_def card.insert_remove card_ge_0_finite gr_zeroI insert_Diff
    insert_Diff_single less_trans nat_neq_iff)
done

lemma elem_id_unique:
  assumes "valid_ops opers"
    and "Insert listId prev1 elemId \<in> opers"
    and "Insert listId prev2 elemId \<in> opers"
  shows "prev1 = prev2"
  using assms apply(induction rule: valid_ops.induct)
  apply(simp add: have_list_elem_def)
  apply(subgoal_tac "valid_op opers oper") prefer 2
  apply(metis apply_op.elims option.distinct(1))
  apply(subgoal_tac "newOpers = insert oper opers") prefer 2 apply simp
  apply(case_tac "have_list_elem opers listId elemId")
  apply(metis (no_types, lifting) insert_iff valid_op.simps(2))
  apply(subgoal_tac "{prev. Insert listId prev elemId \<in> opers} = {}")
  prefer 2 apply (simp add: have_list_elem_def)
  apply(subgoal_tac "\<exists>prev. oper = Insert listId prev elemId")
  prefer 2 apply(metis have_list_elem_def insertE, erule exE)
  apply(subgoal_tac "{prev. Insert listId prev elemId \<in> newOpers} = {prev}")
  apply simp_all
done

lemma elem_id_card:
  assumes "valid_ops opers"
    and "have_list_elem opers listId elemId"
  shows "card {prev. Insert listId prev elemId \<in> opers} = 1"
  using assms apply(induction rule: valid_ops.induct)
  apply(simp add: have_list_elem_def)
  apply(subgoal_tac "valid_op opers oper") prefer 2
  using apply_op.elims apply fastforce
  apply(subgoal_tac "newOpers = insert oper opers") prefer 2 apply simp
  apply(case_tac "have_list_elem opers listId elemId")
  apply(metis (no_types, lifting) Collect_cong insert_iff valid_op.simps(2))
  apply(subgoal_tac "{prev. Insert listId prev elemId \<in> opers} = {}")
  prefer 2 apply (simp add: have_list_elem_def)
  apply(subgoal_tac "\<exists>prev. oper = Insert listId prev elemId")
  prefer 2 apply(metis have_list_elem_def insertE, erule exE)
  apply(subgoal_tac "{prev. Insert listId prev elemId \<in> newOpers} = {prev}")
  apply simp_all
done

lemma parent_exists:
  assumes "valid_ops opers"
    and "Insert listId (Some parentId) elemId \<in> opers"
  shows "have_list_elem opers listId parentId"
  using assms apply(induction rule: valid_ops.induct)
  apply(simp add: have_list_elem_def)
  apply(subgoal_tac "valid_op opers oper") prefer 2
  apply(metis apply_op.elims option.distinct(1))
  apply(subgoal_tac "newOpers = insert oper opers") prefer 2 apply simp
  apply(case_tac "oper = Insert listId (Some parentId) elemId")
  apply(subgoal_tac "have_list_elem opers listId parentId")
  prefer 2 apply simp
  apply(metis have_list_elem_def insert_iff)+
done

lemma first_child_unique:
  shows "card {childId. first_child opers listId parentId childId} \<le> 1"
  apply(subgoal_tac "card {childId. first_child opers listId parentId childId} > 1 \<Longrightarrow> False", force)
  apply(subgoal_tac "\<exists>x y. x \<noteq> y \<and> {x, y} \<subseteq> {childId. first_child opers listId parentId childId}")
  apply(metis first_child_def insert_subset mem_Collect_eq not_less_iff_gr_or_eq)
  using set_pick_2 apply blast
done

lemma next_sibling_unique:
  shows "card {nextId. next_sibling opers listId prevId nextId} \<le> 1"
  apply(subgoal_tac "card {nextId. next_sibling opers listId prevId nextId} > 1 \<Longrightarrow> False", force)
  apply(subgoal_tac "\<exists>x y. x \<noteq> y \<and> {x, y} \<subseteq> {nextId. next_sibling opers listId prevId nextId}")
  apply(metis next_sibling_def insert_subset mem_Collect_eq not_less_iff_gr_or_eq)
  using set_pick_2 apply blast
done

lemma next_elem_aunt_unique:
  assumes "valid_ops opers"
    and "have_list_elem opers listId prevId"
  shows "card {nextId. next_elem_aunt opers listId prevId nextId} \<le> 1"
  apply(case_tac "{nextId. first_child opers listId (Some prevId) nextId} \<noteq> {}")
  apply(simp add: next_elem_exclusive_child)
  apply(case_tac "{nextId. next_sibling opers listId prevId nextId} \<noteq> {}")
  apply(simp add: next_elem_aunt_def)
  apply(case_tac "\<exists>parentId. child opers listId (Some parentId) prevId", erule exE)
  prefer 2 apply(simp add: next_elem_aunt_def)
  apply(subgoal_tac "\<And>p. Insert listId p prevId \<in> opers \<Longrightarrow> p = Some parentId")
  prefer 2 apply(metis assms(1) child_def elem_id_unique)
  apply(subgoal_tac "card {nextId. next_elem_aunt opers listId prevId nextId} > 1 \<Longrightarrow> False", force)
  apply(subgoal_tac "\<exists>x y. x \<noteq> y \<and> {x, y} \<subseteq> {nextId. next_elem_aunt opers listId prevId nextId}")
  prefer 2 using set_pick_2 apply blast
  apply((erule exE)+, erule conjE)
  apply(simp add: next_elem_aunt_def, erule conjE, (erule exE)+, (erule conjE)+)
  apply(subgoal_tac "parent = parentId \<and> parenta = parentId")
  prefer 2 apply(metis child_def option.inject, clarsimp)
  apply(meson next_sibling_def not_less_iff_gr_or_eq)
done

lemma next_elem_unique:
  assumes "valid_ops opers"
  shows "card {nextId. next_elem opers listId prevId nextId} \<le> 1"
  apply(subgoal_tac "{nextId. next_elem opers listId prevId nextId} =
     {nextId. first_child opers listId (Some prevId) nextId} \<union>
     {nextId. next_elem_sibling opers listId prevId nextId} \<union>
     {nextId. next_elem_aunt opers listId prevId nextId}")
  prefer 2 using next_elem_def apply fastforce
  apply(case_tac "{nextId. first_child opers listId (Some prevId) nextId} \<noteq> {}")
  apply(metis next_elem_exclusive_child first_child_unique Un_empty_right)
  apply(case_tac "{nextId. next_elem_sibling opers listId prevId nextId} \<noteq> {}")
  apply(metis (no_types, lifting) next_elem_exclusive_sibling next_sibling_unique Collect_cong
    Un_absorb1 empty_def empty_subsetI next_elem_sibling_def sup_bot.right_neutral)
  apply(metis assms next_elem_aunt_unique Collect_empty_eq One_nat_def card_eq_0_iff child_def
    have_list_elem_def inf_sup_aci(5) le_SucI le_zero_eq next_elem_aunt_def sup_bot.right_neutral)
done

lemma list_order_complete:
  assumes "list_elem_set opers listId elemIds"
  shows "\<And>elem. elem \<in> elemIds \<longleftrightarrow> have_list_elem opers listId elem"
  oops

end