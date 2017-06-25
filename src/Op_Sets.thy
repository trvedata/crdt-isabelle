theory
  Op_Sets
imports
  Main
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

inductive siblingless_ancestor :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "\<lbrakk> \<nexists>sibling. next_sibling opers listId startId sibling \<rbrakk>
     \<Longrightarrow> siblingless_ancestor opers listId startId startId" |
  "\<lbrakk> siblingless_ancestor opers listId startId prevId;
     child opers listId (Some nextId) prevId;
     \<nexists>sibling. next_sibling opers listId nextId sibling
   \<rbrakk> \<Longrightarrow> siblingless_ancestor opers listId startId nextId"

definition next_elem_auntie :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "next_elem_auntie opers listId prevId nextId \<equiv>
     (\<nexists>child. first_child opers listId (Some prevId) child) \<and>
     (\<nexists>sibling. next_sibling opers listId prevId sibling) \<and>
     (\<exists>ancestor parent. siblingless_ancestor opers listId prevId ancestor \<and>
      child opers listId (Some parent) ancestor \<and>
      next_sibling opers listId parent nextId)"

definition next_elem :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "next_elem opers listId prevId nextId \<equiv>
     first_child opers listId (Some prevId) nextId \<or>
     next_elem_sibling opers listId prevId nextId \<or>
     next_elem_auntie opers listId prevId nextId"

inductive following_elem :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId \<Rightarrow> 'elemId \<Rightarrow> bool" where
  "\<lbrakk> have_list_elem opers listId someId \<rbrakk> \<Longrightarrow> following_elem opers listId someId someId" |
  "\<lbrakk> following_elem opers listId prevId midId; next_elem opers listId midId nextId \<rbrakk> \<Longrightarrow> following_elem opers listId prevId nextId"

definition list_elem_set :: "('objId, 'elemId::linorder) operation set \<Rightarrow> 'objId \<Rightarrow> 'elemId set" where
  "list_elem_set opers listId \<equiv> {elemId. \<exists>firstId.
     first_elem opers listId firstId \<and> following_elem opers listId firstId elemId}"

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

lemma first_child_subset:
  shows "{childId. first_child opers listId parentId childId}
       \<subseteq> {childId. child opers listId parentId childId}"
by(simp add: Collect_mono first_child_def)

lemma next_elem_exclusive_child:
  assumes "{nextId. first_child opers listId (Some prevId) nextId} \<noteq> {}"
  shows "{nextId. next_elem_sibling opers listId prevId nextId} = {}"
    and "{nextId. next_elem_auntie opers listId prevId nextId} = {}"
using assms apply(simp add: next_elem_sibling_def)
using assms next_elem_auntie_def by force

lemma next_elem_exclusive_sibling:
  assumes "{nextId. next_elem_sibling opers listId prevId nextId} \<noteq> {}"
  shows "{nextId. first_child opers listId (Some prevId) nextId} = {}"
    and "{nextId. next_elem_auntie opers listId prevId nextId} = {}"
using assms by(simp_all add: next_elem_auntie_def next_elem_sibling_def)

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
  assumes "first_child opers listId parentId child1"
  assumes "first_child opers listId parentId child2"
  shows "child1 = child2"
by (meson assms first_child_def not_less_iff_gr_or_eq)

lemma list_invariant:
  assumes "valid_ops opers"
    and "P {}"
    and "\<And>opers oper. \<nexists>prev elemId. oper = Insert listId prev elemId \<Longrightarrow>
           P opers \<Longrightarrow> P (insert oper opers)"
    and "\<And>opers oper prev elemId.
           oper = Insert listId prev elemId \<Longrightarrow>
           prev = None \<or> (\<exists>prevId. prev = Some prevId \<and> have_list_elem opers listId prevId) \<Longrightarrow>
           P opers \<Longrightarrow> P (insert oper opers)"
  shows "P opers"
  using assms(1) apply(induction rule: valid_ops.induct)
  using assms(2) apply simp
  apply(subgoal_tac "valid_op opers oper") prefer 2
  apply(metis apply_op.elims option.distinct(1))
  apply(subgoal_tac "newOpers = insert oper opers") prefer 2 apply simp
  apply(case_tac oper, simp add: assms(3))
  apply(case_tac "x21 = listId") prefer 2 apply(simp add: assms(3))
  apply(subgoal_tac "have_list opers x21") prefer 2 apply force
  apply(subgoal_tac "x22 = None \<or> (\<exists>prevId. x22 = Some prevId \<and> have_list_elem opers x21 prevId)")
  prefer 2 using option.set_sel apply fastforce
  apply(simp add: assms(4))
done

lemma first_elem_exists:
  assumes "valid_ops opers"
  shows "(\<exists>elemId. have_list_elem opers listId elemId) \<longleftrightarrow> (\<exists>firstId. first_elem opers listId firstId)"
  using assms(1) apply -
  apply(drule_tac P="\<lambda>opers. (\<exists>elemId. have_list_elem opers listId elemId) \<longleftrightarrow>
          (\<exists>firstId. first_elem opers listId firstId)" and listId=listId in list_invariant)
  apply(simp add: have_list_elem_def first_elem_def first_child_def child_def)
  prefer 3 apply blast
  apply(rule iffI)
  apply(subgoal_tac "\<exists>elemId. have_list_elem opers listId elemId")
  prefer 2 apply(metis have_list_elem_def insertE)
  apply(metis first_elem_def first_child_def child_def insert_iff)
  apply(erule exE, rule_tac x=firstId in exI)
  apply(meson child_def first_child_def first_elem_def have_list_elem_def)
  apply(rule iffI) prefer 2
  apply(meson have_list_elem_def insertI1)
  apply(case_tac "\<exists>elemId. have_list_elem opers listId elemId") prefer 2
  apply(subgoal_tac "prev = None") prefer 2 apply simp
  apply(rule_tac x=elemId in exI)
  apply(simp add: first_elem_def first_child_def child_def have_list_elem_def)
  apply blast
  apply(subgoal_tac "\<exists>firstId. first_elem opers listId firstId", erule exE)
  prefer 2 apply blast
  apply((erule exE)+, erule disjE)
  apply(case_tac "elemId < firstId")
  apply(rule_tac x=firstId in exI)
  apply(auto simp: first_elem_def first_child_def child_def)[1]
  apply(rule_tac x=elemId in exI)
  apply(auto simp: first_elem_def first_child_def child_def)[1]
  apply(rule_tac x=firstId in exI)
  apply(auto simp: first_elem_def first_child_def child_def)[1]
done

lemma next_sibling_unique:
  assumes "next_sibling opers listId prevId next1"
  assumes "next_sibling opers listId prevId next2"
  shows "next1 = next2"
by (meson assms next_sibling_def not_less_iff_gr_or_eq)

lemma siblingless_ancestor_indeed:
  assumes "siblingless_ancestor opers listId startId anc"
  shows "\<nexists>sibling. next_sibling opers listId anc sibling"
using assms by(induction rule: siblingless_ancestor.induct, auto)

lemma ancestor_chain:
  assumes "valid_ops opers"
    and "ancs = {anc. siblingless_ancestor opers listId startId anc}"
  shows "\<exists>list. set list = ancs \<and>
           (\<forall>pre x y suf. list = pre@x#y#suf \<longrightarrow> child opers listId (Some x) y)"
  using assms
  apply(induction rule: siblingless_ancestor.inducts)
  oops

thm siblingless_ancestor.induct

lemma next_elem_auntie_unique:
  assumes "valid_ops opers"
    and "next_elem_auntie opers listId prevId next1"
    and "next_elem_auntie opers listId prevId next2"
  shows "next1 = next2"
  using assms apply(simp add: next_elem_auntie_def)
  apply(erule exE, (erule conjE)+)+
  apply(case_tac "ancestora = ancestor", clarsimp)
  apply(metis child_def elem_id_unique next_sibling_unique option.sel)
  apply(induction rule: siblingless_ancestor.induct)
  sorry

lemma next_elem_unique:
  assumes "valid_ops opers"
    and "next_elem opers listId prevId next1"
    and "next_elem opers listId prevId next2"
  shows "next1 = next2"
  using assms apply -
  apply(case_tac "{nextId. first_child opers listId (Some prevId) nextId} \<noteq> {}")
  apply(metis bex_empty first_child_unique mem_Collect_eq next_elem_def next_elem_exclusive_child)
  apply(case_tac "{nextId. next_elem_sibling opers listId prevId nextId} \<noteq> {}")
  using next_elem_def next_elem_exclusive_sibling(2) next_elem_sibling_def
    next_sibling_unique apply fastforce
  apply(simp add: next_elem_auntie_unique next_elem_def)
done

thm following_elem.inducts
thm following_elem.induct
thm following_elem.intros
thm following_elem.cases
thm following_elem.simps

lemma following_elem_unaffected:
  assumes "\<forall>prev elemId. oper \<noteq> Insert listId prev elemId"
  shows "following_elem opers listId firstId elemId =
         following_elem (insert oper opers) listId firstId elemId"
  apply(subgoal_tac "following_elem opers listId firstId elemId \<noteq>
         following_elem (insert oper opers) listId firstId elemId \<Longrightarrow>
         \<exists>prev elemId. oper = Insert listId prev elemId")
  using assms apply force
  apply(case_tac "following_elem opers listId firstId elemId")
  oops

lemma list_order_complete:
  assumes "valid_ops opers"
  shows "list_elem_set opers listId = {elemId. have_list_elem opers listId elemId}"
  apply(subgoal_tac "\<And>elemId. have_list_elem opers listId elemId \<longleftrightarrow>
    (\<exists>firstId. first_elem opers listId firstId \<and> following_elem opers listId firstId elemId)")
  apply(simp add: list_elem_set_def)
  using assms(1) apply -
  apply(drule_tac P="\<lambda>opers. \<forall>elemId. have_list_elem opers listId elemId \<longleftrightarrow>
          (\<exists>firstId. first_elem opers listId firstId \<and> following_elem opers listId firstId elemId)"
        and listId=listId in list_invariant)
  apply(simp add: child_def first_child_def first_elem_def have_list_elem_def)
  prefer 3 apply simp
  apply clarsimp
  apply(erule_tac x=elemId in allE)
  apply(subgoal_tac "have_list_elem opers listId elemId =
                have_list_elem (insert oper opers) listId elemId")
  prefer 2 apply(metis have_list_elem_def insert_iff)
  apply(subgoal_tac "\<forall>firstId. first_elem opers listId firstId =
                first_elem (insert oper opers) listId firstId")
  prefer 2 apply(metis child_def first_child_def first_elem_def insert_iff)
  apply(subgoal_tac "\<forall>firstId. following_elem opers listId firstId elemId =
                following_elem (insert oper opers) listId firstId elemId")
  apply(blast, meson following_elem_unaffected)
  oops

end