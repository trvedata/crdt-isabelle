theory
  Ordered_List
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin

type_synonym ('id, 'v) elt = "'id \<times> 'v \<times> bool"

section\<open>Insert\<close>

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

find_consts name: insert

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
        apply(case_tac "ab < fst e1")
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

lemma insert_no_failure:
  assumes "i = None \<or> (i = Some i' \<and> (\<exists>v b. (i', v, b) \<in> set xs))"
  shows   "\<exists>xs'. insert xs e i = Some xs'"
  using assms
  apply (induct rule: insert.induct)
  apply force
  apply force
  apply clarsimp
  apply (erule meta_impE)
  apply force
  apply clarsimp
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
          apply(case_tac "ad = i")
            apply clarsimp
            apply(metis bind_assoc)
            apply clarsimp
            apply(case_tac "a = ad")
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
      apply(case_tac "insert' list (a, aa, b) None")
        apply clarsimp+
      apply safe
      apply(case_tac "insert' list (a, aa, b) None")
        apply force
        apply(force simp add: insert_body_insert')
    apply(case_tac "insert' list (a, aa, b) (Some ad)")
      apply clarsimp
      apply clarsimp
  done

section\<open>Delete\<close>

fun delete :: "('id::{linorder}, 'v) elt list \<Rightarrow> 'id \<rightharpoonup> ('id, 'v) elt list" where
  "delete []                 i = None" |
  "delete ((i', v, flag)#xs) i = 
     (if i' = i then
        Some ((i', v, True)#xs)
      else
        do { t \<leftarrow> delete xs i
           ; Some ((i',v,flag)#t)
           })"

lemma delete_no_failure:
  assumes "\<exists>v b. (i, v, b) \<in> set xs"
  shows   "\<exists>xs'. delete xs i = Some xs'"
  using assms
  apply (induct xs)
  apply clarsimp
  apply clarsimp
  apply (erule meta_impE)
  apply force
  apply clarsimp
done

lemma delete_commutes:
  shows "do { ys \<leftarrow> delete xs i1; delete ys i2 } = do { ys \<leftarrow> delete xs i2; delete ys i1 }"
  apply(induction xs, simp)
  apply(case_tac "delete xs i1"; case_tac "delete xs i2"; clarsimp)
done

lemma insert_body_delete_commute:
  assumes "i2 \<noteq> fst e"
          "fst x \<noteq> fst e"
          "fst e \<notin> fst ` set xs"
          "distinct (map fst xs)"
  shows   "delete (insert_body xs e) i2 \<bind> (\<lambda>t. Some (x # t)) =
            delete xs i2 \<bind> (\<lambda>y. Some (x # insert_body y e))"
using assms
  apply(induction xs arbitrary: x)
  apply simp
  apply(case_tac "e"; simp)
  apply simp
  apply(case_tac x; clarsimp)
  apply(case_tac "a=i2"; clarsimp)
  apply(case_tac "e"; clarsimp)
  apply(case_tac "e"; clarsimp)
done

lemma insert_delete_commute:
  assumes "distinct (map fst (e#xs))"
          "i1 = None \<or> i1 \<noteq> Some (fst e)"
          "i2 \<noteq> fst e"
  shows   "do { ys \<leftarrow> insert xs e i1; delete ys i2 } = do { ys \<leftarrow> delete xs i2; insert ys e i1 }"
using assms
  apply(induction xs)
  apply(erule disjE; clarsimp)
  apply(cases e; clarsimp)
  apply(cases i1; clarsimp)
  apply(cases e; clarsimp)
  apply(erule disjE; clarsimp)
  apply(case_tac "a=i2"; clarsimp)
  apply(case_tac "e"; clarsimp)
  apply(case_tac "e"; clarsimp)
  apply(case_tac "a=i2"; clarsimp)
  apply(case_tac "i1"; clarsimp)
  apply(case_tac "e"; clarsimp)
  apply(case_tac "i1", simp, case_tac "a < fst e", simp, case_tac e, simp, case_tac e, simp)
  apply clarsimp
  apply(case_tac "ab=i2"; clarsimp)
  apply(subst bind_assoc[symmetric], simp)
  apply(case_tac "a=ab"; clarsimp)
  apply(rule insert_body_delete_commute; simp_all)
  apply(subst bind_assoc[symmetric], simp)
done

end