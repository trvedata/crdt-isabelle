theory
  Fresh_Start
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin

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
  shows "insert [] e2 i2 \<bind> (\<lambda>ys. insert ys e1 (Some i)) = None"
using assms by (case_tac "i2") clarsimp+

lemma insert_insert_body_commute:
  assumes "a \<noteq> aa"
          "aa \<noteq> fst e2"
          "aa \<notin> fst ` set xs"
          "fst e2 \<notin> fst ` set xs"
          "distinct (map fst xs)"
  shows   "insert (insert_body xs (aa, ba)) e2 (Some a) = insert xs e2 (Some a) \<bind> (\<lambda>y. Some (insert_body y (aa, ba)))"
using assms
  apply(induction xs)
    apply clarsimp
    apply clarsimp
    apply(force simp add: insert_body_commutes)
  done

lemma insert_commutes:
  assumes "distinct (map fst (e1#e2#xs))" "i1 = None \<or> i1 \<noteq> Some (fst e2)" "i2 = None \<or> i2 \<noteq> Some (fst e1)"
  shows   "do { ys \<leftarrow> insert xs e1 i1; insert ys e2 i2 } = do { ys \<leftarrow> insert xs e2 i2; insert ys e1 i1 }"
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

end