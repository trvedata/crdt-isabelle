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

fun insert_after :: "('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt \<Rightarrow> 'id option \<rightharpoonup> ('id, 'v) elt list" where
  "insert_after xs     e None     = Some (insert_body xs e)" |
  "insert_after []     e (Some i) = None" |
  "insert_after (x#xs) e (Some i) =
     (if fst x = i then
        Some (x#insert_body xs e)
      else
        do { t \<leftarrow> insert_after xs e (Some i)
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

lemma insert_after_insert_body:
  assumes "distinct (map fst (e1#e2#xs))" "i2 \<noteq> Some (fst e1)"
  shows   "insert_after (insert_body xs e1) e2 i2 = do { ys \<leftarrow> insert_after xs e2 i2; Some (insert_body ys e1) }"
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

lemma insert_after_Nil_None:
  assumes "fst e1 \<noteq> fst e2" "i \<noteq> fst e2" "i2 \<noteq> Some (fst e1)"
  shows "insert_after [] e2 i2 \<bind> (\<lambda>ys. insert_after ys e1 (Some i)) = None"
using assms by (case_tac "i2") clarsimp+

lemma insert_after_insert_body_commute:
  assumes "a \<noteq> aa"
          "aa \<noteq> fst e2"
          "aa \<notin> fst ` set xs"
          "fst e2 \<notin> fst ` set xs"
          "distinct (map fst xs)"
  shows   "insert_after (insert_body xs (aa, ba)) e2 (Some a) = insert_after xs e2 (Some a) \<bind> (\<lambda>y. Some (insert_body y (aa, ba)))"
using assms
  apply(induction xs)
    apply clarsimp
    apply clarsimp
    apply(force simp add: insert_body_commutes)
  done

lemma insert_after_commutes:
  assumes "distinct (map fst (e1#e2#xs))" "i1 = None \<or> i1 \<noteq> Some (fst e2)" "i2 = None \<or> i2 \<noteq> Some (fst e1)"
  shows   "do { ys \<leftarrow> insert_after xs e1 i1; insert_after ys e2 i2 } = do { ys \<leftarrow> insert_after xs e2 i2; insert_after ys e1 i1 }"
using assms
  apply(induction rule: insert_after.induct)
    apply clarsimp
    apply(erule disjE)
      apply clarsimp
      apply(force simp add: insert_body_commutes)
      apply(rule insert_after_insert_body, simp, simp, simp)
    apply(erule disjE)
      apply simp
      apply clarsimp
      apply(rule insert_after_Nil_None[symmetric], simp, simp, simp)
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
        apply(force simp add: insert_after_insert_body_commute)
        apply clarsimp
        apply(case_tac i2)
          apply(force cong: Option.bind_cong simp add: insert_after_insert_body)
          apply clarsimp
          apply(case_tac "ab = i")
            apply clarsimp
            apply(metis bind_assoc)
            apply clarsimp
            apply(case_tac "a = ab")
              apply clarsimp
              apply(force cong: Option.bind_cong simp add: insert_after_insert_body)
              apply clarsimp
              apply(metis bind_assoc)
  done




















fun insert :: "('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt \<Rightarrow> 'id option \<rightharpoonup> ('id::{linorder}, 'v) elt list" where
  "insert [] e     None     = Some [e]" |
  "insert [] e     (Some i) = None" |
  "insert (x#xs) e None     =
     (if fst x < fst e then
        Some (e#x#xs)
      else
        case insert xs e None of
          None   \<Rightarrow> None
        | Some t \<Rightarrow> Some (x#t))" |
  "insert (x#xs) e (Some i) =
     (if fst x = i then
        case insert xs e None of
          None   \<Rightarrow> None
        | Some t \<Rightarrow> Some (x#t)
      else
        case insert xs e (Some i) of
          None   \<Rightarrow> None
        | Some t \<Rightarrow> Some (x#t))"

lemma insert_None_condition2 [elim!, dest]:
  assumes "insert xs e None = None"
  shows   "False"
using assms
  by (induction xs, auto, case_tac "a < fst e"; clarsimp) (case_tac "insert xsa e None"; clarsimp)

lemma insert_Some_empty [elim!, dest]:
  assumes "insert xs e i = Some []"
  shows   "False"
using assms
  apply (induct xs)
  apply (case_tac i)
    apply force
    apply force
  apply (case_tac i)
    apply clarsimp
    apply (case_tac "a < fst e")
      apply force
    apply clarsimp
    apply (case_tac "insert xs e None")
      apply force
    apply force
  apply clarsimp
  apply (case_tac "a=aa")
    apply clarsimp
    apply (case_tac "insert xs e None")
      apply force
    apply force
  apply clarsimp
  apply (case_tac "insert xs e (Some aa)")
    apply force
  apply force
done

lemma insert_Some_None_iff:
  shows   "insert xs e (Some i) = None \<longleftrightarrow> i \<notin> set (map fst xs)"
  apply(induction xs, simp)
  apply(case_tac a)
  apply clarsimp
  apply(case_tac "aa = i")
    apply clarsimp
    apply(case_tac "insert xs e None")
      apply clarsimp
      apply clarsimp
    apply clarsimp
    apply(case_tac "insert xs e (Some i)")
      apply force
      apply clarsimp
done

lemma insertNoneNoneNoneNone:
  assumes
    "distinct (map fst (e1#e2#xs))"
    "insert xs e1 None = Some xs1"
    "insert xs e2 None = Some xs2"
    "insert xs1 e2 None = Some xs1'"
    "insert xs2 e1 None = Some xs2'"
  shows "xs1' = xs2'"
using assms
  apply (induct xs arbitrary: xs1 xs2 xs1' xs2')
  apply clarsimp
  apply(cases "fst e1 < fst e2"; clarsimp)
    apply(cases "fst e2 < fst e1"; clarsimp)    
    apply force
  apply(cases "fst e2 < fst e1")
    apply force
  apply force
  apply clarsimp
  apply (rename_tac i e xs xs1 xs2 xs1' xs2')
  apply (case_tac " insert xs e1 None")
    apply force
  apply (case_tac " insert xs e2 None")
    apply force
  apply (case_tac "i < fst e1")
   apply (case_tac "fst e1 < fst e2")
    apply (case_tac "i < fst e2")
      apply (case_tac "fst e2 < fst e1")
        using less_trans apply fastforce
      apply fastforce
    apply fastforce
  apply (case_tac "i < fst e2")
    apply (case_tac "fst e2 < fst e1")
      apply fastforce
    apply fastforce
    apply fastforce
  apply (case_tac "i < fst e2")
    apply (case_tac "fst e2 < fst e1")
      apply fastforce
    apply fastforce
  apply (case_tac "insert a e2 None")
    apply fastforce
  apply (case_tac "insert aa e1 None")
    apply fastforce
  apply fastforce
done

lemma insertSomeSome1:
      "insert xs e1 (Some i1') \<bind> (\<lambda>ys. insert ys e2 i2) = insert xs e2 i2 \<bind> (\<lambda>ys. insert ys e1 (Some i1')) \<Longrightarrow>
       i1' \<noteq> fst e2 \<Longrightarrow>
       i2 = None \<or> i2 \<noteq> Some (fst e1) \<Longrightarrow>
       fst e1 \<noteq> fst e2 \<Longrightarrow>
       fst e1 \<noteq> idx \<Longrightarrow>
       fst e1 \<notin> fst ` set xs \<Longrightarrow>
       fst e2 \<noteq> idx \<Longrightarrow>
       fst e2 \<notin> fst ` set xs \<Longrightarrow>
       idx \<notin> fst ` set xs \<Longrightarrow>
       distinct (map fst xs) \<Longrightarrow>
       i1 = Some i1' \<Longrightarrow>
       i2 = Some i2' \<Longrightarrow>
       idx = i1' \<Longrightarrow> (case insert xs e1 None of None \<Rightarrow> None | Some t \<Rightarrow> Some ((idx, e) # t)) \<bind> (\<lambda>ys. insert ys e2 i2) = insert ((i1', e) # xs) e2 i2 \<bind> (\<lambda>ys. insert ys e1 (Some i1'))"
sorry

lemma insertSomeSome2:
       "insert xs e1 (Some i1') \<bind> (\<lambda>ys. insert ys e2 i2) = insert xs e2 i2 \<bind> (\<lambda>ys. insert ys e1 (Some i1')) \<Longrightarrow>
       i1' \<noteq> fst e2 \<Longrightarrow>
       i2 = None \<or> i2 \<noteq> Some (fst e1) \<Longrightarrow>
       fst e1 \<noteq> fst e2 \<Longrightarrow>
       fst e1 \<noteq> idx \<Longrightarrow>
       fst e1 \<notin> fst ` set xs \<Longrightarrow>
       fst e2 \<noteq> idx \<Longrightarrow>
       fst e2 \<notin> fst ` set xs \<Longrightarrow>
       idx \<notin> fst ` set xs \<Longrightarrow>
       distinct (map fst xs) \<Longrightarrow>
       i1 = Some i1' \<Longrightarrow>
       i2 = Some i2' \<Longrightarrow>
       idx \<noteq> i1' \<Longrightarrow> (case insert xs e1 (Some i1') of None \<Rightarrow> None | Some t \<Rightarrow> Some ((idx, e) # t)) \<bind> (\<lambda>ys. insert ys e2 i2) = insert ((idx, e) # xs) e2 i2 \<bind> (\<lambda>ys. insert ys e1 (Some i1'))"
sorry

lemma insert_Cons_Some_Some_bind:
  assumes "i1 \<noteq> fst x" "i2 \<noteq> fst x"
  shows "insert (x#xs) e1 (Some i1) \<bind> (\<lambda>ys. insert ys e2 (Some i2)) = insert xs e1 (Some i1) \<bind> (\<lambda>ys. insert ys e2 (Some i2) \<bind> (\<lambda>zs. Some (x#zs)))"
using assms
  apply clarsimp
  apply(case_tac "insert xs e1 (Some i1)")
    apply clarsimp+
    apply(case_tac "insert a e2 (Some i2)")
    apply clarsimp+
  done

lemma foo:
  assumes "i1 = fst x" "i2 \<noteq> fst x"
  shows "insert (x#xs) e1 (Some i1) \<bind> (\<lambda>ys. insert ys e2 (Some i2)) = insert xs e1 None \<bind> (\<lambda>ys. insert ys e2 (Some i2) \<bind> (\<lambda>zs. Some (x#zs)))"
using assms
sorry

lemma insert_preserves_fst_set:
  assumes "i2' \<notin> set (map fst xs)" "insert xs e1 None = Some a" "i2' \<noteq> fst e1"
  shows   "i2' \<notin> set (map fst a)"
using assms
sorry

lemma insert_commutes:
  assumes "distinct (map fst (e1#e2#xs))" "i1 = None \<or> i1 \<noteq> Some (fst e2)" "i2 = None \<or> i2 \<noteq> Some (fst e1)"
  shows   "insert xs e1 i1 \<bind> (\<lambda>ys. insert ys e2 i2) = insert xs e2 i2 \<bind> (\<lambda>ys. insert ys e1 i1)"
using assms
  apply(induction xs)
  (* Empty case *)
  apply clarsimp
  apply(cases i1; clarsimp; cases i2; clarsimp)
  apply force
  (* Step case *)
  apply clarsimp
  apply (rename_tac idx e xs)
  (* i1 = None *)
  apply(cases i1, clarsimp)
    (* i2 = None *)
    apply(cases i2; clarsimp)
      apply(case_tac "insert xs e1 None")
        apply force
      apply(case_tac "insert xs e2 None")
        apply force
      apply force
    (* i2 = Some i *)
    apply (rename_tac i2')
    apply(case_tac "insert xs e1 None")
      (* insert xs e1 None = None *)
      apply force
    (* insert xs e1 None = Some xs1 *)
    apply(rename_tac xs1) 
    apply(case_tac "insert xs e2 (Some i2')")
      apply clarsimp
      apply (case_tac "insert xs e2 None")
        apply force
      apply (rename_tac xs2')
      apply clarsimp
      apply (case_tac "insert xs1 e2 None")
        apply force
      apply (rename_tac xs1')
      apply clarsimp
      apply (case_tac "insert xs2' e1 None")
        apply force
      apply clarsimp
      apply(rule insertNoneNoneNoneNone)
        prefer 2
        apply assumption
        prefer 2
        apply assumption back
        apply simp
        apply simp
        apply simp
      apply clarsimp
      apply (case_tac "insert xs e2 None")
        apply force
      apply clarsimp
      apply (case_tac "insert xs1 e2 None")
        apply force
      apply clarsimp  
      apply (case_tac "insert aa e1 None")
        apply force
      apply clarsimp
      apply(rule insertNoneNoneNoneNone)
        prefer 2
        apply assumption
        prefer 2
        apply assumption back
        apply simp
        apply simp
        apply simp
  (* i1 = Some i1' *)
  apply (rename_tac i1')
  apply(cases i2, clarsimp)
    (* i2 = None *)
    apply(case_tac "insert xs e1 None")
      apply force
    apply(case_tac "insert xs e2 None")
      apply force
    apply(case_tac "insert xs e1 (Some i1')")
      apply clarsimp
      apply (case_tac "insert a e2 None")
        apply force
      apply clarsimp
      apply (case_tac "insert aa e1 None")
        apply force
      apply clarsimp
      apply(rule insertNoneNoneNoneNone)
        prefer 2
        apply assumption
        prefer 2
        apply assumption back
        apply simp
        apply simp
        apply simp
    apply clarsimp
      apply (case_tac "insert a e2 None")
        apply force
      apply clarsimp
      apply (case_tac "insert aa e1 None")
        apply force
      apply clarsimp
      apply(rule insertNoneNoneNoneNone)
        prefer 2
        apply assumption
        prefer 2
        apply assumption back
        apply simp
        apply simp
        apply simp

(* i2 = Some i2' *)
apply (rename_tac i2')
  apply clarsimp
  apply(case_tac "insert xs e1 None")
    apply force
  apply clarsimp
  apply(case_tac "insert xs e2 None")
    apply force
  apply clarsimp
  apply(case_tac "insert a e2 None")
    apply force
  apply clarsimp
  apply(case_tac "insert aa e1 None")
    apply force
  apply clarsimp
  apply(case_tac "i2' = i1'")
    apply clarsimp
    apply(case_tac "idx = i1'")
      apply clarsimp
      apply(rule insertNoneNoneNoneNone)
        prefer 2
        apply assumption
        prefer 2
        apply assumption back
        apply simp
        apply simp
        apply simp
      apply clarsimp
      apply(case_tac "insert xs e1 (Some i1')")
        apply clarsimp
        apply(case_tac "insert xs e2 (Some i1')")
          apply clarsimp
          apply clarsimp
        apply clarsimp
        apply(case_tac "insert xs e2 (Some i1')")
          apply clarsimp
          apply clarsimp
  apply safe
    apply clarsimp
    apply(case_tac "insert xs e2 (Some i2')")
      apply clarsimp
        apply(case_tac "insert xs e2 (Some i2')")
          apply clarsimp
          apply(subgoal_tac "insert a e2 (Some i2') = None")
          prefer 2
          apply(subst (asm) insert_Some_None_iff)
          apply(subst insert_Some_None_iff)



          apply(frule insert_Some_NoneE)
          apply clarsimp
          apply(case_tac "insert ad e1 None")
            apply clarsimp
            apply clarsimp
    
(*
  apply(case_tac "idx \<noteq> i1' \<and> idx \<noteq> i2'")
  apply(subst insert_Cons_Some_Some_bind, simp)
  apply(erule conjE, simp, simp)+
  apply(subgoal_tac "insert xs e2 (Some i2') \<bind> (\<lambda>ys. insert ys e1 (Some i1') \<bind> (\<lambda>zs. Some ((idx, e) # zs))) =
       (case insert xs e2 (Some i2') of None \<Rightarrow> None | Some t \<Rightarrow> Some ((idx, e) # t)) \<bind> (\<lambda>ys. insert ys e1 (Some i1'))")
  prefer 2
  apply clarsimp
*)

apply clarsimp
apply (rule conjI, rule impI)
  (* idx = i1' *)
  prefer 2
  apply clarsimp
  prefer 2
  apply assumption
apply (rule insertSomeSome1)
apply assumption+
apply (rule impI)
apply (rule insertSomeSome2)
apply assumption+
done


end