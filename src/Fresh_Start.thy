theory
  Fresh_Start
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin

type_synonym ('id, 'v) elt = "'id \<times> 'v"

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

lemma insert_None_condition1 [elim!, dest]:
  assumes "insert xs e (Some i) = None"
  shows   "xs = [] \<or> i \<notin> set (map fst xs)"
sorry

lemma insert_None_condition2 [elim!, dest]:
  assumes "insert xs e None = None"
  shows   "False"
using assms
  by (induction xs, auto, case_tac "a < fst e"; clarsimp) (case_tac "Fresh_Start.insert xsa e None"; clarsimp)

lemma insert_Some_condition1 [elim!, dest]:
  assumes "insert xs e None = Some []"
  shows   "False"
using assms
  by (induction xs, auto, case_tac "a < fst e"; clarsimp) (case_tac "Fresh_Start.insert xsa e None"; clarsimp)

lemma insert_commutes:
  assumes "distinct (map fst (e1#e2#xs))" "the i1 \<noteq> fst e2" "the i2 \<noteq> fst e1"
  shows   "insert xs e1 i1 \<bind> (\<lambda>ys. insert ys e2 i2) = insert xs e2 i2 \<bind> (\<lambda>ys. insert ys e1 i1)"
using assms
  apply(induction xs)
  (* Empty case *)
  apply clarsimp
  apply(cases i1; clarsimp; cases i2; clarsimp)
  apply force
  (* Step case *)
  apply(cases i1; clarsimp; cases i2; clarsimp)
  apply(case_tac "a < fst e1 \<and> fst e1 < fst e2"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)+
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply force
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply auto[1]
  apply(case_tac "a < fst e2 \<and> fst e2 < fst e1"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e2 (Some aa)"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply force
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert ab e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert a e1 None"; clarsimp)
    apply auto[1]
    
  apply(case_tac "a < fst e1 \<and> a > fst e2"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply auto[1]
  apply(case_tac "a < fst e2 \<and> a > fst e1"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply auto[1]
  apply(case_tac "fst e1 < fst e2 \<and> fst e2 < a"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply auto[1]
  apply(case_tac "fst e2 < fst e1 \<and> fst e1 < a"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e1 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert xs e2 (Some aa)"; clarsimp)
    apply(case_tac "Fresh_Start.insert ab e2 None"; clarsimp)
    apply(drule insert_None_condition2, simp)
    apply(case_tac "Fresh_Start.insert ac e1 None"; clarsimp)
    
    


(*
  apply(induction rule: insert.induct)
    (* First case *)
    apply(cases "i1"; simp; cases "i2"; simp; (force+))
    (* Second case *)
    apply(cases "i1"; simp; cases "i2"; simp; (force+))
    (* Third case *)
    apply(case_tac "fst x < fst e")
      (* If: true case *)
      apply clarsimp
      apply(case_tac "Fresh_Start.insert ((a, b) # xs) e2 i2"; clarsimp)
      apply(case_tac "i2"; clarsimp)
      apply(case_tac "a < fst e2"; clarsimp)
      apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
      apply(case_tac "i2"; clarsimp)
      apply(case_tac "a < fst e2"; clarsimp)
      apply force
      apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
      apply simp
      apply(case_tac "a = ac"; clarsimp)
      apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
      apply(case_tac "Fresh_Start.insert xs e2 (Some ac)"; clarsimp)
      (* If: false case *)
      apply clarsimp
      apply(case_tac "Fresh_Start.insert xs (aa, ba) None"; clarsimp)
      apply(drule insert_None_condition2, force)
      apply(cases "i2"; clarsimp)
      apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
      apply(drule insert_None_condition2, force)
      apply force
      apply(case_tac "a = ac"; clarsimp)
      apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
      apply(case_tac "Fresh_Start.insert xs e2 (Some ac)"; clarsimp)
      apply(drule insert_None_condition2, force)
      apply(drule insert_None_condition2, force)
      apply(case_tac "Fresh_Start.insert ab e2 None"; clarsimp)
      apply(case_tac "Fresh_Start.insert a (aa, ba) None"; clarsimp)
      apply(case_tac "Fresh_Start.insert a (aa, ba) None"; clarsimp)
      apply(case_tac "Fresh_Start.insert xs e2 (Some ac)"; clarsimp)
      apply(drule insert_None_condition1, erule disjE)
        apply(clarsimp)
        apply(drule insert_Some_condition1, force)
        apply(drule insert_None_condition1, erule disjE)
          apply clarsimp
          apply(case_tac "aa < fst e2"; clarsimp)
          apply(case_tac "fst e2 < aa"; clarsimp)
          apply simp
          apply(case_tac "fst e2 < aa"; clarsimp)
*)

(*
    apply(cases "i1"; simp; cases "i2"; simp; (force+))
    apply(cases "i1"; simp; cases "i2"; simp)
    apply(case_tac "fst x < fst e"; clarsimp)
    apply(cases "i2"; simp)
    apply(case_tac "fst e2 < aa"; clarsimp)
    apply(case_tac "a < fst e2"; clarsimp)
    apply force
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp; force; force)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp; force; force)
    apply(case_tac "a = ab"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 (Some ab)"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs (aa, ba) None"; clarsimp)
    apply(cases i2; clarsimp)
    apply(case_tac "fst e2 < aa"; clarsimp)
    apply(case_tac "a < fst e2"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "a = ab"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert a (aa, ba) None"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 (Some ab)"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 i2"; clarsimp)
    apply(case_tac "Fresh_Start.insert ((a, b) # xs) e2 i2"; clarsimp)
    apply(case_tac "i2"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(drule insert_None_condition1)
    apply(erule disjE; clarsimp)
    apply(case_tac "Fresh_Start.insert ab e2 None"; clarsimp)
    apply(case_tac "i2"; clarsimp)
    apply(case_tac "a < fst e2"; clarsimp)
    apply(drule insert_None_condition2)
    apply force
    apply(case_tac "a = ad"; clarsimp)
    apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert a (aa, ba) None"; clarsimp)
    apply(case_tac "Fresh_Start.insert ab e2 None"; clarsimp)
    apply(case_tac "Fresh_Start.insert ab e2 None"; clarsimp)
    apply(drule insert_None_condition1)
    apply(erule disjE; clarsimp)
    apply(drule insert_Some_condition1, force)
    apply(drule insert_None_condition1, erule disjE, clarsimp)
*)    
(*
  apply(case_tac "Fresh_Start.insert xs e None"; clarsimp)
  apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp; force; force)
  apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp; force; force)
  apply(case_tac "Fresh_Start.insert xs e2 None"; clarsimp)
  apply(case_tac "Fresh_Start.insert xs e2 (Some ab)"; clarsimp)
  apply(case_tac "Fresh_Start.insert xs (aa, ba) None"; clarsimp)
  apply(case_tac "Fresh_Start.insert ac e2 None"; clarsimp)
  *)
  
  

end