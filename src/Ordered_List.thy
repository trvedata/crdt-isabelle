theory
  Ordered_List
imports
  "~~/src/HOL/Library/Monad_Syntax"
begin

type_synonym ('id, 'v) elt = "'id \<times> 'v \<times> bool"

section\<open>Definitions of insert and delete\<close>

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

fun delete :: "('id::{linorder}, 'v) elt list \<Rightarrow> 'id \<rightharpoonup> ('id, 'v) elt list" where
  "delete []                 i = None" |
  "delete ((i', v, flag)#xs) i = 
     (if i' = i then
        Some ((i', v, True)#xs)
      else
        do { t \<leftarrow> delete xs i
           ; Some ((i',v,flag)#t)
           })"

section\<open>Well-definedness of insert and delete\<close>

lemma insert_no_failure:
  assumes "i = None \<or> (\<exists>i'. i = Some i' \<and> i' \<in> fst ` set xs)"
  shows   "\<exists>xs'. insert xs e i = Some xs'"
using assms by(induction rule: insert.induct; force)

lemma insert_None_index_neq_None [dest]:
  assumes "insert xs e i = None"
  shows   "i \<noteq> None"
using assms by(cases i, auto)
  
lemma insert_Some_None_index_not_in [dest]:
  assumes "insert xs e (Some i) = None"
  shows   "i \<notin> fst ` set xs"
using assms by(induction xs, auto split: if_split_asm bind_splits) 

lemma index_not_in_insert_Some_None [simp]:
  assumes "i \<notin> fst ` set xs"
  shows   "insert xs e (Some i) = None"
using assms by(induction xs, auto)

lemma delete_no_failure:
  assumes "i \<in> fst ` set xs"
  shows   "\<exists>xs'. delete xs i = Some xs'"
using assms by(induction xs; force)

lemma delete_None_index_not_in [dest]:
  assumes "delete xs i = None"
  shows  "i \<notin> fst ` set xs"
using assms by(induction xs, auto split: if_split_asm bind_splits simp add: fst_eq_Domain)

lemma index_not_in_delete_None [simp]:
  assumes "i \<notin> fst ` set xs"
  shows   "delete xs i = None"
using assms by(induction xs, auto)

section\<open>Preservation of indices\<close>

lemma insert_body_preserve_indices [simp]:
  shows  "fst ` set (insert_body xs e) = fst ` set xs \<union> {fst e}"
by(induction xs, auto simp add: insert_commute)

lemma insert_preserve_indices:
  assumes "\<exists>ys. insert xs e i = Some ys"
  shows   "fst ` set (the (insert xs e i)) = fst ` set xs \<union> {fst e}"
using assms by(induction xs; cases i; auto simp add: insert_commute split: bind_splits)

corollary insert_preserve_indices':
  assumes "insert xs e i = Some ys"
  shows   "fst ` set (the (insert xs e i)) = fst ` set xs \<union> {fst e}"
using assms insert_preserve_indices by blast

lemma delete_preserve_indices:
  assumes "delete xs i = Some ys"
  shows   "fst ` set xs = fst ` set ys"
using assms by(induction xs arbitrary: ys, simp) (case_tac a; auto split: if_split_asm bind_splits)

section\<open>Commutativity of insert and delete\<close>

lemma insert_body_commutes:
  assumes "fst e1 \<noteq> fst e2"
  shows   "insert_body (insert_body xs e1) e2 = insert_body (insert_body xs e2) e1"
using assms by(induction xs, auto)

lemma insert_insert_body:
  assumes "fst e1 \<noteq> fst e2"
      and "i2 \<noteq> Some (fst e1)"
  shows   "insert (insert_body xs e1) e2 i2 = do { ys \<leftarrow> insert xs e2 i2; Some (insert_body ys e1) }"
using assms by (induction xs; cases i2) (auto split: if_split_asm simp add: insert_body_commutes)

lemma insert_Nil_None:
  assumes "fst e1 \<noteq> fst e2"
      and "i \<noteq> fst e2"
      and "i2 \<noteq> Some (fst e1)"
  shows   "insert [] e2 i2 \<bind> (\<lambda>ys. insert ys e1 (Some i)) = None"
using assms by (cases "i2") clarsimp+

lemma insert_insert_body_commute:
  assumes "i \<noteq> fst e1"
      and "fst e1 \<noteq> fst e2"
  shows   "insert (insert_body xs e1) e2 (Some i) =
             insert xs e2 (Some i) \<bind> (\<lambda>y. Some (insert_body y e1))"
using assms by(induction xs, auto simp add: insert_body_commutes)

lemma insert_commutes:
  assumes "fst e1 \<noteq> fst e2"
          "i1 = None \<or> i1 \<noteq> Some (fst e2)"
          "i2 = None \<or> i2 \<noteq> Some (fst e1)"
  shows   "do { ys \<leftarrow> insert xs e1 i1; insert ys e2 i2 } =
             do { ys \<leftarrow> insert xs e2 i2; insert ys e1 i1 }"
using assms proof(induction rule: insert.induct)
  fix xs and e :: "('a, 'b) elt"
  assume "i2 = None \<or> i2 \<noteq> Some (fst e)" and "fst e \<noteq> fst e2"
  thus "insert xs e None \<bind> (\<lambda>ys. insert ys e2 i2) = insert xs e2 i2 \<bind> (\<lambda>ys. insert ys e None)"
    by(auto simp add: insert_body_commutes intro: insert_insert_body)
next
  fix i and e :: "('a, 'b) elt"
  assume "fst e \<noteq> fst e2" and "i2 = None \<or> i2 \<noteq> Some (fst e)" and "Some i = None \<or> Some i \<noteq> Some (fst e2)"
  thus "insert [] e (Some i) \<bind> (\<lambda>ys. insert ys e2 i2) = insert [] e2 i2 \<bind> (\<lambda>ys. insert ys e (Some i))"
    by (auto intro: insert_Nil_None[symmetric])
next
  fix xs i and x e :: "('a, 'b) elt"
  assume IH: "(fst x \<noteq> i \<Longrightarrow>
               fst e \<noteq> fst e2 \<Longrightarrow>
               Some i = None \<or> Some i \<noteq> Some (fst e2) \<Longrightarrow>
               i2 = None \<or> i2 \<noteq> Some (fst e) \<Longrightarrow>
               insert xs e (Some i) \<bind> (\<lambda>ys. insert ys e2 i2) = insert xs e2 i2 \<bind> (\<lambda>ys. insert ys e (Some i)))"
     and "fst e \<noteq> fst e2"
     and "Some i = None \<or> Some i \<noteq> Some (fst e2)"
     and "i2 = None \<or> i2 \<noteq> Some (fst e)"
  thus "insert (x # xs) e (Some i) \<bind> (\<lambda>ys. insert ys e2 i2) = insert (x # xs) e2 i2 \<bind> (\<lambda>ys. insert ys e (Some i))"
   apply -
   apply(erule disjE)
      apply clarsimp
      apply clarsimp
      apply(case_tac "fst x = i")
        apply clarsimp
        apply(case_tac "i2")
          apply clarsimp
          apply(force simp add: insert_body_commutes)
        apply clarsimp
      apply(case_tac "fst x = a")
        apply clarsimp
        apply(force simp add: insert_body_commutes)
        apply clarsimp
        apply(force simp add: insert_insert_body_commute)
        apply clarsimp
        apply(case_tac i2)
          apply(force cong: Option.bind_cong simp add: insert_insert_body)
          apply clarsimp
          apply(case_tac "a = i")
            apply clarsimp
            apply(metis bind_assoc)
            apply clarsimp
            apply(case_tac "fst x = a")
              apply clarsimp
              apply(force cong: Option.bind_cong simp add: insert_insert_body)
              apply clarsimp
              apply(metis bind_assoc)
  done
qed

lemma delete_commutes:
  shows "do { ys \<leftarrow> delete xs i1; delete ys i2 } = do { ys \<leftarrow> delete xs i2; delete ys i1 }"
by(induction xs, auto split: bind_splits if_split_asm)

lemma insert_body_delete_commute:
  assumes "i2 \<noteq> fst e"
  shows   "delete (insert_body xs e) i2 \<bind> (\<lambda>t. Some (x#t)) =
            delete xs i2 \<bind> (\<lambda>y. Some (x#insert_body y e))"
using assms by (induction xs arbitrary: x; cases e, auto split: bind_splits if_split_asm)

lemma insert_delete_commute:
  assumes "i1 = None \<or> i1 \<noteq> Some (fst e)"
          "i2 \<noteq> fst e"
  shows   "do { ys \<leftarrow> insert xs e i1; delete ys i2 } = do { ys \<leftarrow> delete xs i2; insert ys e i1 }"
using assms by(induction xs; cases e; cases i1, auto split: bind_splits if_split_asm simp add: insert_body_delete_commute)

section\<open>Alternative definition of insert\<close>

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

lemma [elim!, dest]:
  assumes "insert' xs e None = None"
  shows   "False"
using assms by(induction xs, auto split: if_split_asm option.split_asm)

lemma insert_body_insert':
  shows "insert' xs e None = Some (insert_body xs e)"
by(induction xs, auto)

lemma insert_insert':
  shows "insert xs e i = insert' xs e i"
by(induction xs; cases e; cases i, auto split: option.split simp add: insert_body_insert')

end