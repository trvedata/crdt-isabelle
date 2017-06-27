(* Victor B. F. Gomes, University of Cambridge
   Martin Kleppmann, University of Cambridge
   Dominic P. Mulligan, University of Cambridge
*)

section\<open>Replicated Growable Array\<close>

text\<open>The RGA, introduced by \cite{Roh:2011dw}, is a replicated ordered list (sequence) datatype
     that supports \emph{insert} and \emph{delete} operations.\<close>
  
theory
  Ordered_List
imports
  Util
begin

type_synonym ('id, 'v) elt = "'id \<times> 'v \<times> bool"

subsection\<open>Insert and delete operations\<close>
 
text\<open>Insertion operations place the new element \emph{after} an existing list element with a given ID, or at the head of the list if no ID is given.
Deletion operations refer to the ID of the list element that is to be deleted.
However, it is not safe for a deletion operation to completely remove a list element, because then a concurrent insertion after the deleted element would not be able to locate the insertion position.
Instead, the list retains so-called \emph{tombstones}: a deletion operation merely sets a flag on a list element to mark it as deleted, but the element actually remains in the list.
A separate garbage collection process can be used to eventually purge tombstones \cite{Roh:2011dw}, but we do not consider tombstone removal here.\<close>

hide_const insert

fun insert_body :: "('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt \<Rightarrow> ('id, 'v) elt list" where
  "insert_body []     e = [e]" |
  "insert_body (x#xs) e =
     (if fst x < fst e then
        e#x#xs
      else x#insert_body xs e)"

fun insert :: "('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt \<Rightarrow> 'id option \<Rightarrow> ('id, 'v) elt list option" where
  "insert xs     e None     = Some (insert_body xs e)" |
  "insert []     e (Some i) = None" |
  "insert (x#xs) e (Some i) =
     (if fst x = i then
        Some (x#insert_body xs e)
      else
        insert xs e (Some i) \<bind> (\<lambda>t. Some (x#t)))"

fun delete :: "('id::{linorder}, 'v) elt list \<Rightarrow> 'id \<Rightarrow> ('id, 'v) elt list option" where
  "delete []                 i = None" |
  "delete ((i', v, flag)#xs) i = 
     (if i' = i then
        Some ((i', v, True)#xs)
      else
        delete xs i \<bind> (\<lambda>t. Some ((i',v,flag)#t)))"

subsection\<open>Well-definedness of insert and delete\<close>

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

subsection\<open>Preservation of element indices\<close>

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

subsection\<open>Commutativity of concurrent operations\<close>

lemma insert_body_commutes:
  assumes "fst e1 \<noteq> fst e2"
  shows   "insert_body (insert_body xs e1) e2 = insert_body (insert_body xs e2) e1"
using assms by(induction xs, auto)

lemma insert_insert_body:
  assumes "fst e1 \<noteq> fst e2"
      and "i2 \<noteq> Some (fst e1)"
  shows   "insert (insert_body xs e1) e2 i2 = insert xs e2 i2 \<bind> (\<lambda>ys. Some (insert_body ys e1))"
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
  shows   "insert xs e1 i1 \<bind> (\<lambda>ys. insert ys e2 i2) =
           insert xs e2 i2 \<bind> (\<lambda>ys. insert ys e1 i1)"
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
        apply (rename_tac a)
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
  shows "delete xs i1 \<bind> (\<lambda>ys. delete ys i2) = delete xs i2 \<bind> (\<lambda>ys. delete ys i1)"
by(induction xs, auto split: bind_splits if_split_asm)

lemma insert_body_delete_commute:
  assumes "i2 \<noteq> fst e"
  shows   "delete (insert_body xs e) i2 \<bind> (\<lambda>t. Some (x#t)) =
            delete xs i2 \<bind> (\<lambda>y. Some (x#insert_body y e))"
using assms by (induction xs arbitrary: x; cases e, auto split: bind_splits if_split_asm)

lemma insert_delete_commute:
  assumes "i2 \<noteq> fst e"
  shows   "insert xs e i1 \<bind> (\<lambda>ys. delete ys i2) = delete xs i2 \<bind> (\<lambda>ys. insert ys e i1)"
using assms by(induction xs; cases e; cases i1, auto split: bind_splits if_split_asm simp add: insert_body_delete_commute)

subsection\<open>Alternative definition of insert\<close>

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

lemma insert_body_stop_iteration:
  assumes "fst e > fst x"
  shows "insert_body (x#xs) e = e#x#xs"
using assms by simp

lemma insert_body_contains_new_elem:
  shows "\<exists>p s. xs = p @ s \<and> insert_body xs e = p @ e # s"
  apply (induction xs)
  apply force
  apply clarsimp
  apply (rule conjI)
  apply clarsimp
  apply (rule_tac x="[]" in exI)
  apply fastforce
  apply clarsimp
  apply (rename_tac a b c p s)
  apply (rule_tac x="(a, b, c) # p" in exI)
  apply clarsimp
done

lemma insert_between_elements:
  assumes "xs = pre@ref#suf"
      and "distinct (map fst xs)"
      and "\<And>i'. i' \<in> fst ` set xs \<Longrightarrow> i' < fst e"
    shows "insert xs e (Some (fst ref)) = Some (pre @ ref # e # suf)"
  using assms
  apply(induction xs arbitrary: pre ref suf)
  apply force
  apply(clarsimp)
  apply(case_tac pre)
  apply(clarsimp)
  apply(case_tac suf)
  apply force
  apply force
  apply clarsimp
done

lemma insert_position_element_technical:
  assumes "\<forall>x\<in>set as. a \<noteq> fst x"
    and "insert_body (cs @ ds) e = cs @ e # ds"
  shows "insert (as @ (a, aa, b) # cs @ ds) e (Some a) = Some (as @ (a, aa, b) # cs @ e # ds)"
using assms
  apply(induction as arbitrary: cs ds)
  apply simp
  apply clarsimp
done

lemma split_tuple_list_by_id:
  assumes "(a,b,c) \<in> set xs"
    and "distinct (map fst xs)"
  shows "\<exists>pre suf. xs = pre @ (a,b,c) # suf \<and> (\<forall>y \<in> set pre. fst y \<noteq> a)"
  using assms
  apply(induction xs)
  apply clarsimp
  apply (rename_tac x xs)  
  apply(case_tac "x = (a,b,c)")
  apply(rule_tac x="[]" in exI)
  apply(rule_tac x="xs" in exI)
  apply force
  apply(subgoal_tac "\<exists>pre suf. xs = pre @ (a, b, c) # suf \<and> (\<forall>y\<in>set pre. fst y \<noteq> a)")
  apply(erule exE)+
  apply(rule_tac x="x#pre" in exI)
  apply(rule_tac x="suf" in exI)
  apply(rule conjI)
  apply auto
done

lemma insert_preserves_order:
  assumes "i = None \<or> (\<exists>i'. i = Some i' \<and> i' \<in> fst ` set xs)"
      and "distinct (map fst xs)"
    shows "\<exists>pre suf. xs = pre@suf \<and> insert xs e i = Some (pre @ e # suf)"
  using assms
  apply -
  apply(erule disjE)
  apply clarsimp
  using insert_body_contains_new_elem apply metis
  apply(erule exE, clarsimp)
  apply(rename_tac a b c)
  apply(subgoal_tac "\<exists>as bs. xs = as@(a,b,c)#bs \<and> (\<forall>x \<in> set as. fst x \<noteq> a)")
  apply clarsimp
  apply(rename_tac as bs) 
  apply(subgoal_tac "\<exists>cs ds. insert_body bs e = cs@e#ds \<and> cs@ds = bs")
  apply clarsimp
  apply(rename_tac cs ds) 
  apply(rule_tac x="as@(a,b,c)#cs" in exI)
  apply(rule_tac x="ds" in exI)
  apply clarsimp
  apply(metis insert_position_element_technical)
  apply(metis insert_body_contains_new_elem)
  using split_tuple_list_by_id apply fastforce
done

end
