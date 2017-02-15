theory
  Util
imports
  Main
begin

lemma distinct_set_notin:
  assumes "distinct (x#xs)"
  shows   "x \<notin> set xs"
using assms by(induction xs, auto)

lemma set_insert_inject:
  assumes "a \<notin> set xs"
          "a \<notin> set ys" 
          "set (a#xs) = set (a#ys)"
  shows   "set xs = set ys"
using assms by (induction xs arbitrary: ys) fastforce+

lemma remove1_head:
  shows "remove1 x (x#xs) = xs"
  by(induction xs, auto)

lemma set_membership_equality_technicalD [dest]:
  assumes "{x} \<union> (set xs) = {y} \<union> (set ys)"
  shows "x = y \<or> y \<in> set xs"
using assms by(induction xs, auto)

lemma set_equality_technical:
  assumes "{x} \<union> (set xs) = {y} \<union> (set ys)"
          "x \<notin> set xs" "y \<notin> set ys" "y \<in> set xs"
  shows "{x} \<union> (set xs - {y}) = set ys"
using assms by (induction xs) auto

lemma fold_comp_eq:
  shows "fold op \<circ> xs x = fold op \<circ> xs id \<circ> x"
  apply(induction xs rule: rev_induct)
  apply auto
done

lemma prefix_eq_distinct_list: "distinct xs \<Longrightarrow> pre1@ys = xs \<Longrightarrow> pre2@ys = xs \<Longrightarrow> pre1 = pre2"
  apply (induct xs arbitrary: pre1 pre2)
  apply clarsimp
  apply (case_tac pre1)
  apply (thin_tac "(\<And>pre1 pre2. distinct xs \<Longrightarrow> pre1 @ ys = xs \<Longrightarrow> pre2 @ ys = xs \<Longrightarrow> pre1 = pre2)")
  apply clarsimp
  apply (case_tac pre2)
  apply (thin_tac "(\<And>pre1 pre2. distinct xs \<Longrightarrow> pre1 @ ys = xs \<Longrightarrow> pre2 @ ys = xs \<Longrightarrow> pre1 = pre2)")
  apply clarsimp
  apply (erule_tac x=list in meta_allE)
  apply (erule_tac x=lista in meta_allE)
  apply clarsimp
done

lemma list_nill_or_snoc: "xs = [] \<or> (\<exists>y ys. xs = ys@[y])"
  by (induct xs, auto)

lemma suffix_eq_distinct_list: "distinct xs \<Longrightarrow> ys@suf1 = xs \<Longrightarrow> ys@suf2 = xs \<Longrightarrow> suf1 = suf2"
  apply (induct xs  arbitrary: suf1 suf2 rule: rev_induct)
  apply clarsimp
  apply clarsimp
  apply (subgoal_tac "suf1 = [] \<or> (\<exists>y ys. suf1 = ys@[y])")
  apply (subgoal_tac "suf2 = [] \<or> (\<exists>y ys. suf2 = ys@[y])")
  apply (erule disjE, clarsimp)
  apply clarsimp
  using list_nill_or_snoc apply auto
done

lemma pre_suf_eq_distinct_list: "distinct xs \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> pre1@ys@suf1 = xs \<Longrightarrow> pre2@ys@suf2 = xs \<Longrightarrow> pre1 = pre2 \<and> suf1 = suf2"
  apply (induct xs arbitrary: pre1 pre2 ys)
  apply clarsimp
  apply (case_tac pre1)
  apply (thin_tac " (\<And>pre1 pre2 ys. distinct xs \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> pre1 @ ys @ suf1 = xs \<Longrightarrow> pre2 @ ys @ suf2 = xs \<Longrightarrow> pre1 = pre2 \<and> suf1 = suf2)")
  apply clarsimp
  apply (case_tac pre2)
  apply clarsimp
  apply (rule_tac xs="a#xs" in suffix_eq_distinct_list)
  apply force
  apply assumption
  apply assumption
  apply clarsimp
  apply (metis append_eq_Cons_conv list.set_intros(1))
  apply (case_tac pre2)
  apply (thin_tac " (\<And>pre1 pre2 ys. distinct xs \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> pre1 @ ys @ suf1 = xs \<Longrightarrow> pre2 @ ys @ suf2 = xs \<Longrightarrow> pre1 = pre2 \<and> suf1 = suf2)")
  apply clarsimp
  apply (metis append_eq_Cons_conv list.set_intros(1))
  apply (erule_tac x=list in meta_allE, erule_tac x=lista in meta_allE, erule_tac x=ys in meta_allE)
  apply clarsimp
done

fun merge :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge cmp []     ys     = ys" |
  "merge cmp xs     []     = xs" |
  "merge cmp (x#xs) (y#ys) =
     (if cmp x y then
        x#merge cmp xs (y#ys)
      else
        y#merge cmp (x#xs) ys)"

function (sequential) qsort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "qsort cmp []      = []" |
  "qsort cmp [x]     = [x]" |
  "qsort cmp (x#xs)  =
     (let ls = List.filter (\<lambda>y. cmp x y) xs;
          rs = List.filter (\<lambda>y. cmp y x) xs
      in (qsort cmp ls) @ [x] @ (qsort cmp rs))"
by pat_completeness auto

termination qsort
  apply(relation "measure (\<lambda>(cmp, xs). size xs)")
  apply auto
  apply(simp_all add: le_imp_less_Suc)
  using le_imp_less_Suc less_Suc_eq apply auto
done

lemma qsort_set_mem_preserve:
  shows "(\<forall>x \<in> set xs. \<forall>y \<in> set xs. cmp x y \<or> cmp y x) \<longrightarrow> set xs = set (qsort cmp xs)"
  apply(induction rule: qsort.induct[where P="\<lambda>cmp xs. (\<forall>x \<in> set xs. \<forall>y \<in> set xs. cmp x y \<or> cmp y x) \<longrightarrow> set xs = set (qsort cmp xs)"])
  apply auto
done

lemma filter_empty:
  shows "Set.filter p {} = {}"
by auto

lemma set_filter_Un:
  shows "Set.filter p (xs \<union> ys) = Set.filter p xs \<union> Set.filter p ys"
by auto

corollary set_filter_insert:
  shows "Set.filter p (Set.insert x xs) = (if p x then Set.insert x (Set.filter p xs) else Set.filter p xs)"
using set_filter_Un by(auto split: split_if)

lemma finite_filter:
  assumes "finite A"
  shows   "finite (Set.filter p A)"
using assms
  apply(induction rule: finite.induct)
  apply(auto simp add: filter_empty)
  apply(simp add: set_filter_insert)
done

lemma set_filter_pred:
  assumes "x \<in> Set.filter p xs"
  shows   "p x"
using assms by simp

lemma list_filter_pred:
  assumes "x \<in> set (List.filter p xs)"
  shows   "p x"
using assms by simp

lemma set_elem_nth:
  assumes "x \<in> set xs"
  shows   "\<exists>m. m < length xs \<and> xs ! m = x"
using assms
  apply(induction xs, auto)
  apply(rule_tac x="m+1" in exI)
  apply auto
done

lemma horror_size2:
  assumes "m < length cs"
          "length cs > 0"
  shows   "\<exists>xs ys. cs = xs@(cs!m)#ys"
using assms
apply (induct m arbitrary: cs)
apply clarsimp
apply (rule_tac x="[]" in exI)
apply (rule_tac x="tl cs" in exI)
apply clarsimp
apply (case_tac cs)
apply force
apply force
apply clarsimp
apply (case_tac cs)
apply clarsimp
apply clarsimp
apply (case_tac "list = []")
apply clarsimp
apply (erule_tac x=list in meta_allE)
apply clarsimp
apply (rule_tac x="a#xs" in exI)
apply (rule_tac x="ys" in exI)
apply clarsimp
done

lemma horror_size3:
  assumes "m < length cs"
          "n < m"
          "length cs > 1"
  shows   "\<exists>xs ys zs. xs@(cs!n)#ys@(cs!m)#zs=cs"
using assms
apply (induct n arbitrary: cs m)
apply clarsimp
apply (rule_tac x="[]" in exI)
apply clarsimp
apply (insert horror_size2)
apply (erule_tac x="m-1" in meta_allE)
apply (erule_tac x="tl cs" in meta_allE)
apply clarsimp
apply (subgoal_tac "m - Suc 0 < length cs - Suc 0")
apply clarsimp
apply (rule_tac x=xs in exI)
apply (rule_tac x=ys in exI)
apply (subgoal_tac "cs ! m = tl cs ! (m - Suc 0)")
apply clarsimp
apply (metis gr_implies_not0 length_0_conv list.collapse nth_Cons_0)
apply (metis One_nat_def Suc_pred length_tl nth_tl)
using Suc_leI diff_less_mono apply blast
apply clarsimp
apply (thin_tac "(\<And>m cs. m < length cs \<Longrightarrow> cs \<noteq> [] \<Longrightarrow> \<exists>xs ys. cs = xs @ cs ! m # ys)")
apply (case_tac cs)
apply clarsimp
apply clarsimp
apply (case_tac "list = []")
apply clarsimp
apply (erule_tac x=list in meta_allE)
apply (erule_tac x="m-1" in meta_allE)
apply clarsimp
apply (subgoal_tac "m - Suc 0 < length list")
defer
apply linarith
apply clarsimp
apply (subgoal_tac "n < m - Suc 0")
defer
apply linarith
apply clarsimp
apply (rule_tac x="a#xs" in exI)
apply clarsimp
apply force
done

lemma prefix_set_mem:
  assumes "xs@ys = zs"
          "x \<in> set ys"
  shows   "x \<in> set zs"
using assms by auto

end