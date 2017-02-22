theory
  Convergence2
imports
  Util
begin

locale happens_before = preorder hb_weak hb
  for hb_weak :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes interp :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" ("\<langle>_\<rangle>" [100] 100)
    and initial_state :: "'b"

abbreviation (in happens_before) (input) concurrent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "concurrent s1 s2 \<equiv> \<not> (hb s1 s2) \<and> \<not> (hb s2 s1)"

definition (in happens_before) concurrent_set :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "concurrent_set x xs \<equiv> \<forall>y \<in> set xs. concurrent x y"

definition (in happens_before) concurrent_elems_commute :: "'a list \<Rightarrow> bool" where
  "concurrent_elems_commute ops \<equiv>
    \<forall>pre x mid suf. ops = pre @ [x] @ mid @ suf \<longrightarrow>
      concurrent_set x mid \<longrightarrow>
      fold (op \<circ>) (map interp (pre @ [x] @ mid)) id initial_state =
      fold (op \<circ>) (map interp (pre @ mid @ [x])) id initial_state"


lemma (in happens_before) cec_empty:
  shows "concurrent_elems_commute []"
using concurrent_elems_commute_def by blast

lemma (in happens_before) cec_singleton:
  shows "concurrent_elems_commute [x]"
  apply(unfold concurrent_elems_commute_def)
  apply(intro allI impI)
  apply(case_tac pre)
  apply(subgoal_tac "x = xa \<and> mid = [] \<and> suf = []")
  apply simp+
done

lemma (in happens_before) cec_remove_last:
  assumes "concurrent_elems_commute (xs@[x])"
    shows "concurrent_elems_commute xs"
using assms
  apply(unfold concurrent_elems_commute_def)
  apply(intro allI impI)
  apply(erule_tac x="pre" in allE, erule_tac x="xa" in allE, erule_tac x="mid" in allE, erule_tac x="suf@[x]" in allE)
  apply force
done

lemma (in happens_before) cec_add_last:
  assumes "concurrent_elems_commute (pre @ mid)"
      and "concurrent_set x mid \<longrightarrow>
             fold (op \<circ>) (map interp (pre @ [x] @ mid)) id initial_state =
             fold (op \<circ>) (map interp (pre @ mid @ [x])) id initial_state"
    shows "concurrent_elems_commute (pre @ mid @ [x])"
using assms unfolding concurrent_elems_commute_def
  apply(intro allI impI)
  oops

definition (in happens_before) concurrent_elems_commute' :: "'a list \<Rightarrow> bool" where
  "concurrent_elems_commute' ops \<equiv>
    \<forall>pre x mid suf. ops = pre @ mid @ [x] @ suf \<longrightarrow>
      concurrent_set x mid \<longrightarrow>
      fold (op \<circ>) (map interp (pre @ mid @ [x])) id initial_state =
      fold (op \<circ>) (map interp (pre @ [x] @ mid)) id initial_state"

lemma (in happens_before) cec_to_cec':
  assumes "concurrent_elems_commute ops"
      and "ops = pre @ mid @ [x] @ suf"
      and "(\<forall>y \<in> set mid. concurrent x y)"
    shows "fold (op \<circ>) (map interp (pre @ mid @ [x])) id initial_state =
           fold (op \<circ>) (map interp (pre @ [x] @ mid)) id initial_state"
using assms unfolding concurrent_elems_commute_def
  apply(induction mid rule: rev_induct)
  apply simp
  apply(erule_tac x="pre@xs" in allE, erule_tac x="xa" in allE, erule_tac x="[x]" in allE, erule_tac x="suf" in allE)
  apply(subgoal_tac "fold (op \<circ>) (map interp ((pre @ xs) @ [xa] @ [x])) id initial_state =
                     fold (op \<circ>) (map interp ((pre @ xs) @ [x] @ [xa])) id initial_state")
  defer
  apply(subgoal_tac "concurrent x xa")
  apply(unfold concurrent_set_def)
  apply auto[1]
  apply simp
  apply(erule meta_impE)
  defer
  apply(subgoal_tac "fold (op \<circ>) (map interp (pre @ xs @ [x] @ [xa])) id initial_state =
                     fold (op \<circ>) (map interp (pre @ [x] @ xs @ [xa])) id initial_state")
  apply simp
  apply(subgoal_tac "fold (op \<circ>) (map interp (pre @ xs @ [x])) id initial_state =
                     fold (op \<circ>) (map interp (pre @ [x] @ xs)) id initial_state")
  oops

lemma (in happens_before) cec'_to_cec:
  assumes "concurrent_elems_commute' ops"
      and "ops = pre @ [x] @ mid @ suf"
      and "(\<forall>y \<in> set mid. concurrent x y)"
    shows "fold (op \<circ>) (map interp (pre @ mid @ [x])) id initial_state =
           fold (op \<circ>) (map interp (pre @ [x] @ mid)) id initial_state"
using assms
  apply(unfold concurrent_elems_commute_def concurrent_elems_commute'_def)
  oops

lemma (in happens_before) cec_inverse:
  shows "concurrent_elems_commute ops \<longleftrightarrow> concurrent_elems_commute' ops"
  apply(rule iffI)
  apply(unfold concurrent_elems_commute_def concurrent_elems_commute'_def)
  oops

lemma (in happens_before) cec_reorder_pair:
  assumes "concurrent_elems_commute [a, b]"
      and "concurrent a b"
    shows "concurrent_elems_commute [b, a]"
using assms
  apply(unfold concurrent_elems_commute_def)
  apply(intro allI impI)
  apply(case_tac pre, case_tac suf)
  apply(subgoal_tac "x = b \<and> mid = [a] \<and> suf = []")
  apply(erule_tac x="[]" in allE, erule_tac x="a" in allE, erule_tac x="[b]" in allE, erule_tac x="[]" in allE)
  apply(unfold concurrent_set_def)
  apply force
  apply simp
  apply(subgoal_tac "x = b \<and> mid = [] \<and> suf = [a]")
  apply force
  apply(metis append_is_Nil_conv hd_append list.distinct(1) list.sel(1) list.sel(3) self_append_conv2 tl_append2)
  apply(subgoal_tac "pre = [b] \<and> x = a \<and> mid = [] \<and> suf = []")
  apply force
  apply(metis append_is_Nil_conv hd_append list.distinct(1) list.sel(1) list.sel(3) self_append_conv2 tl_append2)
done

lemma (in happens_before) cec_reorder_triple:
  assumes "concurrent_elems_commute [a, b, c]"
      and "concurrent b c"
    shows "concurrent_elems_commute [a, c, b]"
using assms
  apply -
  apply(subgoal_tac "concurrent_elems_commute ([a, b] @ [c])")
  defer
  apply simp
  apply(drule cec_remove_last)
  apply(unfold concurrent_elems_commute_def)
  apply(intro allI impI)
  apply(case_tac pre, case_tac mid)
  apply(subgoal_tac "x = a \<and> suf=[c, b]")
  apply force
  apply(metis hd_append list.distinct(1) list.sel(1) list.sel(3) self_append_conv2 tl_append2)
  apply(case_tac "mid = [c]")
  apply(case_tac "concurrent a c")
  apply(subgoal_tac "x = a \<and> suf=[b]")
  apply(erule_tac x="[]" in allE)
  (* erule_tac x=a in allE, erule_tac x="[b, c]" in allE, erule_tac x="[]" in allE) back*)
  apply(case_tac "\<forall>y\<in>set [b, c]. concurrent a y")
  oops

end