theory
  Application
imports
  Network
  Ordered_list
begin

definition Insert :: "('id, 'v) elt \<Rightarrow> 'id option \<Rightarrow> ('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt list" where
  "Insert e n \<equiv> (\<lambda>xs. the (insert xs e n))"

definition Delete :: "'id \<Rightarrow> ('id::{linorder}, 'v) elt list \<Rightarrow> ('id, 'v) elt list" where
  "Delete n \<equiv> (\<lambda>xs. the (delete xs n))"

locale example = finite_event_structure carriers for
  carriers :: "nat \<Rightarrow> ((('id::{linorder}, 'v) elt) list) event set" +
  assumes insert_flag: "(i, Broadcast, Insert e n) \<in> carriers i \<Longrightarrow> snd (snd e) = False"
  assumes allowed_insert: "(i, Broadcast, Insert e n) \<in> carriers i \<Longrightarrow> n = None \<or> 
                            (\<exists>n' n'' v b. n = Some n' \<and> (i, Deliver, Insert (n', v, b) n'') \<sqsubset>\<^sup>i (i, Broadcast, Insert e n))"
  assumes insert_id_unique: "id1 = id2 \<Longrightarrow> (i, Broadcast, Insert (id1, v1, b1) n1) \<in> carriers i \<Longrightarrow> (j, Broadcast, Insert (id2, v2, b2) n2) \<in> carriers j \<Longrightarrow> v1 = v2 \<and> n1 = n2"
  assumes allowed_delete: "(i, Broadcast, Delete x) \<in> carriers i \<Longrightarrow> (\<exists>n' v b. (i, Deliver, Insert (x, v, b) n') \<sqsubset>\<^sup>i (i, Broadcast, Delete x))"


end