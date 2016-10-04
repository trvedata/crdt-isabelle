theory
  JSON_Document
imports
  Main
  "~~/src/HOL/Library/DAList"
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Multiset"
begin

section\<open>Utilities\<close>

definition snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" ("_/ #>/ _" [65,65]65) where
  "xs #> x \<equiv> xs @ [x]"

definition split_at :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a \<times> 'a list)" where
  "split_at xs m \<equiv> (take m xs, xs ! m, drop (Suc m) xs)"

lemma split_at_correct [simp]:
  assumes "split_at xs m = (ps, e, ss)" "m < length xs"
  shows   "xs = ps @ [e] @ ss"
using assms unfolding split_at_def by(auto simp add: id_take_nth_drop)

section\<open>JSON documents\<close>

datatype primitive
  = Int    "int"
  | String "string"
  | Bool   "bool"
  | Null

datatype json_document
  = Map_Node  "(string, json_document) alist"
  | List_Node "json_document list"
  | Leaf      "primitive"

datatype json_cursor_element
  = ListC "nat"
  | MapC  "string"

datatype json_cursor
  = Cursor "json_cursor_element list"

function (sequential) fetch :: "json_document \<Rightarrow> json_cursor \<rightharpoonup> json_document" where
  "fetch j             (Cursor [])           = Some j" |
  "fetch (Map_Node m)  (Cursor (MapC  k#cs)) =
     do { n \<leftarrow> DAList.lookup m k
        ; fetch n (Cursor cs)
        }" |
  "fetch (List_Node l) (Cursor (ListC i#cs)) =
     (if i < length l then
        fetch (l ! i) (Cursor cs)
      else
        None)" |
  "fetch _             _                     = None"
by pat_completeness auto

termination fetch
  apply(relation "measures [\<lambda>(doc, c). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(doc, c). size doc]")
  apply auto
done

function (sequential) edit :: "json_document \<Rightarrow> json_cursor \<Rightarrow> (json_document \<rightharpoonup> json_document) \<Rightarrow> json_document \<rightharpoonup> json_document" where
  "edit j             (Cursor [])           f v  = f j" |
  "edit (Map_Node m)  (Cursor (MapC k#cs))  f v =
     (let current_node =
        case DAList.lookup m k of
          None \<Rightarrow>
            (case cs of
               []            \<Rightarrow> v
             | ((MapC _) #_) \<Rightarrow> Map_Node DAList.empty
             | ((ListC _)#_) \<Rightarrow> List_Node [])
        | Some n \<Rightarrow> n
      in
        do { t \<leftarrow> edit current_node (Cursor cs) f v
           ; Some (Map_Node (DAList.update k t m))
           })" |
  "edit (List_Node m) (Cursor (ListC k#cs)) f v =
     (if k < length m then
        let (lt, e, gt) = split_at m k in
        do { t \<leftarrow> edit e (Cursor cs) f v
           ; Some (List_Node (lt @ [t] @ gt))
           }
      else None)" |
  "edit _             _                     _ _ = None"
by pat_completeness auto

termination edit
  apply(relation "measures [\<lambda>(d, c, f, v). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(d, c, f, v). size d]")
  apply auto
done

function (sequential) insert :: "json_document \<Rightarrow> json_cursor \<Rightarrow> json_document \<rightharpoonup> json_document" where
  "insert _              (Cursor [])                 v = None" |
  "insert (Map_Node  ms) (Cursor (MapC k#cs))        v =
     (let current_node =
        case DAList.lookup ms k of
          None   \<Rightarrow> Map_Node DAList.empty
        | Some n \<Rightarrow> n
      in
        do { t \<leftarrow> insert current_node (Cursor cs) v
           ; Some (Map_Node (DAList.update k t ms))
           })" |
  "insert (List_Node xs) (Cursor [ListC k]) v =
     (if k < length xs then
        let (lt, e, gt) = split_at xs k in
          Some (List_Node (lt @ [v, e] @ gt))
      else if k = length xs then
        Some (List_Node (xs #> v))
      else None)" |
  "insert (List_Node xs) (Cursor (ListC k#cs))        v =
     (if k < length xs then
        let (lt, e, gt) = split_at xs k in
        do { t \<leftarrow> insert e (Cursor cs) v
           ; Some (List_Node (lt @ [t] @ gt))
           }
      else None)" |
  "insert _              _                  _ = None"
by pat_completeness auto

termination insert
  apply(relation "measures [\<lambda>(d, c, v). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(d, c, v). size d]")
  apply auto
done

function (sequential) extend_map_branch :: "json_document \<Rightarrow> json_cursor \<Rightarrow> string \<Rightarrow> json_document \<rightharpoonup> json_document" where
  "extend_map_branch (Map_Node m) (Cursor [])          key v = Some (Map_Node (DAList.update key v m))" |
  "extend_map_branch (Map_Node m) (Cursor (MapC k#cs)) key v =
     do { n \<leftarrow> DAList.lookup m k
        ; t \<leftarrow> extend_map_branch n (Cursor cs) key v
        ; Some (Map_Node (DAList.update k t m))
        }" |
  "extend_map_branch (List_Node ls) (Cursor (ListC i#cs)) key v =
     (if i < length ls then
        let (lt, e, gt) = split_at ls i in
          do { t \<leftarrow> extend_map_branch e (Cursor cs) key v
             ; Some (List_Node (lt @ [t] @ gt))
             }
      else None)" |
  "extend_map_branch _              _                     _  _ = None"
by pat_completeness auto

termination extend_map_branch
  apply(relation "measures [\<lambda>(doc, c, s). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(doc, c, s). size doc]")
  apply auto
done

function (sequential) extend_list_branch :: "json_document \<Rightarrow> json_cursor \<Rightarrow> nat \<Rightarrow> json_document \<rightharpoonup> json_document" where
  "extend_list_branch (List_Node l) (Cursor [])           j v =
     (if j < length l then
        let (lt, e, gt) = split_at l j in
          Some (List_Node (gt @ [v] @ lt))
      else if j = length l then
        Some (List_Node (l #> v))
      else None)" |
  "extend_list_branch (List_Node l) (Cursor (ListC i#cs)) j v =
     (if i < length l then
        let (lt, e, gt) = split_at l i in
          do { t \<leftarrow> extend_list_branch e (Cursor cs) j v
             ; Some (List_Node (lt @ [t] @ gt))
             }
      else None)" |
  "extend_list_branch (Map_Node m)  (Cursor (MapC k#cs))  j v =
     do { n \<leftarrow> DAList.lookup m k
        ; t \<leftarrow> extend_list_branch n (Cursor cs) j v
        ; Some (Map_Node (DAList.update k t m))
        }" |
  "extend_list_branch _             _                     _ _ = None"
by pat_completeness auto

termination extend_list_branch
  apply(relation "measures [\<lambda>(doc, c, m). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(doc, c, m). size doc]")
  apply auto
done

definition grow_map_entry :: "json_cursor \<Rightarrow> string \<Rightarrow> json_cursor" where
  "grow_map_entry c k \<equiv>
     case c of
       Cursor cs \<Rightarrow> Cursor (cs #> MapC k)"

definition grow_list_entry :: "json_cursor \<Rightarrow> nat \<Rightarrow> json_cursor" where
  "grow_list_entry c i \<equiv>
     case c of
       Cursor cs \<Rightarrow> Cursor (cs #> ListC i)"

inductive compatible_json_cursor :: "json_document \<Rightarrow> json_cursor \<Rightarrow> bool" ("_/ \<bowtie>/ _" [65,65]65) where
  compatible_json_cursor_Nil [intro!]: "j \<bowtie> (Cursor [])" |
  compatible_json_cursor_MapC [intro!]: "\<lbrakk> DAList.lookup m k = Some n; n \<bowtie> Cursor cs \<rbrakk> \<Longrightarrow> Map_Node m \<bowtie> (Cursor (MapC k#cs))" |
  compatible_json_cursor_ListC [intro!]: "\<lbrakk> i < length l; l ! i = n; n \<bowtie> Cursor cs \<rbrakk> \<Longrightarrow> List_Node l \<bowtie> (Cursor (ListC i#cs))"

function (sequential) json_document_cursor_compatible :: "json_document \<Rightarrow> json_cursor \<Rightarrow> bool" where
  "json_document_cursor_compatible j             (Cursor [])           = True" |
  "json_document_cursor_compatible (Map_Node m)  (Cursor (MapC k#cs))  =
     (case DAList.lookup m k of
        Some n \<Rightarrow> json_document_cursor_compatible n (Cursor cs)
      | _ \<Rightarrow> False)" |
  "json_document_cursor_compatible (List_Node l) (Cursor (ListC i#cs)) =
     (if i < length l then
        json_document_cursor_compatible (List.nth l i) (Cursor cs)
      else False)" |
  "json_document_cursor_compatible _             _                     = False"
by pat_completeness auto

termination json_document_cursor_compatible
  apply(relation "measures [\<lambda>(doc, c). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(doc, c). size doc]")
  apply auto
done

lemma json_document_cursor_compatible_sound:
  assumes "json_document_cursor_compatible j c"
  shows   "j \<bowtie> c"
using assms proof(induction rule: json_document_cursor_compatible.induct)
  fix j
  show "j \<bowtie> Cursor []"
    by auto
next
  fix m k cs
  assume IH: "json_document_cursor_compatible (Map_Node m) (Cursor (MapC k # cs))" and
    *: "(\<And>x2. DAList.lookup m k = Some x2 \<Longrightarrow> json_document_cursor_compatible x2 (Cursor cs) \<Longrightarrow> x2 \<bowtie> Cursor cs)"
  from this obtain n where **: "DAList.lookup m k = Some n"
    by fastforce
  hence "json_document_cursor_compatible n (Cursor cs)"
    using IH by simp
  hence "n \<bowtie> Cursor cs"
    using * ** by simp
  thus "Map_Node m \<bowtie> Cursor (MapC k # cs)"
    using ** by auto
next
  fix l i cs
  assume IH: "json_document_cursor_compatible (List_Node l) (Cursor (ListC i # cs))" and
    *: "(i < length l \<Longrightarrow> json_document_cursor_compatible (l ! i) (Cursor cs) \<Longrightarrow> l ! i \<bowtie> Cursor cs)"
  hence "i < length l"
    by (meson json_document_cursor_compatible.simps)
  hence "json_document_cursor_compatible (List.nth l i) (Cursor cs)"
    using IH by simp
  hence "l ! i \<bowtie> Cursor cs"
    using * `i < length l` by simp
  thus "List_Node l \<bowtie> Cursor (ListC i # cs)"
    using `i < length l` by auto
qed auto

lemma json_document_cursor_compatible_complete:
  assumes "j \<bowtie> c"
  shows   "json_document_cursor_compatible j c"
using assms by(induction, auto)

lemma compatible_json_cursor_fetch:
  assumes "doc \<bowtie> c"
  shows   "\<exists>j. fetch doc c = Some j"
using assms by(induction, simp_all)

end