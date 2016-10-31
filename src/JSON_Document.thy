theory
  JSON_Document
imports
  Main
  "Editing_Language"
  "~~/src/HOL/Library/DAList"
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Multiset"
  "~~/src/HOL/Library/Product_Lexorder"
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

fun index_of' :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('a \<times> nat) option" where
  "index_of' [] p cnt = None" |
  "index_of' (x#xs) p cnt =
     (if p x then
        Some (x, cnt)
      else index_of' xs p (Suc cnt))"

definition index_of :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> nat) option" where
  "index_of xs p \<equiv> index_of' xs p 0"

fun modify_element :: "('a \<times> 'b) list \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> ('a \<times> 'b) list option" where
  "modify_element [] p f = Some []" |
  "modify_element ((v, k)#xs) p f =
     (if p k then
        do { x \<leftarrow> f v
           ; t \<leftarrow> modify_element xs p f
           ; Some ((x, k)#t)
           }
      else
        do { t \<leftarrow> modify_element xs p f
           ; Some ((v, k)#t)
           })"

section\<open>JSON documents\<close>

type_synonym lamport = "nat \<times> nat"

datatype primitive
  = Int    "int"
  | String "string"
  | Bool   "bool"
  | Null

datatype map_type_tag
  = Reg  "string"
  | Map  "string"
  | List "string"

datatype json_document
  = Map_Node  "(map_type_tag, json_document) alist"
  | List_Node "(json_document \<times> lamport) list"
  | Leaf      "(lamport, primitive) alist"

lemmas size_alist_def [simp]

function (sequential) size_json_document :: "json_document \<Rightarrow> nat" where
  "size_json_document (Leaf ls) = Suc (size_list (\<lambda>x. 1) (DAList.impl_of ls))" |
  "size_json_document (List_Node xs) = Suc (size_list (\<lambda>(j, l). size_json_document j) xs)" |
  "size_json_document (Map_Node ms) = Suc (size_list (\<lambda>(k, j). size_json_document j) (DAList.impl_of ms))"
by pat_completeness auto

termination size_json_document
  sorry

function (sequential) valid_json_document_aux :: "json_document \<Rightarrow> lamport set \<Rightarrow> (bool \<times> lamport set)"  where
  "valid_json_document_aux (Map_Node ms)  seen_so_far =
     (let impl = DAList.impl_of ms in
       (foldr (\<lambda>(k, j) (acc, seen_so_far).
          let (acc', seen_so_far) = valid_json_document_aux j seen_so_far in
            (acc \<and> acc', seen_so_far)
       ) impl (True, seen_so_far)))" |
  "valid_json_document_aux (List_Node ms) seen_so_far =
     (foldr (\<lambda>(j, l) (acc, seen_so_far).
       if l \<in> seen_so_far then
         (False, seen_so_far)
       else
         let (acc', seen_so_far) = valid_json_document_aux j (seen_so_far \<union> {l}) in
           (acc \<and> acc', seen_so_far)
     ) ms (True, seen_so_far))" |
  "valid_json_document_aux (Leaf ls)      seen_so_far =
     (foldr (\<lambda>l (acc, seen_so_far).
        if l \<in> seen_so_far then
          (False, seen_so_far)
        else
          (acc, seen_so_far \<union> {l})) (map fst (DAList.impl_of ls)) (True, seen_so_far))"
by pat_completeness auto

termination valid_json_document_aux
  sorry

definition valid_json_document :: "json_document \<Rightarrow> bool" where
  "valid_json_document j \<equiv> fst (valid_json_document_aux j {})"

datatype json_cursor_element
  = ListC "lamport"
  | MapC  "map_type_tag"

datatype json_cursor_head
  = Root
  | Head
  | List_Element "lamport"
  | Map_Key      "string"

datatype json_cursor
  = Cursor "json_cursor_element list" "json_cursor_head"

datatype mutation
  = Insert "val" "lamport option"
  (*| Delete*)
  | Assign "val"

record operation =
  operation_id     :: "lamport"
  operation_deps   :: "lamport set"
  operation_cursor :: "json_cursor"
  operation_mut    :: "mutation"

definition mk_operation :: "lamport \<Rightarrow> operation list \<Rightarrow> json_cursor \<Rightarrow> mutation \<Rightarrow> operation" where
  "mk_operation i d c m \<equiv>
     let os = set (map operation_id d) in
       \<lparr> operation_id = i, operation_deps = os, operation_cursor = c, operation_mut = m \<rparr>"

definition default_for_type_tag :: "map_type_tag \<Rightarrow> json_document" where
  "default_for_type_tag t \<equiv>
     case t of
       Map  _ \<Rightarrow> Map_Node DAList.empty
     | Reg  _ \<Rightarrow> Leaf DAList.empty
     | List _ \<Rightarrow> List_Node []"

(*
function (sequential) fetch :: "json_document \<Rightarrow> json_cursor \<rightharpoonup> json_document" where
  "fetch j             (Cursor [] Root)           = Some j" |
  "fetch j             (Cursor [] _)              = None" |
  "fetch (Map_Node m)  (Cursor (MapC k#cs) h) =
     (case DAList.lookup m k of
        Some n \<Rightarrow> fetch n (Cursor cs h)
      | None   \<Rightarrow> fetch (default_for_type_tag k) (Cursor cs h))" |
  "fetch (Map_Node m)  (Cursor [] (Map_Key k)) = DAList.lookup m (Map k)" |
  "fetch (List_Node l) (Cursor (ListC i#cs) h) =
     (case index_of l (\<lambda>(d, l). l = i) of
        Some ((d, _), _) \<Rightarrow> fetch d (Cursor cs h)
      | _ \<Rightarrow> None)" |
  "fetch _             _                     = None"
by pat_completeness auto

termination fetch
  apply(relation "measures [\<lambda>(d, c). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(d, c). size d]")
  apply auto
done
*)

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
     do { m \<leftarrow> modify_element m (\<lambda>l. k = l) (\<lambda>j. edit j (Cursor cs) f v)
        ; Some (List_Node m)
        }" |
  "edit _             _                     _ _ = None"
by pat_completeness auto

termination edit
  apply(relation "measures [\<lambda>(d, c, f, v). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(d, c, f, v). size d]")
  apply auto
done

fun (sequential) insert_after :: "(json_document \<times> lamport) list \<Rightarrow> (json_document \<times> lamport) \<Rightarrow> (json_document \<times> lamport) list" where
  "insert_after [] y = [y]" |
  "insert_after ((v1, k1) # xs) (v2, k2) = (
    if k1 < k2
      then (v2, k2) # (v1, k1) # xs
      else (v1, k1) # (insert_after xs (v2, k2))
  )"

function (sequential) insert :: "json_document \<Rightarrow> json_cursor \<Rightarrow> lamport option \<Rightarrow> (json_document \<times> lamport) \<rightharpoonup> json_document" where
  "insert (Map_Node ms) (Cursor (MapC k#cs)) lo v =
     (let current_node =
        case DAList.lookup ms k of
          None    \<Rightarrow> default_for_type_tag k
        | Some n  \<Rightarrow> n
      in
        do { t \<leftarrow> insert current_node (Cursor cs) lo v
           ; Some (Map_Node (DAList.update k t ms))
           })" |
  "insert (List_Node xs) (Cursor (ListC k#cs)) lo v =
     do { m \<leftarrow> modify_element xs (\<lambda>l. k = l) (\<lambda>j. insert j (Cursor cs) lo v)
        ; Some (List_Node m)
        }" |
  "insert (List_Node xs) (Cursor []) None     v = Some (List_Node (insert_after xs v))" |
  "insert (List_Node ((v1, k1) # xs)) (Cursor []) (Some l) v =
     (if k1 = l then Some (List_Node ((v1, k1) # (insert_after xs v)))
      else (case insert (List_Node xs) (Cursor []) (Some l) v of
              Some (List_Node xs') \<Rightarrow> Some (List_Node ((v1, k1) # xs))
            | _ \<Rightarrow> None))" |
  "insert _ _ _ _ = None"
by pat_completeness auto

termination insert
  apply(relation "measures [\<lambda>(d, c, v). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(d, c, v). size d]")
  apply auto
done

definition grow_map_entry :: "json_cursor \<Rightarrow> map_type_tag \<Rightarrow> json_cursor" where
  "grow_map_entry c k \<equiv>
     case c of
       Cursor cs \<Rightarrow> Cursor (cs #> MapC k)"

definition grow_list_entry :: "json_cursor \<Rightarrow> lamport \<Rightarrow> json_cursor" where
  "grow_list_entry c l \<equiv>
     case c of
       Cursor cs \<Rightarrow> Cursor (cs #> ListC l)"
          
inductive compatible_json_cursor :: "json_document \<Rightarrow> json_cursor \<Rightarrow> bool" ("_/ \<bowtie>/ _" [65,65]65) where
  compatible_json_cursor_Nil [intro!]: "j \<bowtie> (Cursor [])" |
  compatible_json_cursor_Some_MapC [intro!]: "\<lbrakk> DAList.lookup m k = Some n; n \<bowtie> Cursor cs \<rbrakk> \<Longrightarrow> Map_Node m \<bowtie> (Cursor (MapC k#cs))" |
  compatible_json_cursor_None_MapC [intro!]: "\<lbrakk> DAList.lookup m k = None; default_for_type_tag k \<bowtie> Cursor cs \<rbrakk> \<Longrightarrow> Map_Node m \<bowtie> (Cursor (MapC k#cs))" |
  compatible_json_cursor_ListC [intro!]: "\<lbrakk> index_of l (\<lambda>(d, l). l = i) = Some ((d, _), idx); d \<bowtie> Cursor cs \<rbrakk> \<Longrightarrow> List_Node l \<bowtie> (Cursor (ListC i#cs))"

function (sequential) json_document_cursor_compatible :: "json_document \<Rightarrow> json_cursor \<Rightarrow> bool" where
  "json_document_cursor_compatible j             (Cursor [])           = True" |
  "json_document_cursor_compatible (Map_Node m)  (Cursor (MapC k#cs))  =
     (case DAList.lookup m k of
        Some n \<Rightarrow> json_document_cursor_compatible n (Cursor cs)
      | None \<Rightarrow> json_document_cursor_compatible (default_for_type_tag k) (Cursor cs))" |
  "json_document_cursor_compatible (List_Node l) (Cursor (ListC i#cs)) =
     (case index_of l (\<lambda>(d, l). l = i) of
        Some ((d, _), idx) \<Rightarrow> json_document_cursor_compatible d (Cursor cs)
      | _ \<Rightarrow> False)" |
  "json_document_cursor_compatible _             _                     = False"
by pat_completeness auto

termination json_document_cursor_compatible
  apply(relation "measures [\<lambda>(d, c). case c of Cursor cs \<Rightarrow> size cs, \<lambda>(d, c). size d]")
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
  assume IH1: "(DAList.lookup m k = None \<Longrightarrow> json_document_cursor_compatible (default_for_type_tag k) (Cursor cs) \<Longrightarrow> default_for_type_tag k \<bowtie> Cursor cs)"
    and IH2: "(\<And>x2. DAList.lookup m k = Some x2 \<Longrightarrow> json_document_cursor_compatible x2 (Cursor cs) \<Longrightarrow> x2 \<bowtie> Cursor cs)"
    and *: "json_document_cursor_compatible (Map_Node m) (Cursor (MapC k # cs))"
  show "Map_Node m \<bowtie> Cursor (MapC k # cs)"
  proof(cases "DAList.lookup m k")
    assume "DAList.lookup m k = None"
    hence "json_document_cursor_compatible (default_for_type_tag k) (Cursor cs)"
      using * by auto
    hence "default_for_type_tag k \<bowtie> Cursor cs"
      using IH1 `DAList.lookup m k = None` by auto
    thus "Map_Node m \<bowtie> Cursor (MapC k # cs)"
      using `DAList.lookup m k = None` by blast
  next
    fix a
    assume "DAList.lookup m k = Some a"
    hence "json_document_cursor_compatible a (Cursor cs)"
      using * by auto
    hence "a \<bowtie> Cursor cs"
      using IH2 `DAList.lookup m k = Some a` by auto
    thus "Map_Node m \<bowtie> Cursor (MapC k # cs)"
      using `DAList.lookup m k = Some a` compatible_json_cursor_Some_MapC by metis
  qed
next
  fix l i cs
  assume IH: "json_document_cursor_compatible (List_Node l) (Cursor (ListC i # cs))" and
    *: "(\<And>x2 x y xa ya. index_of l (\<lambda>(d, l). l = i) = Some x2 \<Longrightarrow> (x, y) = x2 \<Longrightarrow> (xa, ya) = x \<Longrightarrow> json_document_cursor_compatible xa (Cursor cs) \<Longrightarrow> xa \<bowtie> Cursor cs)"
  from this obtain d a idx where **: "index_of l (\<lambda>(d, l). l = i) = Some ((d, a), idx)"
    apply simp
    apply(case_tac "index_of l (\<lambda>(d, l). l = i)"; simp)
    apply(case_tac "a"; simp)
    apply(case_tac "aa"; simp)
    done
  hence "json_document_cursor_compatible d (Cursor cs)"
    using IH by simp
  hence "d \<bowtie> Cursor cs"
    using * ** by simp
  thus "List_Node l \<bowtie> Cursor (ListC i # cs)"
    using ** by auto
qed auto

lemma json_document_cursor_compatible_complete:
  assumes "j \<bowtie> c"
  shows   "json_document_cursor_compatible j c"
using assms by(induction, auto)

lemma compatible_json_cursor_fetch:
  assumes "d \<bowtie> c"
  shows   "\<exists>j. fetch d c = Some j"
using assms by(induction; simp)

end