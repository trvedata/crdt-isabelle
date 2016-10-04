theory
  JSON_Semantics
imports
  Main
  JSON
  "~~/src/HOL/Library/Monad_Syntax"
begin

section\<open>Utility functions (move elsewhere)\<close>

definition snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" ("_#>_" [65,65]65) where
  "xs #> x \<equiv> xs @ [x]"

section\<open>Local peer state and related\<close>

subsection\<open>Identifiers\<close>

type_synonym lamport = "nat \<times> nat"

datatype ident
  = Root
  | Head
  | Id   "lamport"
  | Key  "string"

subsection\<open>State keys\<close>

datatype state_key
  = MapType  "ident"
  | ListType "ident"
  | RegType  "ident"

definition get_ident :: "state_key \<Rightarrow> ident" where
  "get_ident k \<equiv>
     case k of
       MapType  i \<Rightarrow> i
     | ListType i \<Rightarrow> i
     | RegType  i \<Rightarrow> i"

subsection\<open>Cursors\<close>

record cursor =
  path :: "state_key list"
  head :: "ident"

definition mk_cursor :: "state_key list \<Rightarrow> ident \<Rightarrow> cursor" ("cursor\<lparr>_/ \<cdot>/ _\<rparr>" [65,65]65) where
  "cursor\<lparr> ks \<cdot> i \<rparr> \<equiv> \<lparr> path = ks, head = i \<rparr>"

instantiation cursor_ext :: (size)size
begin

  definition size_cursor_ext :: "cursor \<Rightarrow> nat" where
    "size_cursor_ext \<equiv> Suc o length o path"

  instance by standard
end

subsection\<open>Document state\<close>

datatype document_state
  = MapV  "state_key \<rightharpoonup> (lamport set \<times> document_state)"
  | ListV "(state_key \<times> lamport set \<times> document_state) list"
  | RegV  "lamport \<rightharpoonup> val"

subsection\<open>Operations\<close>

datatype mutation
  = Assign "val"
  | Insert "val"
  | Delete

record operation =
  operation_id     :: "lamport"
  dependencies     :: "lamport set"
  operation_cursor :: "cursor"
  mutation         :: "mutation"

definition apply_operation :: "cursor \<Rightarrow> operation \<Rightarrow> document_state \<Rightarrow> document_state option" where
  "apply_operation c opn \<sigma> \<equiv> undefined"

subsection\<open>Local peer state\<close>

record 'a local_peer_state =
  peer_id             :: "nat"
  current_state       :: "document_state"
  var_cursor_map      :: "'a \<rightharpoonup> cursor"
  operation_queue     :: "operation set"
  sent_operations     :: "operation set"
  received_operations :: "operation set"
  operations          :: "lamport set"

definition defined :: "'a \<Rightarrow> 'a local_peer_state \<Rightarrow> bool" where
  "defined x \<sigma> \<equiv> x \<in> dom (var_cursor_map \<sigma>)"

definition assign_var :: "'a local_peer_state \<Rightarrow> 'a \<Rightarrow> cursor \<Rightarrow> 'a local_peer_state" where
  "assign_var \<sigma> x c \<equiv> \<sigma>\<lparr> var_cursor_map := (var_cursor_map \<sigma>)(x \<mapsto> c) \<rparr>"

definition make_operation :: "'a local_peer_state \<Rightarrow> cursor \<Rightarrow> mutation \<Rightarrow> 'a local_peer_state option" where
  "make_operation \<sigma> c mut \<equiv>
     let s       = {c. \<exists>p. (c, p) \<in> operations \<sigma>};
         counter = if s = {} then 0 else Suc (Max s);
         opn     = \<lparr> operation_id = (counter, peer_id \<sigma>), dependencies = operations \<sigma>,
                     operation_cursor = c, mutation = mut \<rparr>
     in
       do { new_doc \<leftarrow> apply_operation c opn (current_state \<sigma>)
          ; Some (\<sigma>\<lparr> current_state := new_doc, operations := {operation_id opn} \<union> operations \<sigma>, operation_queue := {opn} \<union> operation_queue \<sigma> \<rparr>)
          }"

lemma defined_assign_var [simp]:
  shows "defined x (assign_var \<sigma> x c)"
unfolding defined_def assign_var_def by auto

definition initial_local_peer_state :: "'a local_peer_state" where
  "initial_local_peer_state \<equiv>
     \<lparr> peer_id             = 0
     , current_state       = MapV Map.empty
     , var_cursor_map      = Map.empty
     , operation_queue     = {}
     , sent_operations     = {}
     , received_operations = {}
     , operations          = {}
     \<rparr>"

section\<open>Operational semantics\<close>

text\<open>Finds the first element in the list of tuples given as first argument whose second element
     is not an empty set.  Extracts the identifier from the first element of that tuple.\<close>
fun first_present :: "(state_key \<times> 'b set \<times> 'c) list \<Rightarrow> ident option" where
  "first_present []     = None" |
  "first_present (x#xs) =
     (let (state, s, _) = x in
        if s = {} then
          first_present xs
        else
          Some (get_ident state))"

function cursor_next :: "document_state \<Rightarrow> cursor \<Rightarrow> cursor option" where
  "cursor_next (MapV  mv) cursor =
     (case path cursor of
        []   \<Rightarrow> None
      | k#ks \<Rightarrow>
        do { (pres, child) \<leftarrow> mv k
           ; cursor        \<leftarrow> cursor_next child (cursor\<lparr> ks \<cdot> head cursor \<rparr>)
           ; Some (cursor\<lparr> k#(path cursor) \<cdot> (head cursor) \<rparr>)
           })" |
  "cursor_next (ListV lv) cursor =
     (case (lv, path cursor) of
        ((key, pres, child)#ls, [])   \<Rightarrow>
          if get_ident key = head cursor then
            do { h \<leftarrow> first_present ls
               ; Some (cursor\<lparr> [] \<cdot> h \<rparr>)
               }
          else
            cursor_next (ListV ls) (cursor\<lparr> [] \<cdot> head cursor \<rparr>)
      | ((key, pres, child)#ls, k#ks) \<Rightarrow>
          if key = k then
            do { cursor \<leftarrow> cursor_next child (cursor\<lparr> ks \<cdot> head cursor \<rparr>)
               ; Some (cursor\<lparr> k#path cursor \<cdot> head cursor \<rparr>)
               }
          else
            cursor_next (ListV ls) cursor
      | _                             \<Rightarrow> None)" |
  "cursor_next (RegV  rv) cursor = None"
by pat_completeness auto

termination cursor_next
  apply(relation "measures [\<lambda>(d, c). size c, \<lambda>(d, c). size d]")
  apply(auto simp add: mk_cursor_def size_cursor_ext_def)
  apply(case_tac "cursor", clarify, simp, auto)+
done

inductive expr_semantics :: "'a local_peer_state \<Rightarrow> 'a expr \<Rightarrow> cursor \<Rightarrow> bool" ("_/ \<turnstile>/ _/ \<longmapsto>e/ _" [65,65,65]65)
      and cmd_semantics :: "'a local_peer_state \<Rightarrow> 'a cmd \<Rightarrow> 'a local_peer_state \<Rightarrow> bool" ("_/ \<turnstile>/ _/ \<longmapsto>c/ _" [65,65,65]65) where
  (* expression semantics, TODO: keys and values *)
  expr_semantics_Doc [intro!]: "\<A> \<turnstile> doc \<longmapsto>e cursor\<lparr> [] \<cdot> Root \<rparr>" |
  expr_semantics_Var [intro!]: "\<lbrakk> var_cursor_map \<A> x = Some c \<rbrakk> \<Longrightarrow> \<A> \<turnstile> x\<acute> \<longmapsto>e c" |
  expr_semantics_Lookup [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longmapsto>e cursor\<lparr> ks \<cdot> kn \<rparr> \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<lbrakk> key \<rbrakk> \<longmapsto>e cursor\<lparr> ks #> MapType kn \<cdot> Key key \<rparr>" |
  expr_semantics_Iter [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longmapsto>e cursor\<lparr> ks \<cdot> kn \<rparr> \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>iter \<longmapsto>e cursor\<lparr> ks #> ListType kn \<cdot> Head \<rparr>" |
  expr_semantics_Next [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longmapsto>e c; cursor_next (document_state \<A>) c = Some c' \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>next \<longmapsto>e c'" |
  (* command semantics *)
  cmd_semantics_Let [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longmapsto>e c; \<A>' = assign_var \<A> x c \<rbrakk> \<Longrightarrow> \<A> \<turnstile> (let x\<acute> \<Leftarrow> e) \<longmapsto>c \<A>'" |
  cmd_semantics_Assign [intro!]: "\<A> \<turnstile> e \<Leftarrow> v \<longmapsto>c \<A>'"

end