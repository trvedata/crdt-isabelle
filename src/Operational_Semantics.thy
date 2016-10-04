theory
  Operational_Semantics
imports
  Main
  JSON_Document
  Editing_Language
  "~~/src/HOL/Library/Product_Lexorder"
begin

record 'a node_state =
  document     :: json_document
  vars         :: "('a, json_cursor) alist"
  highest_seen :: "nat"

definition valid_node_state :: "'a node_state \<Rightarrow> bool" where
  "valid_node_state \<sigma> \<equiv> \<forall>v c. DAList.lookup (vars \<sigma>) v = Some c \<longrightarrow> document \<sigma> \<bowtie> c"

definition initial_node_state :: "'a node_state" where
  "initial_node_state \<equiv>
     \<lparr> document     = Map_Node DAList.empty
     , vars         = DAList.empty
     , highest_seen = 0
     \<rparr>"

definition generate_operation_id :: "'a node_state \<Rightarrow> nat \<Rightarrow> (lamport \<times> 'a node_state)" where
  "generate_operation_id \<A> ident \<equiv>
     let c = Suc (highest_seen \<A>);
         a = \<A>\<lparr> highest_seen := c \<rparr>
     in ((c, ident), a)"

lemma initial_node_state_valid [simp]:
  shows "valid_node_state initial_node_state"
by (auto simp add: valid_node_state_def initial_node_state_def)
                                                                         
inductive expr_operational_semantics :: "'a node_state \<Rightarrow> 'a expr \<Rightarrow> json_cursor \<Rightarrow> bool" ("_/ \<turnstile>/ _/ \<longlonglongrightarrow>e/ _" [65,65,65]65) where
  expr_operational_semantics_Doc [intro!]: "\<A> \<turnstile> doc \<longlonglongrightarrow>e Cursor []" |
  expr_operational_semantics_Var [intro!]: "\<lbrakk> DAList.lookup (vars \<A>) v = Some c \<rbrakk> \<Longrightarrow> \<A> \<turnstile> v\<acute> \<longlonglongrightarrow>e c" |
  expr_operational_semantics_Lookup [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; c' = grow_map_entry c k \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<lbrakk> k \<rbrakk> \<longlonglongrightarrow>e c'" |
  expr_operational_semantics_Iter [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; c' = grow_list_entry c 0 \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>iter \<longlonglongrightarrow>e c'" |
  expr_operational_semantics_Next [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; c = Cursor cs; cs \<noteq> []; last cs = ListC k; c' = Cursor (butlast cs #> ListC (Suc k)); document \<A> \<bowtie> c' \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>next \<longlonglongrightarrow>e c'"

fun execute_expr :: "'a node_state \<Rightarrow> 'a expr \<rightharpoonup> json_cursor" where
  "execute_expr \<A> Doc     = Some (Cursor [])" |
  "execute_expr \<A> (Var v) = DAList.lookup (vars \<A>) v" |
  "execute_expr \<A> (Lookup e k) =
     do { c \<leftarrow> execute_expr \<A> e
        ; Some (grow_map_entry c k)
        }" |
  "execute_expr \<A> (Iter e) =
     do { c \<leftarrow> execute_expr \<A> e
        ; Some (grow_list_entry c 0)
        }" |
  "execute_expr \<A> (Next e) =
     do { c \<leftarrow> execute_expr \<A> e
        ; case c of
            Cursor cs \<Rightarrow>
              if cs = [] then
                None
              else
                (case last cs of
                   ListC k \<Rightarrow>
                     let c' = Cursor (butlast cs #> ListC (Suc k)) in
                       if json_document_cursor_compatible (document \<A>) c' then
                         Some c'
                       else None
                 | _ \<Rightarrow> None)
        }"

lemma execute_expr_sound:
  assumes "execute_expr \<A> e = Some c"
  shows   "\<A> \<turnstile> e \<longlonglongrightarrow>e c"
using assms proof(induction arbitrary: c rule: execute_expr.induct)
  fix \<A> :: "'a node_state" and c
  assume IH: "execute_expr \<A> (doc) = Some c"
  hence "c = Cursor []"
    by simp
  thus "\<A> \<turnstile> doc \<longlonglongrightarrow>e c"
    by auto
next
  fix \<A> :: "'a node_state" and v :: "'a" and c
  assume "execute_expr \<A> (v\<acute>) = Some c"
  hence "DAList.lookup (vars \<A>) v = Some c"
    by simp
  thus "\<A> \<turnstile> v\<acute> \<longlonglongrightarrow>e c"
    by auto
next
  fix \<A> :: "'a node_state" and e :: "'a expr" and k :: "string" and c
  assume IH: "(\<And>c. execute_expr \<A> e = Some c \<Longrightarrow> \<A> \<turnstile> e \<longlonglongrightarrow>e c)" and
    *: "execute_expr \<A> (e\<lbrakk> k \<rbrakk>) = Some c"
  from this obtain c' where **: "execute_expr \<A> e = Some c'"
    by fastforce
  hence "\<A> \<turnstile>e \<longlonglongrightarrow>e c'"
    using IH by simp
  have "c = grow_map_entry c' k"
    using * ** by simp
  thus "\<A> \<turnstile> e\<lbrakk> k \<rbrakk> \<longlonglongrightarrow>e c"
    using `\<A> \<turnstile>e \<longlonglongrightarrow>e c'` by auto
next
  fix \<A> :: "'a node_state" and e :: "'a expr" and c
  assume IH: "(\<And>c. execute_expr \<A> e = Some c \<Longrightarrow> \<A> \<turnstile> e \<longlonglongrightarrow>e c)" and
    *: "execute_expr \<A> (e\<cdot>iter) = Some c"
  from this obtain c' where **: "execute_expr \<A> e = Some c'"
    by fastforce
  hence "\<A> \<turnstile>e \<longlonglongrightarrow>e c'"
    using IH by simp
  have "c = grow_list_entry c' 0"
    using * ** by simp
  thus "\<A> \<turnstile> e\<cdot>iter \<longlonglongrightarrow>e c"
    using `\<A> \<turnstile>e \<longlonglongrightarrow>e c'` by auto
next
  fix \<A> :: "'a node_state" and e :: "'a expr" and c'
  assume IH: "(\<And>c. execute_expr \<A> e = Some c \<Longrightarrow> \<A> \<turnstile> e \<longlonglongrightarrow>e c)" and
    *: "execute_expr \<A> (e\<cdot>next) = Some c'"
  from this obtain c where **: "execute_expr \<A> e = Some c"
    by fastforce
  hence 1: "\<A> \<turnstile> e \<longlonglongrightarrow>e c"
    using IH by simp
  from * and ** obtain cs k where 2: "c = Cursor cs \<and> cs \<noteq> [] \<and> last cs = ListC k"
    apply(simp only: execute_expr.simps)
    apply(cases "execute_expr \<A> e"; simp)
    apply(case_tac "c"; simp)
    apply(case_tac "x = []"; simp)
    apply(case_tac "last x"; simp add: Let_def)
    done
  from this and * ** have 3: "c' = Cursor (butlast cs #> ListC (Suc k))"
    apply(simp only: execute_expr.simps)
    apply(cases "execute_expr \<A> e"; simp)
    apply(case_tac "a"; simp)
    apply(case_tac "x = []"; simp)
    apply(case_tac "last x"; simp add: Let_def)
    apply(case_tac "json_document_cursor_compatible (document \<A>) (Cursor (butlast x #> ListC (Suc x1)))"; simp)
    done
  from this and * ** have 4: "document \<A> \<bowtie> c'"
    apply(simp only: execute_expr.simps bind.simps)
    apply(case_tac "c"; simp)
    apply(case_tac "x = []"; simp)
    apply(case_tac "last x"; simp add: Let_def)
    apply(case_tac "json_document_cursor_compatible (document \<A>) (Cursor (butlast x #> ListC (Suc x1)))"; simp)
    apply(simp add: json_document_cursor_compatible_sound)
    done
  thus "\<A> \<turnstile> e\<cdot>next \<longlonglongrightarrow>e c'"
    using 1 2 3 by auto
qed

lemma execute_expr_sound_complete:
  assumes "\<A> \<turnstile> e \<longlonglongrightarrow>e c"
  shows   "execute_expr \<A> e = Some c"
using assms by(induction rule: expr_operational_semantics.induct, auto simp add: json_document_cursor_compatible_complete)

definition json_document_of_val :: "val \<Rightarrow> json_document" where
  "json_document_of_val v \<equiv>
     case v of
       val.Int i \<Rightarrow> Leaf (primitive.Int i)
     | val.String s \<Rightarrow> Leaf (primitive.String s)
     | val.Bool b \<Rightarrow> Leaf (primitive.Bool b)
     | val.Null \<Rightarrow> Leaf primitive.Null
     | val.Empty_Map \<Rightarrow> Map_Node DAList.empty
     | val.Empty_List \<Rightarrow> List_Node []"

definition assign :: "json_document \<Rightarrow> json_cursor \<Rightarrow> val \<rightharpoonup> json_document" where
  "assign j c v \<equiv>                                      
     edit j c (\<lambda>_. Some (json_document_of_val v)) (json_document_of_val v)"

inductive cmd_operation_semantics :: "'a node_state \<Rightarrow> 'a cmd \<Rightarrow> 'a node_state \<Rightarrow> bool" ("_/ \<turnstile>/ _/ \<longlonglongrightarrow>c/ _" [65,65,65]65) where
  "\<lbrakk> \<A> \<turnstile> c \<longlonglongrightarrow>c \<A>'; \<A>' \<turnstile> d \<longlonglongrightarrow>c \<A>'' \<rbrakk> \<Longrightarrow> \<A> \<turnstile> (c \<triangleright> d) \<longlonglongrightarrow>c \<A>''" |
  "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; \<A>' = \<A>\<lparr> vars := DAList.update x c (vars \<A>) \<rparr> \<rbrakk> \<Longrightarrow> \<A> \<turnstile> (let x\<acute> \<Leftarrow> e) \<longlonglongrightarrow>c \<A>'" |
  "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; Some d = assign (document \<A>) c v; \<A>' = \<A>\<lparr> document := d \<rparr> \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e \<Leftarrow> v \<longlonglongrightarrow>c \<A>'" |
  "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; Some d = insert (document \<A>) c (json_document_of_val v); \<A>' = \<A>\<lparr> document := d \<rparr> \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>insert\<lparr> v \<rparr> \<longlonglongrightarrow>c \<A>'"
(*
  "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>delete \<longlonglongrightarrow>c undefined" |
  "\<A> \<turnstile> yield \<longlonglongrightarrow>c undefined"
*)

end