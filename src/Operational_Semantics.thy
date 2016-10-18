theory
  Operational_Semantics
imports
  Main
  JSON_Document
  Editing_Language
  "~~/src/HOL/Library/Product_Lexorder"
begin

datatype mutation
  = Insert "val"
  (*| Delete*)
  | Assign "val"

record operation =
  operation_id     :: "lamport"
  operation_deps   :: "lamport set"
  operation_cursor :: "json_cursor"
  operation_mut    :: "mutation"

definition mk_operation :: "lamport \<Rightarrow> lamport set \<Rightarrow> json_cursor \<Rightarrow> mutation \<Rightarrow> operation" where
  "mk_operation i d c m \<equiv> \<lparr> operation_id = i, operation_deps = d, operation_cursor = c, operation_mut = m \<rparr>"

record 'a node_state =
  document       :: json_document
  vars           :: "('a, json_cursor) alist"
  highest_seen   :: "nat"
  send_buffer    :: "operation set"
  receive_buffer :: "operation set"
  applied_opers  :: "lamport set"

definition valid_node_state :: "'a node_state \<Rightarrow> bool" where
  "valid_node_state \<sigma> \<equiv> \<forall>v c. DAList.lookup (vars \<sigma>) v = Some c \<longrightarrow> document \<sigma> \<bowtie> c"

definition initial_state :: "'a node_state" where
  "initial_state \<equiv>
     \<lparr> document       = Map_Node DAList.empty
     , vars           = DAList.empty
     , highest_seen   = 0
     , send_buffer    = {}
     , receive_buffer = {}
     , applied_opers  = {}
     \<rparr>"

definition generate_operation_id :: "'a node_state \<Rightarrow> nat \<Rightarrow> (lamport \<times> 'a node_state)" where
  "generate_operation_id \<A> ident \<equiv>
     let c = Suc (highest_seen \<A>);
         a = \<A>\<lparr> highest_seen := c \<rparr>
     in (OperationID (c, ident), a)"

lemma initial_node_state_valid [simp]:
  shows "valid_node_state initial_state"
by (auto simp add: initial_state_def valid_node_state_def)

fun next_list_element :: "('a \<times> lamport) list \<Rightarrow> lamport \<Rightarrow> lamport option" where
  "next_list_element []       l = None" |
  "next_list_element [(v, k)]      Head = Some k" |
  "next_list_element [x]      (OperationID k) = None" |
  "next_list_element ((v,k)#y#xs) Head = Some k" |
  "next_list_element ((v,k')#y#xs) (OperationID k) =
     (if OperationID k = k' then
        Some (snd y)
      else next_list_element (y#xs) (OperationID k))"
                                                                         
inductive expr_operational_semantics :: "'a node_state \<Rightarrow> 'a expr \<Rightarrow> json_cursor \<Rightarrow> bool" ("_/ \<turnstile>/ _/ \<longlonglongrightarrow>e/ _" [65,65,65]65) where
  expr_operational_semantics_Doc [intro!]: "\<A> \<turnstile> doc \<longlonglongrightarrow>e Cursor []" |
  expr_operational_semantics_Var [intro!]: "\<lbrakk> DAList.lookup (vars \<A>) v = Some c \<rbrakk> \<Longrightarrow> \<A> \<turnstile> v\<acute> \<longlonglongrightarrow>e c" |
  expr_operational_semantics_Lookup [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; c' = grow_map_entry c k \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<lbrakk> k \<rbrakk> \<longlonglongrightarrow>e c'" |
  expr_operational_semantics_Iter [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; c' = grow_list_entry c Head \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>iter \<longlonglongrightarrow>e c'" |
  expr_operational_semantics_Next [intro!]: "\<lbrakk> \<A> \<turnstile> e \<longlonglongrightarrow>e c; c = Cursor cs; cs \<noteq> []; last cs = ListC k; Some (List_Node js) = fetch (document \<A>) (Cursor (butlast cs));
                                               Some c' = next_list_element js k; c'' = Cursor (butlast cs #> ListC c'); document \<A> \<bowtie> c'' \<rbrakk> \<Longrightarrow> \<A> \<turnstile> e\<cdot>next \<longlonglongrightarrow>e c''"

definition from_list_node :: "json_document \<Rightarrow> (json_document \<times> lamport) list option" where
  "from_list_node j \<equiv>
     case j of
       List_Node js \<Rightarrow> Some js
     | _ \<Rightarrow> None"

fun execute_expr :: "'a node_state \<Rightarrow> 'a expr \<rightharpoonup> json_cursor" where
  "execute_expr \<A> Doc     = Some (Cursor [])" |
  "execute_expr \<A> (Var v) = DAList.lookup (vars \<A>) v" |
  "execute_expr \<A> (Lookup e k) =
     do { c \<leftarrow> execute_expr \<A> e
        ; Some (grow_map_entry c k)
        }" |
  "execute_expr \<A> (Iter e) =
     do { c \<leftarrow> execute_expr \<A> e
        ; Some (grow_list_entry c Head)
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
                     do { js \<leftarrow> fetch (document \<A>) (Cursor (butlast cs))
                        ; js \<leftarrow> from_list_node js
                        ; c' \<leftarrow> next_list_element js k
                        ; let c'' = Cursor (butlast cs #> ListC c')
                        ; if json_document_cursor_compatible (document \<A>) c'' then
                            Some c''
                          else None
                        }
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
  have "c = grow_list_entry c' Head"
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
  from * ** and this obtain js where 3: "Some (List_Node js) = fetch (document \<A>) (Cursor (butlast cs))"
    apply simp
    apply(case_tac "execute_expr \<A> e"; simp)
    apply(case_tac "a"; simp)
    apply(case_tac "x=[]"; simp)
    apply(case_tac "last x"; simp)
    apply(case_tac "fetch (document \<A>) (Cursor (butlast x))"; simp)
    apply(case_tac "from_list_node aa"; simp)
    apply(case_tac "next_list_element ab x1"; simp add: Let_def)
    apply(case_tac "json_document_cursor_compatible (document \<A>) (Cursor (butlast x #> ListC ac))"; simp)
    apply(case_tac aa; simp add: from_list_node_def)
    done
  from * ** and 2 3 obtain c'' where 4: "Some c'' = next_list_element js k"
    apply simp
    apply(case_tac "execute_expr \<A> e"; simp)
    apply(case_tac "a"; simp)
    apply(case_tac "x=[]"; simp)
    apply(case_tac "last x"; simp)
    apply(case_tac "fetch (document \<A>) (Cursor (butlast x))"; simp)
    apply(case_tac "from_list_node aa"; simp)
    apply(case_tac "next_list_element ab x1"; simp add: Let_def)
    apply(case_tac "json_document_cursor_compatible (document \<A>) (Cursor (butlast x #> ListC ac))"; simp)
    apply(simp add: from_list_node_def)
    apply(case_tac "aa"; simp)
    done
  from * ** and 2 3 4 have 5: "c' = Cursor (butlast cs #> ListC c'')"
    apply simp
    apply(case_tac "execute_expr \<A> e"; simp)
    apply(case_tac "a"; simp)
    apply(case_tac "x=[]"; simp)
    apply(case_tac "last x"; simp)
    apply(case_tac "fetch (document \<A>) (Cursor (butlast x))"; simp)
    apply(case_tac "from_list_node aa"; simp)
    apply(case_tac "next_list_element ab x1"; simp add: Let_def)
    apply(case_tac "json_document_cursor_compatible (document \<A>) (Cursor (butlast x #> ListC ac))"; simp)
    apply(simp add: from_list_node_def)
    apply(case_tac "aa"; simp)
    done
  from * have 6: "document \<A> \<bowtie> c'"
    apply simp
    apply(case_tac "execute_expr \<A> e"; simp)
    apply(case_tac "a"; simp)
    apply(case_tac "x=[]"; simp)
    apply(case_tac "last x"; simp)
    apply(case_tac "fetch (document \<A>) (Cursor (butlast x))"; simp)
    apply(case_tac "from_list_node aa"; simp)
    apply(case_tac "next_list_element ab x1"; simp add: Let_def)
    apply(case_tac "json_document_cursor_compatible (document \<A>) (Cursor (butlast x #> ListC ac))"; simp)
    apply(rule json_document_cursor_compatible_sound, assumption)
    done
  thus "\<A> \<turnstile> e\<cdot>next \<longlonglongrightarrow>e c'"
    using 1 2 3 4 5 by auto
qed

lemma execute_expr_sound_complete:
  assumes "\<A> \<turnstile> e \<longlonglongrightarrow>e c"
  shows   "execute_expr \<A> e = Some c"
using assms
  apply(induction rule: expr_operational_semantics.induct; simp)
  apply(case_tac "fetch (document \<A>') (Cursor (butlast cs))"; simp)
  apply(case_tac "a"; simp add: from_list_node_def)
  apply(case_tac "next_list_element x2 k"; simp add: Let_def)
  apply(rule json_document_cursor_compatible_complete, assumption)
done

definition singleton_alist :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) alist" where
  "singleton_alist k v \<equiv> DAList.update k v (DAList.empty)"

definition json_document_of_val :: "val \<Rightarrow> lamport \<Rightarrow> json_document" where
  "json_document_of_val v l \<equiv>
     case v of
       val.Int i \<Rightarrow> Leaf (singleton_alist l (primitive.Int i))
     | val.String s \<Rightarrow> Leaf (singleton_alist l (primitive.String s))
     | val.Bool b \<Rightarrow> Leaf (singleton_alist l (primitive.Bool b))
     | val.Null \<Rightarrow> Leaf (singleton_alist l primitive.Null)
     | val.Empty_Map \<Rightarrow> Map_Node DAList.empty
     | val.Empty_List \<Rightarrow> List_Node []"

definition assign :: "json_document \<Rightarrow> json_cursor \<Rightarrow> (val \<times> lamport) \<rightharpoonup> json_document" where
  "assign j c v \<equiv>                                      
     edit j c (\<lambda>_. Some (json_document_of_val (fst v) (snd v))) (json_document_of_val (fst v) (snd v))"

definition interpret_operation :: "'a node_state \<Rightarrow> operation \<rightharpoonup> 'a node_state" where
  "interpret_operation n oper \<equiv>                         
     case operation_mut oper of
       Assign v \<Rightarrow>
         do { let lamport = operation_id oper
            ; d \<leftarrow> assign (document n) (operation_cursor oper) (v, lamport)
            ; Some (n\<lparr> applied_opers := applied_opers n \<union> {lamport}, document := d\<rparr>)
            }
     | Insert v \<Rightarrow>
         do { let lamport = operation_id oper
            ; d \<leftarrow> insert (document n) (operation_cursor oper) (json_document_of_val v lamport, lamport)
            ; Some (n\<lparr> applied_opers := applied_opers n \<union> {lamport}, document := d\<rparr>)
            }"

inductive cmd_operation_semantics :: "'a node_state list \<Rightarrow> nat \<Rightarrow> 'a cmd \<Rightarrow> 'a node_state list \<Rightarrow> bool" ("_\<langle>_\<rangle>/ \<turnstile>/ _/ \<longlonglongrightarrow>c/ _" [65,65,65,65]65) where
  "\<lbrakk> m < length \<A>s; (lt, \<A>, gt) = split_at \<A>s m; \<A> \<turnstile> e \<longlonglongrightarrow>e c; \<A>' = \<A>\<lparr> vars := DAList.update x c (vars \<A>) \<rparr>; \<A>s' = lt @ [\<A>'] @ gt \<rbrakk> \<Longrightarrow> \<A>s\<langle>m\<rangle> \<turnstile> (let x\<acute> \<Leftarrow> e) \<longlonglongrightarrow>c \<A>s'" |
  "\<lbrakk> m < length \<A>s; (lt, \<A>, gt) = split_at \<A>s m; \<A> \<turnstile> e \<longlonglongrightarrow>e c; (lamport, \<A>') = generate_operation_id \<A> m; oper = mk_operation lamport (applied_opers \<A>') c (Assign v);
      Some \<A>'' = interpret_operation \<A>' oper; \<A>''' = \<A>''\<lparr> send_buffer := send_buffer \<A>'' \<union> {oper} \<rparr>; \<A>s' = lt @ [\<A>'''] @ gt \<rbrakk> \<Longrightarrow> \<A>s\<langle>m\<rangle> \<turnstile> e \<Leftarrow> v \<longlonglongrightarrow>c \<A>s'" |
  "\<lbrakk> m < length \<A>s; (lt, \<A>, gt) = split_at \<A>s m; \<A> \<turnstile> e \<longlonglongrightarrow>e c; (lamport, \<A>') = generate_operation_id \<A> m; oper = mk_operation lamport (applied_opers \<A>') c (Insert v);
      Some \<A>'' = interpret_operation \<A>' oper; \<A>''' = \<A>''\<lparr> send_buffer := send_buffer \<A>'' \<union> {oper} \<rparr>; \<A>s' = lt @ [\<A>'''] @ gt \<rbrakk> \<Longrightarrow> \<A>s\<langle>m\<rangle> \<turnstile> e\<cdot>insert\<lparr> v \<rparr> \<longlonglongrightarrow>c \<A>s'" |
  "\<lbrakk> m < length \<A>s \<rbrakk> \<Longrightarrow> \<A>s\<langle>m\<rangle> \<turnstile> yield \<longlonglongrightarrow>c \<A>s" |
  "\<lbrakk> m < length \<A>s; n < length \<A>s; (lt, \<A>, gt) = split_at \<A>s i; focus = \<A>s!n; \<A>' = \<A>\<lparr> receive_buffer := receive_buffer \<A> \<union> send_buffer focus \<rparr>;
      \<A>s' = lt @ [\<A>'] @ gt \<rbrakk> \<Longrightarrow> \<A>s\<langle>m\<rangle> \<turnstile> yield \<longlonglongrightarrow>c \<A>s'" |
  "\<lbrakk> m < length \<A>s; (lt, \<A>, gt) = split_at \<A>s m; receive_buffer \<A> \<noteq> {}; oper = (SOME x. x \<in> receive_buffer \<A>);
      operation_id oper \<notin> applied_opers \<A>; operation_deps oper \<subseteq> applied_opers \<A>; Some \<A>' = interpret_operation \<A> oper;
      \<A>s' = lt @ [\<A>'] @ gt \<rbrakk> \<Longrightarrow> \<A>s\<langle>m\<rangle> \<turnstile> yield \<longlonglongrightarrow>c \<A>s'" |
  "\<lbrakk> \<A>s\<langle>m\<rangle> \<turnstile> yield \<longlonglongrightarrow>c \<A>s'; \<A>s'\<langle>m\<rangle> \<turnstile> yield \<longlonglongrightarrow>c \<A>s'' \<rbrakk> \<Longrightarrow> \<A>s\<langle>m\<rangle> \<turnstile> yield \<longlonglongrightarrow>c \<A>s''"

inductive valid_execution :: "'a node_state list \<Rightarrow> bool" where
  "valid_execution []" |                             
  "\<lbrakk> valid_execution \<A>s \<rbrakk> \<Longrightarrow> valid_execution (initial_state # \<A>s)" |
  "\<lbrakk> valid_execution \<A>s; \<A>s\<langle>i\<rangle> \<turnstile> c \<longlonglongrightarrow>c \<A>s' \<rbrakk> \<Longrightarrow> valid_execution \<A>s'"

lemma backchain_empty_applied_orders:
  assumes "\<A>s\<langle>i\<rangle> \<turnstile> c \<longlonglongrightarrow>c \<A>s'" "\<A>s!i = m" "applied_opers m = {}"
  shows   "m \<in> set \<A>s"
using assms
  apply(induction)
  apply(simp add: split_at_def)
  apply(erule conjE)+
  apply clarify
  apply simp
  apply(simp add: split_at_def)
  apply(erule conjE)+
  apply clarify
  apply simp
  apply(simp add: split_at_def)
  apply(erule conjE)+
  apply clarify
  apply simp
  apply clarify
  apply simp
  apply(simp add: split_at_def)
  apply(erule conjE)+
  apply clarify
  apply simp
  apply(simp add: split_at_def)
  apply(erule conjE)+
  apply clarify
  apply simp
  apply(simp add: split_at_def)
done

lemma valid_execution_applied_opers_empty_document:
  assumes "valid_execution \<A>s" "m \<in> set \<A>s" "applied_opers m = {}"
  shows   "document m = Map_Node DAList.empty"
using assms proof(induction)
  assume "m \<in> set []"
  thus "document m = Map_Node DAList.empty"
    by auto
next
  fix \<A>s :: "'a node_state list"
  assume "valid_execution \<A>s" and IH: "(m \<in> set \<A>s \<Longrightarrow> applied_opers m = {} \<Longrightarrow> document m = Map_Node DAList.empty)"
    "m \<in> set (initial_state # \<A>s)" "applied_opers m = {}"
  hence "m = initial_state \<or> m \<in> set \<A>s"
    by auto
  thus "document m = Map_Node DAList.empty"
  proof
    assume "m = initial_state"
    thus "document m = Map_Node DAList.empty"
      by(auto simp add: initial_state_def)
  next
    assume "m \<in> set \<A>s"
    thus "document m = Map_Node DAList.empty"
      using `valid_execution \<A>s` `applied_opers m = {}` IH by simp
  qed
next
  fix \<A>s \<A>s' :: "'a node_state list" and i :: "nat" and c :: "'a cmd"
  assume "\<A>s\<langle>i\<rangle> \<turnstile> c \<longlonglongrightarrow>c \<A>s'" "valid_execution \<A>s" "(m \<in> set \<A>s \<Longrightarrow> applied_opers m = {} \<Longrightarrow> document m = Map_Node DAList.empty)"
    and "m \<in> set \<A>s'" "applied_opers m = {}"
  hence "document m = Map_Node DAList.empty"
    apply(induction rule: cmd_operation_semantics.induct)
    apply(simp only: split_at_def prod.inject)
    apply(erule conjE)+
    apply(case_tac "m = \<A>s ! ma")
    apply clarify

lemma
  assumes "valid_execution \<A>s" "m \<in> set \<A>s" "n \<in> set \<A>s" "applied_opers m = applied_opers n"
  shows   "document m = document n"
using assms proof(induction)
  assume "m \<in> set []"
  hence "m \<in> {}"
    by auto
  thus "document m = document n"
    by auto
next
  fix \<A>s :: "'a node_state list"
  assume "valid_execution \<A>s" and IH: "(m \<in> set \<A>s \<Longrightarrow> n \<in> set \<A>s \<Longrightarrow> applied_opers m = applied_opers n \<Longrightarrow> document m = document n)"
    and "m \<in> set (initial_state # \<A>s)" "n \<in> set (initial_state # \<A>s)" "applied_opers m = applied_opers n"
  hence "m = initial_state \<or> m \<in> set \<A>s" "n = initial_state \<or> n \<in> set \<A>s"
    by auto
  show "document m = document n"
  proof(rule disjE[OF `m = initial_state \<or> m \<in> set \<A>s`])
    assume "m = initial_state"
    show "document m = document n"
    proof(rule disjE[OF `n = initial_state \<or> n \<in> set \<A>s`])
      assume "n = initial_state"
      thus "document m = document n"
        using `m = initial_state` by(auto simp add: initial_state_def)
    next
      assume "n \<in> set \<A>s"
      have "applied_opers n = {}"
        using `applied_opers m = applied_opers n` `m = initial_state` by(auto simp add: initial_state_def)
      hence "document n = Map_Node DAList.empty"
        using valid_execution_applied_opers_empty_document `n \<in> set \<A>s` `valid_execution \<A>s` by auto
      thus "document m = document n"
        using `m = initial_state` by(auto simp add: initial_state_def)
    qed
  next
    assume "m \<in> set \<A>s"
    show "document m = document n"
    proof(rule disjE[OF `n = initial_state \<or> n \<in> set \<A>s`])
      assume "n = initial_state"
      have "applied_opers m = {}"
        using `applied_opers m = applied_opers n` `n = initial_state` by(auto simp add: initial_state_def)
      hence "document m = Map_Node DAList.empty"
        using valid_execution_applied_opers_empty_document `m \<in> set \<A>s` `valid_execution \<A>s` by auto
      thus "document m = document n"
        using `n = initial_state` by(auto simp add: initial_state_def)
    next
      assume "n \<in> set \<A>s"
      thus "document m = document n"
        using `m \<in> set \<A>s` `valid_execution \<A>s` IH `applied_opers m = applied_opers n` by simp
    qed
  qed
next
  fix \<A>s \<A>s' :: "'a node_state list" and i :: "nat" and c :: "'a cmd"
  assume "valid_execution \<A>s" and IH: "(m \<in> set \<A>s \<Longrightarrow> n \<in> set \<A>s \<Longrightarrow> applied_opers m = applied_opers n \<Longrightarrow> document m = document n)"
    and "\<A>s\<langle>i\<rangle> \<turnstile> c \<longlonglongrightarrow>c \<A>s'" "m \<in> set \<A>s'" "n \<in> set \<A>s'" "applied_opers m = applied_opers n"
  from `\<A>s\<langle>i\<rangle> \<turnstile> c \<longlonglongrightarrow>c \<A>s'` `m \<in> set \<A>s'` `n \<in> set \<A>s'` show "document m = document n"
  proof(induction)
    fix m :: "nat" and \<A>s \<A>s' lt gt :: "'a node_state list" and \<A> \<A>' :: "'a node_state"
      and e :: "'a expr" and c :: "json_cursor" and v :: "'a"
    assume "m < length \<A>s" "(lt, \<A>, gt) = split_at \<A>s m" "\<A> \<turnstile> e \<longlonglongrightarrow>e c" "\<A>' = \<A>\<lparr>vars := DAList.update v c (vars \<A>)\<rparr>"
      and "\<A>s' = lt @ [\<A>'] @ gt"

end