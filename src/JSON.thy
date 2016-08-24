chapter\<open>The JSON datatype\<close>

theory
  JSON
imports
  Main
begin

section\<open>Commands, expressions, and values\<close>

text\<open>The expression datatype \<open>'a expr\<close> is parameterised by the type of variables.\<close>
datatype 'a expr
  = Doc
  | Var "'a"
  | Lookup "'a expr" "string"
  | Iter   "'a expr"
  | Next   "'a expr"
  | Keys   "'a expr"
  | Values "'a expr"

syntax
  expr_doc_syntax    :: "'a expr"                      ("doc" 65)
  expr_var_syntax    :: "'a \<Rightarrow> 'a expr"                ("_\<acute>" [65]65)
  expr_lookup_syntax :: "'a expr \<Rightarrow> string \<Rightarrow> 'a expr" ("_\<lbrakk>/ _/ \<rbrakk>" [50,50]65)
  expr_iter_syntax   :: "'a expr \<Rightarrow> 'a expr"           ("_\<cdot>iter" [50]65)
  expr_next_syntax   :: "'a expr \<Rightarrow> 'a expr"           ("_\<cdot>next" [50]65)
  expr_keys_syntax   :: "'a expr \<Rightarrow> 'a expr"           ("_\<cdot>keys" [50]65)
  expr_values_syntax :: "'a expr \<Rightarrow> 'a expr"           ("_\<cdot>values" [50]65)

translations
  "doc"      \<rightleftharpoons> "CONST Doc"
  "v\<acute>"       \<rightleftharpoons> "CONST Var v"
  "e\<lbrakk> key \<rbrakk>" \<rightleftharpoons> "CONST Lookup e key"
  "e\<cdot>iter"   \<rightleftharpoons> "CONST Iter e"
  "e\<cdot>next"   \<rightleftharpoons> "CONST Next e"
  "e\<cdot>keys"   \<rightleftharpoons> "CONST Keys e"
  "e\<cdot>values" \<rightleftharpoons> "CONST Values e"

datatype val
  = Int    "int"
  | String "string"
  | Bool   "bool"
  | Null
  | Empty_Map
  | Empty_List

syntax
  val_int_syntax :: "int \<Rightarrow> val" ("\<up>i/ _" [65]65)
  val_string_syntax :: "string \<Rightarrow> val" ("\<up>s/ _" [65]65)
  val_bool_syntax :: "bool \<Rightarrow> val" ("\<up>b/ _" [65]65)
  val_null_syntax :: "val" ("null" 65)
  val_empty_map_syntax :: "val" ("\<lbrace>\<hyphen>\<rbrace>" 65)
  val_empty_list_syntax :: "val" ("\<lbrakk>\<hyphen>\<rbrakk>" 65)

translations
  "\<up>i i" \<rightleftharpoons> "CONST val.Int i"
  "\<up>s s" \<rightleftharpoons> "CONST val.String s"
  "\<up>b b" \<rightleftharpoons> "CONST val.Bool b"
  "null" \<rightleftharpoons> "CONST Null"
  "\<lbrace>\<hyphen>\<rbrace>"  \<rightleftharpoons> "CONST Empty_Map"
  "\<lbrakk>\<hyphen>\<rbrakk>"  \<rightleftharpoons> "CONST Empty_List"

datatype 'a cmd
  = Let "'a" "'a expr"
  | Assign "'a expr" "val"
  | Insert "'a expr" "val"
  | Delete "'a expr"
  | Yield
  | Sequence "'a cmd" "'a cmd" (infixr "\<triangleright>" 35)

syntax
  cmd_let_syntax      :: "'a \<Rightarrow> 'a expr \<Rightarrow> 'a cmd"    ("let/ _\<acute>/ \<Leftarrow>/ _" [45,45]45)
  cmd_assign_syntax   :: "'a expr \<Rightarrow> val \<Rightarrow> 'a cmd"   ("_/ \<Leftarrow>/ _" [65,65]65)
  cmd_insert_syntax   :: "'a expr \<Rightarrow> val \<Rightarrow> 'a cmd"   ("_\<cdot>insert\<lparr>_\<rparr>" [65,65]65)
  cmd_delete_syntax   :: "'a expr \<Rightarrow> 'a cmd"          ("_\<cdot>delete" [65]65)
  cmd_yield_syntax    :: "'a cmd"                     ("yield" 65)
  cmd_sequence_syntax :: "'a cmd \<Rightarrow> 'a cmd \<Rightarrow> 'a cmd"

translations
  "let x\<acute> \<Leftarrow> e"  \<rightleftharpoons> "CONST Let x e"
  "e \<Leftarrow> v"      \<rightleftharpoons> "CONST Assign e v"
  "e\<cdot>insert\<lparr>v\<rparr>" \<rightleftharpoons> "CONST Insert e v"
  "e\<cdot>delete"    \<rightleftharpoons> "CONST Delete e"
  "yield"      \<rightleftharpoons> "CONST Yield"

text\<open>The example from the paper...\<close>

value
  "doc \<Leftarrow> \<lbrace>\<hyphen>\<rbrace> \<triangleright>
   let list\<acute> \<Leftarrow> doc\<lbrakk> ''shopping'' \<rbrakk>\<cdot>iter \<triangleright>
   list\<acute>\<cdot>insert\<lparr> \<up>s ''eggs'' \<rparr> \<triangleright>
   let eggs\<acute> \<Leftarrow> list\<acute>\<cdot>next \<triangleright>
   eggs\<acute>\<cdot>insert\<lparr> \<up>s ''milk'' \<rparr> \<triangleright>
   list\<acute>\<cdot>insert\<lparr> \<up>s ''cheese'' \<rparr>"

end