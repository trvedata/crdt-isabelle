theory
  Datalog
imports
  Main
begin

section \<open>Datalog syntax\<close>

subsection \<open>Syntax of a rule\<close>

record ('rel, 'var) atom =
  atom_rel  :: "'rel"
  atom_vars :: "'var list"
  atom_neg  :: "bool"

type_synonym ('rel, 'var) rule = "('rel \<times> 'var list) \<times> ('rel, 'var) atom set"

nonterminal atomvars and ruleatom and ruleatoms
syntax
  "_atomvar"   :: "'a \<Rightarrow> atomvars"             ("_")
  "_atomvars"  :: "['a, atomvars] \<Rightarrow> atomvars" ("_,/ _" [86,85] 85)
  "_posatom"   :: "['a, atomvars] \<Rightarrow> ruleatom" ("_\<langle>_\<rangle>"   [100,80] 80)
  "_negatom"   :: "['a, atomvars] \<Rightarrow> ruleatom" ("\<not>_\<langle>_\<rangle>"  [100,80] 80)
  "_ruleatom"  :: "ruleatom \<Rightarrow> ruleatoms"      ("_")
  "_ruleatoms" :: "[ruleatom, ruleatoms] \<Rightarrow> ruleatoms" ("_,/ _" [75,76] 75)
  "_ruleexpr"  :: "['a, atomvars, ruleatoms] \<Rightarrow> 'a"    ("_\<langle>_\<rangle>/ \<leftarrow>/ _" [70,70,70] 70)
translations
  "_atomvar v"        \<rightleftharpoons> "(v#[])"
  "_atomvars v vs"    \<rightleftharpoons> "(v#vs)"
  "_posatom R vs"     \<rightleftharpoons> "\<lparr>atom_rel=R, atom_vars=vs, atom_neg=CONST True\<rparr>"
  "_negatom R vs"     \<rightleftharpoons> "\<lparr>atom_rel=R, atom_vars=vs, atom_neg=CONST False\<rparr>"
  "_ruleatom a"       \<rightleftharpoons> "CONST insert a {}"
  "_ruleatoms a as"   \<rightleftharpoons> "CONST insert a as"
  "_ruleexpr R vs as" \<rightleftharpoons> "((R, vs), as)"

term "R\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>"
term "R\<langle>x\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> S\<langle>x\<rangle>, T\<langle>x, y\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> S\<langle>x\<rangle>, \<not>T\<langle>x, y\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>, T\<langle>x, y\<rangle>"

(* Example *)
lemma "R\<langle>x, y\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>, T\<langle>x, y\<rangle> =
       ((R, [x, y]), {
         \<lparr>atom_rel=S, atom_vars=[x], atom_neg=False\<rparr>,
         \<lparr>atom_rel=T, atom_vars=[x, y], atom_neg=True\<rparr>})"
by auto

subsection \<open>Syntax of a ruleset\<close>

type_synonym ('rel, 'var) ruleset = "('rel, 'var) rule set"

definition to_ruleset :: "('rel, 'var) rule \<Rightarrow> ('rel, 'var) ruleset"
  ("_." [60] 60) where
  "r. \<equiv> {r}"

definition add_rule :: "('rel, 'var) rule \<Rightarrow> ('rel, 'var) ruleset \<Rightarrow> ('rel, 'var) ruleset"
  ("_;//_" [51,50] 50) where
  "r ; rs \<equiv> insert r rs"

term "S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>."
term "S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>; S\<langle>x,y\<rangle> \<leftarrow> S\<langle>x,z\<rangle>, R\<langle>z,y\<rangle>."
term "S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>; S\<langle>x,y\<rangle> \<leftarrow> S\<langle>x,z\<rangle>, R\<langle>z,y\<rangle>."
term "A\<langle>x\<rangle> \<leftarrow> R\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> T\<langle>x\<rangle>, \<not>U\<langle>x\<rangle>."


end
