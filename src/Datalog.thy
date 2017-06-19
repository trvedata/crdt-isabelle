theory
  Datalog
imports
  Main
begin

section \<open>Datalog syntax\<close>

subsection \<open>Syntax of a rule\<close>

type_synonym ('rel, 'var) rule = "('rel \<times> 'var list) \<times> ('rel \<times> 'var list \<times> bool) set"

definition add_premise :: "'rel \<times> 'var list \<times> bool \<Rightarrow> ('rel, 'var) rule \<Rightarrow> ('rel, 'var) rule"
  (infixr "premiseof" 50) where
  "atom premiseof rule \<equiv> (fst rule, insert atom (snd rule))"

nonterminal atomvars and ruleatom and ruleatoms
syntax
  "_atomvar"  :: "'a \<Rightarrow> atomvars"              ("_")
  "_atomvars" :: "['a, atomvars] \<Rightarrow> atomvars"  ("_,/ _" [86,85] 85)
  "_posatom"   :: "['a, atomvars] \<Rightarrow> ruleatom" ("_\<langle>_\<rangle>" [100,80] 80)
  "_negatom"   :: "['a, atomvars] \<Rightarrow> ruleatom" ("\<not>_\<langle>_\<rangle>" [100,80] 80)
  "_ruleatom"  :: "ruleatom \<Rightarrow> ruleatoms"      ("_")
  "_ruleatoms" :: "[ruleatom, ruleatoms] \<Rightarrow> ruleatoms" ("_,/ _" [75,76] 75)
  "_ruleexpr"  :: "['a, atomvars, ruleatoms] \<Rightarrow> 'a"    ("_\<langle>_\<rangle>/ \<leftarrow>/ _" [70,70,70] 70)
translations
  "_atomvar v" == "(v#[])"
  "_atomvars v vs" == "(v#vs)"
  "_posatom R vs" == "(R, vs, HOL.True)"
  "_negatom R vs" == "(R, vs, HOL.False)"
  "_ruleexpr R vs (_ruleatom a)" == "((R, vs), {a})"
  "_ruleexpr R vs (_ruleatoms a as)" == "a premiseof (_ruleexpr R vs as)"

term "R\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>"
term "R\<langle>x\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> S\<langle>x\<rangle>, T\<langle>x, y\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> S\<langle>x\<rangle>, \<not>T\<langle>x, y\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>, T\<langle>x, y\<rangle>"

(* Example *)
lemma "R\<langle>x, y\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>, T\<langle>x, y\<rangle> =
       ((R, [x, y]), {(S, [x], False), (T, [x, y], True)})"
by (simp add: add_premise_def)

subsection \<open>Syntax of a ruleset\<close>

type_synonym ('rel, 'var) ruleset = "('rel, 'var) rule set"

definition to_ruleset :: "('rel, 'var) rule \<Rightarrow> ('rel, 'var) ruleset"
  ("toruleset/ _" 50) where
  "toruleset rule \<equiv> {rule}"

definition add_rule :: "('rel, 'var) rule \<Rightarrow> ('rel, 'var) ruleset \<Rightarrow> ('rel, 'var) ruleset"
  (infixr "ruleinto" 50) where
  "r ruleinto rs \<equiv> insert r rs"

nonterminal rules
syntax
  "_ruleone" :: "'a \<Rightarrow> rules"          ("_")
  "_ruleadd" :: "['a, rules] \<Rightarrow> rules" ("_;//_" [56,55] 55)
  "_ruleset" :: "['a, rules] \<Rightarrow> 'a"    ("{_;//_}"  [56,55] 50)
translations
  "_ruleset p (_ruleone q)" == "p ruleinto (toruleset q)"
  "_ruleset p (_ruleadd q qs)" == "p ruleinto (_ruleset q qs)"

term "{S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>}"
term "{S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>; S\<langle>x,y\<rangle> \<leftarrow> S\<langle>x,z\<rangle>, R\<langle>z,y\<rangle>}"
term "{A\<langle>x\<rangle> \<leftarrow> R\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> T\<langle>x\<rangle>, \<not>U\<langle>x\<rangle>}"

end
