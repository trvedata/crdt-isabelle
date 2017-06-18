theory
  Datalog
imports
  Main
begin

section \<open>Datalog syntax\<close>

subsection \<open>Syntax for an atom\<close>

type_synonym ('rel, 'var) atom = "'rel \<times> 'var list"

definition null_relation :: "'rel \<Rightarrow> ('rel, 'var) atom" ("_\<langle>\<rangle>" [60] 60) where
  "R\<langle>\<rangle> \<equiv> (R, [])"

definition atom_var_cons :: "'var \<Rightarrow> ('rel, 'var) atom \<Rightarrow> ('rel, 'var) atom"
  (infixr "varcons" 50) where
  "x varcons atom \<equiv> (fst atom, x # (snd atom))"

nonterminal atomvars
syntax
  "_atomvar"  :: "'a \<Rightarrow> atomvars"             ("_")
  "_atomvars" :: "['a, atomvars] \<Rightarrow> atomvars" ("_,/ _" [86,85] 85)
  "_atomterm" :: "['a, atomvars] \<Rightarrow> 'a"       ("_\<langle>_\<rangle>" [100,80] 80)
translations
  "R\<langle>x\<rangle>" == "x varcons R\<langle>\<rangle>"
  "_atomterm R (_atomvars x xs)" == "x varcons (_atomterm R xs)"

term "R\<langle>\<rangle>"
term "R\<langle>x\<rangle>"
term "R\<langle>x, y\<rangle>"
term "R\<langle>x, y, z\<rangle>"
term "x varcons y varcons z varcons R\<langle>\<rangle>"
(*print_syntax*)

subsection \<open>Syntax for a rule\<close>

type_synonym ('rel, 'var) rule = "('rel, 'var) atom \<times> ('rel, 'var) atom set"

definition rule_fact :: "('rel, 'var) atom \<Rightarrow> ('rel, 'var) rule" ("_." 50) where
  "atom. \<equiv> (atom, {})"

definition add_premise :: "('rel, 'var) atom \<Rightarrow> ('rel, 'var) rule \<Rightarrow> ('rel, 'var) rule"
  (infixr "premiseof" 50) where
  "atom premiseof rule \<equiv> (fst rule, insert atom (snd rule))"

nonterminal ruleatoms
syntax
  "_ruleatom"  :: "'a \<Rightarrow> ruleatoms"              ("_")
  "_ruleatoms" :: "['a, ruleatoms] \<Rightarrow> ruleatoms" ("_,/ _" [76,75] 75)
  "_ruleexpr"  :: "['a, ruleatoms] \<Rightarrow> 'a"        ("_/ \<leftarrow>/ _" [70,70] 70)
translations
  "h \<leftarrow> x" == "x premiseof (h.)"
  "_ruleexpr h (_ruleatoms x xs)" == "x premiseof (_ruleexpr h xs)"

term "R\<langle>a\<rangle>"
term "R\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> S\<langle>x\<rangle>, T\<langle>x, y\<rangle>"

subsection \<open>Syntax for a ruleset\<close>

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
term "{A\<langle>x\<rangle> \<leftarrow> R\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> T\<langle>x\<rangle>}"

end
