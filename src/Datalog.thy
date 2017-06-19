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

definition rule_body :: "'a \<Rightarrow> 'a" where "rule_body body \<equiv> body"

nonterminal atomvars and ruleatom and ruleatoms and rulebody
syntax
  "_atomvar"   :: "'a \<Rightarrow> atomvars"                     ("_")
  "_atomvars"  :: "['a, atomvars] \<Rightarrow> atomvars"         ("_,/ _" [86,85] 85)
  "_posatom"   :: "[pttrn, atomvars] \<Rightarrow> ruleatom"      ("_\<langle>_\<rangle>"   [100,80] 80)
  "_negatom"   :: "[pttrn, atomvars] \<Rightarrow> ruleatom"      ("\<not>_\<langle>_\<rangle>"  [100,80] 80)
  "_ruleatom"  :: "ruleatom \<Rightarrow> ruleatoms"              ("_")
  "_ruleatoms" :: "[ruleatom, ruleatoms] \<Rightarrow> ruleatoms" ("_,/ _" [75,76] 75)
  "_rulebody"  :: "ruleatoms \<Rightarrow> rulebody"              ("_")
  "_ruleany"   :: "[idts, rulebody] \<Rightarrow> rulebody"       ("any/ (_),/ _" [76,75] 75)
  "_ruleexpr"  :: "[pttrn, atomvars, rulebody] \<Rightarrow> 'a"  ("_\<langle>_\<rangle>/ \<leftarrow>/ _" [70,70,70] 70)
translations
  "_atomvar v"        \<rightleftharpoons> "(v#[])"
  "_atomvars v vs"    \<rightleftharpoons> "(v#vs)"
  "_posatom R vs"     \<rightleftharpoons> "\<lparr>atom_rel=R, atom_vars=vs, atom_neg=CONST True\<rparr>"
  "_negatom R vs"     \<rightleftharpoons> "\<lparr>atom_rel=R, atom_vars=vs, atom_neg=CONST False\<rparr>"
  "_ruleatom a"       \<rightleftharpoons> "CONST insert a {}"
  "_ruleatoms a as"   \<rightleftharpoons> "CONST insert a as"
  "_rulebody as"      \<rightleftharpoons> "CONST rule_body as"
  "_ruleany v body"   \<rightleftharpoons> "CONST rule_body (\<lambda>v. body)"
  "_ruleexpr R (v#vs) body" \<rightleftharpoons> "\<lambda>v. _ruleexpr R vs body"
  "_ruleexpr R [] (CONST rule_body body)" \<rightleftharpoons> "(R, body)"

term "R\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>"
term "R\<langle>x\<rangle> \<leftarrow> any y, any z, S\<langle>w, x, y, z\<rangle>"
term "R\<langle>x\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> S\<langle>x\<rangle>, T\<langle>x, y\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> S\<langle>x, a\<rangle>, \<not>T\<langle>x, y, 3\<rangle>"
term "R\<langle>x, y\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>, T\<langle>x, y\<rangle>"
term "R\<langle>x, z\<rangle> \<leftarrow> any y, S\<langle>x,y\<rangle>, S\<langle>y,z\<rangle>"
term "\<lambda>x y. x"

(* Example *)
lemma "R\<langle>x, y\<rangle> \<leftarrow> \<not>S\<langle>x\<rangle>, T\<langle>x, y\<rangle> =
       (\<lambda>x y. (R, {
         \<lparr>atom_rel=S, atom_vars=[x], atom_neg=False\<rparr>,
         \<lparr>atom_rel=T, atom_vars=[x, y], atom_neg=True\<rparr>}))"
by auto

definition to_ruleset :: "'a \<Rightarrow> 'a set"
  ("_." [60] 60) where
  "r. \<equiv> {r}"

definition add_rule :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  ("_;//_" [51,50] 50) where
  "r ; rs \<equiv> insert r rs"

term "S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>."
term "S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>; S\<langle>x,y\<rangle> \<leftarrow> S\<langle>x,z\<rangle>, R\<langle>z,y\<rangle>."
term "S\<langle>x,y\<rangle> \<leftarrow> R\<langle>x,y\<rangle>; S\<langle>x,y\<rangle> \<leftarrow> S\<langle>x,z\<rangle>, R\<langle>z,y\<rangle>."
term "A\<langle>x\<rangle> \<leftarrow> R\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> S\<langle>x\<rangle>; A\<langle>x\<rangle> \<leftarrow> T\<langle>x\<rangle>, \<not>U\<langle>x\<rangle>."


end
