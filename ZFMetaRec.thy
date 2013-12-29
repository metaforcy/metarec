theory ZFMetaRec
imports ZFMetaRecSyntax
begin

(* ML_file "zfmetarec.ML"

setup {* ZFMetaRec.setup *} *)



definition
  failjud :: "i => o" where
  [MRjud 1 0]: "failjud(u) == True"

definition
  intensionally_inequal :: "i => i => o" where
  [MRjud 2 0]: "intensionally_inequal(x, y) == True"

lemma [MR]: "intensionally_inequal(x, y)" by (simp add: intensionally_inequal_def)
lemma [MR]: "failjud(0) ==> intensionally_inequal(x, x)" by (simp add: intensionally_inequal_def)



end
