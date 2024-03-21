theory CSAT_SAT
	imports Main SAT_3SAT
begin

term "Trueprop (a \<and> b)"
term "a \<longrightarrow> b"

lemma "(True \<longrightarrow> True) = True"
	by simp
datatype 'a gate 	= NOT "'a" 				("\<not>_")
									| AND "'a" "'a" 	("_\<and>_")
									| OR "'a" "'a" 		("_\<or>_")
									| NAND "'a" "'a" 	("_\<not>\<and>_")
									| NOR "'a" "'a"		("_\<not>\<or>_")
									| XOR "'a" "'a"		("_\<noteq>_")
									| XNOR "'a" "'a"	("_=_")


end