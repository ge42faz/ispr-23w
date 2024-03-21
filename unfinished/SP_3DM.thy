theory SP_3DM
	imports Main "../Reductions" "../CNF_SAT_To_Clique/CNF_SAT_To_Clique" "CLQ_SP"
begin

fun snd :: "'a * 'b * 'c \<Rightarrow> 'b"
	where "snd (x, y, z) = y"

fun trd :: "'a * 'b * 'c \<Rightarrow> 'c"
	where "trd (x, y, z) = z"

definition pw_dj :: "'a * 'b * 'c \<Rightarrow> 'a * 'b * 'c \<Rightarrow> bool"
	where "pw_dj xyz abc \<longleftrightarrow> fst xyz \<noteq> fst abc \<and> snd xyz \<noteq> snd abc \<and> trd xyz \<noteq> trd abc"

definition finite :: "'a set * 'b set * 'c set \<Rightarrow> bool"
	where "finite xyz \<longleftrightarrow> Finite_Set.finite (fst xyz) \<and> Finite_Set.finite (snd xyz) \<and> Finite_Set.finite (trd xyz)"

definition is_3dm :: "('a * 'b * 'c) set \<Rightarrow> bool"
	where "is_3dm M \<longleftrightarrow> (\<forall>xyz \<in> M. \<forall>abc \<in> M. xyz = abc \<or> pw_dj xyz abc)"

definition pset_3dm :: "(('a set * 'b set * 'c set) * ('a * 'b * 'c) set * nat) set"
	where "pset_3dm = {(XYZ, T, k). \<exists>M. finite XYZ \<and> M \<subseteq> T \<and> (\<forall>t \<in> T. fst t \<in> fst XYZ \<and> snd t \<in> snd XYZ \<and> trd t \<in> trd XYZ) \<and> is_3dm M}"

fun card3 :: "('a * 'a set) set \<Rightarrow> 'a set \<Rightarrow> bool"
	where "card3 coll elems \<longleftrightarrow> (\<Union>(prod.snd ` coll)) \<subseteq> elems \<and> (\<forall>e \<in> coll. card (prod.snd e) = 3)"

fun sp_3dm :: "(('a * 'a set) set * 'a set * nat) \<Rightarrow> ('a set set * 'a set * nat)"
	where "sp_3dm (coll, elems, k) = (if card3 coll elems then (prod.snd ` coll, elems, k) else ({}, {}, 1))"



end