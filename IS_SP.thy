theory IS_SP
	imports Main "../Reductions" "../Three_Sat_To_Set_Cover"
begin

definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
	where "disjoint s1 s2 = (\<forall>e1 \<in> s1. \<forall>e2 \<in> s2. e1 \<noteq> e2)"

definition elem_set :: "'a set \<Rightarrow> 'a set set"
	where "elem_set s = {{x} | x. x \<in> s}"

definition set_packing :: "'b set set \<Rightarrow> 'b set set \<Rightarrow> bool"
	where "set_packing coll subsets = ((\<forall>s1 \<in> subsets. \<forall>s2 \<in> subsets. s1 \<noteq> s2 \<longrightarrow> disjoint s1 s2) \<and> subsets \<subseteq> coll)"

definition "set_packing_pset = {(coll, n). \<exists>subsets. card subsets \<ge> n \<and> set_packing coll subsets}"

fun is_sp :: "'a set set * nat \<Rightarrow> 'a set set set * nat"
	where "is_sp (E, k) = (
		let V = \<Union>E in
			({adjE | adjE. adjE \<subseteq> E \<and> (\<exists>v \<in> V. \<forall>e \<in> adjE. v \<in> e)}, k)
	)"

value "fold (+) [] 0::nat"

definition node_range :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set set"
	where "node_range E v = {{v, v_adj} | v_adj. {v, v_adj} \<in> E}"

definition adj_count :: "'a set set \<Rightarrow> 'a \<Rightarrow> nat"
	where "adj_count E v = card (node_range E v)"

definition node_range_univ :: "'a set set \<Rightarrow> 'a set set set"
	where "node_range_univ E = {node_range E v | v. v \<in> \<Union>E}"

definition node_range_set :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set set"
	where "node_range_set E subV = {node_range E v | v. v \<in> subV}"

lemma nr_sub: "ugraph E \<Longrightarrow> node_range E v \<subseteq> E"
	unfolding node_range_def
	by auto

lemma nrs_sub: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> \<Union>(node_range_set E subV) \<subseteq> E"
	unfolding node_range_def node_range_set_def
	by auto

lemma nru_sub: "ugraph E \<Longrightarrow> \<Union>(node_range_univ E) \<subseteq> E"
	unfolding node_range_def node_range_univ_def
	by auto

lemma tmp: "\<not>(A \<subseteq> B) \<Longrightarrow> \<exists>x \<in> A. x \<notin> B"
	by blast

lemma tmp2: "\<lbrakk> ugraph E; e \<in> E \<rbrakk> \<Longrightarrow> (\<exists>u \<in> \<Union>E. \<exists>v \<in> \<Union>E. e = {u, v})"
	unfolding ugraph_def
	by (metis UnionI card_2_iff insert_iff)

lemma nru_sup:
	assumes "ugraph E"
	shows "E \<subseteq> \<Union>(node_range_univ E)"
proof (rule ccontr)
	assume a: "\<not> E \<subseteq> \<Union>(node_range_univ E)"

	obtain u v where edge: "{u, v} \<in> E" and false: "{u, v} \<notin> \<Union>(node_range_univ E)"
		by (metis a assms tmp tmp2)

	from edge have "v \<in> \<Union>(node_range E u)"
		unfolding node_range_def by auto

	hence "{u, v} \<in> \<Union>(node_range_univ E)"
		unfolding node_range_univ_def
		apply auto
		by (metis (mono_tags, lifting) edge insertCI mem_Collect_eq node_range_def)

	from this false show "False" by simp
qed

lemma nru_eq: "ugraph E \<Longrightarrow> \<Union> (node_range_univ E) = E"
	using nru_sub nru_sup by fast


lemma "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> subV \<subseteq> \<Union>(\<Union>(node_range_set E subV))"
	unfolding node_range_set_def using nrs_sub
	apply auto
	oops


definition node_range_collapse :: "'a set set set \<Rightarrow> 'a set"
	where "node_range_collapse nrs = {v | v. \<forall>adjE \<in> nrs. \<forall>e \<in> adjE. v \<in> e}"

lemma "\<lbrakk> E \<noteq> {}; ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> subV \<subseteq> node_range_collapse (node_range_set E subV)"
	unfolding node_range_set_def node_range_collapse_def node_range_def
	apply auto

lemma "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> is_independent_set E subV \<Longrightarrow> set_packing (node_range_univ E) (node_range_set E subV)"
	unfolding is_independent_set_def set_packing_def using nru_eq
proof -
	oops

lemma "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E; k = card subV \<rbrakk> \<Longrightarrow> k = card (node_range_set E subV)"
	unfolding node_range_set_def node_range_def
	apply (auto simp add: finite_subset ugraph_vertex_set_finite)


lemma "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E; k \<le> card subV \<rbrakk> \<Longrightarrow> k \<le> card (node_range_set E subV)"
	unfolding node_range_set_def node_range_def
	apply (induction k)
	 apply auto



lemma "is_reduction is_sp independent_set set_packing_pset"
	unfolding is_reduction_def independent_set_def set_packing_pset_def
proof safe
	fix E :: "'a set set"
	fix k :: "nat"
	fix subsets :: "'a set set set"
	fix n :: "nat"
	fix subV :: "'a set"
	assume conv: "is_sp (E, k) = (subsets, n)"
	assume graph: "ugraph E" "subV \<subseteq> \<Union>E"
	assume count: "k \<le> card subV"
	assume IS: "is_independent_set E subV"

	have num_eq: "n = k" using conv by simp

	obtain subsets where "subsets = node_range_set E subV"
		by simp

	hence "n \<le> card subsets"
		using num_eq count conv nrs_sub


		apply (intro exI)

end