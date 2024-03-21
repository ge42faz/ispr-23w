theory CLQ_SP
	imports Main "../Reductions" "../CNF_SAT_To_Clique/CNF_SAT_To_Clique"
begin

datatype 'a graph = graph "'a set set" "'a set"

definition set_packing :: "('a * 'a set) set \<Rightarrow> ('a * 'a set) set \<Rightarrow> 'a set \<Rightarrow> bool"
	where "set_packing coll subsets elems \<longleftrightarrow> (\<Union>(snd ` coll)) \<subseteq> elems \<and> (\<forall>s \<in> subsets. \<forall>t \<in> subsets. s = t \<or> snd s \<inter> snd t = {})"


fun inv_graph :: "'a graph \<Rightarrow> 'a graph" ("*_" 51)
	where "inv_graph (graph E V) = graph {{u, v} | u v. u \<in> V \<and> v \<in> V \<and> {u, v} \<notin> E \<and> card {u, v} = 2} V"
value "*graph {{a\<^sub>1::Enum.finite_2, a\<^sub>2}} {a\<^sub>1, a\<^sub>2}"

lemma "ugraph_nodes E V \<Longrightarrow> finite E"
	unfolding ugraph_nodes_def ugraph_def by simp

lemma node_finite_edge: "finite V \<Longrightarrow> finite {{u, v} | u v. u \<in> V \<and> v \<in> V}"
	by (simp add: finite_image_set2)

lemma invg_finite_aux: "\<lbrakk> \<Union>E \<subseteq> V; finite E; finite {{u, v} | u v. u \<in> V \<and> v \<in> V} \<rbrakk> \<Longrightarrow> finite {{u, v} | u v. u \<in> V \<and> v \<in> V \<and> {u, v} \<notin> E \<and> card {u, v} = 2}"
	by (smt (verit) finite_subset mem_Collect_eq subsetI)

lemma invg_finite_edge: "\<lbrakk> ugraph_nodes E V; graph E' V' = *graph E V \<rbrakk> \<Longrightarrow> finite E'"
	unfolding ugraph_nodes_def ugraph_def
	using invg_finite_aux node_finite_edge by auto


fun node_range :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a set * 'a set set"
	where "node_range (graph E V) v = ({v}, {{v, u} | u. u \<in> V \<and> {u, v} \<notin> E})"

fun node_range_univ :: "'a graph \<Rightarrow> ('a set * 'a set set) set"
	where "node_range_univ (graph E V) = {node_range (graph E V) v | v. v \<in> V}"

fun node_range_set :: "'a graph \<Rightarrow> 'a set \<Rightarrow> ('a set * 'a set set) set"
	where "node_range_set (graph E V) C = {node_range (graph E V) v | v. v \<in> C}"

definition set_packing_pset :: "(('a * 'a set) set * 'a set * nat) set"
	where "set_packing_pset = {(c, e, k). \<exists>subsets. finite c \<and> subsets \<subseteq> c \<and> card subsets \<ge> k \<and> set_packing c subsets e}"

definition kgraph :: "'a set \<Rightarrow> 'a set set"
	where "kgraph V = {{v, u} | v u. v \<in> V \<and> u \<in> V}"

fun clq_sp :: "'a set set * 'a set * nat \<Rightarrow> ('a set * 'a set set) set * 'a set set * nat"
	where "clq_sp (E, V, k) = (if ugraph_nodes E V then (node_range_univ (graph E V), kgraph V, k) else ({}, {}, 1))"

lemma node_range_univ_finite: "finite V \<Longrightarrow> finite (node_range_univ (graph E V))"
	by auto

lemma node_range_univ_inv: "\<Union>(snd ` node_range_univ (graph E V)) \<inter> E = {}"
	by (auto simp add: insert_commute)

lemma node_range_inj: "\<lbrakk> ugraph_nodes E V; u \<in> V; v \<in> V \<rbrakk> \<Longrightarrow> node_range (graph E V) u = node_range (graph E V) v \<Longrightarrow> u = v"
	by auto

lemma node_range_set_subset: "C \<subseteq> V \<longleftrightarrow> node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
	by auto

lemma node_range_set_eq: "node_range_set (graph E V) V = node_range_univ (graph E V)"
	by auto

lemma node_range_subset: "\<lbrakk> v \<in> V; ugraph_nodes E V; C \<subseteq> V \<rbrakk> \<Longrightarrow> snd (node_range (graph E C) v) \<subseteq> snd (node_range (graph E V) v)"
	by auto

lemma node_range_univ_subset: "v \<in> V \<Longrightarrow> node_range (graph E V) v \<in> node_range_univ (graph E V)"
	by auto

lemma node_range_insert: "ugraph_nodes E V \<Longrightarrow> x \<in> F \<longleftrightarrow> node_range (graph E V) x \<in> node_range_set (graph E V) F"
	by auto

lemma card_insert_old: "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> card (insert x A) = card A"
	by (induction A arbitrary: x rule: finite_induct) (auto simp add: insert_absorb)

lemma card_insert_new: "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> card (insert x A) = Suc (card A)"
	by (rule card.insert)

lemma node_range_set_0: "node_range_set G {} = {}"
	by (smt Collect_empty_eq empty_iff node_range_set.elims)

lemma node_range_set_0_card: "card (node_range_set G {}) = 0"
	by (smt Collect_empty_eq card_eq_0_iff empty_iff node_range_set.elims)

lemma "node_range_set G C = node_range G ` C"
	by (cases G, auto)


lemma card_clq_sp: "finite C \<Longrightarrow> card (node_range_set (graph E V) C) = card C"
proof (induction C arbitrary: E V rule: finite_induct)
  case empty
  thus ?case by simp
next
  case (insert x F)
  thm insert.prems
  thm insert.hyps
  thm insert.IH

  hence "node_range_set (graph E V) (insert x F) = insert (node_range (graph E V) x) (node_range_set (graph E V) F)"
  	by auto
  hence eq: "card (node_range_set (graph E V) (insert x F)) = card (insert (node_range (graph E V) x) (node_range_set (graph E V) F))"
  	by simp

  then consider (new) "x \<notin> F"
  	| (old) "x \<in> F"
  	by arith
  thus ?case
  proof cases
  	case new

  	hence "card (node_range_set (graph E V) (insert x F)) = card (insert (node_range (graph E V) x) (node_range_set (graph E V) F))"
  		using eq by simp
  	also have "... = Suc (card (node_range_set (graph E V) F))"
  		apply (rule card_insert_new)
  		using insert node_range_insert new by auto
  	also have "... = Suc (card F)"
  		using insert.prems insert.IH by auto
  	also have "... = card (insert x F)"
  		apply (rule card_insert_new[symmetric])
  		using insert node_range_insert new by auto

  	finally show ?thesis .
  next
  	case old

  	hence "card (node_range_set (graph E V) (insert x F)) = card (insert (node_range (graph E V) x) (node_range_set (graph E V) F))"
  		using eq by simp
  	also have "... = card (node_range_set (graph E V) F)"
  		apply (rule card_insert_old)
  		using old insert.hyps by auto
  	also have "... = card F"
  		using insert.prems insert.IH by auto
  	also have "... = card (insert x F)"
  		apply (rule card_insert_old[symmetric])
  		using old insert.hyps by auto

  	finally show ?thesis .
  qed
qed


lemma reduction_forward: "x \<in> clique \<Longrightarrow> clq_sp x \<in> set_packing_pset"
proof -
	assume a: "x \<in> clique"
	then obtain E V k where x: "x = (E, V, k)"
		unfolding clique_def by blast

	hence "(E, V, k) \<in> {(E, V, k). \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}"
		using clique_def a by metis

	then obtain C where g: "ugraph_nodes E V" and c: "C \<subseteq> V" and k: "card C \<ge> k" and clq: "is_clique E C"
		by blast

	have "card (node_range_set (graph E V) C) = card C"
		apply (rule card_clq_sp)
		using g c finite_subset
		unfolding ugraph_nodes_def
		by auto

	hence "card (node_range_set (graph E V) C) \<ge> k"
		using k by arith

	moreover have "set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
		unfolding set_packing_def
		using clq is_clique_def apply auto
		using kgraph_def apply fastforce
		by (metis doubleton_eq_iff)+

	moreover have "node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
		using c by auto

	moreover have "finite (node_range_univ (graph E V))"
		using node_range_univ_finite g
		by (metis ugraph_nodes_def)

	ultimately show "clq_sp x \<in> set_packing_pset"
		unfolding set_packing_pset_def 
		by (auto simp add: x) (use g in blast)
qed


lemma bin: "({}, {}, 1) \<notin> set_packing_pset"
	unfolding set_packing_pset_def by auto

lemma sp_clq: "set_packing (node_range_univ (graph E V)) subsets (kgraph V) \<Longrightarrow> \<exists>C. is_clique E C \<and> C \<subseteq> V \<and> node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
	unfolding set_packing_def is_clique_def kgraph_def by auto


term clique
term set_packing_pset

thm node_range_set_subset (* subset iff *)
thm card_clq_sp (* card iff *)

lemma clq_imp_sp: "is_clique E C \<Longrightarrow> set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
	unfolding is_clique_def set_packing_def kgraph_def by auto (metis doubleton_eq_iff)+

lemma clq_imp_sp': "C \<subseteq> V \<Longrightarrow> \<not>is_clique E C \<Longrightarrow> \<not>set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
proof -
	assume a1: "C \<subseteq> V"
	assume "\<not>is_clique E C"
	hence a2: "\<exists>u \<in> C. \<exists>v \<in> C. v \<noteq> u \<and> {u, v} \<notin> E"
		unfolding is_clique_def by blast

	then obtain u v where u: "u \<in> C" and v: "v \<in> C" and neq: "u \<noteq> v" and nedge: "{u, v} \<notin> E"
		by blast

	hence "{u, v} \<in> {{v, u} | u. u \<in> V \<and> {u, v} \<notin> E}"
		using a1 by blast
	hence nrv: "{u, v} \<in> snd (node_range (graph E V) v)"
		by simp

	hence "{u, v} \<in> {{u, v} | v. v \<in> V \<and> {v, u} \<notin> E}"
		using a1 nedge neq v by (smt CollectI in_mono insert_commute)
	hence nru: "{u, v} \<in> snd (node_range (graph E V) u)"
		by simp

	hence "node_range (graph E V) v \<noteq> node_range (graph E V) u"
		using neq by auto

	moreover have "{u, v} \<in> snd (node_range (graph E V) v) \<inter> snd (node_range (graph E V) u)"
		using nrv nru by blast

	ultimately have "\<exists>s \<in> node_range_set (graph E V) C. \<exists>t \<in> node_range_set (graph E V) C. s \<noteq> t \<and> snd s \<inter> snd t \<noteq> {}"
		using u v by (smt empty_iff mem_Collect_eq node_range_set.simps)

	thus "\<not>set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
		unfolding set_packing_def by meson
qed

lemma clq_iff_sp: "C \<subseteq> V \<Longrightarrow> is_clique E C \<longleftrightarrow> set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
	using clq_imp_sp clq_imp_sp' by blast

lemma node_range_univ_elem: "e \<in> node_range_univ (graph E V) \<Longrightarrow> \<exists>v \<in> V. e = node_range (graph E V) v"
	by auto

lemma node_range_set_insert: "insert (node_range (graph E V) v) (node_range_set (graph E V) C) = node_range_set (graph E V) (insert v C)"
	by auto

lemma "fst (node_range (graph E V) v) = ({v})"
	by auto

lemma h1: "node_range_univ (graph E V) = node_range_set (graph E V) V"
	by auto

lemma subset_ex: "finite s \<Longrightarrow> s \<subseteq> node_range_univ (graph E V) \<Longrightarrow> \<exists>C. s = node_range_set (graph E V) C"
proof (induction "card s" arbitrary: s E V)
  case 0
  thus ?case by simp
next
  case (Suc x)

  then obtain s' e where s': "card s' = x" and s: "s = insert (node_range (graph E V) e) s'"
  	by (metis node_range_univ_elem card_Suc_eq insert_subset)

  have "\<exists>C. s' = node_range_set (graph E V) C"
  	apply (rule Suc.hyps)
  	using Suc.prems s s' by auto

  then obtain C where C: "s' = node_range_set (graph E V) C"
  	by blast

  hence "s = node_range_set (graph E V) (insert e C)"
  	using node_range_set_insert s by meson

  thus ?case by blast
qed
	

lemma reduction_reverse: "clq_sp x \<in> set_packing_pset \<Longrightarrow> x \<in> clique"
proof -
	assume a: "clq_sp x \<in> set_packing_pset"
	then obtain E V k where "clq_sp x \<in> set_packing_pset" and x: "x = (E, V, k)"
										and clq_sp: "clq_sp x = (if ugraph_nodes E V then (node_range_univ (graph E V), kgraph V, k) else ({}, {}, 1))"
		by (meson clq_sp.elims)

	then consider (graph) "ugraph_nodes E V"
		| (ngraph) "\<not>ugraph_nodes E V"
		by blast
	thus ?thesis
	proof cases
		case graph

		hence sp_set: "(node_range_univ (graph E V), kgraph V, k) \<in> {(c, e, k). \<exists>subsets. finite c \<and> subsets \<subseteq> c \<and> card subsets \<ge> k \<and> set_packing c subsets e}"
			using set_packing_pset_def a x clq_sp by metis

		then obtain subsets where nru_fin: "finite (node_range_univ (graph E V))" and subset_sub: "subsets \<subseteq> node_range_univ (graph E V)"
												and subset_card: "card subsets \<ge> k" and subset_sp: "set_packing (node_range_univ (graph E V)) subsets (kgraph V)"
			by blast

		have "\<exists>C. subsets = node_range_set (graph E V) C"
			apply (rule subset_ex)
			using finite_subset nru_fin subset_sub by auto

		then obtain C where subset_nrs: "subsets = node_range_set (graph E V) C"
			by blast

		thm node_range_set_subset
		hence f1: "node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
			using node_range_set_subset subset_sub by meson

		have "finite C"
			using subset_sub graph finite_subset ugraph_nodes_def f1 node_range_set_subset by metis
		thm card_clq_sp
		hence "card (node_range_set (graph E V) C) = card C"
			using card_clq_sp by blast
		hence f2: "card C \<ge> k"
			using subset_card subset_nrs by simp

		have f3: "is_clique E C"
			using clq_iff_sp subset_sp f1 node_range_set_subset subset_nrs by metis

		have checkpoint: "(E, V, k) \<in> {(E, V, k). ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}"
			using graph subset_sub f1 f2 f3 by auto

		thus ?thesis unfolding clique_def using x by blast
	next
		case ngraph
		thus ?thesis using bin clq_sp a by auto
	qed
qed


lemma "is_reduction clq_sp clique set_packing_pset"
	unfolding is_reduction_def
	using reduction_forward reduction_reverse
	by blast


end