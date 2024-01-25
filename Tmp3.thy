theory Tmp3
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

(*
lemma "\<lbrakk> ugraph_nodes E V; graph E' V' = *graph E V \<rbrakk> \<Longrightarrow> card E' \<le> card {{u, v} | u v. u \<in> V \<and> v \<in> V}"
	unfolding ugraph_nodes_def ugraph_def
	using invg_finite_edge apply auto
*)


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

lemma "card {{v, u} | u. u \<in> V} = card V"
proof (induction V)


lemma "finite {{v, u} | u. u \<in> V} \<Longrightarrow> finite V"
proof (induction "{{v, u} | u. u \<in> V}" arbitrary: v V rule: finite_induct)
  case empty
  thus ?case by simp
next
  case (insert x F)
  hence "F = {{v, u} | u. u \<in> V} - {x}"
  	by (metis Diff_insert_absorb)

  then obtain u' where x: "x = {v, u'}"
  	using insert by (smt insertCI mem_Collect_eq)

(*
  then obtain V' where v: "insert u' V' = V"
  	by (smt doubleton_eq_iff insert.hyps(4) insertCI insert_absorb mem_Collect_eq)
*)
  then obtain V' where "F = {{v, u} | u. u \<in> V'}"
  	

  then consider (new) "u' \<notin> V'"
  	| (old) "u' \<in> V'"
  	by arith
  thus ?case
  proof cases
  	case new
  	hence "x \<notin> F"
  		using insert.hyps by simp

  	hence "F = insert x F - {x}"
  		by simp
		moreover have "insert x F = {{v, u} | u. u \<in> insert u' V'}"
			using insert v by simp
		ultimately have "F = {{v, u} | u. u \<in> insert u' V'} - {x}"
			by simp
		hence "F = {{v, u} | u. u \<in> insert u' V'} - {{v, u'}}"
			using x by simp
		hence "F = {{v, u} | u. u \<in> V'}"
			
			
			

  	then show ?thesis sorry
  next
  	case old

		hence "insert x F = {{v, u} | u. u \<in> insert u' V'}"
			using insert v by simp

  	thus ?thesis
  		using insert.hyps(2) old by blast
  qed

(*
  have "finite V'"
  	apply (rule insert.hyps(3)[where ?v = v])
*)

  thus ?case 

  then show ?case sorry
qed

lemma node_range_univ_inv: "\<Union>(snd ` node_range_univ (graph E V)) \<inter> E = {}"
	by (auto simp add: insert_commute)

lemma "ugraph_nodes E V \<Longrightarrow> graph E' V = *graph (\<Union>(node_range_univ (graph E V))) V \<Longrightarrow> E' = E"
	apply (auto simp add: ugraph_nodes_def ugraph_def insert_commute)
	 apply (smt (verit) CollectI insert_commute)
	oops


lemma "node_range (graph E V) v = node_range (graph E V) u \<Longrightarrow> v = u"
	

lemma "infinite V \<Longrightarrow> infinite (node_range_univ (graph E V))"
	apply auto 

lemma "finite {f x | x. x \<in> A} \<Longrightarrow> finite A"
proof (induction "{f x | x. x \<in> A}" arbitrary: f A rule: finite_induct)
  case empty
  thus ?case by simp
next
  case (insert x F)
  oops
  then obtain f_inv where "f (f_inv x) = x"
  	by (metis Setcompr_eq_image imageE insert_iff)

(*
  then obtain A' where "A' = A - {f_inv x}"
  	by blast
*)

  hence "F = {f x | x. x \<in> A} - {x}"
  	by (metis Diff_insert_absorb insert.hyps)

  then obtain A' where "F = {f x | x. x \<in> A'}"
  	
  	
  then show ?case sorry
qed

lemma "finite (node_range_set (graph E V) C) \<Longrightarrow> finite C"
proof (induction "node_range_set (graph E V) C" arbitrary: E V C rule: finite_induct)
  case empty
  thus ?case by simp
next
  case (insert x NRS)
  thm insert.hyps

  then obtain v where "NRS = node_range_set (graph E V) (insert v C)"

  hence "insert x NRS = node_range_set (graph E V) C"

  then show ?case sorry
qed

lemma node_range_inj: "\<lbrakk> ugraph_nodes E V; u \<in> V; v \<in> V \<rbrakk> \<Longrightarrow> node_range (graph E V) u = node_range (graph E V) v \<Longrightarrow> u = v"
	by auto

(*
lemma "\<lbrakk> ugraph_nodes E V; C \<subseteq> V; D \<subseteq> V \<rbrakk> \<Longrightarrow> node_range_set (graph E V) C = node_range_set (graph E V) D \<Longrightarrow> C = D"
	apply (auto)
*)

lemma node_range_set_card: "card (node_range_set (graph E V) C) = card C"
	oops

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

lemma "finite C \<Longrightarrow> ugraph_nodes E V \<Longrightarrow> C \<subseteq> V \<Longrightarrow> card (snd ` node_range_set (graph E V) C) = card C"
proof (induction C arbitrary: E V rule: finite_induct)
  case empty
  thus ?case
  	using node_range_set_0 by simp
next
  case (insert x F)
  thm insert.prems
  thm insert.hyps
  thm insert.IH

  hence "node_range_set (graph E V) (insert x F) = insert (node_range (graph E V) x) (node_range_set (graph E V) F)"
  	by auto
  hence "snd ` node_range_set (graph E V) (insert x F) = snd ` insert (node_range (graph E V) x) (node_range_set (graph E V) F)"
  	by simp
  hence eq: "card (snd ` node_range_set (graph E V) (insert x F)) = card (snd ` insert (node_range (graph E V) x) (node_range_set (graph E V) F))"
  	by simp

  then consider (new) "x \<notin> F"
  	| (old) "x \<in> F"
  	by arith
  thus ?case
  proof cases
  	case new

  	hence "card (snd ` node_range_set (graph E V) (insert x F)) = card (snd ` insert (node_range (graph E V) x) (node_range_set (graph E V) F))"
  		using eq by simp
  	also have "... = Suc (card (snd ` node_range_set (graph E V) F))"
  		apply (rule card_insert_new)
  		using insert node_range_insert new by auto
  	also have "... = Suc (card F)"
  		using insert.prems insert.IH by auto
  	also have "... = card (insert x F)"
  		apply (rule card_insert_new[symmetric])
  		using insert node_range_insert new by auto
  	thus
  next
  	case old
  	then show ?thesis sorry
  qed
qed


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

value "node_range_set (graph {} {Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}) {Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}"

lemma "finite C \<Longrightarrow> subsets = node_range_set (graph E V) C \<Longrightarrow> card subsets = card C"
	apply (induction C arbitrary: subsets E V rule: finite_induct)
	 apply auto


lemma "\<lbrakk> finite C; ugraph_nodes E V; C \<subseteq> V \<rbrakk> \<Longrightarrow> node_range_univ (*graph E C) \<subseteq> node_range_univ (*graph E V)"
	apply (induction C arbitrary: E V rule: finite_induct)
	apply auto

proof -
	assume g: "ugraph_nodes E V"
	assume c: "C \<subseteq> V"

	consider (nil) "V = {}"
		| (notnil) "V \<noteq> {}"
		by arith
	thus "node_range_univ (*graph E C) \<subseteq> node_range_univ (*graph E V)"
	proof cases
		case nil
		thus ?thesis using c by simp
	next
		case notnil
		then obtain v where v: "v \<in> V"
			by blast
	
		hence "node_range (*graph E C) v \<subseteq> node_range (*graph E V) v"
			using g c by (rule node_range_inv_subset)

		hence "{node_range (*graph E C) v | v. v \<in> V} \<subseteq> {node_range (*graph E V) v | v. v \<in> V}"
			


		thus ?thesis
	qed


	show "node_range_univ (*graph E C) \<subseteq> node_range_univ (*graph E V)"



lemma "set_packing_pset = {(c, e, k). \<exists>subsets. finite c \<and> subsets \<subseteq> c \<and> card subsets \<ge> k \<and> set_packing c subsets e}"


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
(*
		apply blast
		by (smt (verit) insertCI insert_absorb insert_iff is_clique_def)+
*)
	moreover have "node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
		using c by auto

	moreover have "finite (node_range_univ (graph E V))"
		using node_range_univ_finite g
		by (metis ugraph_nodes_def)

	ultimately show "clq_sp x \<in> set_packing_pset"
		unfolding set_packing_pset_def using x apply auto using g apply blast done
qed

(*
lemma "subsets \<subseteq> node_range_univ (graph E V) \<Longrightarrow> set_packing (node_range_univ (graph E V)) subsets \<Longrightarrow> ugraph_nodes E V" quickcheck
*)

lemma bin: "({}, {}, 1) \<notin> set_packing_pset"
	unfolding set_packing_pset_def by auto

lemma sp_clq: "set_packing (node_range_univ (graph E V)) subsets (kgraph V) \<Longrightarrow> \<exists>C. is_clique E C \<and> C \<subseteq> V \<and> node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
	unfolding set_packing_def is_clique_def kgraph_def by auto


term clique
term set_packing_pset

thm node_range_set_subset (* subset iff *)
thm card_clq_sp (* card iff *)

lemma clq_imp_sp: "is_clique E C \<Longrightarrow> set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
	unfolding is_clique_def set_packing_def kgraph_def apply auto
	by (metis doubleton_eq_iff)+

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

lemma "\<exists>subsets. finite (node_range_univ (graph E V)) \<and> subsets \<subseteq> node_range_univ (graph E V) \<and> card subsets \<ge> k \<and> set_packing (node_range_univ (graph E V)) subsets (kgraph V)
				\<Longrightarrow> \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C"
	using node_range_set_subset card_clq_sp clq_iff_sp 


lemma "subsets \<subseteq> node_range_univ (graph E V) \<Longrightarrow> \<exists>C. C \<subseteq> V \<longrightarrow> subsets = node_range_set (graph E V) C"
	using node_range_set_subset 
	

lemma "x \<notin> clique \<Longrightarrow> clq_sp x \<notin> set_packing_pset"
proof -
	assume a: "x \<notin> clique"
	then obtain E V k where x: "x = (E, V, k)"
		unfolding clique_def by blast

	hence "(E, V, k) \<notin> {(E, V, k). \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}"
		using clique_def a by metis

	hence c: "\<forall>C. \<not>ugraph_nodes E V \<or> \<not>C \<subseteq> V \<or> card C < k \<or> \<not>is_clique E C"
		by auto

	show "clq_sp x \<notin> set_packing_pset"
	proof (rule ccontr)
		assume "\<not> clq_sp x \<notin> set_packing_pset"
		hence f: "clq_sp x \<in> set_packing_pset"
			by simp

		consider (ngraph) "\<not>ugraph_nodes E V"
			| (graph) "ugraph_nodes E V"
			by arith
		thus "False"
		proof cases
			case ngraph
			thus "False" using bin f x by auto
		next
			case graph
			hence clq_sp_x: "clq_sp x = (node_range_univ (graph E V), kgraph V, k)"
				using x by simp

			hence expand: "(node_range_univ (graph E V), kgraph V, k) \<in> {(c, e, k). \<exists>subsets. finite c \<and> subsets \<subseteq> c \<and> card subsets \<ge> k \<and> set_packing c subsets e}"
				using f by (simp add: set_packing_pset_def)

(*
			then obtain subsets where fin: "finite (node_range_univ (graph E V))" and sub: "subsets \<subseteq> node_range_univ (graph E V)"
													and card: "card subsets \<ge> k" and sp: "set_packing (node_range_univ (graph E V)) subsets (kgraph V)"
				by blast
*)
			thm node_range_set_subset
			hence "\<exists>C. node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
				by auto

			thm card_clq_sp
			hence "\<exists>C. node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)
							\<and> finite C \<longrightarrow> card (node_range_set (graph E V) C) = card C"
				using card_clq_sp by blast

			thm clq_iff_sp
			hence "\<exists>C. node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)
							\<and> finite C \<longrightarrow> card (node_range_set (graph E V) C) = card C
							\<and> C \<subseteq> V \<longrightarrow> is_clique E C = set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
				using clq_iff_sp by metis

			then obtain C where c_sub: "node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
										and c_card: "card (node_range_set (graph E V) C) = card C"
										and c_clq_sp: "is_clique E C = set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
				by (metis card_clq_sp clq_iff_sp graph infinite_super node_range_set_subset ugraph_nodes_def)

			then obtain subsets where fin: "finite (node_range_univ (graph E V))" and sub: "subsets \<subseteq> node_range_univ (graph E V)"
													and card: "card subsets \<ge> k" and sp: "set_packing (node_range_univ (graph E V)) subsets (kgraph V)"
				using expand by blast

			hence "subsets = node_range_set (graph E V) C"


			define subsets where "subsets = node_range_set (graph E V) C"

			hence "subsets \<subseteq> node_range_univ (graph E V)"
				using c_sub by blast
			moreover have "card subsets \<ge> k"
				using c_card

			then show "False" sorry
		qed


		hence ""



	proof (elim allE)
		fix C
		consider (ngraph) "\<not>ugraph_nodes E V"
			| (graph) "ugraph_nodes E V"
			by arith
		thus ?thesis
		proof cases
			case ngraph
			thus ?thesis using bin x by simp
		next
			case graph

			then consider (nsubset) "\<not>C \<subseteq> V"
				| (ncard) "card C < k"
				| (nclq) "\<not>is_clique E C"
				using graph c by blast
			thus ?thesis
			proof cases
				case nsubset

				hence "\<not>node_range_set (graph E V) C \<subseteq> node_range_univ (graph E V)"
					using node_range_set_subset by meson

				hence "\<nexists>subsets. subsets \<subseteq> node_range_univ (graph E V)"
					by blast

				then show ?thesis sorry
			next
				case ncard

				hence "card (node_range_set (graph E V) C) \<le> k"
					
				then show ?thesis sorry
			next
				case nclq
				then show ?thesis sorry
			qed
		qed



lemma node_range_univ_elem: "e \<in> node_range_univ (graph E V) \<Longrightarrow> \<exists>v \<in> V. e = node_range (graph E V) v"
	by auto

lemma node_range_set_insert: "insert (node_range (graph E V) v) (node_range_set (graph E V) C) = node_range_set (graph E V) (insert v C)"
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

(*
		then obtain subsets C where subsets: "subsets = node_range_set (graph E V) C" and c_sub_v: "C \<subseteq> V"
													and card: "card subsets \<ge> k"
			by (smt card_mono case_prodD dual_order.trans mem_Collect_eq node_range_set_eq order_refl)
*)
			
(*
		then obtain subsets C where "subsets = node_range_set (graph E V) C" and c_sub_v: "C \<subseteq> V"
													and sp: "set_packing (node_range_univ (graph E V)) (node_range_set (graph E V) C) (kgraph V)"
													and "card (node_range_set (graph E V) C) \<ge> k"
			
			by (smt case_prodD clq_iff_sp mem_Collect_eq sp_clq)
*)
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