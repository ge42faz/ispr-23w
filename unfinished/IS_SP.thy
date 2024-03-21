theory IS_SP
	imports Main "../Reductions" "../Three_Sat_To_Set_Cover"
begin

definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
	where "disjoint s1 s2 = (\<forall>e1 \<in> s1. \<forall>e2 \<in> s2. e1 \<noteq> e2)"

definition elem_set :: "'a set \<Rightarrow> 'a set set"
	where "elem_set s = {{x} | x. x \<in> s}"

definition set_packing :: "'a set set \<Rightarrow> bool"
	where "set_packing subsets \<longleftrightarrow> (\<forall>s1 \<in> subsets. \<forall>s2 \<in> subsets. s1 = s2 \<or> s1 \<inter> s2 = {})"


value "fold (+) [] 0::nat"

(* builds the set of all edges {v, v_adj} \<in> E adjacent to v *)
definition node_range :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set set"
	where "node_range E v = {{v, v_adj} | v_adj. v \<noteq> v_adj \<and> {v, v_adj} \<in> E}"

definition adj_count :: "'a set set \<Rightarrow> 'a \<Rightarrow> nat"
	where "adj_count E v = card (node_range E v)"


(* builds the set of all edges {v, v_adj} \<in> E adjacent to v, \<forall>v \<in> \<Union>E *)
definition node_range_univ :: "'a set set \<Rightarrow> 'a set set set"
	where "node_range_univ E = {node_range E v | v. v \<in> \<Union>E}"

(* builds the set of all edges {v, v_adj} \<in> E adjacent to v, v \<in> subV \<subseteq> \<Union>E *)
definition node_range_set :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set set"
	where "node_range_set E subV = {node_range E v | v. v \<in> subV}"

lemma card_fin: "finite A \<Longrightarrow> x = card A \<Longrightarrow> x = card {e | e. e \<in> A}"
	by (induction x arbitrary: A) auto

lemma card_inf: "infinite A \<Longrightarrow> x = card A \<Longrightarrow> x = card {e | e. e \<in> A}"
	by auto

lemma card': "x = card A \<Longrightarrow> x = card {e | e. e \<in> A}"
	using card_fin card_inf by simp

lemma card_tuple:
	assumes "finite A"
	shows "card A = card {(e, f e) | e. e \<in> A}"
	using assms
proof (induction A)
  case empty
  thus ?case by simp
next
  case (insert x F)
  hence "{(e, f e) | e. e \<in> insert x F} = insert (x, f x) {(e, f e) | e. e \<in> F}"
  	by auto
  thus ?case
  	using insert by simp
qed

value "card {(e, (\<lambda>x. case x of Enum.finite_2.a\<^sub>1 \<Rightarrow> 0::nat | Enum.finite_2.a\<^sub>2 \<Rightarrow> 1) e) | e. e \<in> {Enum.finite_2.a\<^sub>1}}"

lemma ugraph_finite: "ugraph E \<Longrightarrow> finite E"
	unfolding ugraph_def using ugraph_vertex_set_finite
	by blast

lemma vertex_finite: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> finite subV"
	using finite_subset ugraph_vertex_set_finite by auto

lemma "finite E \<Longrightarrow> u \<in> \<Union>E \<Longrightarrow> v \<in> \<Union>E \<Longrightarrow> node_range E u = node_range E v \<Longrightarrow> u = v"
	apply (induction E arbitrary: u v rule: finite_induct)
	 apply auto


lemma nrs_card': "\<lbrakk> finite E; ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> card subV = card (node_range_set E subV)"
	unfolding node_range_set_def
proof (induction "card subV" arbitrary: subV E)
  case 0
  thus ?case using vertex_finite by fastforce
next
  case (Suc x)
  hence "card subV = card {v | v. v \<in> subV}"
  	by simp
  also have "... = card {node_range E v | v. v \<in> subV}"
  then show ?case 
qed



proof (induction E arbitrary: subV rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then consider (card2) "card x = 2"
  	| (invalid) "card x \<noteq> 2"
  	by arith
  thus ?case
  proof cases
  	case card2
  	then consider (old) "x \<in> F"
  		| (new) "x \<notin> F"
  		by arith
  	thus ?thesis
  	proof cases
  		case old
  		thus ?thesis
  			using insert.hyps(2) by blast
  	next
  		case new
			then obtain a b where "x = {a, b}"
				using card2 by (meson card_2_iff)

  		then show ?thesis sledgehammer
  	qed
  next
  	case invalid
  	thus ?thesis using insert.prems ugraph_def
  		by (meson insertCI)
  qed
qed

lemma nrs_card: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> card subV = card (node_range_set E subV)"
	using nrs_card' vertex_finite by metis
*)

lemma nr_sub: "ugraph E \<Longrightarrow> node_range E v \<subseteq> E"
	unfolding node_range_def
	by auto

lemma nrs_sub: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> \<Union>(node_range_set E subV) \<subseteq> E"
	unfolding node_range_def node_range_set_def
	by auto


lemma tmp: "\<not>(A \<subseteq> B) \<Longrightarrow> \<exists>x \<in> A. x \<notin> B"
	by blast

lemma tmp2: "\<lbrakk> ugraph E; e \<in> E \<rbrakk> \<Longrightarrow> (\<exists>u \<in> \<Union>E. \<exists>v \<in> \<Union>E. e = {u, v})"
	unfolding ugraph_def
	by (metis UnionI card_2_iff insert_iff)

lemma nru_sub: "ugraph E \<Longrightarrow> \<Union>(node_range_univ E) \<subseteq> E"
	unfolding node_range_def node_range_univ_def
	by auto

lemma nru_sup:
	assumes "ugraph E"
	shows "E \<subseteq> \<Union>(node_range_univ E)"
proof (rule ccontr)
	assume a: "\<not> E \<subseteq> \<Union>(node_range_univ E)"

	obtain u v where edge: "{u, v} \<in> E" and false: "{u, v} \<notin> \<Union>(node_range_univ E)"
		by (metis a assms tmp tmp2)

	from edge have "v \<in> \<Union>(node_range E u)"
		unfolding node_range_def using assms ugraph_def
		by (smt CollectI Union_iff card.empty card_insert_if empty_iff finite.emptyI insertCI insert_absorb2 n_not_Suc_n numeral_2_eq_2)

	hence "{u, v} \<in> \<Union>(node_range_univ E)"
		unfolding node_range_univ_def
		apply auto
		using assms edge node_range_def ugraph_def
		by (smt One_nat_def Suc_1 card_1_singleton_iff insert_absorb2 insert_commute mem_Collect_eq n_not_Suc_n)

	from this false show "False" by simp
qed

lemma nru_eq: "ugraph E \<Longrightarrow> \<Union>(node_range_univ E) = E"
	using nru_sub nru_sup by fast

lemma nrs_sub_nru: "subV \<subseteq> \<Union>E \<Longrightarrow> node_range_set E subV \<subseteq> node_range_univ E"
	unfolding node_range_univ_def node_range_set_def node_range_def
	by fastforce

lemma nru_nrs: "node_range_univ E = node_range_set E (\<Union>E)"
	unfolding node_range_univ_def node_range_set_def node_range_def
	by simp

(*
lemma nrs_fst: "fst ` node_range_set E subV = subV"
	unfolding node_range_set_def by force
*)

lemma nru_fin: "ugraph E \<Longrightarrow> finite (node_range_univ E)"
	using nru_eq ugraph_finite
	by (metis finite_UnionD)

(*
lemma nru_inf: "infinite E \<Longrightarrow> infinite (node_range_univ E)"
	
	by (metis finite_UnionD finite_imageI nrs_fst nru_nrs)
*)

(*
lemma "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> subV \<subseteq> \<Union>(\<Union>(node_range_set E subV))"
	unfolding node_range_set_def using nrs_sub
	apply auto

definition node_range_collapse :: "'a set set set \<Rightarrow> 'a set"
	where "node_range_collapse nrs = {v | v. \<forall>adjE \<in> nrs. \<forall>e \<in> adjE. v \<in> e}"

lemma "\<lbrakk> E \<noteq> {}; ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> subV \<subseteq> node_range_collapse (node_range_set E subV)"
	unfolding node_range_set_def node_range_collapse_def node_range_def
	apply auto
*)

lemma "is_independent_set E V \<Longrightarrow> set_packing (node_range_set E V)"
	unfolding is_independent_set_def set_packing_def node_range_set_def node_range_def disjoint_def
	by auto

lemma
	assumes "\<not>is_independent_set E V"
	shows "\<not>set_packing (node_range_set E V)"
	using assms
proof -
	have "\<exists>u \<in> V. \<exists>v \<in> V. {u, v} \<in> E"
		using assms is_independent_set_def by blast

	then obtain u v where u: "u \<in> V" and v: "v \<in> V" and uv: "{u, v} \<in> E"
		by blast

	have "node_range_set E V = {node_range E v | v. v \<in> V}"
		unfolding node_range_set_def by simp

	hence "node_range E u \<in> node_range_set E V" and "node_range E v \<in> node_range_set E V"
		using u v by blast+

	then consider (same) "u = v"
		| (diff) "u \<noteq> v"
		by arith
	thus ?thesis
	proof cases
		case same
		then show ?thesis 
	next
		case diff
		then show ?thesis sorry
	qed




lemma "\<not>is_independent_set E V \<Longrightarrow> \<not>set_packing (node_range_set E V)"
	unfolding is_independent_set_def set_packing_def node_range_set_def node_range_def disjoint_def
	apply auto

lemma "set_packing (node_range_set E V) \<Longrightarrow> is_independent_set E V"
	unfolding is_independent_set_def set_packing_def node_range_set_def node_range_def disjoint_def
	apply auto

	value "node_range {{Enum.finite_3.a\<^sub>1}} Enum.finite_3.a\<^sub>1"
	value "is_independent_set {{Enum.finite_3.a\<^sub>1}} {Enum.finite_3.a\<^sub>1}"
	value "node_range_set {{Enum.finite_3.a\<^sub>1}} {Enum.finite_3.a\<^sub>1}"
	value "set_packing (node_range_set {{Enum.finite_3.a\<^sub>1}} {Enum.finite_3.a\<^sub>1})"

lemma hi: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> is_independent_set E subV \<Longrightarrow>
				 (\<forall>s1 \<in> (node_range_set E subV). \<forall>s2 \<in> (node_range_set E subV). s1 = s2 \<or> s1 \<inter> s2 = {})"
	unfolding is_independent_set_def node_range_set_def node_range_def disjoint_def
	by auto

lemma "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> \<not>is_independent_set E subV \<Longrightarrow>
				\<not>(\<forall>s1 \<in> (node_range_set E subV). \<forall>s2 \<in> (node_range_set E subV) - {s1}. s1 \<inter> s2 = {})"
	unfolding is_independent_set_def node_range_set_def node_range_def disjoint_def
	apply auto

	value "is_independent_set {{Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}} {Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}"
	value "\<forall>s1 \<in> (node_range_set {{Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}} {Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}). \<forall>s2 \<in> (node_range_set {{Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}} {Enum.finite_2.a\<^sub>1, Enum.finite_2.a\<^sub>2}). s1 = s2 \<or> s1 \<inter> s2 = {}"

lemma hi': "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> \<forall>s1 \<in> (node_range_set E subV). \<forall>s2 \<in> (node_range_set E subV). s1 = s2 \<or> s1 \<inter> s2 = {}
							\<Longrightarrow> is_independent_set E subV"
	unfolding is_independent_set_def node_range_set_def node_range_def disjoint_def ugraph_def
	apply auto
	oops
	by (metis Suc_n_not_n card.empty card_insert_if doubleton_eq_iff empty_not_insert finite.emptyI insert_absorb insert_absorb2 numeral_2_eq_2)

lemma is_sp: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> is_independent_set E subV \<Longrightarrow> set_packing (node_range_univ E) (node_range_set E subV)"
	unfolding is_independent_set_def set_packing_def node_range_univ_def
	by (auto simp add: hi nru_eq disjoint_def node_range_set_def node_range_def)

lemma sp_is: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> set_packing (node_range_univ E) (node_range_set E subV) \<Longrightarrow> is_independent_set E subV"
	unfolding is_independent_set_def set_packing_def node_range_univ_def ugraph_def
	apply (auto simp add: hi' nru_eq disjoint_def node_range_set_def node_range_def)
	by (smt (verit) card.empty card_insert_if empty_iff finite.emptyI insert_absorb insert_commute n_not_Suc_n numeral_2_eq_2 singletonI)


definition set_packing_pset :: "(('a \<times> 'b set) set \<times> nat) set"
	where "set_packing_pset = {(c, n). \<exists>subsets. finite c \<and> subsets \<subseteq> c \<and> card subsets \<ge> n \<and> set_packing c subsets}"

term independent_set

fun is_sp where "is_sp (E, k) = (node_range_univ E, k)"

definition "to_ugraph c = \<Union>(snd ` c)"

(*
lemma "ugraph E \<Longrightarrow> to_ugraph (node_range_univ E) = E"
	unfolding to_ugraph_def
	sorry

lemma "ugraph (to_ugraph c) \<Longrightarrow> node_range_univ (to_ugraph c) = c"
	unfolding to_ugraph_def 
*)

lemma "x \<in> independent_set \<Longrightarrow> is_sp x \<in> set_packing_pset"
proof -
	assume a: "x \<in> independent_set"
	then obtain E k where x: "x = (E, k)"
		unfolding independent_set_def by blast

	hence "\<exists>V. ugraph E \<and> V \<subseteq> \<Union>E \<and> card V \<ge> k \<and> is_independent_set E V"
		using a independent_set_def
		by (smt (verit) Pair_inject case_prodE mem_Collect_eq)

	then obtain V where e: "ugraph E" and v: "V \<subseteq> \<Union>E" and k: "k \<le> card V" and is_ev: "is_independent_set E V"
		by blast

	hence "\<forall>u \<in> V. \<forall>v \<in> V. {u, v} \<notin> E"
		unfolding is_independent_set_def using is_ev by simp

	have "set_packing (node_range_univ E) (node_range_set E V)"
		using e v is_ev by (rule is_sp)

	moreover have "node_range_set E V \<subseteq> node_range_univ E"
		using nrs_sub_nru v by fast

	moreover have "card (node_range_set E V) \<ge> k"
		using e v nrs_card k by metis

	moreover have "finite (node_range_univ E)"
		by (smt (verit) card_eq_0_iff e empty_iff node_range_univ_def not_finite_existsD nrs_card' nru_nrs ugraph_vertex_set_finite)

	ultimately have "x \<in> {(E, k). finite (node_range_univ E) \<and> node_range_set E V \<subseteq> node_range_univ E \<and> card (node_range_set E V) \<ge> k \<and> set_packing (node_range_univ E) (node_range_set E V)}"
		using x e 
		by (smt (verit, ccfv_SIG) card_eq_0_iff case_prodI empty_iff mem_Collect_eq node_range_univ_def not_finite_existsD nrs_card' nru_nrs ugraph_vertex_set_finite)

	hence "is_sp x \<in> set_packing_pset"
		unfolding set_packing_pset_def using x by auto

	thus ?thesis .
qed

lemma "x \<notin> independent_set \<Longrightarrow> is_sp x \<notin> set_packing_pset"
proof -
	assume a: "x \<notin> independent_set"
	then obtain E k where x: "x = (E, k)"
		unfolding independent_set_def by blast

	hence "\<forall>V. \<not>(ugraph E \<and> V \<subseteq> \<Union>E \<and> card V \<ge> k \<and> is_independent_set E V)"
		using a independent_set_def by blast

	hence "\<forall>V. \<not>ugraph E \<or> \<not>(V \<subseteq> \<Union>E) \<or> card V < k \<or> \<not>is_independent_set E V"
		by fastforce

	thus ?thesis
	proof (elim allE disjE)
		assume "\<not>ugraph E"
		then consider (inf) "infinite E"
			| (card) "\<exists>e \<in> E. card e \<noteq> 2"
			unfolding ugraph_def by blast
		thus ?thesis
		proof cases
			case inf
			thus ?thesis
				unfolding set_packing_pset_def using nru_inf x
				by auto
		next
			case card
			then show ?thesis sorry
		qed
	next
		fix v
		assume "\<not> v \<subseteq> \<Union> E"
		thus ?thesis
			unfolding set_packing_pset_def using x 


lemma "is_sp x \<in> set_packing_pset \<Longrightarrow> x \<in> independent_set"
proof -
	assume a: "is_sp x \<in> set_packing_pset"
	then obtain c n where x: "is_sp x = (c, n)"
		unfolding set_packing_pset_def by blast

	hence "\<exists>subsets. subsets \<subseteq> c \<and> card subsets \<ge> n \<and> set_packing c subsets"
		using a set_packing_pset_def
		by (smt (verit) Pair_inject case_prodE mem_Collect_eq)

	then obtain subsets where subs: "subsets \<subseteq> c" and n: "n \<le> card subsets" and sp: "set_packing c subsets"
		by blast

	hence "\<forall>s1 \<in> subsets. \<forall>s2 \<in> subsets. s1 \<noteq> s2 \<longrightarrow> disjoint (snd s1) (snd s2)"
		unfolding set_packing_def using sp by simp

	obtain E k where "x = (E, k)" and "c = node_range_univ E"
		using x by (metis fst_conv is_sp.elims)

	have "is_independent_set E (fst ` subsets)"
		apply (rule sp_is)
		oops
			apply (metis \<open>x = (E, k)\<close> fst_conv image_mono is_sp.simps nrs_fst nru_nrs subs x)
		apply (smt (verit, best) \<open>\<forall>s1\<in>subsets. \<forall>s2\<in>subsets. s1 \<noteq> s2 \<longrightarrow> disjoint (snd s1) (snd s2)\<close> \<open>x = (E, k)\<close> fst_conv image_iff is_sp.simps mem_Collect_eq node_range_set_def nru_nrs set_packing_def subs subset_eq x)
		




(*
lemma "is_reduction is_sp independent_set set_packing_pset"
	unfolding is_reduction_def independent_set_def set_packing_pset_def
	unfolding is_independent_set_def set_packing_def node_range_univ_def node_range_def disjoint_def ugraph_def
	apply auto
			 apply (metis finite_UnionD nru_eq ugraph_def)
*)
	



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