theory IS_SP_alt
	imports Main "../Reductions" "../Three_Sat_To_Set_Cover"
begin

definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
	where "disjoint s1 s2 = (\<forall>e1 \<in> s1. \<forall>e2 \<in> s2. e1 \<noteq> e2)"

definition elem_set :: "'a set \<Rightarrow> 'a set set"
	where "elem_set s = {{x} | x. x \<in> s}"

definition set_packing :: "('a * 'a set) set \<Rightarrow> bool"
	where "set_packing subsets \<longleftrightarrow> (\<forall>s1 \<in> subsets. \<forall>s2 \<in> subsets. s1 = s2 \<or> snd s1 \<inter> snd s2 = {})"

(* {{0, 1, 2} {2, 3} {5, 7}} *)

datatype 'a Node = Node "'a set set"

value "fold (+) [] 0::nat"

(* builds the set of all edges {v, v_adj} \<in> E adjacent to v *)
definition node_range :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set set"
	where "node_range E v = {{v, v_adj} | v_adj. v_adj \<noteq> v \<and> {v, v_adj} \<in> E}"

definition adj_count :: "'a set set \<Rightarrow> 'a \<Rightarrow> nat"
	where "adj_count E v = card (node_range E v)"


(* builds the set of all edges {v, v_adj} \<in> E adjacent to v, \<forall>v \<in> \<Union>E *)
definition node_range_univ :: "'a set set \<Rightarrow> ('a set * 'a set set) set"
	where "node_range_univ E = {({v}, node_range E v) | v. v \<in> \<Union>E}"

(* builds the set of all edges {v, v_adj} \<in> E adjacent to v, v \<in> subV \<subseteq> \<Union>E *)
definition node_range_set :: "'a set set \<Rightarrow> 'a set \<Rightarrow> ('a set * 'a set set) set"
	where "node_range_set E subV = {({v}, node_range E v) | v. v \<in> subV}"

lemma card_fin: "finite A \<Longrightarrow> x = card A \<Longrightarrow> x = card {e | e. e \<in> A}"
	by (induction x arbitrary: A) auto

lemma card_inf: "infinite A \<Longrightarrow> x = card A \<Longrightarrow> x = card {e | e. e \<in> A}"
	by auto

lemma card': "x = card A \<Longrightarrow> x = card {e | e. e \<in> A}"
	using card_fin card_inf by simp

lemma card_tuple:
	assumes "finite A"
	shows "card A = card {({e}, f e) | e. e \<in> A}"
	using assms
proof (induction A)
  case empty
  thus ?case by simp
next
  case (insert x F)
  hence "{({e}, f e) | e. e \<in> insert x F} = insert ({x}, f x) {({e}, f e) | e. e \<in> F}"
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

lemma nrs_card': "\<lbrakk> finite subV \<rbrakk> \<Longrightarrow> card subV = card (node_range_set E subV)"
	unfolding node_range_set_def using card_tuple by blast

lemma nrs_card: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> card subV = card (node_range_set E subV)"
	using nrs_card' vertex_finite by metis

value "card (snd ` {(0::nat, {1::nat}), (1, {2}), (2, {3})})"

lemma nr_card: "\<forall>e \<in> node_range E v. card e = 2"
	unfolding node_range_def by auto

lemma nr_sub: "node_range E v \<subseteq> E"
	unfolding node_range_def
	by auto

lemma nrs_sub: "\<Union>(snd ` node_range_set E subV) \<subseteq> E"
	unfolding node_range_def node_range_set_def
	by auto


lemma tmp: "\<not>(A \<subseteq> B) \<Longrightarrow> \<exists>x \<in> A. x \<notin> B"
	by blast

lemma tmp2: "\<lbrakk> ugraph E; e \<in> E \<rbrakk> \<Longrightarrow> (\<exists>u \<in> \<Union>E. \<exists>v \<in> \<Union>E. e = {u, v})"
	unfolding ugraph_def
	by (metis UnionI card_2_iff insert_iff)

lemma nru_sub: "\<Union>(snd ` node_range_univ E) \<subseteq> E"
	unfolding node_range_def node_range_univ_def
	by auto

lemma nru_sup:
	assumes "ugraph E"
	shows "E \<subseteq> \<Union>(snd ` node_range_univ E)"
proof (rule ccontr)
	assume a: "\<not> E \<subseteq> \<Union>(snd ` node_range_univ E)"

	obtain u v where edge: "{u, v} \<in> E" and false: "{u, v} \<notin> \<Union>(snd ` node_range_univ E)"
		by (metis a assms tmp tmp2)

	from edge have "v \<in> \<Union>(node_range E u)"
		unfolding node_range_def ugraph_def using assms
		by (smt (verit, best) card.empty card_insert_if empty_iff finite.emptyI finite_insert insert_iff mem_Collect_eq mem_simps(9) n_not_Suc_n numeral_2_eq_2 ugraph_def)

	hence "{u, v} \<in> \<Union>(snd ` node_range_univ E)"
		unfolding node_range_univ_def
		apply auto
		by (smt (verit) assms card.empty card_insert_if edge finite.emptyI insertCI insert_absorb mem_Collect_eq n_not_Suc_n node_range_def numeral_2_eq_2 ugraph_def)

	from this false show "False" by simp
qed

lemma "\<forall>e \<in> node_range E v. v \<in> e"
	unfolding node_range_def by blast

lemma "{} \<notin> E \<Longrightarrow> finite E \<Longrightarrow> E \<subseteq> \<Union>{node_range E v | v. v \<in> \<Union>E}"
	unfolding node_range_def
	apply auto

lemma
	assumes "E \<noteq> {{}}"
	shows "E \<subseteq> \<Union>(snd ` node_range_univ E)"
proof (rule ccontr)
	assume a: "\<not> E \<subseteq> \<Union>(snd ` node_range_univ E)"

	obtain u v where edge: "{u, v} \<in> E" and false: "{u, v} \<notin> \<Union>(snd ` node_range_univ E)"
		


lemma nru_eq: "ugraph E \<Longrightarrow> \<Union>(snd ` node_range_univ E) = E"
	using nru_sub nru_sup by fastforce

lemma nrs_sub_nru: "subV \<subseteq> \<Union>E \<longleftrightarrow> node_range_set E subV \<subseteq> node_range_univ E"
	unfolding node_range_univ_def node_range_set_def node_range_def
	by fastforce

lemma aux: "inj f \<Longrightarrow> A \<subseteq> B \<longleftrightarrow> {f x | x. x \<in> A} \<subseteq> {f x | x. x \<in> B}"
	by (simp add: Setcompr_eq_image inj_image_subset_iff)

term "inj"

lemma "\<lbrakk> ugraph E; v \<in> \<Union>E; u \<in> \<Union>E \<rbrakk> \<Longrightarrow> node_range E v = node_range E u \<Longrightarrow> v = u"
	unfolding node_range_def ugraph_def
	apply auto

lemma "subV \<subseteq> \<Union>E \<Longrightarrow> snd ` node_range_set E subV \<subseteq> snd ` node_range_univ E"
	unfolding node_range_univ_def node_range_set_def node_range_def
	using image_iff by fastforce

lemma
	assumes "\<not>subV \<subseteq> \<Union>E" 
	shows "\<not>snd ` node_range_set E subV \<subseteq> snd ` node_range_univ E"
proof (rule ccontr)
	assume "\<not>\<not>snd ` node_range_set E subV \<subseteq> snd ` node_range_univ E"
	hence a: "snd ` node_range_set E subV \<subseteq> snd ` node_range_univ E"
		by simp

	hence "snd ` {({v}, node_range E v) | v. v \<in> subV} \<subseteq> snd ` {({v}, node_range E v) | v. v \<in> \<Union>E}"
		unfolding node_range_set_def node_range_univ_def by simp

	hence "{node_range E v | v. v \<in> subV} \<subseteq> {node_range E v | v. v \<in> \<Union>E}"
		unfolding image_def by simp

	hence "subV \<subseteq> \<Union>E"
		

	show False	

lemma "\<not>node_range_set E subV \<subseteq> node_range_univ E \<Longrightarrow> \<not>snd ` node_range_set E subV \<subseteq> snd ` node_range_univ E"
	

lemma nru_nrs: "node_range_univ E = node_range_set E (\<Union>E)"
	unfolding node_range_univ_def node_range_set_def node_range_def
	by simp

lemma nrs_fst: "\<Union>(fst ` node_range_set E subV) = subV"
	unfolding node_range_set_def by force

lemma nru_fin: "ugraph E \<Longrightarrow> finite (node_range_univ E)"
	using nru_eq ugraph_finite
	by (smt (verit) card_eq_0_iff empty_iff node_range_univ_def not_finite_existsD nrs_card nru_nrs tmp ugraph_vertex_set_finite)


(*
lemma nru_inf: "infinite E \<Longrightarrow> infinite (node_range_univ E)"
	by (metis finite_UnionD finite_imageI nrs_fst nru_nrs)
*)

definition nru_ugraph :: "('a set * 'a set set) set \<Rightarrow> 'a set set"
	where "nru_ugraph E = Set.filter (\<lambda>s. card s = 2) (\<Union>(snd ` E))"

definition collgraph :: "('a set * 'a set set) set \<Rightarrow> 'a set set set"
	where "collgraph coll = {{u, v} | u s v t. (u, s) \<in> coll \<and> (v, t) \<in> coll \<and> s \<noteq> t \<and> s \<inter> t \<noteq> {}}"

definition uniq
	where "uniq coll \<longleftrightarrow> card coll = card (fst ` coll)"

definition set_packing_pset :: "(('a set * 'a set set) set * nat) set"
	where "set_packing_pset = {(c, n). \<exists>subsets. ugraph (collgraph c) \<and> uniq c
					 \<and> subsets \<subseteq> c \<and> card subsets \<ge> n \<and> set_packing subsets}"

lemma "finite c \<Longrightarrow> uniq c \<Longrightarrow> card c \<ge> card (collgraph c)"
	apply (induction c rule: finite_induct)
	 apply (auto simp add: uniq_def collgraph_def)


	

lemma "\<forall>e \<in> snd ` c. finite e \<Longrightarrow> finite c \<Longrightarrow> finite (collgraph c)"	

	apply (induction c rule: finite_induct)
	 apply auto


lemma
	assumes "finite c"
	shows "finite (collgraph c)"
	using assms unfolding collgraph_def
proof (induction c)
  case empty
  thus ?case by simp
next
  case (insert x F)
  then consider (same) "x \<in> F"
  	| (new) "x \<notin> F"
  	by arith
  thus ?case
  proof cases
  	case same
  	thus ?thesis
  		using insert.hyps(2) by blast
  next
  	case new
  	let ?c = "{{u, v} |u s v t. (u, s) \<in> F \<and> (v, t) \<in> F \<and> s \<noteq> t \<and> s \<inter> t \<noteq> {}}"
  	let ?step = "{{u, v} |u s v t. (u, s) \<in> insert x F \<and> (v, t) \<in> insert x F \<and> s \<noteq> t \<and> s \<inter> t \<noteq> {}}"
  	have "card ?step \<le> 1 + (card ?c) + (card ?c)"
  		


  then show ?case sorry
qed

lemma
	assumes "finite c" "uniq c"
	shows "card c \<ge> card (collgraph c)"
	using assms unfolding collgraph_def
proof (induction c)
  case empty
  thus ?case by simp
next
  case (insert x F)
  then consider (same) "x \<in> F"
  	| (new) "x \<notin> F"
  	by arith
  thus ?case
  proof cases
  	case same
  	thus ?thesis
  		using insert.hyps(2) by blast
  next
  	case new
  	let ?c = "{{(u, s), (v, t)} |u s v t. (u, s) \<in> F \<and> (v, t) \<in> F \<and> s \<noteq> t \<and> s \<inter> t \<noteq> {}}"
  	let ?step = "{{(u, s), (v, t)} |u s v t. (u, s) \<in> insert x F \<and> (v, t) \<in> insert x F \<and> s \<noteq> t \<and> s \<inter> t \<noteq> {}}"

  	have "?c \<subseteq> ?step"
  		by blast
  	have "finite ?c"
  	hence "card ?c \<le> card ?step"
  		

  	have "card (insert x F) = Suc (card F)"
  		using new insert.hyps(1) by simp
  	moreover have "card ?step \<ge> card ?c"
  		
  	then show ?thesis sorry
  qed

  obtain a b where "x = (a, b)"
  	by fastforce
  then show ?case sorry
qed



lemma "\<lbrakk> ugraph E; c = node_range_univ E \<rbrakk> \<Longrightarrow> ugraph (collgraph c)"
	unfolding collgraph_def ugraph_def node_range_univ_def node_range_def
	apply auto


	value "ugraph ({}::Enum.finite_1 set set)"
	value "node_range_univ ({}::Enum.finite_1 set set)"
	value "collgraph ({}::(Enum.finite_1 set \<times> Enum.finite_1 set set) set)"

	apply (induction E rule: finite_induct)
	
	unfolding collgraph_def

definition coll_to_nr
	where "coll_to_nr c = {(subset, nr) | subset nr. subset \<in> c \<and> (\<forall>s \<in> c. s \<noteq> subset \<and> (\<exists>e \<in> s. e \<in> subset \<longrightarrow> s \<in> nr))}"

lemma coll_nr_fst: "ugraph (fst ` coll_to_nr c)"
	unfolding ugraph_def coll_to_nr_def
	using not_finite_existsD by blast

lemma coll_nr_un: "\<Union>(snd ` coll_to_nr c) = fst ` coll_to_nr c"
	unfolding coll_to_nr_def by blast

lemma coll_nr_snd: "ugraph (\<Union>(snd ` coll_to_nr c))"
	using coll_nr_fst coll_nr_un by metis


lemma "set_packing c subsets \<Longrightarrow> nru_ugraph c"



value "nru_ugraph {(0::nat, {{0::nat, 1, 2}, {0, 2}}), (1, {{1, 0}, {1, 2}}), (2, {{2, 0}, {2, 1}})}"


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

lemma hi: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> is_independent_set E subV \<Longrightarrow>
				\<forall>s1 \<in> node_range_set E subV. \<forall>s2 \<in> node_range_set E subV. s1 = s2 \<or> snd s1 \<inter> snd s2 = {}"
	unfolding is_independent_set_def node_range_set_def node_range_def disjoint_def
	by auto

lemma nr_empty: "v \<notin> \<Union>E \<Longrightarrow> card (node_range E v) = 0"
	unfolding node_range_def
	using card_eq_0_iff by blast


lemma ugraph_nr_card:
	assumes "ugraph E" "v \<in> \<Union>E"
	shows "card (node_range E v) > 0"
proof (rule ccontr)
	assume "\<not>card (node_range E v) > 0"
	hence a: "card (node_range E v) = 0"
		by simp

	hence "card {{v, v_adj} | v_adj. v_adj \<noteq> v \<and> {v, v_adj} \<in> E} = 0"
		unfolding node_range_def using assms ugraph_finite by simp

	moreover have "finite (node_range E v)"
		by (meson assms(1) finite_subset nr_sub ugraph_finite)

	ultimately have "{{v, v_adj} | v_adj. v_adj \<noteq> v \<and> {v, v_adj} \<in> E} = {}"
		unfolding node_range_def by simp

	hence adj: "\<forall>v_adj. (v_adj = v) \<or> {v, v_adj} \<notin> E"
		by blast
	thus "False"
	proof (elim allE disjE)
		fix v_adj
		assume "v_adj = v"
		show False
			using adj assms tmp2 ugraph_def
			by (smt One_nat_def Suc_1 UnionE card.empty card.insert empty_iff finite.intros(1) insertE insert_absorb2 insert_commute n_not_Suc_n)
	next
		fix v_adj
		assume "{v, v_adj} \<notin> E"
		show False using adj assms tmp2 ugraph_def
			by (smt One_nat_def Suc_1 UnionE card.empty card.insert finite.intros(1) insertE insert_absorb insert_commute insert_not_empty n_not_Suc_n singletonI)
	qed
qed

lemma ugraph_nrs_card: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> 
				\<forall>s \<in> node_range_set E subV. card (snd s) > 0"
	unfolding node_range_set_def
	using ugraph_nr_card by fastforce

lemma "finite E \<Longrightarrow> subV \<noteq> {} \<Longrightarrow> subV \<subseteq> \<Union>E \<Longrightarrow> (\<forall>s \<in> node_range_set E subV. card (snd s) > 0) \<Longrightarrow> ugraph E"
	unfolding node_range_set_def ugraph_def
	apply auto

lemma "ugraph E \<Longrightarrow> \<forall>v \<in> \<Union>E. card (node_range E v) > 0"
	by (meson ugraph_nr_card)

lemma "finite E \<Longrightarrow> \<Union>E \<noteq> {} \<Longrightarrow> \<forall>v \<in> \<Union>E. card (node_range E v) > 0 \<Longrightarrow> \<forall>e \<in> E. card e < 3"
	unfolding node_range_def ugraph_def
	apply auto


lemma
	assumes "finite E" "subV \<noteq> {}" "subV \<subseteq> \<Union>E" "\<forall>s \<in> node_range_set E subV. card (snd s) > 0"
	shows "ugraph E"
	using assms
proof -
	have "\<forall>e \<in> E. card e = 2"


	show "ugraph E"

definition coll where "coll E = (if \<not>ugraph E then {{}} else snd ` node_range_univ E)"
value "snd ` node_range_univ ({} :: Enum.finite_1 set set)"
value "snd ` node_range_univ ({{}} :: Enum.finite_1 set set)"
value "coll ({}::Enum.finite_1 set set)"
value "ugraph ({}::Enum.finite_1 set set)"
lemma "card (coll E) > 0"



lemma ugraph_coll: "ugraph E \<longleftrightarrow> (\<forall>e \<in> coll E. card e > 0)"
	unfolding ugraph_def coll_def node_range_univ_def
	apply auto
	by (meson UnionI ugraph_def ugraph_nr_card)


lemma "\<lbrakk> \<forall>s \<in> c. card s > 0; finite c; snd ` subsets \<subseteq> c; set_packing subsets; c = coll E; ugraph E \<rbrakk>
				\<Longrightarrow> \<exists>subV. subsets = node_range_set E subV"
	unfolding set_packing_def node_range_set_def coll_def
	apply (auto split: if_splits)
	


lemma is_sp: "is_independent_set E subV \<Longrightarrow> set_packing (node_range_set E subV)"
	unfolding is_independent_set_def set_packing_def node_range_univ_def
	by (auto simp add: hi nru_eq disjoint_def node_range_set_def node_range_def)

lemma hi':
	assumes "ugraph E" "subV \<subseteq> \<Union>E" "\<not>is_independent_set E subV"
	shows "\<not>set_packing (node_range_set E subV)"
	using assms
proof -
	have a: "\<exists>u \<in> subV. \<exists>v \<in> subV. {u, v} \<in> E"
		using assms is_independent_set_def by blast
	then obtain u v where u: "u \<in> subV" and v: "v \<in> subV" and e: "{u, v} \<in> E"
		by blast
	hence uv1: "{u, v} \<in> node_range E u" and uv2: "{u, v} \<in> node_range E v"
		unfolding node_range_def using e assms(1) ugraph_def 
		by (smt card.empty card_insert_if empty_iff finite.emptyI finite_insert insert_commute mem_Collect_eq n_not_Suc_n numeral_2_eq_2 singletonI)+

	have "node_range E u \<in> snd ` node_range_set E subV" and "node_range E v \<in> snd ` node_range_set E subV"
		unfolding node_range_set_def using u v by force+

	hence "({u}, node_range E u) \<in> node_range_set E subV" and "({v}, node_range E v) \<in> node_range_set E subV"
		unfolding node_range_set_def using u v by force+

	moreover have "({u}, node_range E u) \<noteq> ({v}, node_range E v)"
		using assms(1) e ugraph_def by fastforce

	moreover have "node_range E u \<inter> node_range E v \<noteq> {}"
		using uv1 uv2 by blast

	ultimately show ?thesis
		unfolding set_packing_def by fastforce
qed


lemma sp_is: "\<lbrakk> ugraph E; subV \<subseteq> \<Union>E \<rbrakk> \<Longrightarrow> set_packing (node_range_set E subV) \<Longrightarrow> is_independent_set E subV"
	unfolding coll_def using hi' by auto

value "(snd ` node_range_univ ({{}}::Enum.finite_1 set set))"
value "(node_range_set ({{}}::Enum.finite_1 set set) {})"
value "ugraph ({{}}::Enum.finite_1 set set)"
value "set_packing (snd ` node_range_univ ({{}}::Enum.finite_1 set set)) (node_range_set {{}} {})"

lemma "set_packing (snd ` node_range_univ E) (node_range_set E subV) \<Longrightarrow> subV \<subseteq> \<Union>E \<Longrightarrow> ugraph E"

term independent_set

(*
lemma "ugraph E \<Longrightarrow> to_ugraph (node_range_univ E) = E"
	unfolding to_ugraph_def
	sorry

lemma "ugraph (to_ugraph c) \<Longrightarrow> node_range_univ (to_ugraph c) = c"
	unfolding to_ugraph_def 
*)

fun is_sp where "is_sp (E, k) = (coll E, k)"

lemma "x \<in> independent_set \<Longrightarrow> fst (is_sp x) \<noteq> {{}}"
	unfolding independent_set_def coll_def

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

	have "set_packing (node_range_set E V)"
		using is_ev by (rule is_sp)

	moreover have "snd ` node_range_set E V \<subseteq> coll E"
		unfolding coll_def using nrs_sub_nru e v by (metis image_mono)

	moreover have "card (node_range_set E V) \<ge> k"
		using e v k nrs_card by metis

	moreover have "finite (coll E)"
		unfolding coll_def using nru_fin by auto

	moreover have "\<forall>s \<in> coll E. card s > 0"
		using e ugraph_coll by blast

	ultimately have "x \<in> {(E, k). (\<forall>s \<in> coll E. card s > 0) \<and> finite (coll E) \<and> snd ` node_range_set E V \<subseteq> coll E \<and> card (node_range_set E V) \<ge> k \<and> set_packing (node_range_set E V)}"
		using x e 
		by (smt (verit, ccfv_SIG) card_eq_0_iff case_prodI empty_iff mem_Collect_eq node_range_univ_def not_finite_existsD nrs_card' nru_nrs ugraph_vertex_set_finite)

	hence "is_sp x \<in> set_packing_pset"
		unfolding set_packing_pset_def
		using x by auto

	thus ?thesis .
qed

lemma "x \<notin> independent_set \<Longrightarrow> is_sp x \<notin> set_packing_pset"
proof -
	assume a: "x \<notin> independent_set"
	then obtain E k where x: "x = (E, k)"
		unfolding independent_set_def by blast

	hence "\<forall>V. \<not>(ugraph E \<and> V \<subseteq> \<Union>E \<and> card V \<ge> k \<and> is_independent_set E V)"
		using a independent_set_def by blast

	hence disj: "\<forall>V. \<not>ugraph E \<or> \<not>(V \<subseteq> \<Union>E) \<or> card V < k \<or> \<not>is_independent_set E V"
		by fastforce

	thus ?thesis
	proof (elim allE)
		fix v :: "'a set"
		consider (ugraph) "\<not>ugraph E"
			| (subset) "\<not> v \<subseteq> \<Union>E"
			| (card) "card v < k"
			| (indset) "\<not>is_independent_set E v"
			using disj by blast
		thus "is_sp x \<notin> set_packing_pset"
		proof cases
			case ugraph
			thus ?thesis unfolding set_packing_pset_def
				using ugraph_coll x by fastforce
		next
			case subset
			then show ?thesis sorry
		next
			case card
			then show ?thesis sorry
		next
			case indset

			have "\<not> set_packing (node_range_set E v)"
				apply (rule hi')
				using disj indset 
			then show ?thesis sorry
		qed

		assume "\<not>ugraph E"
		thus ?thesis
			unfolding set_packing_pset_def
			using ugraph_coll x by fastforce
	next
		fix v :: "'a set"
		assume "\<not> v \<subseteq> \<Union> E"

		thm nrs_sub_nru
		hence "\<not> node_range_set E v \<subseteq> node_range_univ E"
			using nrs_sub_nru by meson

		hence "\<not> snd ` node_range_set E v \<subseteq> snd ` node_range_univ E"
			unfolding node_range_set_def node_range_univ_def node_range_def
			using image_mono 

		hence "\<not>(snd ` node_range_set E v \<subseteq> coll E)"
			unfolding node_range_set_def coll_def
			apply (auto split: if_splits)
			sorry

		thus ?thesis
			unfolding set_packing_pset_def using x
			sorry
	next
		fix v :: "'a set"
		assume "card v < k"
		thus ?thesis sorry
	next
		fix v :: "'a set"
		assume "\<not> is_independent_set E v"
		thm hi'
		have "\<not> set_packing (node_range_set E v)"
			apply (rule hi')

		thus ?thesis 

			thm nru_fin
lemma "is_sp (E, k) \<in> set_packing_pset \<Longrightarrow> ugraph E"
	unfolding set_packing_pset_def ugraph_def
	apply auto

lemma "({{}}, n) \<notin> set_packing_pset"
	unfolding set_packing_pset_def set_packing_def
	apply auto

lemma "is_sp x \<in> set_packing_pset \<Longrightarrow> x \<in> independent_set"
proof -
	assume a: "is_sp x \<in> set_packing_pset"
	then obtain c n where x: "is_sp x = (c, n)"
		unfolding set_packing_pset_def by blast

	obtain E k where "k = n" and c: "c = coll E"
		using x by (metis fst_conv is_sp.elims)

	hence "\<exists>subsets. (\<forall>s \<in> c. card s > 0) \<and> finite c \<and> snd ` subsets \<subseteq> c \<and> card subsets \<ge> n \<and> set_packing subsets"
		using a x set_packing_pset_def
		by (smt (verit) Pair_inject case_prodE mem_Collect_eq)

	hence "\<exists>subsets. (\<forall>s \<in> c. card s > 0) \<and> finite c \<and> snd ` subsets \<subseteq> c \<and> card subsets \<ge> n \<and> set_packing subsets
					\<and> (\<exists>subV. \<Union>(fst ` node_range_set E subV) = \<Union>(fst ` subsets))"
		using nrs_fst 

	then obtain subsets subV where card: "\<forall>s \<in> c. card s > 0" and fin: "finite c"
														and subs: "snd ` subsets \<subseteq> c" and n: "n \<le> card subsets" and sp: "set_packing c subsets"
														and "\<Union>(fst ` node_range_set E subV) = \<Union>(fst ` subsets)"
		by meson

	hence "\<forall>s1 \<in> subsets. \<forall>s2 \<in> subsets. s1 = s2 \<or> snd s1 \<inter> snd s2 = {}"
		unfolding set_packing_def using sp by simp

	have "\<Union>c = E"
		by (metis c card coll_def nru_eq ugraph_coll)

	have "card (fst ` node_range_set E subV) = card (fst ` subsets)"
		
		
		

	have "is_independent_set E subV"
		apply (rule sp_is)
		using ugraph_coll \<open>c = coll E\<close> card apply blast
		 defer
		oops
			apply (metis \<open>is_sp x = (c, n)\<close> fst_conv image_mono is_sp.simps nrs_fst nru_nrs subs x)
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