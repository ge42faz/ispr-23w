theory NAE3SAT_MAXCUT
	imports Main SAT_3SAT "3SAT_NAE3SAT"
begin

hide_const Wfrec.cut

definition cut :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
	where "cut V S T \<longleftrightarrow> (V = S \<union> T) \<and> ({} = S \<inter> T)"

definition cutset :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set"
	where "cutset E S T = {{u, v} | u v. {u, v} \<in> E \<and> u \<in> S \<and> v \<in> T}"

definition graph :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool"
	where "graph E V \<longleftrightarrow> (\<forall>e \<in> E. card e = 2) \<and> \<Union>E \<subseteq> V \<and> finite V"

definition maxcut_pset :: "('a set set * 'a set * nat) set"
	where "maxcut_pset = {(E, V, k). \<exists>S T. cut V S T \<and> card (cutset E S T) \<ge> k \<and> graph E V}"

fun parse_nodes :: "(nat * 'a lit set) list \<Rightarrow> (nat * 'a lit) set"
	where "parse_nodes [] = {}"
	| "parse_nodes ((n, c) # cs) = (
			let (x, p) = pop c in
			let (y, q) = pop p in
			let (z, _) = pop q in
				{(n, x), (n, y), (n, z)} \<union> parse_nodes cs
	)"

definition parse_var_edges :: "(nat * 'a lit) set \<Rightarrow> (nat * 'a lit * 'a lit) set set"
	where "parse_var_edges nodes = {{(n, (Pos \<circ> ident) x, x), (n, (Neg \<circ> ident) x, x)} | n x. (n, x) \<in> nodes}"

(*
lemma parse_var_edges_ident: "parse_var_edges nodes = {{(n, (Pos \<circ> ident) x), (n, (Neg \<circ> ident) x)} | n x. (n, x) \<in> nodes}"
	unfolding parse_var_edges_def 
	by (auto, force+, metis ident.elims)
*)

fun parse_clause_edges :: "(nat * 'a lit set) list \<Rightarrow> (nat * 'a lit * 'a lit) set set"
	where "parse_clause_edges [] = {}"
	| "parse_clause_edges ((n, c) # cs) = (
			let (x, p) = pop c in
			let (y, q) = pop p in
			let (z, _) = pop q in
				{{(n, x, x), (n, y, y)}, {(n, y, y), (n, z, z)}, {(n, z, z), (n, x, x)}} \<union> parse_clause_edges cs
	)"

definition parse_edges :: "(nat * 'a lit set) list \<Rightarrow> (nat * 'a lit) set \<Rightarrow> (nat * 'a lit * 'a lit) set set"
	where "parse_edges expr nodes = parse_var_edges nodes \<union> parse_clause_edges expr"

fun split_nodes :: "'a * 'b \<Rightarrow> 'a * 'b * 'b"
	where "split_nodes (a, b) = (a, b, b)"

definition parse :: "(nat * 'a lit set) list \<Rightarrow> (nat * 'a lit * 'a lit) set set * (nat * 'a lit * 'a lit) set"
	where "parse expr = (let nodes = parse_nodes expr in (parse_edges expr nodes, \<Union>(parse_var_edges nodes)))"

term map2
term Pair
definition tag :: "'a list \<Rightarrow> (nat * 'a) list"
	where "tag expr = zip [0 ..< (length expr)] expr"

value "tag [0::nat, 1, 2]"

lemma nae3sat_tl: "nae3sat expr \<Longrightarrow> nae3sat (tl expr)"
	unfolding nae3sat_def naesat_def nae_models_def
	by (smt list.sel(2) list.set_sel(2))

lemma tag_uniq: "card (set (tag expr)) = length (tag expr)"
	unfolding tag_def
	by (simp add: distinct_card distinct_zipI1)

lemma tag_nil: "tag [] = []"
	unfolding tag_def by simp

lemma tag_cons: "tag (x # xs) = (0, x) # zip [1 ..< Suc (length xs)] xs"
	unfolding tag_def using upt_rec
	by (auto simp add: not_less_eq_eq)

lemma parse_clause_edges_split: "parse_clause_edges (xs @ ys) = parse_clause_edges xs \<union> parse_clause_edges ys"
	by (induction xs arbitrary: ys) (auto split: prod.splits)

lemma parse_clause_edges_cons: "parse_clause_edges (x # xs) = parse_clause_edges (x # []) \<union> parse_clause_edges xs"
	using parse_clause_edges_split[of "x # []" xs] by simp

lemma parse_clause_edges_zip: "length xs = length ys \<Longrightarrow> parse_clause_edges (zip (xs @ xss) (ys @ yss)) = parse_clause_edges (zip xs ys) \<union> parse_clause_edges (zip xss yss)"
	using parse_clause_edges_split by auto

lemma parse_nodes_split: "parse_nodes (xs @ ys) = parse_nodes xs \<union> parse_nodes ys"
	by (induction xs arbitrary: ys) auto

lemma parse_nodes_cons: "parse_nodes (x # xs) = parse_nodes (x # []) \<union> parse_nodes xs"
	using parse_nodes_split[of "x # []" xs] by simp

lemma parse_nodes_zip: "length xs = length ys \<Longrightarrow> parse_nodes (zip (xs @ xss) (ys @ yss)) = parse_nodes (zip xs ys) \<union> parse_nodes (zip xss yss)"
	using parse_nodes_split by auto

lemma parse_nodes_subset: "x \<in> set xs \<Longrightarrow> parse_nodes (x # []) \<subseteq> parse_nodes xs"
	using parse_nodes_cons parse_nodes_split 
	by (metis Un_subset_iff split_list_first subset_refl)

lemma parse_var_edges_split: "parse_var_edges (xs \<union> ys) = parse_var_edges xs \<union> parse_var_edges ys"
	unfolding parse_var_edges_def by blast

lemma parse_var_edges_insert: "parse_var_edges (insert x xs) = parse_var_edges {x} \<union> parse_var_edges xs"
	unfolding parse_var_edges_def by blast

lemma parse_var_edges_subset: "x \<subseteq> xs \<Longrightarrow> parse_var_edges x \<subseteq> parse_var_edges xs"
	unfolding parse_var_edges_def by blast



(*
lemma tmp: "expr \<noteq> [] \<Longrightarrow> zip [1 ..< Suc (length expr)] expr = zip [1 ..< length expr] (butlast expr) @ ((length expr, last expr) # [])"
	apply (induction expr)
	 apply auto
	by (smt One_nat_def Suc_pred append.assoc append.simps(2) append_Nil append_butlast_last_id last_snoc length_Cons length_butlast length_greater_0_conv length_upt list.simps(3) zip_Cons_Cons zip_Nil zip_append)
*)

lemma tag_fst: "\<lbrakk> n \<in> set (zip xs ys); x \<notin> set xs \<rbrakk> \<Longrightarrow> fst n \<noteq> x"
	by (metis in_set_zipE prod.collapse)

lemma tag_fst_nat: "\<lbrakk> n \<in> set (zip [0 ..< length ys] ys) \<rbrakk> \<Longrightarrow> fst n < length ys"
	using tag_fst by fastforce

lemma tag_len: "length xs = length (tag xs)"
	unfolding tag_def by simp

lemma tag_card: "card (set xs) \<le> card (set (tag xs))"
	using tag_len tag_uniq by (metis card_length)

lemma tag_card_single: "card (set (c # [])) = card (set (tag (c # [])))"
	unfolding tag_def by simp

lemma tag_sup_node:
	assumes "\<forall>y \<in> set ys. card y = 3"
	shows "\<forall>e \<in> parse_nodes (zip [0 ..< length ys] ys). fst e < length ys"
	using assms
proof (induction ys rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc y ys)

  have "length (y # ys) = Suc (length ys)"
  	by simp
  hence parse_butlast: "\<forall>e \<in> parse_nodes (zip [0 ..< length ys] ys). fst e < Suc (length ys)"
  	using snoc.IH snoc.prems by (simp add: less_SucI)

  have parse_split: "parse_nodes (zip [0 ..< Suc (length ys)] (ys @ [y])) = parse_nodes (zip [0 ..< length ys] ys) \<union> parse_nodes ((length ys, y) # [])"
  	using parse_nodes_zip
  	by (metis diff_zero length_upt list.size(3) old.nat.distinct(1) upt_Suc zip_Cons_Cons zip_Nil)

  let ?l = "length ys"
  let ?x = "fst (pop y)"
  let ?p = "snd (pop y)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  have "card y = 3"
  	using snoc.prems by simp
  hence "parse_nodes ((length ys, y) # []) = {(?l, ?x), (?l, ?y), (?l, ?z)}"
  	by (simp split: prod.splits)
  hence "\<forall>e \<in> parse_nodes ((length ys, y) # []). fst e < Suc (length ys)"
  	by simp

  thus ?case using parse_butlast parse_split by fastforce
qed

lemma tag_sup_var:
	assumes "\<forall>y \<in> set ys. card y = 3"
	shows "\<forall>e \<in> parse_var_edges (parse_nodes (zip [0 ..< length ys] ys)). \<forall>n \<in> e. fst n < length ys"
	using assms tag_sup_node unfolding parse_var_edges_def by fastforce


lemma tag_sup_clause:
	assumes "\<forall>y \<in> set ys. card y = 3"
	shows "\<forall>e \<in> parse_clause_edges (zip [0 ..< length ys] ys). \<forall>n \<in> e. fst n < length ys"
	using assms
proof (induction ys rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc y ys)

  have "length (y # ys) = Suc (length ys)"
  	by simp
  hence parse_butlast: "\<forall>e \<in> parse_clause_edges (zip [0 ..< length ys] ys). \<forall>n \<in> e. fst n < Suc (length ys)"
  	using snoc.IH snoc.prems by (simp add: less_SucI)

  have parse_split: "parse_clause_edges (zip [0 ..< Suc (length ys)] (ys @ [y])) = parse_clause_edges (zip [0 ..< length ys] ys) \<union> parse_clause_edges ((length ys, y) # [])"
  	using parse_clause_edges_zip 
  	by (metis diff_zero length_upt list.size(3) old.nat.distinct(1) upt_Suc zip_Cons_Cons zip_Nil)

  let ?l = "length ys"
  let ?x = "fst (pop y)"
  let ?p = "snd (pop y)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  have "card y = 3"
  	using snoc.prems by simp
  hence "parse_clause_edges ((length ys, y) # []) = {{(?l, ?x, ?x), (?l, ?y, ?y)}, {(?l, ?y, ?y), (?l, ?z, ?z)}, {(?l, ?z, ?z), (?l, ?x, ?x)}}"
  	by (simp split: prod.splits)
  hence "\<forall>e \<in> parse_clause_edges ((length ys, y) # []). \<forall>n \<in> e. fst n < Suc (length ys)"
  	by simp

  thus ?case using parse_butlast parse_split by fastforce
qed

lemma parse_edge_card:
	assumes "length xs = length ys" "\<forall>y \<in> set ys. card y = 3"
	shows "\<forall>e \<in> parse_clause_edges (zip xs ys). card e = 2"
	using assms
proof (induction ys arbitrary: xs)
  case Nil
  thus ?case by simp
next
  case (Cons y ys)
  then obtain x xs' where tl_xs': "xs = x # xs'" and length_xs': "length xs' = length ys"
  	by (metis Suc_length_conv)

  have parse_tl: "\<forall>e \<in> parse_clause_edges (zip xs' ys). card e = 2"
  	apply (rule Cons.IH)
  	using length_xs' Cons.prems by auto

  have parse_split: "parse_clause_edges (zip xs (y # ys)) = parse_clause_edges ((x, y) # []) \<union> parse_clause_edges (zip xs' ys)"
  	using parse_clause_edges_cons tl_xs' by (metis zip_Cons_Cons)

  let ?x = "fst (pop y)"
  let ?p = "snd (pop y)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  have card_y: "card y = 3"
  	using Cons.prems by simp
  hence "parse_clause_edges ((x, y) # []) = {{(x, ?x, ?x), (x, ?y, ?y)}, {(x, ?y, ?y), (x, ?z, ?z)}, {(x, ?z, ?z), (x, ?x, ?x)}}"
		by (simp split: prod.splits)
	moreover have "?x \<noteq> ?y"
		using card_y pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have "?y \<noteq> ?z"
		using card_y pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have "?x \<noteq> ?z"
		using card_y pop_card pop_ins
		by (smt card.empty card.infinite diff_Suc_1 insert_absorb insert_iff numeral_3_eq_3 old.nat.distinct(1))
  ultimately have "\<forall>e \<in> parse_clause_edges ((x, y) # []). card e = 2"
  	by simp

  thus ?case using parse_tl parse_split by blast
qed

lemma "length [0 ..< length ys] = length ys"
	by (induction ys) auto

lemma parse_edge_disj:
	assumes "\<forall>y \<in> set ys. card y = 3"
	shows "parse_clause_edges (zip [0 ..< length (butlast ys)] (butlast ys)) \<inter> parse_clause_edges ((length (butlast ys), last ys) # []) = {}"
	using assms
proof (induction ys rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc y ys)
  hence card_y: "card y = 3"
  	by simp

  have butlast_sup: "\<forall>e \<in> parse_clause_edges (zip [0 ..< length ys] ys). \<forall>n \<in> e. fst n < length ys"
  	using snoc.prems tag_sup_clause by auto

  have parse_split: "parse_clause_edges (zip [0 ..< Suc (length ys)] (ys @ [y])) = parse_clause_edges (zip [0 ..< length ys] ys) \<union> parse_clause_edges ((length ys, y) # [])"
  	using parse_clause_edges_zip 
  	by (metis diff_zero length_upt list.size(3) old.nat.distinct(1) upt_Suc zip_Cons_Cons zip_Nil)

  let ?l = "length ys"
  let ?x = "fst (pop y)"
  let ?p = "snd (pop y)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  have expand_last: "parse_clause_edges ((length ys, y) # []) = {{(?l, ?x, ?x), (?l, ?y, ?y)}, {(?l, ?y, ?y), (?l, ?z, ?z)}, {(?l, ?z, ?z), (?l, ?x, ?x)}}"
  	by (simp split: prod.splits)
  hence "\<forall>e \<in> parse_clause_edges ((length ys, y) # []). \<forall>n \<in> e. fst n = length ys"
  	by simp

  thus ?case using butlast_sup by fastforce
qed


lemma triangle_edge_card:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card ((parse_clause_edges \<circ> tag) expr) = 3 * length expr"
	using assms
proof (induction expr rule: rev_induct)
  case Nil
  thus ?case by (simp add: tag_nil)
next
  case (snoc c expr)

  let ?l = "length expr"
  let ?x = "fst (pop c)"
  let ?p = "snd (pop c)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  have card_c: "card c = 3"
  	by (simp add: snoc.prems)

  have parse_split: "(parse_clause_edges \<circ> tag) (expr @ [c]) = (parse_clause_edges \<circ> tag) expr \<union> parse_clause_edges ((length expr, c) # [])"
  	using parse_clause_edges_zip tag_def
  	by (smt comp_apply diff_zero length_0_conv length_append_singleton length_upt tag_nil upt_Suc zip_Cons_Cons)

  have card_hyp: "card ((parse_clause_edges \<circ> tag) expr) = 3 * length expr"
  	apply (rule snoc.IH) using snoc.prems by simp

  have expand: "parse_clause_edges ((length expr, c) # []) = {{(?l, ?x, ?x), (?l, ?y, ?y)}, {(?l, ?y, ?y), (?l, ?z, ?z)}, {(?l, ?z, ?z), (?l, ?x, ?x)}}"
  	by (simp split: prod.splits)
	moreover have 1: "?x \<noteq> ?y"
		using card_c pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have 2: "?y \<noteq> ?z"
		using card_c pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have 3: "?x \<noteq> ?z"
		using card_c pop_card pop_ins
		by (smt card.empty card.infinite diff_Suc_1 insert_absorb insert_iff numeral_3_eq_3 old.nat.distinct(1))
	ultimately have "{(?l, ?x, ?x), (?l, ?y, ?y)} \<noteq> {(?l, ?y, ?y), (?l, ?z, ?z)}"
		and "{(?l, ?y, ?y), (?l, ?z, ?z)} \<noteq> {(?l, ?z, ?z), (?l, ?x, ?x)}"
		and "{(?l, ?z, ?z), (?l, ?x, ?x)} \<noteq> {(?l, ?x, ?x), (?l, ?y, ?y)}"
		using 1 2 3 by (metis Pair_inject doubleton_eq_iff)+

	hence card_new: "card (parse_clause_edges ((length expr, c) # [])) = 3"
		using expand by simp

	moreover have "parse_clause_edges ((length expr, c) # []) \<inter> (parse_clause_edges \<circ> tag) expr = {}"
		unfolding tag_def using parse_edge_disj snoc.prems
		by (smt butlast_snoc comp_apply inf.commute last_snoc)

	ultimately have "card ((parse_clause_edges \<circ> tag) (expr @ [c])) = card (parse_clause_edges ((length expr, c) # [])) + card ((parse_clause_edges \<circ> tag) expr)"
		using parse_split card_hyp
		by (smt add.commute card.infinite card_Un_disjoint comp_apply finite.emptyI inf.commute length_0_conv mult_is_0 parse_clause_edges.simps(1) tag_nil zero_neq_numeral)
	also have "... = 3 + 3 * length expr"
		by (subst card_new, subst card_hyp, rule refl)
	also have "... = 3 * length (expr @ [c])"
		by simp
	finally show ?case .
qed

lemma "\<forall>c \<in> set expr. card (snd c) = 3 \<Longrightarrow> card (parse_nodes expr) = 3 * length expr"
proof (induction expr)


lemma parse_var_card: "e \<in> parse_var_edges nodes \<Longrightarrow> card e = 2"
	unfolding parse_var_edges_def by force

lemma parse_node_disj:
	assumes "\<forall>y \<in> set ys. card y = 3"
	shows "parse_nodes (zip [0 ..< length (butlast ys)] (butlast ys)) \<inter> parse_nodes ((length (butlast ys), last ys) # []) = {}"
	using assms
proof (induction ys rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc y ys)
  hence card_y: "card y = 3"
  	by simp

  have butlast_sup: "\<forall>e \<in> parse_nodes (zip [0 ..< length ys] ys). fst e < length ys"
  	using snoc.prems tag_sup_node by auto

  have parse_split: "parse_nodes (zip [0 ..< Suc (length ys)] (ys @ [y])) = parse_nodes (zip [0 ..< length ys] ys) \<union> parse_nodes ((length ys, y) # [])"
  	using parse_nodes_zip 
  	by (metis diff_zero length_upt list.size(3) old.nat.distinct(1) upt_Suc zip_Cons_Cons zip_Nil)

  let ?l = "length ys"
  let ?x = "fst (pop y)"
  let ?p = "snd (pop y)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  have expand_last: "parse_nodes ((length ys, y) # []) = {(?l, ?x), (?l, ?y), (?l, ?z)}"
  	by (simp split: prod.splits)
  hence "\<forall>e \<in> parse_nodes ((length ys, y) # []). fst e = length ys"
  	by simp

  thus ?case using butlast_sup by fastforce
qed

lemma parse_var_disj: "xs \<inter> ys = {} \<Longrightarrow> parse_var_edges xs \<inter> parse_var_edges ys = {}"
	unfolding parse_var_edges_def by (auto simp add: doubleton_eq_iff)


lemma parse_var_finite_aux: "{{(n, Pos (ident x), x), (n, Neg (ident x), x)} |n x. n = a \<and> x = b \<or> (n, x) \<in> A} = insert {(a, Pos (ident b), b), (a, Neg (ident b), b)} {{(n, Pos (ident x), x), (n, Neg (ident x), x)} |n x. (n, x) \<in> A}"
	by blast

lemma parse_var_finite: "finite A \<Longrightarrow> finite (parse_var_edges A)"
	unfolding parse_var_edges_def
	by (induction A rule: finite.induct) (auto simp add: parse_var_finite_aux)

lemma card_set_disj: "finite A \<Longrightarrow> A = A1 \<union> A2 \<Longrightarrow> A1 \<inter> A2 = {} \<Longrightarrow> card A = card A1 + card A2"
	apply (induction A arbitrary: A1 A2 rule: finite.induct)
	 apply auto
	by (metis card_Un_disjoint finite_Un finite_insert)

lemma parse_var_triple:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card ((parse_nodes \<circ> tag) expr) = 3 * length expr"
	using assms
proof (induction expr rule: rev_induct)
  case Nil
  thus ?case unfolding tag_def by simp
next
  case (snoc c expr)

  let ?l = "length expr"
  let ?x = "fst (pop c)"
  let ?p = "snd (pop c)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  have card_c: "card c = 3"
  	by (simp add: snoc.prems)

  have parse_split: "(parse_nodes \<circ> tag) (expr @ [c]) = (parse_nodes \<circ> tag) expr \<union> parse_nodes ((length expr, c) # [])"
  	using parse_nodes_zip tag_def
  	by (smt comp_apply diff_zero length_0_conv length_append_singleton length_upt tag_nil upt_Suc zip_Cons_Cons)

  have card_hyp: "card ((parse_nodes \<circ> tag) expr) = 3 * length expr"
  	apply (rule snoc.IH) using snoc.prems by simp

  have expand: "parse_nodes ((length expr, c) # []) = {(?l, ?x), (?l, ?y), (?l, ?z)}"
  	by (simp split: prod.splits)
	moreover have 1: "?x \<noteq> ?y"
		using card_c pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have 2: "?y \<noteq> ?z"
		using card_c pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have 3: "?x \<noteq> ?z"
		using card_c pop_card pop_ins
		by (smt card.empty card.infinite diff_Suc_1 insert_absorb insert_iff numeral_3_eq_3 old.nat.distinct(1))
	ultimately have card_new: "card (parse_nodes ((length expr, c) # [])) = 3"
		by simp

	have "card ((parse_nodes \<circ> tag) (expr @ [c])) = card (parse_nodes ((length expr, c) # [])) + card ((parse_nodes \<circ> tag) expr)"
		using parse_split card_hyp parse_node_disj tag_def tag_nil snoc.prems
		by (smt add.commute butlast_snoc card.infinite card_Un_disjoint comp_apply expand finite.emptyI finite.insertI last_snoc length_greater_0_conv mult_Suc not_add_less1 numeral_3_eq_3 parse_nodes.simps(1))
	also have "... = 3 + 3 * length expr"
		by (subst card_new, subst card_hyp, rule refl)
	also have "... = 3 * length (expr @ [c])"
		by simp
  finally show ?case .
qed

lemma set3card: "a \<noteq> b \<Longrightarrow> b \<noteq> c \<Longrightarrow> c \<noteq> a \<Longrightarrow> card {a, b, c} = 3"
	by force

lemma var_card_inv:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card ((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) = card ((parse_nodes \<circ> tag) expr)"
	using assms
proof (induction expr rule: rev_induct)
  case Nil
  thus ?case unfolding parse_var_edges_def tag_def by simp
next
  case (snoc c expr)
  hence expr: "\<forall>c \<in> set expr. card c = 3"
  	by simp
  hence card_hyp: "card ((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) = card ((parse_nodes \<circ> tag) expr)"
  	by (rule snoc.IH)

  have card_c: "card c = 3"
  	using snoc.prems by simp

  have rhs: "card ((parse_nodes \<circ> tag) (expr @ [c])) = 3 + card ((parse_nodes \<circ> tag) expr)"
  	using parse_var_triple expr snoc.prems
  	by (metis length_append_singleton mult_Suc_right)

  have parse_split: "(parse_var_edges \<circ> parse_nodes \<circ> tag) (expr @ [c]) = (parse_var_edges \<circ> parse_nodes) ((length expr, c) # []) \<union> (parse_var_edges \<circ> parse_nodes \<circ> tag) expr"
  	unfolding tag_def using parse_nodes_split parse_var_edges_split parse_nodes_cons parse_nodes_zip
  	by (smt append_Cons append_is_Nil_conv comp_apply diff_zero length_0_conv length_append_singleton length_upt list.size(3) self_append_conv sup.commute upt_Suc zip_Cons_Cons)

  moreover have "parse_nodes ((length expr, c) # []) \<inter> (parse_nodes \<circ> tag) expr = {}"
  	using parse_node_disj tag_def snoc.prems
  	by (smt butlast_snoc comp_apply inf.commute last_snoc)

  ultimately have parse_disj: "(parse_var_edges \<circ> parse_nodes) ((length expr, c) # []) \<inter> (parse_var_edges \<circ> parse_nodes \<circ> tag) expr = {}"
  	using parse_var_disj by (metis comp_apply)

  have "finite (set (expr @ [c]))"
  	by simp
  hence "finite (set (tag (expr @ [c])))"
  	by simp
  hence "finite ((parse_nodes \<circ> tag) (expr @ [c]))"
  	using card.infinite rhs by fastforce
  hence "finite ((parse_var_edges \<circ> parse_nodes \<circ> tag) (expr @ [c]))"
  	using parse_var_finite by auto
  hence card_var: "card ((parse_var_edges \<circ> parse_nodes \<circ> tag) (expr @ [c])) = card ((parse_var_edges \<circ> parse_nodes) ((length expr, c) # [])) + card ((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
		apply (rule card_set_disj)
		apply (rule parse_split)
		apply (rule parse_disj)
		done

  let ?l = "length expr"
  let ?x = "fst (pop c)"
  let ?p = "snd (pop c)"
  let ?y = "fst (pop ?p)"
  let ?q = "snd (pop ?p)"
  let ?z = "fst (pop ?q)"

  let ?pos = "Pos \<circ> ident"
  let ?neg = "Neg \<circ> ident"

  have expand_last: "parse_nodes ((length expr, c) # []) = {(?l, ?x), (?l, ?y), (?l, ?z)}"
  	by (simp split: prod.splits)
  hence "(parse_var_edges \<circ> parse_nodes) ((length expr, c) # []) = parse_var_edges {(?l, ?x), (?l, ?y), (?l, ?z)}"
  	by simp
  also have expand_full: "... = {{(?l, ?pos?x, ?x), (?l, ?neg?x, ?x)}, {(?l, ?pos?y, ?y), (?l, ?neg?y, ?y)}, {(?l, ?pos?z, ?z), (?l, ?neg?z, ?z)}}"
  	unfolding parse_var_edges_def by fast

  have "?x \<noteq> ?y"
		using card_c pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
  hence 1: "{(?l, ?pos?x, ?x), (?l, ?neg?x, ?x)} \<noteq> {(?l, ?pos?y, ?y), (?l, ?neg?y, ?y)}"
  	by blast

  have "?y \<noteq> ?z"
		using card_c pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	hence 2: "{(?l, ?pos?y, ?y), (?l, ?neg?y, ?y)} \<noteq> {(?l, ?pos?z, ?z), (?l, ?neg?z, ?z)}"
		by blast

	have "?x \<noteq> ?z"
		using card_c pop_card pop_ins
		by (smt card.empty card.infinite diff_Suc_1 insert_absorb insert_iff numeral_3_eq_3 old.nat.distinct(1))
  hence 3: "{(?l, ?pos?z, ?z), (?l, ?neg?z, ?z)} \<noteq> {(?l, ?pos?x, ?x), (?l, ?neg?x, ?x)}"
  	by blast

  have "card {{(?l, ?pos?x, ?x), (?l, ?neg?x, ?x)}, {(?l, ?pos?y, ?y), (?l, ?neg?y, ?y)}, {(?l, ?pos?z, ?z), (?l, ?neg?z, ?z)}} = 3"
  	by (rule set3card, insert 1 2 3, assumption)+

  hence "card ((parse_var_edges \<circ> parse_nodes) ((length expr, c) # [])) = 3"
  	using expand_full expand_last by simp
  moreover have "card ((parse_var_edges \<circ> parse_nodes \<circ> tag) (expr @ [c])) = 3 + card ((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
  	using card_var calculation by simp
  ultimately show ?case
  	using card_hyp card_var rhs by arith
qed

lemma parallel_edge_card:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card ((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) = 3 * length expr"
	using assms parse_var_triple var_card_inv by metis

lemma parallel_edge_card_single: "card c = 3 \<Longrightarrow> card ((parse_var_edges \<circ> parse_nodes \<circ> tag) (c # [])) = 3"
	using parallel_edge_card
	by (metis One_nat_def add.commute list.distinct(1) list.set_cases list.size(3) list.size(4) nat_mult_1_right plus_1_eq_Suc set_ConsD)

lemma var_edge_card_single_alt:
	assumes "card c = 3"
	shows "card (parse_var_edges {(n, fst (pop c)), (n, fst (pop (snd (pop c)))), (n, fst (pop (snd (pop (snd (pop c))))))}) = 3"
	using assms
proof -
	let ?x = "fst (pop c)"
	let ?y = "fst (pop (snd (pop c)))"
	let ?z = "fst (pop (snd (pop (snd (pop c)))))"

	have "parse_var_edges {(n, ?x), (n, ?y), (n, ?z)} = {{(n, (Pos \<circ> ident) ?x, ?x), (n, (Neg \<circ> ident) ?x, ?x)}, {(n, (Pos \<circ> ident) ?y, ?y), (n, (Neg \<circ> ident) ?y, ?y)}, {(n, (Pos \<circ> ident) ?z, ?z), (n, (Neg \<circ> ident) ?z, ?z)}}"
		unfolding parse_var_edges_def by fast

	moreover have 1: "?x \<noteq> ?y"
		using assms pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have 2: "?y \<noteq> ?z"
		using assms pop_card pop_def pop_ins
		by (smt card.insert_remove card_eq_0_iff diff_Suc_1 fst_conv numeral_3_eq_3 old.nat.distinct(1) snd_conv)
	moreover have 3: "?x \<noteq> ?z"
		using assms pop_card pop_ins
		by (smt card.empty card.infinite diff_Suc_1 insert_absorb insert_iff numeral_3_eq_3 old.nat.distinct(1))

	ultimately show ?thesis by (simp add: doubleton_eq_iff)
qed

lemma var_edge_card_single: "card c = 3 \<Longrightarrow> card ((parse_var_edges \<circ> parse_nodes) ((n, c) # [])) = 3"
	using parallel_edge_card_single tag_card_single var_edge_card_single_alt by (fastforce split: prod.splits)

lemma var_edge_card_eq:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card ((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) = card ((parse_clause_edges \<circ> tag) expr)"
	using assms parallel_edge_card triangle_edge_card by metis

value "snd (a, b, c)"

(*
lemma
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "\<forall>e \<in> (parse_var_edges \<circ> parse_nodes \<circ> tag) expr. \<exists>a b. e = {a, b} \<and> snd a \<noteq> snd b"
	using assms unfolding parse_var_edges_def by fastforce
*)

lemma var_edge_trait_aux: "\<exists>e \<in> {(n, (Pos \<circ> ident) x, x), (n, (Neg \<circ> ident) x, x)}. (fst \<circ> snd) e \<noteq> (snd \<circ> snd) e"
	by (metis comp_def fst_conv insertCI lit.distinct(1) snd_conv)

lemma var_edge_trait: "\<forall>e \<in> parse_var_edges expr. \<exists>n \<in> e. (fst \<circ> snd) n \<noteq> (snd \<circ> snd) n"
	unfolding parse_var_edges_def using var_edge_trait_aux by fastforce

lemma clause_edge_trait: "\<forall>e \<in> parse_clause_edges expr. \<forall>n \<in> e. (fst \<circ> snd) n = (snd \<circ> snd) n"
	by (induction expr) auto

lemma var_clause_edge_disj: "(parse_var_edges \<circ> parse_nodes) expr \<inter> parse_clause_edges expr = {}"
	using clause_edge_trait var_edge_trait by fastforce

lemma var_clause_edge_disj_alt: "(parse_var_edges \<circ> parse_nodes \<circ> tag) expr \<inter> (parse_clause_edges \<circ> tag) expr = {}"
	using var_edge_trait clause_edge_trait by fastforce

lemma total_edge_count:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card (parse_edges (tag expr) ((parse_nodes \<circ> tag) expr)) = 6 * length expr"
	using assms var_edge_card_eq var_clause_edge_disj_alt triangle_edge_card unfolding parse_edges_def
	by (smt Groups.mult_ac(2) add_mult_distrib2 card.infinite card_Un_disjoint card_set_disj comp_apply mult_is_0 numeral_Bit0)

lemma subgraph_edge_count:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "\<forall>c \<in> set expr. card (parse_edges (tag (c # [])) ((parse_nodes \<circ> tag) (c # []))) = 6"
	using assms total_edge_count
	by (metis One_nat_def empty_set length_Cons list.set(2) list.size(3) nat_mult_1_right singletonD)

(*
lemma 
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card (parse_edges (tag expr) ((parse_nodes \<circ> tag) expr)) = card (\<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr))"
	using assms
proof -
	have "card (parse_edges (tag expr) ((parse_nodes \<circ> tag) expr)) = card (parse_var_edges (parse_nodes (tag expr)) \<union> parse_clause_edges (tag expr))"
		unfolding parse_edges_def by simp
	also have "... = card (parse_var_edges (parse_nodes (tag expr))) + card (parse_clause_edges (tag expr))"
		using assms calculation total_edge_count triangle_edge_card var_edge_card_eq by fastforce
	also have "... = card (parse_var_edges (parse_nodes (tag expr))) + card (parse_var_edges (parse_nodes (tag expr)))"
		using assms var_edge_card_eq by fastforce
	also have "... = card (\<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr))"
		using parse_var_card
*)

lemma "finite B \<Longrightarrow> card A = card B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<subseteq> A"
	using card_subset_eq by blast

lemma parse_un_disj:
	assumes "\<forall>c \<in> set xs. card c = 3"
	shows "\<Union>((parse_var_edges \<circ> parse_nodes) (zip [0 ..< length (butlast xs)] (butlast xs))) \<inter> \<Union>((parse_var_edges \<circ> parse_nodes) ((length (butlast xs), last xs) # [])) = {}"
	using assms
proof (induction xs rule: rev_induct)
  case Nil
  thus ?case unfolding parse_var_edges_def by simp
next
  case (snoc x xs)
  hence card_x: "card x = 3"
  	by simp

  have card_hyp: "\<Union>((parse_var_edges \<circ> parse_nodes) (zip [0..<length (butlast xs)] (butlast xs))) \<inter> \<Union>((parse_var_edges \<circ> parse_nodes) [(length (butlast xs), last xs)]) = {}"
  	apply (rule snoc.IH) using snoc.prems by simp

  have rewrite: "\<Union>((parse_var_edges \<circ> parse_nodes) (zip [0..<length (butlast (xs @ [x]))] (butlast (xs @ [x])))) \<inter> \<Union>((parse_var_edges \<circ> parse_nodes) [(length (butlast (xs @ [x])), last (xs @ [x]))])
				= \<Union>((parse_var_edges \<circ> parse_nodes) (zip [0..<length xs] xs)) \<inter> \<Union>((parse_var_edges \<circ> parse_nodes) [(length xs, x)])"
		by simp

	have "\<forall>n \<in> \<Union>((parse_var_edges \<circ> parse_nodes) (zip [0..<length xs] xs)). fst n < length xs"
		unfolding parse_var_edges_def apply auto
		using tag_sup_node snoc.prems by (metis Un_iff fst_conv set_append)+
	moreover have "\<forall>n \<in> \<Union>((parse_var_edges \<circ> parse_nodes) [(length xs, x)]). fst n = length xs"
		unfolding parse_var_edges_def by fastforce
	ultimately have "\<Union>((parse_var_edges \<circ> parse_nodes) (zip [0..<length xs] xs)) \<inter> \<Union>((parse_var_edges \<circ> parse_nodes) [(length xs, x)]) = {}"
		by fastforce

	thus ?case using rewrite by simp
qed


lemma total_node_count:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card ((snd \<circ> parse \<circ> tag) expr) = 6 * length expr"
	using assms
proof (induction expr rule: rev_induct)
  case Nil
  thus ?case unfolding parse_def parse_var_edges_def tag_def by simp
next
  case (snoc c expr)
  hence card_c: "card c = 3"
  	by simp

	let ?x = "fst (pop c)"
	let ?y = "fst (pop (snd (pop c)))"
	let ?z = "fst (pop (snd (pop (snd (pop c)))))"
	let ?n = "length expr"
	have expand: "(parse_var_edges \<circ> parse_nodes) ((length expr, c) # []) = {{(?n, (Pos \<circ> ident) ?x, ?x), (?n, (Neg \<circ> ident) ?x, ?x)}, {(?n, (Pos \<circ> ident) ?y, ?y), (?n, (Neg \<circ> ident) ?y, ?y)}, {(?n, (Pos \<circ> ident) ?z, ?z), (?n, (Neg \<circ> ident) ?z, ?z)}}"
		unfolding parse_var_edges_def using card_c by (auto split: prod.splits)
	hence "\<Union>((parse_var_edges \<circ> parse_nodes) ((length expr, c) # [])) = {(?n, (Pos \<circ> ident) ?x, ?x), (?n, (Neg \<circ> ident) ?x, ?x), (?n, (Pos \<circ> ident) ?y, ?y), (?n, (Neg \<circ> ident) ?y, ?y), (?n, (Pos \<circ> ident) ?z, ?z), (?n, (Neg \<circ> ident) ?z, ?z)}"
		by auto
	moreover have 1: "?x \<noteq> ?y"
		using assms pop_card pop_ins pop_isin card_c
		by (metis One_nat_def card.empty card.infinite insert_absorb n_not_Suc_n numeral_3_eq_3 numeral_eq_one_iff old.nat.distinct(1) semiring_norm(84))
	moreover have 2: "?y \<noteq> ?z"
		using assms pop_card pop_ins pop_isin card_c
		by (metis One_nat_def card.empty card.infinite insert_absorb n_not_Suc_n numeral_3_eq_3 numeral_eq_one_iff old.nat.distinct(1) semiring_norm(84))
	moreover have 3: "?x \<noteq> ?z"
		using expand card_c var_edge_card_single
		by (smt card.empty card_insert_if finite.emptyI finite.insertI insertCI nat.inject nat.simps(3) numeral_3_eq_3)
	ultimately have card_last: "card (\<Union>((parse_var_edges \<circ> parse_nodes) ((length expr, c) # []))) = 6"
		by simp

  have card_hyp: "card ((snd \<circ> parse \<circ> tag) expr) = 6 * length expr"
  	apply (rule snoc.IH) using snoc.prems by simp


  have "(parse_nodes \<circ> tag) (expr @ [c]) = (parse_nodes \<circ> tag) expr \<union> parse_nodes ((length expr, c) # [])"
  	using tag_def tag_len parse_nodes_zip
  	by (smt comp_apply diff_zero length_0_conv length_append_singleton length_upt upt_Suc zip_Cons_Cons)
  hence "(parse_var_edges \<circ> parse_nodes \<circ> tag) (expr @ [c]) = (parse_var_edges \<circ> parse_nodes \<circ> tag) expr \<union> (parse_var_edges \<circ> parse_nodes) ((length expr, c) # [])"
  	using parse_var_edges_split by force
  moreover have "(parse_var_edges \<circ> parse_nodes \<circ> tag) expr \<inter> (parse_var_edges \<circ> parse_nodes) ((length expr, c) # []) = {}"
  	using parse_node_disj parse_var_disj snoc.prems tag_def
  	by (metis butlast_snoc comp_apply last_snoc)
  ultimately have "\<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) (expr @ [c])) = \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<union> \<Union>((parse_var_edges \<circ> parse_nodes) ((length expr, c) # []))"
  	by blast

  moreover have "\<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<inter> \<Union>((parse_var_edges \<circ> parse_nodes) ((length expr, c) # [])) = {}"
  	using parse_un_disj snoc.prems tag_def
  	by (metis butlast_snoc comp_apply last_snoc)

  ultimately have "card (\<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) (expr @ [c]))) = card (\<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)) + card (\<Union>((parse_var_edges \<circ> parse_nodes) ((length expr, c) # [])))"
  	using card_set_disj parallel_edge_card parse_var_card snoc.prems
  	by (smt append_is_Nil_conv card_gt_0_iff comp_apply finite_Union length_greater_0_conv list.distinct(1) nat_0_less_mult_iff zero_less_numeral)
  also have "... = card (\<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)) + 6"
  	by (subst card_last, rule refl)
  also have "... = card ((snd \<circ> parse \<circ> tag) expr) + 6"
  	by (metis comp_apply parse_def snd_conv)
  also have "... = 6 * length expr + 6"
  	by (subst card_hyp, rule refl)
  also have "... = 6 * length (expr @ [c])"
  	by simp
  finally show ?case
  	by (metis comp_apply parse_def snd_conv)
qed

lemma card_parse_nodes_single: "card c = 3 \<Longrightarrow> card (parse_nodes ((n, c) # [])) = card ((parse_nodes \<circ> tag) (c # []))"
	unfolding tag_def by (simp add: card_insert_if split: prod.splits)


lemma var_edge_card_single_eq: "card c = 3 \<Longrightarrow> card ((parse_var_edges \<circ> parse_nodes) ((n, c) # [])) = card ((parse_var_edges \<circ> parse_nodes \<circ> tag) (c # []))"
	unfolding tag_def using card_parse_nodes_single var_edge_card_single var_edge_card_single_alt by (fastforce split: prod.splits)

lemma clause_edge_card_single_eq: "card c = 3 \<Longrightarrow> card (parse_clause_edges ((n, c) # [])) = card ((parse_clause_edges \<circ> tag) (c # []))"
	unfolding tag_def by (auto simp add: card_insert_if doubleton_eq_iff split: prod.splits)

lemma
	assumes "\<forall>c \<in> set expr. card (snd c) = 3"
	shows "card (parse_edges expr (parse_nodes expr)) = card ((parse_var_edges \<circ> parse_nodes) expr) + card (parse_clause_edges expr)"
	using assms var_clause_edge_disj_alt 

lemma parse_edge_card_single:
	assumes "card c = 3"
	shows "card (parse_edges (tag (c # [])) ((parse_nodes \<circ> tag) (c # []))) = card (parse_edges ((n, c) # []) (parse_nodes ((n, c) # [])))"
	using assms
proof -
	have fin: "finite (parse_var_edges (parse_nodes [(n, c)]) \<union> parse_clause_edges [(n, c)])"
		using assms using clause_edge_card_single_eq var_edge_card_eq var_edge_card_single var_edge_card_single_eq
		by (smt card.infinite comp_apply finite_Un list.distinct(1) list.set_cases set_ConsD zero_neq_numeral)

	have "card (parse_edges (tag (c # [])) ((parse_nodes \<circ> tag) (c # []))) = card (parse_edges ((0, c) # []) (parse_nodes ((0, c) # [])))"
		unfolding tag_def by simp
	also have "... = card ((parse_var_edges \<circ> parse_nodes) ((0, c) # [])) + card (parse_clause_edges ((0, c) # []))"
		using assms calculation clause_edge_card_single_eq var_edge_card_single triangle_edge_card total_edge_count
		by (metis One_nat_def add.commute list.distinct(1) list.set_cases list.size(3) list.size(4) nat_mult_1_right numeral_Bit0 plus_1_eq_Suc set_ConsD)
	also have "... = card ((parse_var_edges \<circ> parse_nodes) ((n, c) # [])) + card (parse_clause_edges ((n, c) # []))"
		using assms var_edge_card_single_eq clause_edge_card_single_eq by metis
	also have "... = card (parse_edges ((n, c) # []) (parse_nodes ((n, c) # [])))"
		unfolding parse_edges_def
		apply (rule card_set_disj[symmetric, of "parse_var_edges (parse_nodes [(n, c)]) \<union> parse_clause_edges [(n, c)]" "(parse_var_edges \<circ> parse_nodes) [(n, c)]" "parse_clause_edges [(n, c)]"])
		subgoal apply (rule fin) done
		subgoal apply (subst o_apply) apply (rule refl) done
		subgoal apply (rule var_clause_edge_disj) done
		done
	finally show ?thesis .
qed
	

lemma full_parse_split: "parse (xs @ ys) = ((fst \<circ> parse) xs \<union> (fst \<circ> parse) ys, (snd \<circ> parse) xs \<union> (snd \<circ> parse) ys)"
	unfolding parse_def tag_def parse_edges_def
	by (auto simp add: Let_def parse_var_edges_split parse_nodes_split parse_clause_edges_split)

lemma "parse_var_edges (parse_nodes expr)"


lemma "\<lbrakk> nae3sat expr; c1 \<in> cutset (fst ((parse \<circ> tag) expr)) S T; c2 \<in> cutset (fst ((parse \<circ> tag) expr)) S T \<rbrakk>
				\<Longrightarrow> c1 \<inter> c2 = {}"
	unfolding nae3sat_def naesat_def nae_models_def cutset_def parse_def tag_def parse_edges_def

lemma "length expr > 0 \<Longrightarrow> card (cutset (fst ((parse \<circ> tag) expr)) S T)
				= card (cutset (fst ((parse \<circ> tag) (hd expr # []))) S T) + card (cutset (fst ((parse \<circ> tag) (tl expr))) S T)"
proof (induction "length expr" arbitrary: expr S T)
  case 0
  thus ?case by simp
next
  case (Suc n)
  then show ?case sorry
qed
  case Nil
  thus ?case by (simp add: cutset_def parse_def tag_def parse_edges_def parse_var_edges_def)
next
  case (Cons a expr)
  thm Cons.IH
  hence "card (cutset (fst ((parse \<circ> tag) (a # expr))) ?S ?T) =
  card (cutset (fst ((parse \<circ> tag) [?a])) ?S ?T) + card (cutset (fst ((parse \<circ> tag) expr)) ?S ?T)"

  then show ?case sorry
qed


lemma "card (cutset (fst ((parse \<circ> tag) [])) S T) = 0"
	unfolding cutset_def parse_def tag_def parse_edges_def parse_var_edges_def
	by (simp add: Let_def)

lemma "nae3sat (a # expr) \<Longrightarrow> 5 + card (cutset (fst ((parse \<circ> tag) expr)) S T) = card (cutset (fst ((parse \<circ> tag) (a # expr))) S T)"
	unfolding cutset_def parse_def tag_def parse_edges_def parse_var_edges_def nae3sat_def
	apply (induction expr arbitrary: a S T)
	 apply (simp add: Let_def)
	


lemma "5 + card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) = card (cutset ((fst \<circ> parse \<circ> tag) (a # expr)) S T)"
	unfolding parse_def tag_def cutset_def parse_edges_def parse_var_edges_def
	apply (induction expr arbitrary: a S T)
	 apply (simp add: Let_def)

lemma cutset_split: "cutset (E1 \<union> E2) S T = cutset E1 S T \<union> cutset E2 S T"
	unfolding cutset_def by blast


lemma aux: "\<forall>n \<in> \<Union>(parse_clause_edges expr). \<exists>v x. n = (v, (Pos \<circ> ident) x, x) \<or> n = (v, (Neg \<circ> ident) x, x)"
	apply (induction expr, auto)
	prefer 7 apply fastforce
	by (metis ident.elims)+

lemma clause_edges_subset: "\<Union>(parse_clause_edges expr) \<subseteq> snd (parse expr)"
	unfolding parse_def
	apply (induction expr)
  apply (auto simp add: Let_def parse_var_edges_def)
	apply (metis (no_types, lifting) ident.elims insertCI)+
	by (smt Union_iff mem_Collect_eq subsetD)

lemma var_edges_subset: "\<Union>((parse_var_edges \<circ> parse_nodes) expr) \<subseteq> snd (parse expr)"
	unfolding parse_def
	by (induction expr) (auto simp add: Let_def split: prod.splits)

lemma edges_subset: "\<Union>(fst (parse expr)) \<subseteq> snd (parse expr)"
	unfolding parse_def parse_edges_def apply (simp add: Let_def)
	using clause_edges_subset by (metis parse_def snd_conv)

lemma edges_subset_alt: "snd (parse expr) \<subseteq> \<Union>(fst (parse expr))"
	unfolding parse_def parse_edges_def by (simp add: Let_def)

lemma no_island_nodes: "\<Union>(fst (parse expr)) = snd (parse expr)"
	using edges_subset edges_subset_alt by blast

lemma var_edge_lift: "\<forall>vmap. \<forall>e \<in> (parse_var_edges expr). \<exists>a b. e = {a, b} \<and> (vmap\<up>) ((fst \<circ> snd) a) \<and> \<not>(vmap\<up>) ((fst \<circ> snd) b)"
	unfolding parse_var_edges_def apply simp
	by (metis doubleton_eq_iff ex_mid_lift)

lemma var_edge_cut: "\<forall>vmap. \<forall>e \<in> (parse_var_edges expr). \<exists>a b. e = {a, b} \<and> a \<in> {(n, l, t). (n, l, t) \<in> \<Union>(parse_var_edges expr) \<and> (vmap\<up>) l} \<and> b \<in> {(n, l, t). (n, l, t) \<in> \<Union>(parse_var_edges expr) \<and> \<not>(vmap\<up>) l}"
	unfolding parse_var_edges_def apply simp
	using var_edge_lift ex_mid_lift by (smt ex_mid_lift insertCI insert_commute)

lemma var_edge_cut_subset: "c \<subseteq> expr \<Longrightarrow> \<forall>vmap. \<forall>e \<in> (parse_var_edges c). \<exists>a b. e = {a, b} \<and> a \<in> {(n, l, t). (n, l, t) \<in> \<Union>(parse_var_edges expr) \<and> (vmap\<up>) l} \<and> b \<in> {(n, l, t). (n, l, t) \<in> \<Union>(parse_var_edges expr) \<and> \<not>(vmap\<up>) l}"
	using var_edge_cut parse_var_edges_subset by blast

value "take 2 [0::nat, 1, 2, 3, 4]"
value "drop 2 [0::nat, 1, 2, 3, 4]"

lemma tag_split: "n < length expr \<Longrightarrow> [0 ..< length expr] = [0 ..< n] @ [n ..< length expr]"
	by (induction expr arbitrary: n) (auto split: if_splits simp add: less_Suc_eq)

lemma drop_nth: "n < length expr \<Longrightarrow> drop n expr = expr ! n # drop (Suc n) expr"
	apply (induction expr arbitrary: n)
	 apply auto
	using less_Suc_eq_0_disj by fastforce

lemma clause_triangle:
	assumes "nae3sat expr" "c = expr ! n" "n < length expr" "vmap \<turnstile> expr"
	shows "\<exists>n1 n2 n3. parse_clause_edges ((n, c) # []) = {{n1, n2}, {n2, n3}, {n3, n1}}
					\<and> (n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l} \<and> n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l} \<and> n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l} 
					\<or> n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l} \<and> n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l} \<and> n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l})"
	using assms
proof -
	have c_expr: "c \<in> set expr"
		using assms(2-3) by simp
	hence card_c: "card c = 3"
		using assms(1) unfolding nae3sat_def by blast
	hence "card (parse_clause_edges ((n, c) # [])) = 3"
		using clause_edge_card_single_eq parallel_edge_card_single var_edge_card_eq
		by (metis list.distinct(1) list.set_cases set_ConsD)

	hence "\<exists>n1 n2 n3. parse_clause_edges ((n, c) # []) = {{n1, n2}, {n2, n3}, {n3, n1}}"
		by (simp split: prod.splits, blast)
	hence "\<exists>l1 l2 l3. parse_clause_edges ((n, c) # []) = {{(n, l1, l1), (n, l2, l2)}, {(n, l2, l2), (n, l3, l3)}, {(n, l3, l3), (n, l1, l1)}}"
		by (auto split: prod.splits)
	hence expand_clause: "\<exists>l1 l2 l3. c = {l1, l2, l3} \<and> parse_clause_edges ((n, c) # []) = {{(n, l1, l1), (n, l2, l2)}, {(n, l2, l2), (n, l3, l3)}, {(n, l3, l3), (n, l1, l1)}}"
		using assms apply (auto split: prod.splits)
		using card_c pop_card pop_ins 
		by (smt Suc_inject card.empty card.infinite finite_insert fst_conv nat.simps(3) numeral_3_eq_3 snd_conv)

	have "nae3sat (c # [])"
		using assms(1) c_expr unfolding nae3sat_def naesat_def nae_models_def by fastforce
	hence "\<exists>l1 l2 l3. c = {l1, l2, l3} \<and> (vmap\<up>) l3 \<noteq> (vmap\<up>) l1 \<and> (vmap\<up>) l3 \<noteq> (vmap\<up>) l2"
		using assms(4) expand_clause c_expr unfolding nae3sat_def naesat_def nae_models_def
		by (smt insertE insert_commute singletonD)

	hence "\<exists>l1 l2 l3. c = {l1, l2, l3} \<and> (vmap\<up>) l3 \<noteq> (vmap\<up>) l1 \<and> (vmap\<up>) l3 \<noteq> (vmap\<up>) l2
					\<and> parse_clause_edges ((n, c) # []) = {{(n, l1, l1), (n, l2, l2)}, {(n, l2, l2), (n, l3, l3)}, {(n, l3, l3), (n, l1, l1)}}"
		using expand_clause by (smt insertE insertI1 insert_commute singletonD)

	then obtain l1 l2 l3 where clause: "c = {l1, l2, l3}" and nae: "(vmap\<up>) l3 \<noteq> (vmap\<up>) l1 \<and> (vmap\<up>) l3 \<noteq> (vmap\<up>) l2"
		and clause_edges: "parse_clause_edges ((n, c) # []) = {{(n, l1, l1), (n, l2, l2)}, {(n, l2, l2), (n, l3, l3)}, {(n, l3, l3), (n, l1, l1)}}"
		by force

	define n1 n2 n3 where n1: "n1 = (n, l1, l1)" and n2: "n2 = (n, l2, l2)" and n3: "n3 = (n, l3, l3)"

	hence triangle: "parse_clause_edges ((n, c) # []) = {{n1, n2}, {n2, n3}, {n3, n1}}"
		using clause_edges n1 n2 n3 by meson

	hence lift_two: "(vmap\<up>) ((fst \<circ> snd) n1) \<and> (vmap\<up>) ((fst \<circ> snd) n2) \<or> \<not>(vmap\<up>) ((fst \<circ> snd) n1) \<and> \<not>(vmap\<up>) ((fst \<circ> snd) n2)"
		using parallel_edge_card_single assms n1 n2 nae unfolding nae3sat_def naesat_def nae_models_def by auto

	show "\<exists>n1 n2 n3. parse_clause_edges ((n, c) # []) = {{n1, n2}, {n2, n3}, {n3, n1}}
					\<and> (n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l} \<and> n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l} \<and> n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}
					\<or> n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l} \<and> n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l} \<and> n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l})"
	proof (intro exI conjI)
		show "parse_clause_edges ((n, c) # []) = {{n1, n2}, {n2, n3}, {n3, n1}}"
			using triangle .
	next
		consider (two_true) "(vmap\<up>) ((fst \<circ> snd) n1) \<and> (vmap\<up>) ((fst \<circ> snd) n2)"
			| (two_false) "\<not>(vmap\<up>) ((fst \<circ> snd) n1) \<and> \<not>(vmap\<up>) ((fst \<circ> snd) n2)"
			using lift_two by blast
		thus "n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l}
    			\<and> n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l}
    			\<and> n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}
    			\<or> n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}
    			\<and> n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}
    			\<and> n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l}"
    proof cases
    	case two_true
    	have "l1 = (fst \<circ> snd) n1"
    		using n1 by simp
    	moreover from this have "(vmap\<up>) l1"
    		using two_true by blast
    	ultimately have n1_vmap: "n1 \<in> {(n, l, t). (vmap\<up>) l}"
    		by force

    	have "l2 = (fst \<circ> snd) n2"
    		using n2 by simp
    	moreover from this have "(vmap\<up>) l2"
    		using two_true by blast
    	ultimately have n2_vmap: "n2 \<in> {(n, l, t). (vmap\<up>) l}"
    		by force

    	have n3_vmap: "n3 \<in> {(n, l, t). \<not>(vmap\<up>) l}"
    		using nae n3 \<open>(vmap\<up>) l1\<close> by simp

    	have "drop n expr = c # (drop (Suc n) expr)"
    		using assms(2-3) by (simp add: drop_nth)
    	hence zip_drop_cons: "zip [n ..< length expr] (drop n expr) = (n, c) # (zip [Suc n ..< length expr] (drop (Suc n) expr))"
    		by (simp add: assms(3) upt_conv_Cons)

    	have "(parse_clause_edges \<circ> tag) expr = parse_clause_edges (zip [0 ..< n] (take n expr)) \<union> parse_clause_edges (zip [n ..< length expr] (drop n expr))"
    		apply (insert assms(3), subst comp_apply, subst tag_def)
    		apply (subst tag_split[of n])
    		subgoal by assumption
    		apply (subst (6) append_take_drop_id[symmetric, of _ n])
    		apply (rule parse_clause_edges_zip)
    		apply (subst length_upt, subst minus_nat.diff_0, subst length_take, subst min.absorb4)
    		by (assumption, rule refl)
    	moreover have "... = parse_clause_edges (zip [0 ..< n] (take n expr)) \<union> parse_clause_edges ((n, c) # []) \<union> parse_clause_edges (zip [Suc n ..< length expr] (drop (Suc n) expr))"
    		apply (subst zip_drop_cons)
    		apply (subst parse_clause_edges_cons)
    		by (subst Un_assoc, rule refl)
    	ultimately have c_subset: "parse_clause_edges ((n, c) # []) \<subseteq> (parse_clause_edges \<circ> tag) expr"
    		by blast

    	hence "\<Union>(parse_clause_edges ((n, c) # [])) \<subseteq> \<Union>((parse_clause_edges \<circ> tag) expr)"
    		by blast
    	moreover have "\<Union>((parse_clause_edges \<circ> tag) expr) \<subseteq> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
    		using edges_subset unfolding parse_def parse_edges_def by (auto simp add: Let_def)
    	moreover have "n1 \<in> \<Union>((parse_clause_edges \<circ> tag) expr)"
    						and "n2 \<in> \<Union>((parse_clause_edges \<circ> tag) expr)"
								and "n3 \<in> \<Union>((parse_clause_edges \<circ> tag) expr)"
    		using triangle c_subset by blast+
    	ultimately have n1_isin: "n1 \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
    							and n2_isin: "n2 \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
									and n3_isin: "n3 \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
    		by blast+

    	have "n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l}"
    		using n1_isin n1_vmap by auto
    	moreover have "n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l}"
    		using n2_isin n2_vmap by auto
    	moreover have "n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}"
    		using n3_isin n3_vmap by auto
    	ultimately show ?thesis by blast
    next
    	case two_false
    	have "l1 = (fst \<circ> snd) n1"
    		using n1 by simp
    	moreover from this have "\<not>(vmap\<up>) l1"
    		using two_false by blast
    	ultimately have n1_vmap: "n1 \<in> {(n, l, t). \<not>(vmap\<up>) l}"
    		by force

    	have "l2 = (fst \<circ> snd) n2"
    		using n2 by simp
    	moreover from this have "\<not>(vmap\<up>) l2"
    		using two_false by blast
    	ultimately have n2_vmap: "n2 \<in> {(n, l, t). \<not>(vmap\<up>) l}"
    		by force

    	have n3_vmap: "n3 \<in> {(n, l, t). (vmap\<up>) l}"
    		using nae n3 \<open>\<not>(vmap\<up>) l1\<close> by simp

    	have "drop n expr = c # (drop (Suc n) expr)"
    		using assms(2-3) by (simp add: drop_nth)
    	hence zip_drop_cons: "zip [n ..< length expr] (drop n expr) = (n, c) # (zip [Suc n ..< length expr] (drop (Suc n) expr))"
    		by (simp add: assms(3) upt_conv_Cons)

    	have "(parse_clause_edges \<circ> tag) expr = parse_clause_edges (zip [0 ..< n] (take n expr)) \<union> parse_clause_edges (zip [n ..< length expr] (drop n expr))"
    		apply (insert assms(3), subst comp_apply, subst tag_def)
    		apply (subst tag_split[of n])
    		subgoal by assumption
    		apply (subst (6) append_take_drop_id[symmetric, of _ n])
    		apply (rule parse_clause_edges_zip)
    		apply (subst length_upt, subst minus_nat.diff_0, subst length_take, subst min.absorb4)
    		by (assumption, rule refl)
    	moreover have "... = parse_clause_edges (zip [0 ..< n] (take n expr)) \<union> parse_clause_edges ((n, c) # []) \<union> parse_clause_edges (zip [Suc n ..< length expr] (drop (Suc n) expr))"
    		apply (subst zip_drop_cons)
    		apply (subst parse_clause_edges_cons)
    		by (subst Un_assoc, rule refl)
    	ultimately have c_subset: "parse_clause_edges ((n, c) # []) \<subseteq> (parse_clause_edges \<circ> tag) expr"
    		by blast

    	hence "\<Union>(parse_clause_edges ((n, c) # [])) \<subseteq> \<Union>((parse_clause_edges \<circ> tag) expr)"
    		by blast
    	moreover have "\<Union>((parse_clause_edges \<circ> tag) expr) \<subseteq> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
    		using edges_subset unfolding parse_def parse_edges_def by (auto simp add: Let_def)
    	moreover have "n1 \<in> \<Union>((parse_clause_edges \<circ> tag) expr)"
    						and "n2 \<in> \<Union>((parse_clause_edges \<circ> tag) expr)"
    						and "n3 \<in> \<Union>((parse_clause_edges \<circ> tag) expr)"
    		using triangle c_subset by blast+
    	ultimately have n1_isin: "n1 \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
									and n2_isin: "n2 \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
									and n3_isin: "n3 \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr)"
    		by blast+

    	have "n1 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}"
    		using n1_isin n1_vmap by auto
    	moreover have "n2 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}"
    		using n2_isin n2_vmap by auto
    	moreover have "n3 \<in> {(n, l, t). (n, l, t) \<in> \<Union>((parse_var_edges \<circ> parse_nodes \<circ> tag) expr) \<and> (vmap\<up>) l}"
    		using n3_isin n3_vmap by auto
    	ultimately show ?thesis by blast
    qed
  qed
qed

find_theorems "?A \<subseteq> ?B \<Longrightarrow> card ?A \<le> card ?B"

lemma "a = {u, v} \<Longrightarrow> {{u, v} |u v. ({u, v} = a \<or> {u, v} \<in> A) \<and> u \<in> S \<and> v \<in> T} =
						(if u \<in> S \<and> v \<in> T \<or> v \<in> S \<and> u \<in> T then insert a {{u, v} |u v. {u, v} \<in> A \<and> u \<in> S \<and> v \<in> T} else {{u, v} |u v. {u, v} \<in> A \<and> u \<in> S \<and> v \<in> T})"
	by (auto simp add: doubleton_eq_iff)

thm finite_insert
lemma finite_cutset:
	assumes "finite E"
	shows "finite (cutset E S T)"
	using assms unfolding cutset_def
proof (induction E)
  case empty
  thus ?case by simp
next
  case (insert a F)
  then consider (cut) "\<exists>u v. a = {u, v} \<and> u \<in> S \<and> v \<in> T"
  	| (noncut) "\<nexists>u v. a = {u, v} \<and> u \<in> S \<and> v \<in> T"
  	by blast
  thus ?case
  proof cases
  	case cut
  	hence "{{u, v} |u v. {u, v} \<in> insert a F \<and> u \<in> S \<and> v \<in> T} = insert a {{u, v} |u v. {u, v} \<in> F \<and> u \<in> S \<and> v \<in> T}"
  		by blast
  	moreover have "finite (insert a {{u, v} |u v. {u, v} \<in> F \<and> u \<in> S \<and> v \<in> T})"
  		by (insert insert(3), subst finite_insert, assumption)
  	ultimately show ?thesis by simp
  next
  	case noncut
  	hence "{{u, v} |u v. {u, v} \<in> insert a F \<and> u \<in> S \<and> v \<in> T} = {{u, v} |u v. {u, v} \<in> F \<and> u \<in> S \<and> v \<in> T}"
  		by blast
  	thus ?thesis using insert by simp
  qed
qed

lemma cutset_disj:
	assumes "E1 \<inter> E2 = {}"
	shows "cutset E1 S T \<inter> cutset E2 S T = {}"
	using assms unfolding cutset_def by auto

lemma cutset_disj_s: "\<lbrakk> S \<inter> T = {}; s \<inter> S = {} \<rbrakk> \<Longrightarrow> cutset E s T \<inter> cutset E S T = {}"
	unfolding cutset_def by (smt disjoint_iff doubleton_eq_iff mem_Collect_eq)

lemma cutset_disj_t: "\<lbrakk> S \<inter> T = {}; t \<inter> T = {} \<rbrakk> \<Longrightarrow> cutset E S t \<inter> cutset E S T = {}"
	unfolding cutset_def by (smt disjoint_iff doubleton_eq_iff mem_Collect_eq)

lemma cutset_disj_all: "\<lbrakk> S \<inter> T = {}; s \<inter> S = {}; t \<inter> T = {}; e \<inter> E = {} \<rbrakk> \<Longrightarrow> cutset e s t \<inter> cutset E S T = {}"
	unfolding cutset_def by (smt disjoint_iff doubleton_eq_iff mem_Collect_eq)


lemma disj_un_empty: "\<lbrakk> A \<inter> B = {}; C \<inter> D = {}; A \<inter> C = {}; B \<inter> D = {}; A \<inter> D = {}; B \<inter> C = {} \<rbrakk> \<Longrightarrow> (A \<union> B) \<inter> (C \<union> D) = {}"
	by auto

lemma parse_edges_disj:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "parse_edges [(length (butlast expr), last expr)] (parse_nodes [(length (butlast expr), last expr)]) \<inter> parse_edges (tag (butlast expr)) (parse_nodes (tag (butlast expr))) = {}"
	using assms unfolding parse_edges_def
	apply (subst disj_un_empty)
	subgoal apply (subst comp_apply[symmetric, of parse_var_edges parse_nodes])
		by (subst var_clause_edge_disj, rule refl)
	subgoal apply (subst comp_apply[symmetric, of parse_var_edges parse_nodes])
		by (subst var_clause_edge_disj, rule refl)
	subgoal apply (subst parse_var_disj)
		subgoal apply (subst tag_def, subst Int_commute)
			by (erule parse_node_disj)
		subgoal by (rule refl).
	subgoal apply (subst tag_def, subst Int_commute)
		by (erule parse_edge_disj)
	subgoal using clause_edge_trait var_edge_trait by fastforce
	subgoal using clause_edge_trait var_edge_trait by fastforce
	subgoal by (rule refl).

lemma cutset_filter: "cutset E S T = Set.filter (\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T) E"
	unfolding cutset_def by fastforce

lemma cutset_un_disj:
	assumes "\<forall>x \<in> s. \<forall>y \<in> T. {x, y} \<notin> E" "\<forall>x \<in> S. \<forall>y \<in> t. {x, y} \<notin> E"
	shows "cutset E (s \<union> S) (t \<union> T) = cutset E S T \<union> cutset E s t"
proof (rule ccontr)
	assume "cutset E (s \<union> S) (t \<union> T) \<noteq> cutset E S T \<union> cutset E s t"
	hence "\<exists>x. x \<in> cutset E (s \<union> S) (t \<union> T) \<and> x \<notin> cutset E S T \<union> cutset E s t \<or> x \<notin> cutset E (s \<union> S) (t \<union> T) \<and> x \<in> cutset E S T \<union> cutset E s t"
		by blast
	then consider (left) "\<exists>u v. {u, v} \<in> cutset E (s \<union> S) (t \<union> T) \<and> {u, v} \<notin> cutset E S T \<union> cutset E s t"
		| (right) "\<exists>u v. {u, v} \<notin> cutset E (s \<union> S) (t \<union> T) \<and> {u, v} \<in> cutset E S T \<union> cutset E s t"
		using cutset_def by (smt UnE mem_Collect_eq)
	thus "False"
	proof cases
		case left
		hence "\<exists>u v. {u, v} \<in> Set.filter (\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> s \<union> S \<and> v \<in> t \<union> T) E
						\<and> {u, v} \<notin> (Set.filter (\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T) E) \<union> (Set.filter (\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> s \<and> v \<in> t) E)"
			using cutset_filter by blast
		hence "\<exists>u v. {u, v} \<in> E \<and> (\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> s \<union> S \<and> v \<in> t \<union> T) {u, v}
						\<and> ({u, v} \<notin> E \<or> \<not>(\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T) {u, v})
						\<and> ({u, v} \<notin> E \<or> \<not>(\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> s \<and> v \<in> t) {u, v})"
			by auto
		hence "\<exists>u v. {u, v} \<in> E \<and> u \<in> s \<union> S \<and> v \<in> t \<union> T
						\<and> ({u, v} \<notin> E \<or> \<not>(\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T) {u, v})
						\<and> ({u, v} \<notin> E \<or> \<not>(\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> s \<and> v \<in> t) {u, v})"
			by metis
		hence "\<exists>u v. {u, v} \<in> E \<and> u \<in> s \<union> S \<and> v \<in> t \<union> T
						\<and> ({u, v} \<notin> E \<or> u \<notin> S \<or> v \<notin> T)
						\<and> ({u, v} \<notin> E \<or> u \<notin> s \<or> v \<notin> t)"
			by metis
		hence "\<exists>u v. {u, v} \<in> E \<and> u \<in> s \<union> S \<and> v \<in> t \<union> T
						\<and> (u \<notin> S \<or> v \<notin> T) \<and> (u \<notin> s \<or> v \<notin> t)"
			by blast
		hence "\<exists>u v. {u, v} \<in> E \<and> (u \<in> s \<or> u \<in> S) \<and> (v \<in> t \<or> v \<in> T)
						\<and> (u \<notin> S \<or> v \<notin> T) \<and> (u \<notin> s \<or> v \<notin> t)"
			by simp
		thus "False"
			using assms by auto
	next
		case right
		thus?thesis using assms cutset_def
			by (smt UnCI UnE mem_Collect_eq)
	qed
qed

lemma conj_set_card: "card {x | x. x \<in> A \<and> P} \<le> card A"
	by (smt Collect_empty_eq Orderings.order_eq_iff card_eq_0_iff card_mono mem_Collect_eq subsetI)

lemma "{x | x. x \<in> A \<and> P} \<subseteq> A"
	by blast

find_theorems "card ?A = card ?A1 + card ?A2"


lemma cutset_card:
	assumes "nae3sat expr" "vmap \<turnstile> expr"
	shows "card (cutset ((fst \<circ> parse \<circ> tag) expr) {(n, l, t). (n, l, t) \<in> snd ((parse \<circ> tag) expr) \<and> (vmap\<up>) l} {(n, l, t). (n, l, t) \<in> snd ((parse \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}) = 5 * length expr"
	using assms
proof (induction expr rule: rev_induct)
	case Nil
	thus ?case 
		unfolding cutset_def parse_def parse_edges_def tag_def parse_var_edges_def
		by simp
next
	case (snoc a expr)

	let ?E = "fst ((parse \<circ> tag) expr)"
	let ?V = "snd ((parse \<circ> tag) expr)"

	let ?S = "{a. case a of (n, l, t) \<Rightarrow> (n, l, t) \<in> snd ((parse \<circ> tag) expr) \<and> (vmap\<up>) l}"
	let ?T = "{a. case a of (n, l, t) \<Rightarrow> (n, l, t) \<in> snd ((parse \<circ> tag) expr) \<and> \<not>(vmap\<up>) l}"

	let ?V' = "snd ((parse \<circ> tag) (expr @ [a]))"
	let ?S' = "{(n, l, t). (n, l, t) \<in> ?V' \<and> (vmap\<up>) l}"
	let ?T' = "{(n, l, t). (n, l, t) \<in> ?V' \<and> \<not>(vmap\<up>) l}"

	have "parse_nodes (tag (expr @ [a])) = parse_nodes (tag expr) \<union> parse_nodes [(length expr, a)]"
		unfolding tag_def using parse_nodes_split by auto
	hence "parse_var_edges (parse_nodes (tag (expr @ [a]))) = parse_var_edges (parse_nodes (tag expr)) \<union> parse_var_edges (parse_nodes [(length expr, a)])"
		unfolding tag_def using parse_var_edges_split by metis
	hence parse_var_un: "\<Union>(parse_var_edges (parse_nodes (tag (expr @ [a])))) = \<Union>(parse_var_edges (parse_nodes (tag expr))) \<union> \<Union>(parse_var_edges (parse_nodes [(length expr, a)]))"
		by blast
	
	hence insertS: "?S' = ?S \<union> {(n, l, t). (n, l, t) \<in> snd (parse ((length expr, a) # [])) \<and> (vmap\<up>) l}"
		unfolding parse_def by (auto simp only: Let_def comp_apply snd_conv parse_var_un)
	hence insertT: "?T' = ?T \<union> {(n, l, t). (n, l, t) \<in> snd (parse ((length expr, a) # [])) \<and> \<not>(vmap\<up>) l}"
		unfolding parse_def by (auto simp only: Let_def comp_apply snd_conv parse_var_un)

	have card_a: "card a = 3"
		using nae3sat_def snoc.prems
		by (metis Un_insert_right insertCI list.set(2) set_append)

	have cutset_expand: "cutset ((fst \<circ> parse \<circ> tag) (expr @ [a])) ?S' ?T' = cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T' \<union> cutset ((fst \<circ> parse \<circ> tag) expr) ?S' ?T'"
		unfolding parse_def parse_edges_def tag_def
		by (auto simp add: Let_def cutset_split parse_var_edges_split parse_clause_edges_split parse_nodes_split)

	have fst_parse_expand: "(fst \<circ> parse) ((length expr, a) # []) = (parse_var_edges \<circ> parse_nodes) ((length expr, a) # []) \<union> parse_clause_edges ((length expr, a) # [])"
		unfolding parse_def by (simp add: Let_def parse_edges_def)

	have fst_parse: "(fst \<circ> parse) ((length expr, a) # []) = parse_edges ((length expr, a) # []) (parse_nodes ((length expr, a) # []))"
		unfolding parse_def by (simp add: Let_def)
	have card_parse_edges: "card (parse_edges ((length expr, a) # []) (parse_nodes ((length expr, a) # []))) = card (parse_edges (tag (a # [])) ((parse_nodes \<circ> tag) (a # [])))"
		by (rule parse_edge_card_single[symmetric, of a "length expr"], rule card_a)
	hence card_subgraph: "... = 6"
		using subgraph_edge_count card_a
		by (metis list.distinct(1) list.set_cases list.set_intros(1) set_ConsD)

	have card_var: "card ((parse_var_edges \<circ> parse_nodes) ((length expr, a) # [])) = 3"
		using card_a var_edge_card_single by blast
	hence card_clause: "card (parse_clause_edges ((length expr, a) # [])) = 3"
		using card_a clause_edge_card_single_eq var_edge_card_eq var_edge_card_single_eq
		by (metis list.distinct(1) list.set_cases set_ConsD)

	have "\<Union>(parse_var_edges (parse_nodes (zip [0..<length expr] expr))) \<inter> \<Union>(parse_var_edges (parse_nodes [(length expr, a)])) = {}"
		using parse_un_disj nae3sat_def snoc.prems by fastforce

	have "\<forall>e \<in> parse_var_edges (parse_nodes (zip [0..<length expr] expr)). \<forall>n \<in> e. fst n < length expr"
		using tag_sup_var nae3sat_def snoc.prems
		by (metis Un_iff set_append)
	moreover have "\<forall>e \<in> parse_clause_edges (zip [0..<length expr] expr). \<forall>n \<in> e. fst n < length expr"
		using tag_sup_clause nae3sat_def snoc.prems
		by (metis Un_iff set_append)
	ultimately have "\<forall>e \<in> parse_var_edges (parse_nodes (zip [0..<length expr] expr)) \<union> parse_clause_edges (zip [0..<length expr] expr). \<forall>n \<in> e. fst n < length expr"
		by blast
	hence cutset_edge_trait: "\<forall>e \<in> parse_edges (zip [0..<length expr] expr) (parse_nodes (zip [0..<length expr] expr)). \<forall>n \<in> e. fst n < length expr"
		by (subst parse_edges_def)

	have cutset_extend_edge_trait1: "\<forall>x \<in> {(n, l, t). (n, l, t) \<in> \<Union>(parse_var_edges (parse_nodes [(length expr, a)])) \<and> (vmap\<up>) l}.
				fst x = length expr"
		unfolding parse_var_edges_def by auto
	have cutset_extend_edge_trait2: "\<forall>y \<in> {(n, l, t). (n, l, t) \<in> \<Union>(parse_var_edges (parse_nodes [(length expr, a)])) \<and> \<not>(vmap\<up>) l}.
				fst y = length expr"
		unfolding parse_var_edges_def by auto

	have cutset_expand_alt: "cutset ((fst \<circ> parse \<circ> tag) expr) ?S' ?T' = cutset ((fst \<circ> parse \<circ> tag) expr) ?S ?T \<union> cutset ((fst \<circ> parse \<circ> tag) expr) {(n, l, t). (n, l, t) \<in> ((snd \<circ> parse) ((length expr, a) # [])) \<and> (vmap\<up>) l} {(n, l, t). (n, l, t) \<in> ((snd \<circ> parse) ((length expr, a) # [])) \<and> \<not>(vmap\<up>) l}"
		apply (subst insertS, subst insertT)
		apply (subst cutset_un_disj)
		subgoal unfolding parse_def tag_def Let_def comp_apply fst_conv snd_conv
			using cutset_edge_trait cutset_extend_edge_trait2
			by (smt insertI2 less_not_refl singletonI)
		subgoal unfolding parse_def tag_def Let_def comp_apply fst_conv snd_conv
			using cutset_edge_trait cutset_extend_edge_trait1
			by fastforce
		subgoal apply (subst Un_commute, subst (5 6) comp_apply)
			by simp.

	moreover have "cutset ((fst \<circ> parse \<circ> tag) expr) {(n, l, t). (n, l, t) \<in> ((snd \<circ> parse) ((length expr, a) # [])) \<and> (vmap\<up>) l} {(n, l, t). (n, l, t) \<in> ((snd \<circ> parse) ((length expr, a) # [])) \<and> \<not>(vmap\<up>) l} = {}"
		unfolding cutset_def parse_def tag_def Let_def comp_apply fst_conv snd_conv
		using cutset_edge_trait cutset_extend_edge_trait1
		by (smt Collect_empty_eq insertI1 order_less_irrefl)

	ultimately have cutset_extend_disj: "cutset ((fst \<circ> parse \<circ> tag) expr) ?S ?T = cutset ((fst \<circ> parse \<circ> tag) expr) ?S' ?T'"
		by blast

	have card_V: "card ?V = 6 * length expr"
		apply (subst comp_apply[symmetric, of snd "parse \<circ> tag"], subst comp_assoc[symmetric])
		apply (rule total_node_count)
		using nae3sat_def snoc.prems by (metis Un_iff set_append)
	have "card ?V' = 6 + card ?V"
		apply (subst card_V, subst comp_apply[symmetric, of snd "parse \<circ> tag"], subst comp_assoc[symmetric])
		using total_node_count nae3sat_def snoc.prems by fastforce

	have "\<forall>vmap. \<forall>e \<in> (parse_var_edges \<circ> parse_nodes) ((length expr, a) # []). \<exists>x y. e = {x, y} \<and>
			x \<in> {(n, l, t). (n, l, t) \<in> ?V' \<and> (vmap\<up>) l} \<and> y \<in> {(n, l, t). (n, l, t) \<in> ?V' \<and> \<not>(vmap\<up>) l}"
		apply (subst comp_apply)
		apply (subst comp_apply, subst tag_def, subst parse_def, subst Let_def, subst snd_conv)+
		apply (rule var_edge_cut_subset, rule parse_nodes_subset)
		by simp
	hence "\<forall>vmap. \<forall>e \<in> (parse_var_edges \<circ> parse_nodes) ((length expr, a) # []).
					\<exists>x y. e = {x, y} \<and> x \<in> ?S' \<and> y \<in> ?T'"
		by arith
	hence cutset_parallel: "(parse_var_edges \<circ> parse_nodes) ((length expr, a) # []) \<subseteq> cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T'"
		unfolding cutset_def parse_def parse_edges_def apply (auto simp add: Let_def split: prod.splits) by metis

	hence card_cutset_parallel: "card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T') \<ge> 3"
		apply (subst refl, subst card_var[symmetric])
		apply (rule card_mono)
		subgoal apply (rule finite_cutset) 
			using fst_parse card_parse_edges card_subgraph card.infinite by fastforce
		subgoal by assumption.


	thm clause_triangle
	have "\<exists>n1 n2 n3. parse_clause_edges ((length expr, a) # []) = {{n1, n2}, {n2, n3}, {n3, n1}}
		\<and> (n1 \<in> {(n, l, t). (n, l, t) \<in> ?V' \<and> (vmap\<up>) l} \<and> n2 \<in> {(n, l, t). (n, l, t) \<in> ?V' \<and> (vmap\<up>) l} \<and> n3 \<in> {(n, l, t). (n, l, t) \<in> ?V' \<and> \<not>(vmap\<up>) l} 
		\<or> n1 \<in> {(n, l, t). (n, l, t) \<in> ?V' \<and> \<not>(vmap\<up>) l} \<and> n2 \<in> {(n, l, t). (n, l, t) \<in> ?V' \<and> \<not>(vmap\<up>) l} \<and> n3 \<in> {(n, l, t). (n, l, t) \<in> ?V'\<and> (vmap\<up>) l})"
		apply (subst comp_apply, subst parse_def, subst Let_def, subst snd_conv)+
		apply (subst comp_apply[symmetric, of parse_var_edges parse_nodes])+
		apply (subst comp_apply[symmetric, of "parse_var_edges \<circ> parse_nodes" tag])+
		apply (rule clause_triangle)
		subgoal by (rule snoc.prems)
		subgoal by (rule nth_append_length[symmetric])
		subgoal by simp
		subgoal by (rule snoc.prems(2)).

	then obtain n1 n2 n3 where clause_edges: "parse_clause_edges ((length expr, a) # []) = {{n1, n2}, {n2, n3}, {n3, n1}}"
												and triangle: "(n1 \<in> ?S' \<and> n2 \<in> ?S' \<and> n3 \<in> ?T' \<or> n1 \<in> ?T' \<and> n2 \<in> ?T' \<and> n3 \<in> ?S')" 
		by blast

	moreover have "?S' \<inter> ?T' = {}"
		using ex_mid_lift by fastforce

	ultimately have triangle_base: "{n1, n2} \<notin> cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T'"
		unfolding cutset_def
		by (smt (verit) disjoint_iff empty_iff insert_disjoint(2) mem_Collect_eq)

	have "parse_clause_edges ((length expr, a) # []) \<subseteq> (fst \<circ> parse) [(length expr, a)]"
		unfolding parse_def parse_edges_def by (simp add: Let_def)
	hence "{n2, n3} \<in> (fst \<circ> parse) [(length expr, a)]"
		and "{n3, n1} \<in> (fst \<circ> parse) [(length expr, a)]"
		using clause_edges by fastforce+
	hence triangle_edge2: "{n2, n3} \<in> cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T'"
		and triangle_edge1: "{n3, n1} \<in> cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T'"
		unfolding cutset_def using triangle
		by (smt insert_commute mem_Collect_eq)+

	hence subgraph_subset: "(parse_var_edges \<circ> parse_nodes) ((length expr, a) # []) \<union> {{n2, n3}, {n3, n1}} \<subseteq> cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T'"
		using cutset_parallel by simp

	have cutset_subset: "cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T' \<subseteq> parse_edges [(length expr, a)] (parse_nodes [(length expr, a)])"
		unfolding cutset_def parse_def by (simp add: Let_def split: prod.splits, blast)

	have "card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T') \<le> card (parse_edges [(length expr, a)] (parse_nodes [(length expr, a)]))"
		apply (rule card_mono)
		subgoal using card.infinite card_parse_edges card_subgraph by fastforce
		subgoal by (rule cutset_subset).
	moreover have "... = 6"
		using card_parse_edges card_subgraph by arith
	ultimately have "card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T') \<le> 6"
		by simp

	hence subgraph_eq: "(parse_var_edges \<circ> parse_nodes) ((length expr, a) # []) \<union> {{n2, n3}, {n3, n1}} = cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T'"
		using subgraph_subset cutset_subset fst_parse_expand fst_parse clause_edges triangle_base
		by (smt Un_insert_right subset_antisym subset_insert)
	moreover have subgraph_disj: "(parse_var_edges \<circ> parse_nodes) ((length expr, a) # []) \<inter> {{n2, n3}, {n3, n1}} = {}"
		using var_clause_edge_disj clause_edges by blast
	moreover have "{n2, n3} \<noteq> {n3, n1}"
		using card_clause clause_edges triangle_base triangle_edge1
		by (smt card.empty card_insert_if doubleton_eq_iff finite.emptyI finite.insertI insert_absorb insert_absorb2 n_not_Suc_n numeral_3_eq_3)
	ultimately have cutset_extend_card: "card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T') = 5"
		apply (subst subgraph_eq[symmetric])
		apply (subst card_set_disj[of _ "(parse_var_edges \<circ> parse_nodes) ((length expr, a) # [])" "{{n2, n3}, {n3, n1}}"])
		subgoal apply (subst finite_Un, rule conjI)
			subgoal apply (insert card_var, rule card_ge_0_finite) by simp
			subgoal by simp.
		subgoal by (rule refl)
		subgoal by (rule subgraph_disj)
		by (subst card_var, simp)

	have solve: "card (cutset ((fst \<circ> parse \<circ> tag) (expr @ [a])) ?S' ?T') = card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T' \<union> cutset ((fst \<circ> parse \<circ> tag) expr) ?S' ?T')"
		by (subst cutset_expand, rule refl)
	also have "... = card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T') + card (cutset ((fst \<circ> parse \<circ> tag) expr) ?S' ?T')"
		apply (subst card_set_disj[of _ "cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T'" "cutset ((fst \<circ> parse \<circ> tag) expr) ?S' ?T'"])
		subgoal apply (subst cutset_expand[symmetric], rule finite_cutset)
			apply (subst comp_apply)+ apply (subst parse_def, subst Let_def, subst fst_conv)
			apply (subgoal_tac "card (parse_edges (tag (expr @ [a])) (parse_nodes (tag (expr @ [a])))) = 6 * length (expr @ [a])")
			subgoal using card.infinite by fastforce
			subgoal apply (subst comp_apply[symmetric, of parse_nodes tag])
				apply (rule total_edge_count[of "expr @ [a]"])
				by (insert snoc.prems, subst (asm) nae3sat_def, elim conjE, assumption).
		subgoal by (rule refl)
		subgoal apply (rule cutset_disj)
			apply (subst (2) comp_apply)
			apply (subst comp_apply, subst parse_def, subst Let_def, subst fst_conv)+
			using parse_edges_disj[of "expr @ [a]"] nae3sat_def snoc.prems
			by force
		subgoal by (rule refl).
	also have "... = card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T') + card (cutset ((fst \<circ> parse \<circ> tag) expr) ?S ?T)"
		by (subst cutset_extend_disj, rule refl)
	also have "... = card (cutset ((fst \<circ> parse) ((length expr, a) # [])) ?S' ?T') + 5 * length expr"
		apply (subst snoc.IH)
		subgoal using snoc.prems nae3sat_def nae3sat_tl naesat_rotate_append
			by (metis Cons_eq_appendI append_Nil list.sel(3) rotate1.simps(2) set_rotate1)
		subgoal using snoc.prems nae_models_def
			by (smt append.right_neutral butlast.simps(2) butlast_append in_set_butlastD)
		subgoal by (rule refl).
	also have "... = 5 + 5 * length expr"
		by (subst cutset_extend_card, rule refl)
	finally show ?case
		by simp
qed

lemma
	assumes "nae3sat expr"
	shows "\<exists>S T. cut ((snd \<circ> parse \<circ> tag) expr) S T \<and> card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) \<ge> 5 * length expr \<and> graph ((fst \<circ> parse \<circ> tag) expr) ((snd \<circ> parse \<circ> tag) expr)"
	using assms
proof -
	have "\<exists>vmap. vmap \<turnstile> expr"
		using assms unfolding nae3sat_def naesat_def
		by blast

	then obtain vmap where vmap: "vmap \<turnstile> expr"
		by blast

	define E where E: "E = fst ((parse \<circ> tag) expr)"
	define V where V: "V = snd ((parse \<circ> tag) expr)"

	define S where S: "S = {(n, l, t). (n, l, t) \<in> V \<and> (vmap\<up>) l}"
	define T where T: "T = {(n, l, t). (n, l, t) \<in> V \<and> \<not>(vmap\<up>) l}"

	show ?thesis
	proof (intro exI conjI)
		have "cut V S T"
			unfolding cut_def
		proof (intro conjI)
			have "\<forall>(n, l, t) \<in> V. (vmap\<up>) l \<or> \<not>(vmap\<up>) l"
				by blast
			hence "V = {(n, l, t). (n, l, t) \<in> V \<and> (vmap\<up>) l} \<union> {(n, l, t). (n, l, t) \<in> V \<and> \<not>(vmap\<up>) l}"
				by blast
			thus "V = S \<union> T"
				using S T by blast
		next
			have "\<not>(\<exists>(n, l, t) \<in> V. (vmap\<up>) l \<and> \<not>(vmap\<up>) l)"
				by blast
			hence "{} = {(n, l, t). (n, l, t) \<in> V \<and> (vmap\<up>) l} \<inter> {(n, l, t). (n, l, t) \<in> V \<and> \<not>(vmap\<up>) l}"
				by blast
			thus "{} = S \<inter> T"
				using S T by blast
		qed
		thus "cut ((snd \<circ> parse \<circ> tag) expr) S T"
			using V by simp
	next
		show "5 * length expr \<le> card (cutset ((fst \<circ> parse \<circ> tag) expr) S T)"
			using cutset_card S T V assms vmap by fastforce
	next
		show "graph ((fst \<circ> parse \<circ> tag) expr) ((snd \<circ> parse \<circ> tag) expr)"
			apply (subst graph_def)
			apply (subst comp_apply)+
			apply (intro conjI)
			subgoal 
				apply (subst parse_def)+
				apply (subst Let_def)+
				apply (subst fst_conv)+
				apply (subst parse_edges_def)
				using parse_var_card parse_edge_card assms unfolding nae3sat_def tag_def
				by (metis Un_iff diff_zero length_upt)
			subgoal apply (subst parse_def, subst Let_def, subst fst_conv, subst parse_edges_def)
				using var_edges_subset clause_edges_subset by force
			subgoal apply (subgoal_tac "card ((snd \<circ> parse \<circ> tag) expr) = 6 * length expr")
				subgoal apply (cases "length expr")
					subgoal apply (subst parse_def, subst tag_def, subst parse_var_edges_def, subst Let_def)
						by simp
					subgoal apply (insert card_ge_0_finite)
						using card.infinite by fastforce.
				subgoal apply (rule total_node_count)
					by (insert assms, subst (asm) nae3sat_def, erule (1) conjE).
			.
	qed
qed

lemma cut_subset: "v \<subseteq> V \<Longrightarrow> cut V S T \<Longrightarrow> \<exists>s t. cut v s t"
	unfolding cut_def by auto

lemma cut_subset_spec: "v \<subseteq> V \<Longrightarrow> cut V S T \<Longrightarrow> \<exists>s t. cut v s t \<and> s \<subseteq> S \<and> t \<subseteq> T"
	unfolding cut_def
	by (smt (verit) Int_assoc boolean_algebra.conj_disj_distrib boolean_algebra.conj_zero_right inf.absorb_iff1 inf.cobounded2 inf_sup_aci(3))

lemma disj_un_min: "\<lbrakk> S \<inter> T = {}; s \<subseteq> S; t \<subseteq> T \<rbrakk> \<Longrightarrow> (S - s) \<union> (T - t) = (S \<union> T) - (s \<union> t)"
	by blast

lemma cut_subset_minus:
	assumes "v \<subseteq> V" "cut V S T"
	shows "\<exists>s t. cut v s t \<and> s \<subseteq> S \<and> t \<subseteq> T \<and> cut (V - v) (S - s) (T - t)"
	using assms
proof -
	have "\<exists>s t. cut v s t \<and> s \<subseteq> S \<and> t \<subseteq> T"
		by (insert assms, erule cut_subset_spec)
	then obtain s t where cut: "cut v s t" and s: "s \<subseteq> S" and t: "t \<subseteq> T"
		by blast

	have "(S - s) \<inter> (T - t) = {}"
		using assms(2) unfolding cut_def by blast
	moreover have "(S - s) \<union> (T - t) = V - v"
	proof -
		have "(S - s) \<union> (T - t) = (S \<union> T) - (s \<union> t)"
			apply (insert assms(2) s t, subst (asm) cut_def, elim conjE)
			apply (subst (asm) (2) eq_commute)
			by (erule(2) disj_un_min)
		also have "... = V - v"
			apply (insert assms(2) cut)
			apply (subst (asm) cut_def)+
			apply (elim conjE)
			apply (erule ssubst)+
			by (rule refl)
		finally show ?thesis .
	qed

	ultimately have "cut (V - v) (S - s) (T - t)"
		unfolding cut_def by simp

	thus ?thesis using cut s t by blast
qed

find_theorems cutset inter



lemma "v \<noteq> {} \<Longrightarrow> v \<subseteq> \<Union>E \<Longrightarrow> cut (\<Union>E) S T \<Longrightarrow> \<exists>s t. cut v s t 
				\<and> (\<forall>x \<in> S - s. \<forall>y \<in> t. {x, y} \<notin> E)
				\<and> (\<forall>x \<in> S. \<forall>y \<in> T - t. {x, y} \<notin> E)"

lemma "cut E S T \<Longrightarrow> \<exists>e1 e2 s1 s2 t1 t2.
				E = e1 \<union> e2 \<and> S = s1 \<union> s2 \<and> T = t1 \<union> t2
			\<and> {} = e1 \<inter> e2 \<and> S = s1 \<inter> s2 \<and> T = t1 \<inter> t2
			\<and> cut e1 s1 t1 \<and> cut "

lemma "card (cutset (e1 \<union> e2) (s1 \<union> s2) (t1 \<union> t2)) \<le> card (cutset e1 s1 t1) + card (cutset e2 s2 t2)"
	unfolding cutset_def

	find_theorems cutset
	find_theorems cut



lemma cutset_card_max_fin: "finite E \<Longrightarrow> card (cutset E S T) \<le> card E"
	unfolding cutset_def 
	apply (induction E arbitrary: S T rule: finite.induct)
	 apply auto
	by (smt Collect_mono card_mono finite_insert insert_compr)

lemma cutset_subset: "e \<subseteq> E \<Longrightarrow> cutset e S T \<subseteq> cutset E S T"
	unfolding cutset_def by blast

lemma cutset_increment_card:
	assumes "finite E"
	shows "card (cutset (insert e E) S T) \<le> Suc (card (cutset E S T))"
	using assms
proof (induction E arbitrary: e S T)
  case empty
  hence "card (cutset {e} S T) \<le> card {e}"
  	by (rule cutset_card_max_fin, simp)
  hence "card (cutset {e} S T) \<le> 1"
  	by simp
  moreover have "Suc (card (cutset {} S T)) = 1"
  	unfolding cutset_def by simp
  ultimately show ?case by simp
next
  case (insert x F)
  thm insert.IH
  have hyp: "card (cutset (insert x F) S T) \<le> Suc (card (cutset F S T))"
  	by (rule insert.IH)
  then consider (same) "e \<in> insert x F"
  	| (new) "e \<notin> insert x F"
  	by arith
  thus ?case
  proof cases
  	case same
  	hence "card (cutset (insert e (insert x F)) S T) = card (cutset (insert x F) S T)"
  		by (simp add: insert_absorb)
  	also have "... \<le> Suc (card (cutset (insert x F) S T))"
  		by simp
  	finally show ?thesis.
  next
  	case new
  	then consider (cut) "\<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T"
  		| (noncut) "\<not>(\<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T)"
  		by blast
  	thus ?thesis
  	proof cases
  		case cut
  		hence "e \<in> cutset (insert e (insert x F)) S T"
  			unfolding cutset_def by blast
  		hence "cutset (insert e (insert x F)) S T = (cutset (insert x F) S T) \<union> {e}"
  			unfolding cutset_def using cut by blast
  		hence "card (cutset (insert e (insert x F)) S T) = Suc (card (cutset (insert x F) S T))"
  			using new by (simp add: cutset_filter insert.hyps(1))
  		thus ?thesis by simp
  	next
  		case noncut
  		hence "e \<notin> cutset (insert e (insert x F)) S T"
  			unfolding cutset_def by blast
  		hence "card (cutset (insert e (insert x F)) S T) = card (cutset (insert x F) S T)"
  			unfolding cutset_def by (metis (lifting) insert_iff noncut)
  		also have "... \<le> Suc (card (cutset (insert x F) S T))"
  			by simp
  		finally show ?thesis.
  	qed
  qed
qed

lemma cutset_un_card:
	assumes "finite E"
	shows "card (cutset (e \<union> E) S T) \<le> card (cutset e S T) + card (cutset E S T)"
	using assms cutset_increment_card
	by (simp add: card_Un_le cutset_split)

lemma cutset_subset_s: "s \<subseteq> S \<Longrightarrow> cutset E s T \<subseteq> cutset E S T"
	unfolding cutset_def by auto
lemma cutset_subset_t: "t \<subseteq> T \<Longrightarrow> cutset E S t \<subseteq> cutset E S T"
	unfolding cutset_def by auto

lemma cutset_triangle_card:
	assumes "x \<noteq> y" "y \<noteq> z" "z \<noteq> x" "S \<inter> T = {}"
	shows "card (cutset {{x, y}, {y, z}, {z, x}} S T) \<le> 2"
proof (rule ccontr)
	assume a: "\<not> card (cutset {{x, y}, {y, z}, {z, x}} S T) \<le> 2"
	moreover have fin: "finite {{x, y}, {y, z}, {z, x}}"
		by simp
	moreover have eq3: "card {{x, y}, {y, z}, {z, x}} = 3"
		using assms(1-3) by (simp add: doubleton_eq_iff)
	ultimately have le3: "card (cutset {{x, y}, {y, z}, {z, x}} S T) \<le> 3"
		using cutset_card_max_fin by metis

	hence "card (cutset {{x, y}, {y, z}, {z, x}} S T) = 3"
		using a by arith
(*
	hence "card {{u, v} | u v. {u, v} \<in> {{x, y}, {y, z}, {z, x}} \<and> u \<in> S \<and> v \<in> T} = 3"
		unfolding cutset_def.
*)
	thm cutset_filter
	moreover have filter: "cutset {{x, y}, {y, z}, {z, x}} S T = Set.filter (\<lambda>e. \<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T) {{x, y}, {y, z}, {z, x}}"
		by (rule cutset_filter)
	ultimately have expand: "cutset {{x, y}, {y, z}, {z, x}} S T = {{x, y}, {y, z}, {z, x}}"
		using le3 eq3 fin
		by (smt card_seteq member_filter subsetI)

	hence "\<forall>e \<in> {{x, y}, {y, z}, {z, x}}. \<exists>n1 \<in> e. \<exists>n2 \<in> e. n1 \<in> S \<and> n2 \<in> T"
		by (smt filter insertCI member_filter)
	hence pathing1: "x \<in> S \<and> y \<in> T \<or> y \<in> S \<and> x \<in> T" 
		and pathing2: "y \<in> S \<and> z \<in> T \<or> z \<in> S \<and> y \<in> T"
		and pathing3: "z \<in> S \<and> x \<in> T \<or> x \<in> S \<and> z \<in> T"
		using assms(4) by auto

	then consider (000) "x \<in> S \<and> y \<in> T \<and> y \<in> S \<and> z \<in> T \<and> z \<in> S \<and> x \<in> T"
		| (001) "x \<in> S \<and> y \<in> T \<and> y \<in> S \<and> z \<in> T \<and> x \<in> S \<and> z \<in> T"
		| (010) "x \<in> S \<and> y \<in> T \<and> z \<in> S \<and> y \<in> T \<and> z \<in> S \<and> x \<in> T"
		| (011) "x \<in> S \<and> y \<in> T \<and> z \<in> S \<and> y \<in> T \<and> x \<in> S \<and> z \<in> T"
		| (100) "y \<in> S \<and> x \<in> T \<and> y \<in> S \<and> z \<in> T \<and> z \<in> S \<and> x \<in> T"
		| (101) "y \<in> S \<and> x \<in> T \<and> y \<in> S \<and> z \<in> T \<and> x \<in> S \<and> z \<in> T"
		| (110) "y \<in> S \<and> x \<in> T \<and> z \<in> S \<and> y \<in> T \<and> z \<in> S \<and> x \<in> T"
		| (111) "y \<in> S \<and> x \<in> T \<and> z \<in> S \<and> y \<in> T \<and> x \<in> S \<and> z \<in> T"
		using pathing1 pathing2 pathing3 by metis
	thus "False"
		using assms(4)
	proof cases
	qed blast+
qed

lemma cutset_triangle_extend_card:
	assumes "x \<noteq> y" "y \<noteq> z" "z \<noteq> x" "S \<inter> T = {}" "finite e"
	shows "card (cutset ({{x, y}, {y, z}, {z, x}} \<union> e) S T) \<le> 2 + card (cutset e S T)"
	using assms
proof -
	have "card (cutset ({{x, y}, {y, z}, {z, x}} \<union> e) S T) \<le> card (cutset {{x, y}, {y, z}, {z, x}} S T) + card (cutset e S T)"
		by (insert assms(5), erule cutset_un_card)
	also have "... \<le> 2 + card (cutset e S T)"
		using assms(1-4) by (simp add: cutset_triangle_card)
	finally show ?thesis.
qed

lemma subgraph_cutset_max:
	assumes "card c = 3" "S \<inter> T = {}"
	shows "card (cutset ((fst \<circ> parse) ((n, c) # [])) S T) \<le> 5"
	using assms unfolding parse_def Let_def comp_apply fst_conv parse_edges_def
proof -
	let ?x = "fst (pop c)"
	let ?y = "fst (pop (snd (pop c)))"
	let ?z = "fst (pop (snd (pop (snd (pop c)))))"
	let ?pos = "Pos \<circ> ident"
	let ?neg = "Neg \<circ> ident"

  have expand_nodes: "parse_nodes ((n, c) # []) = {(n, ?x), (n, ?y), (n, ?z)}"
  	by (simp split: prod.splits)
  hence "(parse_var_edges \<circ> parse_nodes) ((n, c) # []) = parse_var_edges {(n, ?x), (n, ?y), (n, ?z)}"
  	by simp
  hence expand: "... = {{(n, ?pos?x, ?x), (n, ?neg?x, ?x)}, {(n, ?pos?y, ?y), (n, ?neg?y, ?y)}, {(n, ?pos?z, ?z), (n, ?neg?z, ?z)}}"
  	unfolding parse_var_edges_def by fast

  hence card_var: "card (cutset (parse_var_edges (parse_nodes ((n, c) # []))) S T) \<le> 3"
  	using cutset_card_max_fin apply (auto split: prod.splits)
  	using cutset_card_max_fin
  	by (smt card.empty card_insert_if finite.emptyI finite.insertI le_SucI numeral_3_eq_3)

	have 1: "?x \<noteq> ?y"
		using assms pop_card pop_ins pop_isin
		by (metis One_nat_def card.empty card.infinite insert_absorb n_not_Suc_n numeral_3_eq_3 numeral_eq_one_iff old.nat.distinct(1) semiring_norm(84))
	have 2: "?y \<noteq> ?z"
		using assms pop_card pop_ins pop_isin
		by (metis One_nat_def card.empty card.infinite insert_absorb n_not_Suc_n numeral_3_eq_3 numeral_eq_one_iff old.nat.distinct(1) semiring_norm(84))
	have 3: "?x \<noteq> ?z"
		using assms expand var_edge_card_single var_edge_card_single_alt
		by (smt One_nat_def card.empty card_insert_if finite.emptyI finite.insertI insertCI insert_absorb insert_not_empty n_not_Suc_n numeral_3_eq_3 numeral_One numeral_eq_iff semiring_norm(84))

  have expand_clause: "parse_clause_edges [(n, c)] = {{(n, ?x, ?x), (n, ?y, ?y)}, {(n, ?y, ?y), (n, ?z, ?z)}, {(n, ?z, ?z), (n, ?x, ?x)}}"
  	by (simp split: prod.splits)
  hence "card (cutset (parse_clause_edges [(n, c)]) S T) \<le> 2"
  	apply (subst expand_clause)
  	apply (rule cutset_triangle_card)
  	subgoal using 1 by blast
  	subgoal using 2 by blast
  	subgoal using 3[symmetric] by blast
  	subgoal by (rule assms).

  thm cutset_triangle_extend_card
  hence "card (cutset (parse_var_edges (parse_nodes [(n, c)]) \<union> parse_clause_edges [(n, c)]) S T) \<le> 2 + card (cutset (parse_var_edges (parse_nodes ((n, c) # []))) S T)"
  	apply (subst Un_commute)
  	apply (subst expand_clause)
  	apply (rule cutset_triangle_extend_card)
  	subgoal using 1 by blast
  	subgoal using 2 by blast
  	subgoal using 3[symmetric] by blast
  	subgoal by (rule assms)
  	subgoal apply (subst expand_nodes, subst expand)
  		by blast.
  thus "card (cutset (parse_var_edges (parse_nodes [(n, c)]) \<union> parse_clause_edges [(n, c)]) S T) \<le> 5"
  	using card_var by simp
qed

thm cutset_un_disj
lemma cutset_un_disj_full:
	assumes "(\<Union>e1) \<inter> (\<Union>e2) = {}" "s1 \<inter> s2 = {}" "t1 \<inter> t2 = {}" "cut (\<Union>e1) s1 t1" "cut (\<Union>e2) s2 t2"
	shows "cutset (e1 \<union> e2) (s1 \<union> s2) (t1 \<union> t2) = cutset e1 s1 t1 \<union> cutset e2 s2 t2"
	using assms unfolding cutset_def cut_def
	by auto

find_theorems cutset card


lemma "cut ((snd \<circ> parse \<circ> tag) expr) S T \<Longrightarrow> card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) \<le> 5 * length expr"
proof (induction expr arbitrary: S T rule: rev_induct)
  case Nil
  thus ?case
  	unfolding cutset_def parse_def Let_def parse_edges_def parse_var_edges_def tag_def
  	by simp
next
  case (snoc a expr)
  thm snoc.IH
  thm snoc.prems
  have "\<exists>s t. cut ((snd \<circ> parse \<circ> tag) expr) s t"
  	apply (rule cut_subset[of _ "(snd \<circ> parse \<circ> tag) (expr @ [a])" S T ])
  	subgoal unfolding parse_def Let_def comp_apply snd_conv
			apply (rule Union_mono)
			apply (rule parse_var_edges_subset)
			unfolding tag_def using parse_nodes_subset
			by (smt (verit) Un_iff diff_zero length_0_conv length_append_singleton length_upt parse_nodes_zip subsetI upt_Suc)
		subgoal by (rule snoc.prems).

	then obtain s t where cut_rest: "cut ((snd \<circ> parse \<circ> tag) expr) s t"
										and "\<forall>x\<in>S - s. \<forall>y\<in>t. {x, y} \<notin> (fst \<circ> parse \<circ> tag) (expr @ [a])"
										and "\<forall>x\<in>s. \<forall>y\<in>T - t. {x, y} \<notin> (fst \<circ> parse \<circ> tag) (expr @ [a])"
		

	hence "cut ((snd \<circ> parse \<circ> tag) (expr)) (S - s) (T - t)"



	have "\<forall>n1 \<in> S - s. \<forall>n2 \<in> S - s. fst n1 = fst n2"

(*
	have "\<Union>((fst \<circ> parse \<circ> tag) expr) \<subseteq> (snd \<circ> parse \<circ> tag) expr"
		unfolding comp_apply by (rule edges_subset)

	have "\<forall>e \<in> (snd \<circ> parse \<circ> tag) expr. \<forall>n \<in> e. n \<in> s \<or> n \<in> t"
		unfolding comp_apply parse_def Let_def fst_conv parse_edges_def tag_def 
		apply auto
*)
	have "\<forall>e \<in> parse_edges (tag expr) (parse_nodes (tag expr)). \<forall>n1 \<in> e. \<forall>n2 \<in> e. fst n1 = fst n2"
		sorry

	thm cutset_un_disj
	hence "cutset ((fst \<circ> parse \<circ> tag) (expr @ [a])) (S - s \<union> s) (T - t \<union> t) = cutset ((fst \<circ> parse \<circ> tag) expr) s t \<union> cutset ((fst \<circ> parse) ((length expr, a) # [])) (S - s) (T - t)"
		apply (subst cutset_un_disj)
		subgoal unfolding cut_def parse_def tag_def Let_def comp_apply fst_conv snd_conv
		oops

	hence card_hyp: "card (cutset ((fst \<circ> parse \<circ> tag) expr) s t) \<le> 5 * length expr"
		by (rule snoc.IH)

	hence "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) = card (cutset ((fst \<circ> parse \<circ> tag) expr) s t) + card (cutset ((fst \<circ> parse) ((length expr, a) # [])) s' t')"

  then show ?case sorry
qed

lemma "(a \<union> b) \<union> (c \<union> d) = (a \<union> c) \<union> (b \<union> d)"
	apply (subst Un_assoc[symmetric])
	apply (subst Un_commute)
	apply (subst Un_assoc)
	apply (subst Un_commute)
	apply (subst (2) Un_assoc)

	find_theorems "?s - ?s = {}"
	find_theorems "?s \<union> {} = ?s"
	find_theorems union minus
	find_theorems "?a - ?b - ?c"
lemma "S - s \<union> s - s = S - s"
	apply (subst Un_Diff)
	apply (subst Diff_idemp)
	apply (subst Diff_cancel)
	apply (subst Un_empty_right)
	apply (rule refl)

lemma "naesat a \<Longrightarrow> set a = set b \<Longrightarrow> naesat b"
	unfolding naesat_def nae_models_def by auto

lemma
	assumes "\<forall>c \<in> set expr. card c = 3" "\<not>naesat expr" "cut ((snd \<circ> parse \<circ> tag) expr) S T"
	shows "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) < 5 * length expr"
	using assms unfolding naesat_def nae_models_def
proof -
	have not_nae: "\<forall>vmap. \<exists>c \<in> set expr. \<forall>t \<in> c. \<forall>f \<in> c. \<not>((vmap\<up>) t \<and> \<not>(vmap\<up>) f)"
		using assms unfolding naesat_def nae_models_def by fastforce
	hence "\<forall>vmap. \<exists>c \<in> set expr. \<forall>t \<in> c. \<forall>f \<in> c. \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
		by simp
	hence "\<forall>vmap. \<exists>c \<in> set expr. (\<forall>l \<in> c. (vmap\<up>) l) \<or> (\<forall>l \<in> c. \<not>(vmap\<up>) l)"
		by meson
	thus ?thesis
		using assms
	proof (induction expr arbitrary: S T rule: rev_induct)
		case Nil
		thus ?case by simp
	next
		case (snoc a expr)
		thm snoc.IH
		thm snoc.prems
		then consider (rest_safe) "naesat expr"
			| (rest_unsafe) "\<not>naesat expr"
			by blast
		thus ?case
		proof cases
			case rest_safe
			hence "\<exists>vmap. \<forall>c \<in> set expr. \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f"
				using snoc.prems unfolding naesat_def nae_models_def by blast

			then obtain vmap where vmap: "\<forall>c \<in> set expr. \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f"
				by blast

			hence "\<forall>s t. cut ((snd \<circ> parse \<circ> tag) expr) s t \<longrightarrow> card (cutset ((fst \<circ> parse \<circ> tag) expr) s t) \<le> 5 * length expr"
				sorry
				oops
				using cutset_card nae3sat_def naesat_def rest_safe snoc.prems(2) by fastforce

				
				oops

			then obtain s t where "card (cutset ((fst \<circ> parse \<circ> tag) expr) s t) = 5 * length expr"
				by blast

			oops

			hence "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) < 5 * length expr"
				
				oops
			hence "\<forall>vmap. \<exists>c \<in> set (expr @ [a]). (\<forall>t \<in> c. (vmap\<up>) t) \<or> (\<forall>f \<in> c. \<not>(vmap\<up>) f)"
				using snoc.prems unfolding naesat_def nae_models_def by blast

			have ""


			then show ?thesis sorry
		next
			case rest_unsafe
			hence rest: "\<forall>vmap. \<exists>c \<in> set expr. (\<forall>t \<in> c. (vmap\<up>) t) \<or> (\<forall>f \<in> c. \<not>(vmap\<up>) f)"
				using snoc.prems unfolding naesat_def nae_models_def
				by (metis Un_iff gr0I set_append zero_neq_numeral)

			thm cut_subset_minus
			have "\<exists>s t. cut ((snd \<circ> parse \<circ> tag) expr) s t \<and> s \<subseteq> S \<and> t \<subseteq> T \<and> cut (((snd \<circ> parse \<circ> tag) (expr @ [a])) - ((snd \<circ> parse \<circ> tag) expr)) (S - s) (T - t)"
				apply (rule cut_subset_minus)
				subgoal unfolding parse_def Let_def comp_apply snd_conv
					apply (rule Union_mono)
					apply (rule parse_var_edges_subset)
					unfolding tag_def using parse_nodes_subset
					by (smt (verit) Un_iff diff_zero length_0_conv length_append_singleton length_upt parse_nodes_zip subsetI upt_Suc)
				subgoal by (rule snoc.prems(4)).

			then obtain s t where cut_rest: "cut ((snd \<circ> parse \<circ> tag) expr) s t"
												and s: "s \<subseteq> S" and t: "t \<subseteq> T"
												and cut_minus: "cut (((snd \<circ> parse \<circ> tag) (expr @ [a])) - ((snd \<circ> parse \<circ> tag) expr)) (S - s) (T - t)"
				by blast

			have "parse_nodes (tag expr) \<subseteq> parse_nodes (tag (expr @ [a]))" 
				unfolding tag_def using parse_nodes_zip
				by (smt Un_iff diff_zero length_0_conv length_append_singleton length_upt subsetI upt_Suc)
			hence "parse_var_edges (parse_nodes (tag expr)) \<subseteq> parse_var_edges (parse_nodes (tag (expr @ [a])))"
				by (rule parse_var_edges_subset)
			hence node_subset: "\<Union>(parse_var_edges (parse_nodes (tag expr))) \<subseteq> \<Union>(parse_var_edges (parse_nodes (tag (expr @ [a]))))"
				by (rule Union_mono)
			moreover have node_disj: "\<Union>(parse_var_edges (parse_nodes (tag expr))) \<inter> \<Union>(parse_var_edges (parse_nodes [(length expr, a)])) = {}"
				using parse_un_disj snoc.prems(2) unfolding tag_def comp_apply 
				by (metis butlast_snoc last_snoc)
			moreover have "\<Union>(parse_var_edges (parse_nodes (tag expr))) \<union> \<Union>(parse_var_edges (parse_nodes [(length expr, a)])) = \<Union>(parse_var_edges (parse_nodes (tag (expr @ [a]))))"
				using parse_nodes_zip parse_var_edges_split tag_def tag_nil
				by (smt Union_Un_distrib diff_zero length_0_conv length_append_singleton length_upt upt_Suc zip_Cons_Cons)
			ultimately have node_minus: "\<Union>(parse_var_edges (parse_nodes (tag (expr @ [a])))) - \<Union>(parse_var_edges (parse_nodes (tag expr))) = \<Union>(parse_var_edges (parse_nodes [(length expr, a)]))"
				by blast

			thm snoc.IH
			have card_hyp: "card (cutset ((fst \<circ> parse \<circ> tag) expr) s t) < 5 * length expr"
				apply (rule snoc.IH)
				subgoal using rest by simp
				subgoal using snoc.prems(2) by simp
				subgoal using snoc.prems(3) rest unfolding naesat_def nae_models_def by metis
				subgoal using cut_rest by simp.

			have card_step: "card (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T) \<le> 5"
				apply (rule subgraph_cutset_max)
				subgoal using snoc.prems by simp
				subgoal using snoc.prems unfolding cut_def by simp.

			have var_split: "parse_var_edges (parse_nodes (tag (expr @ [a]))) = parse_var_edges (parse_nodes (tag expr)) \<union> parse_var_edges (parse_nodes [(length expr, a)])"
				using parse_nodes_zip parse_var_edges_split tag_def tag_len 
				by (smt diff_zero length_0_conv length_append_singleton length_upt upt_Suc zip_Cons_Cons)

			have clause_split: "parse_clause_edges (tag (expr @ [a])) = parse_clause_edges (tag expr) \<union> parse_clause_edges [(length expr, a)]"
				using parse_clause_edges_zip tag_def
				by (smt diff_zero length_0_conv length_append_singleton length_upt upt_Suc zip_Cons_Cons zip_eq_Nil_iff)

			have cutset_expand: "cutset ((fst \<circ> parse \<circ> tag) (expr @ [a])) S T = cutset ((fst \<circ> parse \<circ> tag) expr) s t \<union> cutset ((fst \<circ> parse) ((length expr, a) # [])) (S - s) (T - t)"
				unfolding parse_def Let_def comp_apply fst_conv parse_edges_def
				apply (subst var_split, subst clause_split)
				apply (subgoal_tac "S = S - s \<union> s", subgoal_tac "T = T - t \<union> t")
				subgoal
					apply (erule ssubst)+
					apply (subst Un_assoc[symmetric], subst Un_commute, subst Un_assoc, subst Un_commute, subst (2) Un_assoc)
					apply (subst (4 5) Un_commute)
					apply (subst cutset_un_disj_full)
					subgoal proof -
						have "\<Union>(parse_var_edges (parse_nodes (tag expr)) \<union> parse_clause_edges (tag expr)) \<inter> \<Union>(parse_var_edges (parse_nodes [(length expr, a)]) \<union> parse_clause_edges [(length expr, a)])
										= \<Union>(parse_var_edges (parse_nodes (tag expr))) \<inter> \<Union>(parse_var_edges (parse_nodes [(length expr, a)]))"
							by (metis fst_conv no_island_nodes parse_def parse_edges_def snd_conv)
						thus ?thesis using node_disj by simp
					qed
					subgoal by simp
					subgoal by simp
					subgoal unfolding Let_def snd_conv 
						using cut_rest no_island_nodes parse_def parse_edges_def
						by (metis comp_apply fst_conv)
					subgoal proof -
						have "cut (\<Union>(parse_var_edges (parse_nodes [(length expr, a)]) \<union> parse_clause_edges [(length expr, a)])) (S - s) (T - t) = cut (\<Union>(parse_var_edges (parse_nodes [(length expr, a)]))) (S - s) (T - t)"
							by (metis fst_conv no_island_nodes parse_def parse_edges_def snd_conv)
						also have "... = cut ((snd \<circ> parse) ((length expr, a) # [])) (S - s) (T - t)"
							unfolding parse_def Let_def comp_apply snd_conv by simp
						also have "... = cut (((snd \<circ> parse \<circ> tag) (expr @ [a])) - ((snd \<circ> parse \<circ> tag) expr)) (S - s) (T - t)"
							unfolding parse_def Let_def comp_apply snd_conv cut_def using node_minus by simp
						finally show ?thesis using cut_minus by simp
					qed
					subgoal
						apply (subst eq_commute)
						apply (subst Un_Diff)+
						apply (subst Diff_idemp)+
						apply (subst Diff_cancel)+
						apply (subst Un_empty_right)+
						by (rule refl).
				subgoal using t by blast
				subgoal using s by blast.

			have cutset_expand_disj: "cutset ((fst \<circ> parse \<circ> tag) expr) s t \<inter> cutset ((fst \<circ> parse) ((length expr, a) # [])) (S - s) (T - t) = {}"
				apply (rule cutset_disj_all)
				subgoal using cut_def cut_minus by metis
				subgoal by simp
				subgoal by simp
				subgoal unfolding parse_def Let_def comp_apply fst_conv using parse_edges_disj snoc.prems(2)
					by (metis butlast_snoc inf.commute last_snoc).

			have cutset_cross_empty_1: "cutset ((fst \<circ> parse \<circ> tag) expr) (S - s) (T - t) = {}"
				and cutset_cross_empty_2: "cutset ((fst \<circ> parse) ((length expr, a) # [])) s t = {}"
				unfolding parse_def Let_def comp_apply fst_conv cutset_def
				subgoal apply (auto split: prod.splits)
					using cut_def no_island_nodes node_minus parse_def s cutset_expand cutset_expand_disj
					by (smt Diff_partition Un_iff UnionI comp_apply cut_minus disjoint_iff_not_equal fst_conv insertCI node_disj snd_conv)
				subgoal using cut_def cut_rest no_island_nodes node_disj parse_def
					by (smt (verit) Collect_empty_eq Un_iff UnionI comp_apply disjoint_iff_not_equal fst_conv insertCI snd_conv).

			have fin_aux_1: "finite (cutset ((fst \<circ> parse \<circ> tag) expr) S T)"
				using finite_cutset node_subset no_island_nodes parse_def snoc.prems(2) total_node_count
				by (smt add_is_0 card_eq_0_iff comp_apply finite_UnionD length_append_singleton mult_is_0 numeral_nat(1) plus_1_eq_Suc rev_finite_subset snd_conv zero_neq_numeral)

			have fin_aux_2: "finite (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T)"
				using finite_cutset parse_def parse_edge_card_single subgraph_edge_count
				by (smt Un_insert_right card_eq_0_iff comp_apply fst_conv insertCI list.simps(15) set_append snoc.prems(2) zero_neq_numeral)

			have "cutset (fst (parse (tag expr))) S T = cutset (fst (parse (tag expr))) s t \<union> cutset (fst (parse (tag expr))) (S - s) (T - t)"
				unfolding parse_def Let_def comp_apply fst_conv parse_edges_def
				thm cutset_un_disj
				apply (subgoal_tac "S = S - s \<union> s", subgoal_tac "T = T - t \<union> t")
				subgoal
					apply (erule ssubst)+
					apply (subst eq_commute)
					apply (subst Un_Diff)+
					apply (subst Diff_idemp)+
					apply (subst Diff_cancel)+
					apply (subst Un_empty_right)+
					apply (subst eq_commute)
					apply (rule cutset_un_disj)
					subgoal using cut_def cut_rest no_island_nodes parse_def parse_edges_def snoc.prems(4) t
						by (metis Diff_iff Un_iff UnionI comp_apply fst_conv insertCI insert_absorb insert_disjoint(2) subsetD)
					subgoal using cut_def cut_rest no_island_nodes parse_def parse_edges_def snoc.prems(4) s
						by (metis (no_types, lifting) DiffD1 DiffD2 Int_iff Un_iff UnionI comp_apply fst_conv insertCI subsetD).
				subgoal using t by blast
				subgoal using s by blast.
			hence cutset_simp_1: "cutset (fst (parse (tag expr))) S T = cutset (fst (parse (tag expr))) s t"
				using cutset_cross_empty_1 by simp

			have "cutset ((fst \<circ> parse) ((length expr, a) # [])) S T = cutset ((fst \<circ> parse) ((length expr, a) # [])) s t \<union> cutset ((fst \<circ> parse) ((length expr, a) # [])) (S - s) (T - t)"
				unfolding parse_def Let_def comp_apply fst_conv parse_edges_def
				thm cutset_un_disj
				apply (subgoal_tac "S = S - s \<union> s", subgoal_tac "T = T - t \<union> t")
				subgoal
					apply (erule ssubst)+
					apply (subst eq_commute)
					apply (subst Un_Diff)+
					apply (subst Diff_idemp)+
					apply (subst Diff_cancel)+
					apply (subst Un_empty_right)+
					apply (subst eq_commute)
					apply (rule cutset_un_disj)
					using cut_def cut_rest no_island_nodes node_minus parse_def parse_edges_def
					by (smt Diff_iff UnCI UnionI comp_apply fst_conv insertI1 insert_commute snd_conv)+
				subgoal using t by blast
				subgoal using s by blast.
			hence cutset_simp_2: "cutset ((fst \<circ> parse) ((length expr, a) # [])) S T = cutset ((fst \<circ> parse) ((length expr, a) # [])) (S - s) (T - t)"
				using cutset_cross_empty_2 by simp

			find_theorems parse_edges card
			thm cutset_un_card
			have "card (cutset ((fst \<circ> parse \<circ> tag) (expr @ [a])) S T) \<le> card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) + card (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T)"
				unfolding comp_apply parse_def Let_def fst_conv parse_edges_def
				apply (subst var_split, subst clause_split)
				apply (subst Un_assoc[symmetric], subst Un_commute, subst Un_assoc, subst Un_commute, subst (2) Un_assoc)
				apply (rule cutset_un_card)
				apply (subst parse_edges_def[symmetric])
				using subgraph_edge_count parse_edge_card_single
				by (metis Un_iff card_eq_0_iff list.set_intros(1) set_append snoc.prems(2) zero_neq_numeral)
			also have "... = card (cutset ((fst \<circ> parse \<circ> tag) expr) s t) + card (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T)"
				using cutset_simp_1 by simp
			also have "... < 5 * length expr + card (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T)"
				using card_hyp by simp
			also have "... \<le> 5 * length expr + 5"
				using card_step by simp
			also have "... = 5 * length (expr @ [a])"
				by simp
			finally show ?thesis.
		qed
	qed
qed


lemma 
	assumes "\<forall>c \<in> set expr. card c = 3" "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) = n * length expr" "cut ((snd \<circ> parse \<circ> tag) expr) S T" "set mini \<subseteq> set expr"
	shows "\<exists>s t. card (cutset ((fst \<circ> parse \<circ> tag) mini) s t) = n * length mini \<and> cut ((snd \<circ> parse \<circ> tag) mini) s t"
	using assms
proof (induction "length expr" arbitrary: mini n expr S T rule: less_induct)
  case less
  then show ?case sorry
qed


proof (induction mini arbitrary: n expr S T rule: rev_induct)
  case Nil
  hence "card (cutset ((fst \<circ> parse \<circ> tag) []) {} {}) = 0"
  	unfolding cutset_def by auto
  moreover have "cut ((snd \<circ> parse \<circ> tag) []) {} {}"
  	unfolding cut_def parse_def Let_def comp_apply snd_conv parse_var_edges_def tag_def
  	by auto
  ultimately have ?case by auto
next
  case (snoc x xs)
  thm snoc.IH
  thm snoc.prems
  then show ?case sorry
qed

lemma var_split: "parse_var_edges (parse_nodes (tag (expr @ [a]))) = parse_var_edges (parse_nodes (tag expr)) \<union> parse_var_edges (parse_nodes [(length expr, a)])"
	using parse_nodes_zip parse_var_edges_split tag_def tag_len 
	by (smt diff_zero length_0_conv length_append_singleton length_upt upt_Suc zip_Cons_Cons)

lemma clause_split: "parse_clause_edges (tag (expr @ [a])) = parse_clause_edges (tag expr) \<union> parse_clause_edges [(length expr, a)]"
	using parse_clause_edges_zip tag_def
	by (smt diff_zero length_0_conv length_append_singleton length_upt upt_Suc zip_Cons_Cons zip_eq_Nil_iff)

lemma cutset_disj_card: "\<lbrakk> finite E; e1 \<inter> e2 = {}; E = e1 \<union> e2 \<rbrakk> \<Longrightarrow> card (cutset E S T) = card (cutset e1 S T) + card (cutset e2 S T)"
	by (simp add: card_set_disj cutset_disj cutset_split finite_cutset)

lemma cutset_snoc_card: "\<forall>c \<in> set (expr @ [a]). card c = 3
	\<Longrightarrow> card (cutset ((fst \<circ> parse \<circ> tag) (expr @ [a])) S T) = card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) + card (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T)"
	apply (rule cutset_disj_card)
	subgoal unfolding parse_def Let_def comp_apply fst_conv using total_edge_count
		by (metis card_eq_0_iff comp_apply length_append_singleton less_Suc_eq_0_disj less_numeral_extra(3) mult_is_0 zero_neq_numeral)
	subgoal unfolding parse_def Let_def comp_apply fst_conv using parse_edges_disj
		by (metis butlast_snoc inf.commute last_snoc)
	subgoal unfolding parse_def Let_def comp_apply fst_conv parse_edges_def
		using var_split clause_split by blast.

lemma parse_edges_nil: "parse_edges [] {} = {}"
	unfolding parse_edges_def parse_var_edges_def by simp

value "sum (\<lambda>n. n) {0::nat, 1, 2, 3, 4}"
find_theorems "sum ?f (insert ?a ?A)"

lemma cutset_card_sum:
	assumes "\<forall>c \<in> set expr. card c = 3"
	shows "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) = sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr))"
	using assms
proof (induction expr arbitrary: S T rule: rev_induct)
  case Nil
  have "card (cutset ((fst \<circ> parse \<circ> tag) []) S T) = 0"
  	unfolding cutset_def parse_def by (simp add: tag_nil parse_edges_nil)
  also have "... = (\<Sum>n\<in>set (tag []). card (cutset ((fst \<circ> parse) [(fst n, snd n)]) S T))"
  	unfolding cutset_def parse_def by (simp add: tag_nil)
  finally show ?case.
next
  case (snoc a expr)
  thm snoc.IH
  thm snoc.prems
  hence card_hyp: "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) = (\<Sum>n\<in>set (tag expr). card (cutset ((fst \<circ> parse) [(fst n, snd n)]) S T))"
  	by simp

  have "card (cutset ((fst \<circ> parse \<circ> tag) (expr @ [a])) S T) = card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) + card (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T)"
  	by (rule cutset_snoc_card, insert snoc.prems)
  also have "... = (\<Sum>n\<in>set (tag expr). card (cutset ((fst \<circ> parse) [(fst n, snd n)]) S T)) + card (cutset ((fst \<circ> parse) ((length expr, a) # [])) S T)"
  	by (subst card_hyp, rule refl)
  also have "... = (\<Sum>n\<in>set (tag expr). card (cutset ((fst \<circ> parse) [(fst n, snd n)]) S T)) + card (cutset ((fst \<circ> parse) [(fst (length expr, a), snd (length expr, a))]) S T)"
  	by simp
  also have "... = (\<Sum>n\<in>insert (length expr, a) (set (tag expr)). card (cutset ((fst \<circ> parse) [(fst n, snd n)]) S T))"
  	apply (subst add.commute)
  	apply (rule sum.insert[symmetric, where ?A = "set (tag expr)" and ?x = "(length expr, a)" and ?g = "(\<lambda>n. card (cutset ((fst \<circ> parse) [(fst n, snd n)]) S T))"])
  	subgoal by simp
  	subgoal unfolding tag_def using tag_fst_nat
  		by (metis fst_conv less_irrefl_nat).
  also have "... = (\<Sum>n\<in>set (tag (expr @ [a])). card (cutset ((fst \<circ> parse) [(fst n, snd n)]) S T))"
  	unfolding tag_def by simp
  finally show ?case.
qed

find_theorems fold plus
term List.nth

lemma 
	assumes "\<forall>x \<in> set xs. x \<le> n" "fold (+) xs 0 = n * length xs"
	shows "\<forall>x \<in> set xs. x = n"
proof (rule ccontr)
	assume "\<not>(\<forall>x \<in> set xs. x = n)"
	hence "\<exists>x \<in> set xs. x \<noteq> n"
		by simp
	hence "\<exists>x \<in> set xs. x < n"
		using assms(1) by force

	then obtain x where "x \<in> set xs" and "x < n"
		by blast

	hence "\<forall>x \<in> set xs - {x}. x \<le> n"
		using assms(1) by force
	hence "fold (+) (remove1 x xs) 0 \<le> n * length (remove1 x xs)"


proof (induction xs arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  thm Cons.IH
  have "\<forall>x \<in> set xs. x = n"
  	apply (rule Cons.IH)
  	subgoal using Cons.prems(1) by simp
  	subgoal proof (rule ccontr)
  		assume "fold (+) xs 0 \<noteq> n * length xs"
  		moreover have "fold (+) xs 0 \<le> n * length xs"
  			using Cons.prems(1) 
  		hence "fold (+) xs 0 < n * length xs"
  			


  		have "a = n"
  			using Cons.prems
  			oops
  		have "fold (+) (a # xs) 0 = n * length (a # xs)"
  			by (rule Cons.prems(2))
  		hence "fold (+) xs n = n * length (a # xs)"
  			using Cons.prems(1)
  then show ?case sorry
qed
	

lemma
	assumes "\<forall>c \<in> set expr. card c = 3" "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) \<ge> 5 * length expr"
					"S \<inter> T = {}" "n < length expr" "card (cutset ((fst \<circ> parse) ((n, expr ! n) # [])) S T) \<le> 5"
	shows "card (cutset ((fst \<circ> parse) ((n, expr ! n) # [])) S T) = 5"
	using assms
proof (induction expr arbitrary: n S T rule: rev_induct)
  case Nil
  then show ?case sorry
next
  case (snoc a expr)
  then show ?case sorry
qed




proof (rule ccontr)
	assume "card (cutset ((fst \<circ> parse) [(n, expr ! n)]) S T) \<noteq> 5"
	hence "card (cutset ((fst \<circ> parse) [(n, expr ! n)]) S T) < 5"
		using subgraph_cutset_max assms le_eq_less_or_eq nth_mem oops by blast









	assume "\<not>(\<forall>n < length expr. card (cutset ((fst \<circ> parse) [(n, expr ! n)]) S T) = 5)"
	hence "\<exists>n < length expr. card (cutset ((fst \<circ> parse) [(n, expr ! n)]) S T) \<noteq> 5"
		by simp
	hence "\<exists>n < length expr. card (cutset ((fst \<circ> parse) [(n, expr ! n)]) S T) < 5"
		using subgraph_cutset_max using assms cut_def oops
		by (metis le_eq_less_or_eq nth_mem)

	then obtain n where n: "n < length expr" and card_n: "card (cutset ((fst \<circ> parse) [(n, expr ! n)]) S T) < 5"
		by blast

	have "\<forall>n < length expr. card (cutset ((fst \<circ> parse) ((n, expr ! n) # [])) S T) \<le> 5"
		using subgraph_cutset_max assms cut_def
		by (metis nth_mem)
	moreover have "sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr)) \<le> 5 * length expr"
		using assms cutset_card_sum by fastforce

	ultimately have "sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr) - {(n, expr ! n)}) \<le> 5 * length expr - 5"
		apply auto
		
		oops
	hence "(n, expr ! n) \<in> set (tag expr)"
		unfolding tag_def using n in_set_zip by fastforce
	hence "sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr))
					= sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr) - {(n, expr ! n)}) + card (cutset ((fst \<circ> parse) ((fst (n, expr ! n), snd (n, expr ! n)) # [])) S T)"
		by (simp add: sum.remove)
	also have "... \<le> 5 * (length expr - 1) + card (cutset ((fst \<circ> parse) ((fst (n, expr ! n), snd (n, expr ! n)) # [])) S T)"
		


		oops

	have "sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr)) = 5 * length expr"
		using assms cutset_card_sum by fastforce
	moreover have "\<forall>n < length expr. card (cutset ((fst \<circ> parse) ((n, expr ! n) # [])) S T) \<le> 5"
		using subgraph_cutset_max assms cut_def
		by (metis nth_mem)
	ultimately have "\<forall>n < length expr. card (cutset ((fst \<circ> parse) ((n, expr ! n) # [])) S T) = 5"
		


	ultimately have "sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr)) < 5 * length expr"
		
		oops

	have "5 * length expr = card (cutset ((fst \<circ> parse \<circ> tag) expr) S T)"
		using assms by simp
	hence "... = sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr))"
		using cutset_card_sum assms(1) by blast
	moreover have "\<forall>c \<in> set expr. card (cutset ((fst \<circ> parse) ((n, c) # [])) S T) \<le> 5"
		using subgraph_cutset_max assms cut_def by metis
	ultimately have "sum (\<lambda>n. card (cutset ((fst \<circ> parse) ((fst n, snd n) # [])) S T)) (set (tag expr)) \<le> 5 * length expr"
		using assms(2) by arith

	ultimately show ?thesis




proof (induction expr arbitrary: n S T rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc a expr)
  thm snoc.IH
  thm snoc.prems
  then show ?case sorry
qed

find_theorems card 6
find_theorems card 5
find_theorems cutset card
lemma 
	assumes "\<forall>c \<in> set expr. card c = 3" "cut ((snd \<circ> parse \<circ> tag) expr) S T" "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) = 5 * length expr"
	shows "\<forall>e \<in> parse_var_edges (parse_nodes (tag expr)). \<exists>u v. e = {u, v} \<and> u \<in> S \<and> v \<in> T"
	using assms



lemma
	assumes "\<forall>c \<in> set expr. card c = 3" "cut ((snd \<circ> parse \<circ> tag) expr) S T" "card (cutset ((fst \<circ> parse \<circ> tag) expr) S T) = 5 * length expr"
	shows "\<exists>vmap. \<forall>c \<in> set expr. \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f"
	using assms
proof (induction expr arbitrary: S T rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc a expr)
  thm snoc.IH
  thm snoc.prems

  let ?V = "(snd \<circ> parse \<circ> tag) (expr @ [a])"
  let ?v = "(snd \<circ> parse \<circ> tag) expr"

  have "\<exists>s t. cut ?v s t \<and> s \<subseteq> S \<and> t \<subseteq> T \<and> cut (?V - ?v) (S - s) (T - t)"
  	apply (rule cut_subset_minus)
  	subgoal unfolding parse_def Let_def comp_apply snd_conv
  		using parse_nodes_zip parse_var_edges_subset tag_def
  		by (smt (verit) Un_iff Union_mono diff_zero length_0_conv length_append_singleton length_upt subsetI upt_Suc)
  	subgoal by (rule snoc.prems).

  then obtain s t where "cut ?v s t" and "s \<subseteq> S" and "t \<subseteq> T" and "cut (?V - ?v) (S - s) (T - t)"
  	by blast



  find_theorems cutset inter
  hence "card (cutset ((fst \<circ> parse \<circ> tag) expr) (S - {n. n \<in> (snd \<circ> parse) ((length expr, a) # [])}) (T - {n. n \<in> (snd \<circ> parse) ((length expr, a) # [])})) = 5"
  	unfolding cutset_def parse_def Let_def comp_apply fst_conv snd_conv parse_edges_def parse_var_edges_def
  	
  	

  have "\<exists>vmap. \<forall>c\<in>set expr. \<exists>t\<in>c. \<exists>f\<in>c. (vmap\<up>) t \<and> \<not> (vmap\<up>) f"

  then show ?case sorry
qed


end