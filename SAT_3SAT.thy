theory SAT_3SAT
	imports Main "../Reductions" Fresh_Identifiers.Fresh_String
begin


datatype 'a lit = Pos 'a | Neg 'a

definition lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lit \<Rightarrow> bool" ("_\<up>" 60) where
  "lift \<sigma> \<equiv> \<lambda>l. case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not> \<sigma> x"

definition models :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lit set list \<Rightarrow> bool" (infixl "\<Turnstile>" 55) where
  "\<sigma> \<Turnstile> F \<equiv> \<forall>cls \<in> set F. \<exists>l \<in> cls. (\<sigma>\<up>) l"

definition sat :: "'a lit set list \<Rightarrow> bool" where
  "sat F \<equiv> (\<exists>\<sigma>. \<sigma> \<Turnstile> F) \<and> (\<forall>cls \<in> set F. card cls > 0)"

definition le3sat :: "'a lit set list \<Rightarrow> bool"
	where "le3sat expr = (sat expr \<and> (\<forall>clause \<in> set expr. card clause \<le> 3))"

definition eq3sat :: "'a lit set list \<Rightarrow> bool"
	where "eq3sat expr = (sat expr \<and> (\<forall>clause \<in> set expr. card clause = 3))"


lemma "sat Nil"
	unfolding sat_def models_def 
	by simp

fun ident :: "'a lit \<Rightarrow> 'a"
	where "ident (Pos x) = x"
	| "ident (Neg x) = x"

definition idset :: "'a lit set \<Rightarrow> 'a set"
	where "idset clause = {ident x | x. x \<in> clause}"

definition pop :: "'a lit set \<Rightarrow> 'a lit * 'a lit set"
	where "pop c = (
		let elem = SOME x. x \<in> c in
			(elem, c - {elem})
	)"

lemma pop_isin: "c \<noteq> {} \<Longrightarrow> fst (pop c) \<in> c"
	unfolding pop_def Let_def
	by (auto intro: Hilbert_Choice.someI)

lemma pop_card: "\<lbrakk> c \<noteq> {}; finite c \<rbrakk> \<Longrightarrow> Suc (card (snd (pop c))) = card c"
	unfolding pop_def Let_def
	apply (rule Hilbert_Choice.someI2 [where a = "SOME x. x \<in> c"])
	apply (auto intro: Hilbert_Choice.someI)[1]
	using mk_disjoint_insert by fastforce

lemma pop_card_less: "\<lbrakk> c \<noteq> {}; finite c \<rbrakk> \<Longrightarrow> card (snd (pop c)) < card c"
	using pop_card by (metis lessI)

lemma pop_ins: "\<lbrakk> c \<noteq> {}; finite c \<rbrakk> \<Longrightarrow> c = insert (fst (pop c)) (snd (pop c))"
	unfolding pop_def Let_def
	by (auto intro: Hilbert_Choice.someI)


fun stock :: "nat \<Rightarrow> ('a::fresh) set \<Rightarrow> 'a lit list"
	where "stock 0 vars = []"
	| "stock n vars = (
			let f = fresh vars undefined in	(
				Neg f # Pos f # stock (n-1) (insert f vars)
			)
	)"

lemma stock_fresh:
	assumes "finite vars" "f \<in> idset (set (stock n vars))"
	shows "f \<notin> vars"
	using assms
	by (induction n vars arbitrary: f rule: stock.induct) (auto simp add: idset_def Let_def fresh_notIn)

lemma stock_length:
	assumes "finite vars"
	shows "length (stock n vars) = 2*n"
	using assms
	by (induction n vars rule: stock.induct) (auto simp add: Let_def)

lemma stock_card:
	assumes "finite vars"
	shows "card (set (stock n vars)) = 2*n"
	using assms
	apply (induction n vars rule: stock.induct)
	 apply (auto simp add: Let_def)
	using idset_def stock_fresh
	by (smt List.finite_set card_insert_disjoint finite_insert ident.elims ident.simps(2) insertE insert_absorb2 lit.distinct(1) lit.inject(1) mem_Collect_eq n_not_Suc_n)

lemma stock_len_card:
	assumes "finite vars"
	shows "card (set (stock n vars)) = length (stock n vars)"
	using assms stock_length stock_card by metis

lemma stock_map_ident_card:
	assumes "finite vars"
	shows "card (set (map ident (stock n vars))) = n"
	using assms
	apply (induction n vars rule: stock.induct)
	 apply (auto simp add: Let_def)
	using idset_def stock_fresh
	by (smt List.finite_set card_insert_disjoint finite_imageI finite_insert imageE insert_iff mem_Collect_eq)

lemma idset_map_ident:
	assumes "finite vars"
	shows "idset (set (stock n vars)) = set (map ident (stock n vars))"
	using assms by (induction n vars rule: stock.induct) (auto simp add: idset_def)

lemma stock_idset_card:
	assumes "finite vars"
	shows "card (idset (set (stock n vars))) = n"
	using assms stock_map_ident_card idset_map_ident by metis

lemma stock_vars_card:
	assumes "finite vars" "s = idset (set (stock n vars))"
	shows "card (s \<union> vars) = card s + card vars"
	using assms stock_fresh stock_idset_card idset_map_ident
	by (metis Int_emptyI List.finite_set card_Un_disjoint) 

lemma stock_disj:
	assumes "finite vars" "s = idset (set (stock n vars))"
	shows "s \<inter> vars = {}"
	using assms stock_fresh
	by (metis Int_emptyI)

lemma stock_uniq:
	assumes "finite vars" "s = stock n vars" "i < length s" "j < length s" "i \<noteq> j"
	shows "s ! i \<noteq> s ! j"
	using assms
	by (simp add: card_distinct nth_eq_iff_index_eq stock_len_card)

lemma tl_rev_stock_uniq:
	assumes "finite vars" "i < length (stock n vars) - 1" "j < length (stock n vars) - 1" "i \<noteq> j"
	shows "tl (rev (stock n vars)) ! i \<noteq> tl (rev (stock n vars)) ! j"
	using assms
	by (simp add: card_distinct distinct_tl nth_eq_iff_index_eq stock_len_card)

lemma stock_idset:
	assumes "finite c" "finite vars" "idset c \<subseteq> vars" "f \<in> set (stock n vars)"
	shows "ident f \<notin> idset c"
	using assms stock_fresh idset_def by fastforce


fun splc :: "('a :: fresh) lit set \<Rightarrow> 'a lit list \<Rightarrow> 'a lit \<Rightarrow> 'a lit set list"
	where "splc c [] init = c # []"
	| "splc c (nx # []) init = (
			let p = pop c in
			let q = pop (snd p) in
				{fst p, fst q, init} # insert nx (snd q) # []
		)"
	| "splc c (n_prev # p_cur # xs) init = (
			let p = pop c in
				{n_prev, fst p, p_cur} # splc (snd p) xs init
		)"
thm splc.induct

definition refc :: "('a :: fresh) lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit set list * 'a set"
	where "refc c vars = (
		if card c \<le> 3 then
			(c # [], vars)
		else
			let s = stock (card c - 3) vars in
				(splc c (tl (rev s)) (last s), idset (set s) \<union> vars)
	)"


function split_clause :: "('a :: fresh) lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit list \<Rightarrow> 'a lit set list * 'a set"
	where "split_clause c vars carry = (
		if card c \<le> 3 then
			(c # [], vars)
		else if card c = 4 then 
			let p = pop c in	(
			let q = pop (snd p) in	(
				({fst p, fst q, hd (tl carry)} # (insert (hd carry) (snd q)) # [], vars)
		))
		else
			let p = pop c in	(
			let f = fresh vars undefined in	(
				({hd carry, fst p, Pos f} # (fst (split_clause (snd p) (insert f vars) (Neg f # tl carry))), (insert f vars))
		))
	)"
	by auto
termination
	apply (relation "measure (\<lambda>(c, vars, carry). card c)")
	 apply (auto simp add: pop_card)
	by (metis card_eq_0_iff pop_card_less zero_le_numeral)

definition refine_clause :: "('a :: fresh) lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit set list * 'a set"
	where "refine_clause c vars = (
		let f = fresh vars undefined in 
			split_clause c (insert f vars) (Neg f # Pos f # [])
	)"



lemma refine_len_gt0: "finite c \<Longrightarrow> length (fst (refine_clause c vars)) > 0"
	unfolding refine_clause_def
	by (auto simp add: Let_def)

lemma refine_var_sub: "finite c \<Longrightarrow> vars \<subseteq> snd (refine_clause c vars)"
	unfolding refine_clause_def
	by (auto simp add: Let_def)

lemma refine_var_fin: "\<lbrakk> finite c; finite vars \<rbrakk> \<Longrightarrow> finite (snd (refine_clause c vars))"
	unfolding refine_clause_def
	by (auto simp add: Let_def)

lemma split_cls_4: "card c = 4 \<Longrightarrow> c' \<in> set (fst (split_clause c vars carry)) \<Longrightarrow> card c' \<le> 3"
	apply (auto simp add: Let_def)
	 apply (simp add: card_insert_if)
	by (smt (verit) One_nat_def card_gt_0_iff card_insert_disjoint dual_order.eq_iff finite_insert insertE insert_absorb leD leI list.set(1) list.set(2) not_less_eq numeral_3_eq_3 numeral_eq_Suc one_le_numeral pop_card pop_ins pred_numeral_simps(2) prod.sel(1) semiring_norm(26) semiring_norm(27) singletonD)

lemma refine_cls: "card c \<le> 3 \<Longrightarrow> c = hd (fst (refine_clause c vars))"
	unfolding refine_clause_def by auto

lemma splc_4: "card c = 4 \<Longrightarrow> s = stock (card c - 3) vars \<Longrightarrow> c' \<in> set (splc c (tl (rev s)) (last s)) \<Longrightarrow> card c' \<le> 3"
	apply (auto simp add: Let_def card_insert_if split: if_splits)
	by (smt (verit) card_eq_0_iff card_insert_if card_insert_le less_Suc_eq_le not_less_eq_eq numeral_3_eq_3 numeral_eq_Suc pop_card pop_card_less pop_ins pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)

lemma stock_ge4: "stock (card c - 3) vars = x # xs \<Longrightarrow> card c \<ge> 4"
	by (induction "card c - 3" vars arbitrary: c x xs rule: stock.induct) auto

lemma stock_0: "stock 0 vars = []"
	by simp

lemma stock_gt0: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> length (stock n vars) > 0"
	using stock_length
	by (metis nat_0_less_mult_iff zero_less_numeral)

lemma stock_le3: "stock (card c - 3) vars = [] \<longleftrightarrow> card c \<le> 3"
	using stock_0 by (metis diff_is_0_eq list.distinct(1) stock.elims)

lemma stock_eq4: "stock (card c - 3) vars = Neg (fresh vars undefined) # Pos (fresh vars undefined) # [] \<longleftrightarrow> card c = 4"
	apply (auto simp add: Let_def)
	by (metis One_nat_def add.commute add_diff_inverse_nat diff_Suc_1 list.distinct(1) list.sel(3) nat_less_le numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) stock.elims stock_le3)

lemma stock_butlast: "s = stock n vars \<Longrightarrow> butlast (butlast s) = stock (n-1) vars"
	apply (induction n vars arbitrary: s rule: stock.induct)
	 apply (auto simp add: Let_def)
		apply (metis list.distinct(1) stock.elims stock.simps(1))
	 apply (metis butlast.simps(2) list.discI stock.elims)
	by (metis One_nat_def old.nat.exhaust stock.simps(1) stock.simps(2))

lemma stock_hd_tl_disj: "finite vars \<Longrightarrow> s = stock n vars \<Longrightarrow> hd s \<notin> set (tl s)"
	using stock_len_card
	by (metis card_distinct distinct.simps(2) hd_Cons_tl length_pos_if_in_set less_numeral_extra(3) list.sel(2) list.size(3))


lemma splc_eq4: "finite c \<Longrightarrow> finite vars \<Longrightarrow> s = nx # []
									\<Longrightarrow> p = pop c \<Longrightarrow> q = pop (snd p) \<Longrightarrow> card c = 4
									\<Longrightarrow> splc c s init = {fst p, fst q, init} # insert nx (snd q) # []"
	by (auto simp add: Let_def split: if_splits)

lemma splc_gt4: "card c > 4 \<Longrightarrow> p = pop c \<Longrightarrow> length s = 2 * (card c - 3) - 1
									\<Longrightarrow> splc c s init = {hd s, fst p, hd (tl s)} # splc (snd p) (tl (tl s)) init"
	by (induction c s init arbitrary: p rule: splc.induct) (auto simp add: Let_def)

lemma splc_card:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"c' \<in> set (splc c s' init)"
	shows "card c' \<le> 3"
	using assms
proof (induction "card c - 3" arbitrary: c c' s s' init vars)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (simp add: Let_def)
			using pop_card_less pop_ins
  		by (smt (verit) card_eq_0_iff card_insert_if finite_insert leD not_less_eq_eq numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)
  next
  	case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		then consider (safe) "c' = {?n_prev, fst ?p, ?p_cur}"
			| (rest) "c' \<in> set (splc (snd ?p) ?xs init)"
			using gt4 Suc.prems apply (simp add: Let_def)
			using Suc.prems Suc.hyps stock_length suc_card 
			by (smt Nitpick.size_list_simp(2) One_nat_def Suc_diff_Suc Suc_eq_numeral diff_Suc_1 diff_less dual_order.strict_trans hd_Cons_tl insert_iff length_tl less_add_Suc2 list.simps(15) nat_less_le numeral_3_eq_3 plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_numeral)
		thus ?thesis
		proof cases
			case safe
			thus ?thesis by (simp add: card_insert_if)
		next
			case rest
			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by simp
	
			thus ?thesis apply (rule Suc.hyps(1)[where ?c = ?rest and ?s = "butlast (butlast s)"
							and ?vars = "vars" and ?init = init and ?s' = "tl (tl s')"])
				using Suc.prems(1) c apply (metis finite_insert)
				using Suc.prems(2) Suc.hyps stock_butlast n apply (metis diff_Suc_1)
				using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
				using Suc.prems(4) Suc.hyps(2) n apply simp
				using rest apply simp
				done
		qed
	qed
qed

lemma stock_disj_vars:
	assumes "finite c" "finite vars" "idset c \<subseteq> vars"
	shows "c \<inter> set (stock n vars) = {}"
	using assms idset_def stock_idset by fastforce

lemma disj_un_eq: "a1 \<inter> a2 = {} \<Longrightarrow> b1 \<inter> b2 = {} \<Longrightarrow> a1 = b1 \<Longrightarrow> a2 = b2 \<Longrightarrow> a1 \<union> a2 = b1 \<union> b2"
	by (rule arg_cong2)

lemma splc_set:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
	shows "\<Union>(set l) = {init} \<union> set s' \<union> c"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' init vars)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  			 apply (metis card_0_eq pop_isin zero_neq_numeral)
  			apply (metis One_nat_def card.empty card_gt_0_iff insertCI one_eq_numeral_iff pop_card pop_ins pop_isin semiring_norm(83) zero_less_numeral)
  		 apply (metis One_nat_def card_eq_0_iff insertCI one_eq_numeral_iff pop_card pop_ins semiring_norm(83) zero_neq_numeral)
  		by (metis empty_iff finite_insert insert_iff pop_ins)
  next
  	case gt4

  	let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		hence hd: "hd l = {?n_prev, fst ?p, ?p_cur}"
			using Suc.prems(5) expand by simp

		have "fst ?p \<notin> {init}"
			using Suc.prems(8) c by auto
		moreover have "fst ?p \<notin> snd ?p"
			using c insert_absorb suc_card by fastforce
		moreover have "fst ?p \<notin> set (tl (tl s'))"
			using Suc.prems(9) c
			by (metis Nil_tl disjoint_insert(1) list.set_sel(2))
		ultimately have one: "fst ?p \<notin> {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			by simp

		have "?n_prev \<notin> {init}"
			using Suc.prems hd
			by (metis Un_iff empty_iff insert_iff list.sel(1) list.set_sel(1) splc.simps(1))
		moreover have "?n_prev \<notin> snd ?p"
			using c Suc.prems Suc.hyps stock_le3 stock_length
			by (metis Nitpick.size_list_simp(2) Set.set_insert diff_is_0_eq disjoint_insert(1) length_rev lessI list.set_sel(1) mult_Suc_right not_add_less1 numeral_2_eq_2 old.nat.distinct(1))
		moreover have "?n_prev \<notin> set (tl (tl s'))"
			using Suc.prems stock_len_card
			by (metis card_distinct distinct.simps(2) distinct_rev hd_Cons_tl length_pos_if_in_set less_numeral_extra(3) list.sel(2) list.set_sel(2) list.size(3))
		ultimately have two: "?n_prev \<notin> {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			by simp

		have "length s' \<ge> 2 \<Longrightarrow> hd (tl s') \<in> set s'"
			by (metis Suc_1 diff_is_0_eq length_tl list.sel(2) list.set_sel(1) list.set_sel(2) list.size(3) not_less_eq_eq)
		moreover have "length s' \<ge> 2"
			using Suc.prems gt4 by simp
		ultimately have p_cur_set: "?p_cur \<in> set s'"
			by simp
		hence "?p_cur \<notin> {init}"
			using Suc.prems by blast
		moreover have "?p_cur \<notin> snd ?p"
			using c Suc.prems p_cur_set by blast
		moreover have "?p_cur \<notin> set (tl (tl s'))"
			using Suc.prems stock_len_card
			by (metis card_distinct distinct.simps(2) distinct_rev hd_Cons_tl length_pos_if_in_set less_numeral_extra(3) list.sel(2) list.size(3))
		ultimately have three: "?p_cur \<notin> {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			by simp

		have first: "{?n_prev, fst ?p, ?p_cur} \<inter> ({init} \<union> set (tl (tl s')) \<union> snd (pop c)) = {}"
			using one two three by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto

		have tl: "\<Union>(set (tl l)) = {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)"])
			using suc_card Suc.hyps apply simp
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using Suc.prems(5) expand apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
			using disj apply simp
			done

		hence second: "hd l \<inter> \<Union>(set (tl l)) = {}"
			using hd tl first by arith

		have "length s' \<ge> 1 \<Longrightarrow> ?n_prev \<in> set s'"
			by (metis hd_in_set list.sel(2) p_cur_set)
		moreover have "length s' \<ge> 1"
			using Suc.prems by arith
		ultimately have n_prev_set: "?n_prev \<in> set s'"
			by simp
		moreover have fst_p_set: "fst ?p \<in> c"
			using c by blast
		moreover have "?p_cur \<in> set s'"
			using p_cur_set by simp
		ultimately have hd_sub: "hd l \<subseteq> c \<union> set s'"
			using hd by simp

		have "hd l \<union> \<Union>(set (tl l)) = {?n_prev, fst ?p, ?p_cur} \<union> ({init} \<union> set (tl (tl s')) \<union> snd (pop c))"
			apply (rule disj_un_eq)
			using second apply simp
			using first apply simp
			using hd apply simp
			using tl apply simp
			done

		moreover have "\<Union>(set l) = hd l \<union> \<Union>(set (tl l))"
			using Suc.prems(5) expand by simp
		ultimately have "\<Union>(set l) = {init} \<union> set s' \<union> c"
			using hd_sub tl n_prev_set p_cur_set fst_p_set snd_p_set tl_tl_set apply auto
			by (metis list.exhaust_sel list.sel(2) set_ConsD c insert_iff)+

		thus ?thesis .
  qed
qed

lemma splc_idset:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
	shows "idset (\<Union>(set l)) = idset ({init} \<union> set s' \<union> c)"
	using assms splc_set idset_def by (metis (no_types, lifting))


lemma splc_hd_tl_disj:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
	shows "hd l \<inter> \<Union>(set (tl l)) = {}"
	using assms

proof (induction "card c - 3" arbitrary: c l s s' init vars)
	case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def) 
  		by (metis (no_types, opaque_lifting) One_nat_def card.empty finite_insert insertCI insert_absorb n_not_Suc_n numeral_eq_one_iff numeral_less_iff pop_card pop_ins semiring_norm(75) semiring_norm(83) zero_less_one)+
  next
  	case gt4

  	let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		hence hd: "hd l = {?n_prev, fst ?p, ?p_cur}"
			using Suc.prems(5) expand by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto

		have tl: "\<Union>(set (splc (snd ?p) ?xs init)) = {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			apply (rule splc_set[where ?s = "butlast (butlast s)" and ?vars = vars])
			using Suc.prems(1) finite_insert c apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
			using disj apply simp
			done
		moreover have "fst ?p \<notin> {init}"
			using Suc.prems(8) c by auto
		moreover have "fst ?p \<notin> snd ?p"
			using c insert_absorb suc_card by fastforce
		moreover have "fst ?p \<notin> set (tl (tl s'))"
			using Suc.prems(9) c
			by (metis Nil_tl disjoint_insert(1) list.set_sel(2))
		ultimately have one: "fst ?p \<notin> {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			by simp

		have "?n_prev \<notin> {init}"
			using Suc.prems hd
			by (metis Un_iff empty_iff insert_iff list.sel(1) list.set_sel(1) splc.simps(1))
		moreover have "?n_prev \<notin> snd ?p"
			using c Suc.prems Suc.hyps stock_le3 stock_length
			by (metis Nitpick.size_list_simp(2) Set.set_insert diff_is_0_eq disjoint_insert(1) length_rev lessI list.set_sel(1) mult_Suc_right not_add_less1 numeral_2_eq_2 old.nat.distinct(1))
		moreover have "?n_prev \<notin> set (tl (tl s'))"
			using Suc.prems stock_len_card
			by (metis card_distinct distinct.simps(2) distinct_rev hd_Cons_tl length_pos_if_in_set less_numeral_extra(3) list.sel(2) list.set_sel(2) list.size(3))
		ultimately have two: "?n_prev \<notin> {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			by simp

		have "length s' \<ge> 2 \<Longrightarrow> hd (tl s') \<in> set s'"
			by (metis Suc_1 diff_is_0_eq length_tl list.sel(2) list.set_sel(1) list.set_sel(2) list.size(3) not_less_eq_eq)
		moreover have "length s' \<ge> 2"
			using Suc.prems gt4 by simp
		ultimately have p_cur_set: "?p_cur \<in> set s'"
			by simp
		hence "?p_cur \<notin> {init}"
			using Suc.prems by blast
		moreover have "?p_cur \<notin> snd ?p"
			using c Suc.prems p_cur_set by blast
		moreover have "?p_cur \<notin> set (tl (tl s'))"
			using Suc.prems stock_len_card
			by (metis card_distinct distinct.simps(2) distinct_rev hd_Cons_tl length_pos_if_in_set less_numeral_extra(3) list.sel(2) list.size(3))
		ultimately have three: "?p_cur \<notin> {init} \<union> set (tl (tl s')) \<union> snd (pop c)"
			by simp

		have first: "{?n_prev, fst ?p, ?p_cur} \<inter> ({init} \<union> set (tl (tl s')) \<union> snd (pop c)) = {}"
			using one two three by simp
		hence "hd l \<inter> \<Union>(set (tl l)) = {}"
			using hd tl expand Suc.prems(5) by simp
		thus ?thesis .
	qed
qed

lemma splc_card_3:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"c' \<in> set (splc c s' init)" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
	shows "card c' = 3"
	using assms
proof (induction "card c - 3" arbitrary: c c' s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis 
  		using Suc.prems apply (auto simp add: Let_def)
  		using Suc.prems pop_card pop_ins
  		 apply (smt One_nat_def card_eq_0_iff card_insert_if empty_iff finite.emptyI finite.insertI insert_iff not_less_eq_eq numeral_3_eq_3 one_eq_numeral_iff semiring_norm(83) zero_neq_numeral)
  		using pop_card pop_ins
  		apply (smt card_eq_0_iff card_insert_disjoint finite_insert insertCI nat.inject numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)
  		done
  next
  	case gt4
  	
  	let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		then consider (safe) "c' = {?n_prev, fst ?p, ?p_cur}"
			| (rest) "c' \<in> set (splc (snd ?p) ?xs init)"
			using gt4 Suc.prems apply (simp add: Let_def)
			using Suc.prems Suc.hyps stock_length suc_card 
			by (smt Nitpick.size_list_simp(2) One_nat_def Suc_diff_Suc Suc_eq_numeral diff_Suc_1 diff_less dual_order.strict_trans hd_Cons_tl insert_iff length_tl less_add_Suc2 list.simps(15) nat_less_le numeral_3_eq_3 plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_numeral)
		thus ?thesis
		proof cases
			case safe

			have ref1: "hd s' \<in> set s'"
				using Suc.prems Suc.hyps stock_le3 stock_length
				by (metis Nitpick.size_list_simp(2) diff_is_0_eq length_rev lessI list.set_sel(1) mult_Suc_right not_add_less1 numeral_2_eq_2 old.nat.distinct(1))
			moreover have fst_p: "fst (pop c) \<notin> set s'"
				using Suc.prems c by blast
			ultimately have one: "hd s' \<noteq> fst (pop c)"
				using Suc.prems by metis

			have "length s' \<ge> 2 \<Longrightarrow> hd (tl s') \<in> set s'"
				by (metis Suc_1 diff_is_0_eq length_tl list.sel(2) list.set_sel(1) list.set_sel(2) list.size(3) not_less_eq_eq)
			moreover have ref2: "length s' \<ge> 2"
				using Suc.prems gt4 by simp
			ultimately have "hd (tl s') \<in> set s'"
				by simp	
			moreover have two: "fst (pop c) \<noteq> hd (tl s')"
				using fst_p Suc.prems(9) calculation by metis

			have three: "hd (tl s') \<noteq> hd s'"
				using Suc.prems stock_len_card ref1 ref2
				by (metis Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_n_not_le_n card_distinct distinct.simps(2) distinct_rev distinct_tl empty_iff empty_set hd_Cons_tl list.set_sel(1))

			hence "card {hd s', fst (pop c), hd (tl s')} = 3"
				using one two three by simp

			thus ?thesis using safe by simp
		next
			case rest

			have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
				by (metis Nil_tl list.set_sel(2) subsetI)
			moreover have snd_p_set: "snd (pop c) \<subseteq> c"
				using c by auto
			ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
				using Suc.prems(9) by auto

			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by arith
	
			thus ?thesis apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using rest apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
			using disj apply simp
			done
		qed
  qed
qed


lemma
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"l = splc c s' init" "hd l \<inter> \<Union>(set (tl l)) = {}"
	shows "v \<in> hd l \<Longrightarrow> v \<notin> \<Union>(set (tl l))"
	using assms apply auto done

lemma splc_preserve_lit:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "v \<in> c"
	shows "\<exists>c' \<in> set l. v \<in> c'"
	using assms
proof (induction "card c - 3" arbitrary: c v l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  		using pop_ins by (metis empty_iff finite_insert insertE)
  next
  	case gt4

  	let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		then obtain c' where c': "c' \<in> set (splc c s' init)"
			using Suc.prems by auto

		then consider (safe) "v = fst (pop c)"
			| (rest) "v \<in> snd (pop c)"
			using expand Suc.prems c by blast
  	thus ?thesis
  	proof cases
  		case safe

			hence in_hd: "v \<in> hd l"
				using Suc.prems(5) expand by simp
			moreover have "hd l \<in> set l"
				using Suc.prems expand by fastforce
  		ultimately show ?thesis
  			by auto
  	next
  		case rest

			have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
				by (metis Nil_tl list.set_sel(2) subsetI)
			moreover have snd_p_set: "snd (pop c) \<subseteq> c"
				using c by auto
			ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
				using Suc.prems(9) by auto

			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by arith

			hence in_tl: "\<exists>c' \<in> set (tl l). v \<in> c'"
				apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
				using Suc.prems(1) c finite_insert apply metis
				using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
				using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
				using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
				using Suc.prems(5) expand apply simp
				using gt4 suc_card apply simp
				using Suc.prems(7) apply simp
				using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
				using disj apply simp
				using rest apply simp
				done

			moreover have "set (tl l) \<subseteq> set l"
				using Suc.prems(5) expand by fastforce

			ultimately show ?thesis by auto
  	qed
  qed
qed


lemma splc_lit_uniq:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"c' \<in> set l" "v \<in> c'"
	shows "\<forall>cc \<in> set l. cc = c' \<or> v \<notin> cc"
	using assms
proof (induction "card c - 3" arbitrary: c c' l s s' vars init v)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis using Suc.prems apply (auto simp add: Let_def)
  		by (metis (no_types, opaque_lifting) One_nat_def card.empty finite_insert insertCI insert_absorb n_not_Suc_n numeral_eq_one_iff numeral_less_iff pop_card pop_ins semiring_norm(75) semiring_norm(83) zero_less_one)+
  next
  	case gt4

  	let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto

		consider (safe) "c' = hd l"
			| (rest) "c' \<in> set (tl l)"
			using expand Suc.prems by force
		thus ?thesis
		proof cases
			case safe
			thus ?thesis
			proof (intro ballI)
				fix cc
				assume cc: "cc \<in> set l"
				consider (hd) "cc = hd l"
					| (tl) "cc \<in> set (tl l)"
					using cc expand Suc.prems(5) by force
				thus "cc = c' \<or> v \<notin> cc"
				proof cases
					case hd
					thus ?thesis using safe by simp
				next
					case tl
					have "hd l \<inter> \<Union>(set (tl l)) = {}"
						apply (rule splc_hd_tl_disj)
						using Suc.prems by blast+
					thus ?thesis 
						using Suc.prems(11) tl safe by blast
				qed
			qed
		next
			case rest
			thus ?thesis
			proof (intro ballI)
				fix cc
				assume cc: "cc \<in> set l"
				consider (hd) "cc = hd l"
					| (tl) "cc \<in> set (tl l)"
					using cc expand Suc.prems(5) by force
				thus "cc = c' \<or> v \<notin> cc"
				proof cases
					case hd
					have "hd l \<inter> \<Union>(set (tl l)) = {}"
						apply (rule splc_hd_tl_disj)
						using Suc.prems by blast+
					thus ?thesis
						using Suc.prems(11) hd rest by blast
				next
					case tl
					have n: "n = card ?rest - 3"
						using Suc.hyps suc_card by arith
					hence "\<forall>cc \<in> set (tl l). cc = c' \<or> v \<notin> cc"
						apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
						using Suc.prems(1) c finite_insert apply metis
						using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
						using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
						using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
						using Suc.prems(5) expand apply simp
						using gt4 suc_card apply simp
						using Suc.prems(7) apply simp
						using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
						using disj apply simp
						using rest apply simp
						using Suc.prems(11) apply simp
						done
					thus ?thesis using tl by simp
				qed
			qed
		qed
	qed
qed


lemma splc_clause_uniq:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
	shows "\<forall>i j. i < length l \<and> j < length l \<and> i \<noteq> j \<longrightarrow> l ! i \<noteq> l ! j"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
		let ?p = "pop c"
		let ?q = "pop (snd ?p)"

  	have eq4expand: "splc c s' init = {fst ?p, fst ?q, init} # insert (hd s') (snd ?q) # []"
  		using eq4 Suc.prems(4)
  		by (metis (no_types, lifting) One_nat_def Suc_length_conv add_diff_cancel_right' diff_numeral_Suc length_0_conv list.sel(1) mult_2 numeral_3_eq_3 plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) splc.simps(2))

  	hence "l ! 0 = hd l"
  		by (smt (verit) Suc.prems(5) list.sel(1) nth_Cons_0 splc.elims)
  	moreover have "l ! 1 = hd (tl l)"
  		using eq4expand Suc.prems by simp
  	moreover have "hd l \<inter> \<Union>(set (tl l)) = {}"
			apply (rule splc_hd_tl_disj[where ?c = c and ?vars = vars and ?s = "s" and ?s' = "s'" and ?init = init])
			using Suc.prems by blast+
		ultimately show ?thesis
			using eq4expand Suc.prems
			by (metis One_nat_def Union_disjoint inf.idem inf_commute insert_not_empty length_Cons less_Suc_eq less_one list.sel(1) list.sel(3) list.set_intros(1) list.size(3))
  next
  	case gt4
  	thus ?thesis
  	proof (intro allI impI)
  		fix i j
			assume a: "i < length l \<and> j < length l \<and> i \<noteq> j"

			consider (nil_i) "i = 0"
				| (nil_j) "j = 0"
				| (gt0) "i > 0 \<and> j > 0"
				by arith
			thus "l ! i \<noteq> l ! j"
			proof cases
				case nil_i
				hence j: "j > 0"
					using a by simp

				have "hd l \<inter> \<Union>(set (tl l)) = {}"
					apply (rule splc_hd_tl_disj[where ?c = c and ?vars = vars and ?s = "s" and ?s' = "s'" and ?init = init])
					using Suc.prems by blast+
				moreover have "l ! j \<in> set (tl l)"
					using a j
					by (metis Suc_pred diff_Suc_eq_diff_pred length_tl nth_mem nth_tl zero_less_diff)
				moreover have "l ! i = hd l"
					using nil_i a
					by (simp add: hd_conv_nth)
				ultimately show ?thesis
					using Suc.prems Suc.hyps
					by (smt (verit) One_nat_def Suc_pred Sup_upper inf.absorb2 inf_commute insert_not_empty list.sel(1) list.size(3) nat_0_less_mult_iff nat_mult_eq_1_iff one_eq_numeral_iff semiring_norm(83) splc.elims zero_less_Suc zero_less_numeral)
			next
				case nil_j
				hence i: "i > 0"
					using a by simp

				have "hd l \<inter> \<Union>(set (tl l)) = {}"
					apply (rule splc_hd_tl_disj[where ?c = c and ?vars = vars and ?s = "s" and ?s' = "s'" and ?init = init])
					using Suc.prems by blast+
				moreover have "l ! i \<in> set (tl l)"
					using a i
					by (metis Suc_pred diff_Suc_eq_diff_pred length_tl nth_mem nth_tl zero_less_diff)
				moreover have "l ! j = hd l"
					using nil_j a
					by (simp add: hd_conv_nth)
				ultimately show ?thesis
					using Suc.prems Suc.hyps
					by (smt (verit) One_nat_def Suc_pred Sup_upper inf.absorb2 inf_commute insert_not_empty list.sel(1) list.size(3) nat_0_less_mult_iff nat_mult_eq_1_iff one_eq_numeral_iff semiring_norm(83) splc.elims zero_less_Suc zero_less_numeral)
			next
				case gt0
				let ?p = "pop c"
				let ?t = "fst ?p"
				let ?rest = "snd ?p"
			
				have c: "c = insert ?t ?rest"
					using pop_ins Suc.prems Suc.hyps
					by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
			
				have suc_card: "Suc (card ?rest) = card c"
					using Suc.prems(1) c pop_card by auto
		
				let ?n_prev = "hd s'"
				let ?p_cur = "hd (tl s')"
				let ?xs = "tl (tl s')"
		
				have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
					using gt4 Suc.prems splc_gt4 by metis
			
				hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
					by simp
		
		
				have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
					by (metis Nil_tl list.set_sel(2) subsetI)
				moreover have snd_p_set: "snd (pop c) \<subseteq> c"
					using c by auto
				ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
					using Suc.prems(9) by auto
		
				hence n: "n = card ?rest - 3"
					using Suc.hyps suc_card by arith
				hence "\<forall>i j. i < length (tl l) \<and> j < length (tl l) \<and> i \<noteq> j \<longrightarrow> (tl l) ! i \<noteq> (tl l) ! j"
					apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
					using Suc.prems(1) c finite_insert apply metis
					using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
					using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
					using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
					using Suc.prems(5) expand apply simp
					using gt4 suc_card apply simp
					using Suc.prems(7) apply simp
					using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
					using disj apply simp
					done

				thus ?thesis using gt0 a
					by (smt Suc_lessD diff_Suc_eq_diff_pred gr0_conv_Suc length_tl nth_tl zero_less_diff)
			qed
		qed
  qed
qed


lemma splc_lit_clause:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
	shows "\<forall>c' \<in> set l. \<exists>v \<in> c'. v \<in> c"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  		using pop_isin apply (metis card.empty zero_neq_numeral)
  		using pop_card pop_ins pop_isin apply (smt card_0_eq finite_insert insert_iff nat.inject numeral_3_eq_3 numeral_eq_Suc old.nat.distinct(1) pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
  		done
	next
  	case gt4

  	let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		thus ?thesis
		proof (intro ballI)
			fix c'
			assume c': "c' \<in> set l"

			then consider (safe) "c' = hd l"
				| (rest) "c' \<in> set (tl l)"
				using expand Suc.prems c by force
			thus "\<exists>v\<in>c'. v \<in> c"
			proof cases
				case safe
				thus ?thesis using Suc.prems c expand
					by (metis insertCI list.sel(1))
			next
				case rest

				have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
					by (metis Nil_tl list.set_sel(2) subsetI)
				moreover have snd_p_set: "snd (pop c) \<subseteq> c"
					using c by auto
				ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
					using Suc.prems(9) by auto
	
				have n: "n = card ?rest - 3"
					using Suc.hyps suc_card by arith

				hence "\<forall>c' \<in> set (tl l). \<exists>v \<in> c'. v \<in> snd (pop c)"
					apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
					using Suc.prems(1) c finite_insert apply metis
					using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
					using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
					using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
					using Suc.prems(5) expand apply simp
					using gt4 suc_card apply simp
					using Suc.prems(7) apply simp
					using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
					using disj apply simp
					done

				thus ?thesis
					using rest snd_p_set by fastforce
			qed
		qed
  qed
qed


lemma idset_iff: "x \<notin> idset c \<longleftrightarrow> Pos x \<notin> c \<and> Neg x \<notin> c"
	using idset_def
	by (smt (verit, del_insts) ident.elims ident.simps(1) ident.simps(2) mem_Collect_eq)

lemma hd_stock_neg: "n > 0 \<Longrightarrow> hd (stock n vars) = Neg (fresh vars undefined)"
	by (induction n vars rule: stock.induct) (auto simp add: Let_def)

lemma last_stock_pos: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> \<exists>x. x \<notin> vars \<and> last (stock n vars) = Pos x"
	apply (induction n vars rule: stock.induct)
	 apply (auto simp add: Let_def)
	using fresh_notIn stock_0 by blast+

lemma stock_even_neg: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> even m \<Longrightarrow> m < length (stock n vars) \<Longrightarrow> \<exists>x. stock n vars ! m = Neg x"
	apply (induction n vars arbitrary: m rule: stock.induct)
	 apply (auto simp add: Let_def)
	using even_Suc less_Suc_eq_0_disj nth_Cons_Suc numeral_2_eq_2 by fastforce

lemma stock_odd_pos: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> odd m \<Longrightarrow> m < length (stock n vars) \<Longrightarrow> \<exists>x. stock n vars ! m = Pos x"
	apply (induction n vars arbitrary: m rule: stock.induct)
	 apply (auto simp add: Let_def)
	using even_Suc less_Suc_eq_0_disj nth_Cons_Suc numeral_2_eq_2 by fastforce

lemma stock_length_even: "finite vars \<Longrightarrow> even (length (stock n vars))"
	using stock_length by fastforce

lemma rev_stock_even_pos: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> even m \<Longrightarrow> m < length (stock n vars) \<Longrightarrow> \<exists>x. rev (stock n vars) ! m = Pos x"
	by (simp add: rev_nth stock_length_even stock_odd_pos)

lemma rev_stock_odd_neg: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> odd m \<Longrightarrow> m < length (stock n vars) \<Longrightarrow> \<exists>x. rev (stock n vars) ! m = Neg x"
	by (simp add: rev_nth stock_length_even stock_even_neg)

lemma tl_rev_stock_even_neg: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> even m \<Longrightarrow> m < length (tl (stock n vars)) \<Longrightarrow> \<exists>x. tl (rev (stock n vars)) ! m = Neg x"
	by (simp add: nth_tl rev_stock_odd_neg)

lemma tl_rev_stock_odd_pos: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> odd m \<Longrightarrow> m < length (tl (stock n vars)) \<Longrightarrow> \<exists>x. tl (rev (stock n vars)) ! m = Pos x"
	by (simp add: nth_tl rev_stock_even_pos)

lemma stock_pair: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> even m \<Longrightarrow> Suc m < length (stock n vars) \<Longrightarrow> stock n vars ! m = Neg x \<Longrightarrow> stock n vars ! Suc m = Pos x"
	apply (induction n vars arbitrary: m x rule: stock.induct)
	 apply (auto simp add: Let_def)
	by (smt (verit) One_nat_def Suc_diff_Suc bot_nat_0.not_eq_extremum diff_Suc_1 diff_Suc_Suc diff_is_0_eq even_Suc ident.simps(2) list.size(3) nat_less_le nth_Cons' odd_pos stock.elims)

lemma rev_stock_pair: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> even m \<Longrightarrow> Suc m < length (stock n vars) \<Longrightarrow> rev (stock n vars) ! m = Pos x \<Longrightarrow> rev (stock n vars) ! Suc m = Neg x"
	by (smt (verit) Suc_diff_Suc Suc_lessD diff_Suc_less dvd_diff_nat even_Suc lit.inject(1) rev_nth rev_stock_odd_neg stock_gt0 stock_length_even stock_pair)

lemma tl_rev_stock_pair: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> odd m \<Longrightarrow> Suc m < length (tl (stock n vars)) \<Longrightarrow> tl (rev (stock n vars)) ! m = Pos x \<Longrightarrow> tl (rev (stock n vars)) ! Suc m = Neg x"
	by (simp add: nth_tl rev_stock_pair)

lemma tl_rev_stock_pair_alt: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> odd m \<Longrightarrow> Suc m < length (tl (stock n vars)) \<Longrightarrow> tl (rev (stock n vars)) ! Suc m = Neg x \<Longrightarrow> tl (rev (stock n vars)) ! m = Pos x"
	using tl_rev_stock_odd_pos tl_rev_stock_pair
	by (metis Suc_lessD ident.simps(2))

lemma stock_neq_ident: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> odd m \<Longrightarrow> Suc m < length (stock n vars) \<Longrightarrow> ident (stock n vars ! m) \<noteq> ident (stock n vars ! Suc m)"
	apply (induction n vars arbitrary: m rule: stock.induct)
	 apply (auto simp add: Let_def)
	by (smt (verit, best) One_nat_def Suc_diff_Suc Suc_pred bot_nat_0.not_eq_extremum diff_Suc_Suc even_Suc finite_insert fresh_notIn ident.simps(1) ident.simps(2) insertI1 less_Suc0 less_Suc_eq_0_disj list.size(3) nth_Cons' odd_pos stock.elims)

lemma rev_stock_neq_ident: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> odd m \<Longrightarrow> Suc m < length (stock n vars) \<Longrightarrow> ident (rev (stock n vars) ! m) \<noteq> ident (rev (stock n vars) ! Suc m)"
	apply (simp add: rev_nth)
	by (metis Suc_diff_Suc diff_Suc_less dvd_diff_nat even_Suc stock_gt0 stock_length_even stock_neq_ident)

lemma tl_rev_stock_neq_ident: "finite vars \<Longrightarrow> n > 0 \<Longrightarrow> even m \<Longrightarrow> Suc m < length (tl (stock n vars)) \<Longrightarrow> ident (tl (rev (stock n vars)) ! m) \<noteq> ident (tl (rev (stock n vars)) ! Suc m)"
	apply (simp add: nth_tl rev_nth)
	by (smt (verit) One_nat_def Suc_diff_Suc diff_Suc_eq_diff_pred diff_Suc_less dvd_diff_nat even_Suc stock_gt0 stock_length_even stock_neq_ident)


lemma stock_suc_last:
	assumes "finite vars"
	shows "last (stock (Suc n) vars) \<notin> set (stock n vars)"
	using assms
	apply (induction n vars rule: stock.induct)
	 apply (auto simp add: Let_def)
	  apply (metis finite.insertI fresh_notIn insertI1)
	 apply (smt (verit, ccfv_SIG) Int_insert_right_if1 finite.insertI ident.simps(2) idset_map_ident insert_commute insert_not_empty last_in_set last_map list.map_disc_iff stock_disj)
	by (metis finite.insertI ident.simps(1) idset_map_ident insert_subset last_in_set last_map list.map_disc_iff stock_fresh subset_insertI)

lemma stock_suc_butlast:
	assumes "finite vars"
	shows "last (butlast (stock (Suc n) vars)) \<notin> set (stock n vars)"
	using assms
	apply (induction n vars rule: stock.induct)
	 apply (auto simp add: Let_def)
	  apply (metis finite.insertI fresh_notIn insertI1)
	by (metis finite.insertI idset_iff in_set_butlastD insert_subset last_in_set stock_fresh subset_insertI)+

lemma "length l > 2 \<Longrightarrow> hd (tl (tl l)) = l ! 2"
	apply (induction l)
	 apply auto
	by (metis drop0 drop_Suc hd_drop_conv_nth)

lemma refc_stock_clause_disj_le3:
	assumes "fst (refc c vars) = splc c (tl (rev (stock (card c - 3) vars))) (last (stock (card c - 3) vars))"
					"card c \<le> 3"
	shows "set (tl (rev (stock (card c - 3) vars))) \<inter> c = {}"
	using assms unfolding refc_def
	by (auto simp add: Let_def split: if_splits)

lemma refc_stock_clause_disj:
	assumes "fst (refc c vars) = splc c (tl (rev (stock (card c - 3) vars))) (last (stock (card c - 3) vars))"
					"finite vars" "card c \<ge> 4" "idset c \<subseteq> vars"
	shows "set (tl (rev (stock (card c - 3) vars))) \<inter> c = {}"
	using assms unfolding refc_def
	apply (auto simp add: Let_def split: if_splits)
	using stock_disj_vars
	by (smt (verit, del_insts) Collect_mem_eq Int_iff card_gt_0_iff dual_order.trans empty_Collect_eq less_zeroE linorder_not_le list.sel(2) list.set_sel(2) not_less_eq numeral_eq_Suc set_rev)

lemma refc_init_uniq:
	assumes "fst (refc c vars) = splc c (tl (rev (stock (card c - 3) vars))) (last (stock (card c - 3) vars))"
					"finite vars" "card c \<ge> 4" "idset c \<subseteq> vars"
	shows "last (stock (card c - 3) vars) \<notin> set (tl (rev (stock (card c - 3) vars))) \<union> c"
	using assms unfolding refc_def
	apply (auto simp add: Let_def split: if_splits)
	 apply (metis card_distinct distinct.simps(2) distinct_rev equals0D hd_rev list.exhaust_sel set_empty stock_len_card tl_Nil)
	using stock_disj_vars stock_le3
	by (smt BitM_inc_eq One_nat_def add_implies_diff card_gt_0_iff diff_is_0_eq' diff_le_mono diff_numeral_Suc disjoint_iff dual_order.strict_trans1 inc.simps(1) last_in_set not_le_imp_less not_one_less_zero numeral_3_eq_3 one_less_numeral_iff plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(76))

lemma refc_init_pos:
	assumes "fst (refc c vars) = splc c (tl (rev (stock (card c - 3) vars))) (last (stock (card c - 3) vars))"
					"finite vars" "card c \<ge> 4" "idset c \<subseteq> vars"
	shows "\<exists>x. last (stock (card c - 3) vars) = Pos x \<and> hd (tl (rev (stock (card c - 3) vars))) = Neg x"
	using assms unfolding refc_def
proof -
	let ?s = "(stock (card c - 3) vars)"
	let ?s' = "tl (rev ?s)"
	have one: "last ?s = ?s ! (length ?s - 1)"
		using assms stock_le3
		by (metis last_conv_nth not_less_eq_eq numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
	hence two: "hd ?s' = ?s ! (length ?s - 2)"
		using assms stock_length_even nth_tl rev_nth
		by (smt One_nat_def Suc_pred assms(2) butlast_rev diff_Suc_eq_diff_pred even_Suc even_zero hd_conv_nth last_rev length_butlast length_greater_0_conv length_rev list.size(3) numeral_2_eq_2 zero_less_diff)
	thus ?thesis
		using assms one two stock_length_even stock_even_neg stock_pair stock_le3 stock_odd_pos rev_stock_odd_neg rev_nth
		by (smt Suc_diff_Suc bot_nat_0.not_eq_extremum diff_Suc_1 diff_is_0_eq even_Suc length_greater_0_conv lit.distinct(1) nat_less_le not_less_eq_eq numeral_2_eq_2 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_diff)
qed

lemma splc_tmp:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"\<exists>y. init = Pos y" "idset c \<subseteq> vars"
	shows "\<forall>i < length l - 2. \<exists>j x. i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> l ! i \<and> Neg x \<in> l ! j"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis
  		using Suc.prems by (auto simp add: Let_def)
  next
  	case gt4

  	let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set (splc c s' init) = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		thus ?thesis
		proof (intro allI impI)
			fix i
			assume i: "i < length l - 2"

			consider (nil) "i = 0"
				| (gt0) "i > 0"
				by arith
			thus "\<exists>j x. i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> l ! i \<and> Neg x \<in> l ! j"
			proof cases
				case nil
				consider (eq5) "card c = 5"
					| (gt5) "card c > 5"
					using gt4 by arith
				thus ?thesis
				proof cases
					case eq5

					hence tlexpand: "splc (snd ?p) ?xs init = {fst (pop (snd ?p)), fst (pop (snd (pop (snd ?p)))), init} # insert (hd ?xs) (snd (pop (snd (pop (snd ?p))))) # []"
						by (smt (verit) One_nat_def Suc.prems(4) Suc_1 Suc_length_conv diff_Suc_1 diff_Suc_eq_diff_pred eval_nat_numeral(3) length_0_conv length_tl list.sel(1) mult_2 numeral_Bit0 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) splc.simps(2))

					hence eq5expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # {fst (pop (snd ?p)), fst (pop (snd (pop (snd ?p)))), init} # insert (hd ?xs) (snd (pop (snd (pop (snd ?p))))) # []"
						using expand tlexpand by simp

					hence s: "s = Neg (fresh vars undefined) # Pos (fresh vars undefined)
											# Neg (fresh (insert (fresh vars undefined) vars) undefined) # Pos (fresh (insert (fresh vars undefined) vars) undefined)
											# []"
						using eq5 Suc.prems stock_eq4 suc_card
						by (metis Suc_diff_le diff_Suc_1 eval_nat_numeral(3) le_numeral_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) stock.simps(2))

					have len: "length s' = length s - 1"
						using Suc.prems(3) Suc.prems(4) by simp
					

					have n_prev: "?n_prev = s' ! 0"
						using Suc.prems(5) expand tlexpand
						by (metis list.exhaust_sel list.sel(2) list.sel(3) not_Cons_self2 nth_Cons_0 splc.simps(1))
					have p_cur: "?p_cur = s' ! 1"
						using Suc.prems(5) expand tlexpand
						by (metis One_nat_def list.exhaust_sel list.sel(2) list.sel(3) not_Cons_self2 nth_Cons_0 nth_Cons_Suc splc.simps(1))
					hence hd_xs: "hd ?xs = s' ! 2"
						using len Suc.prems(3) Suc.prems(4) tlexpand
						by (smt (verit) Nil_tl One_nat_def Suc_1 diff_Suc_1 hd_conv_nth length_Cons list.distinct(1) list.exhaust_sel list.size(3) nth_Cons_Suc splc.elims zero_neq_one)

					obtain x where x: "?n_prev = Neg x"
						using n_prev tl_rev_stock_even_neg[of vars "card c - 3" 0] stock_length
						by (metis One_nat_def Suc.hyps(2) Suc.prems(2) Suc.prems(3) Suc.prems(7) Suc_diff_Suc diff_zero dvd_def even_zero gr0I length_tl mult_pos_pos odd_one zero_less_Suc zero_less_numeral)
					obtain y where pos_y: "?p_cur = Pos y"
						using p_cur tl_rev_stock_odd_pos[of vars "card c - 3" 1] stock_length
						by (metis (no_types, lifting) One_nat_def Suc.hyps(2) Suc.prems(2) Suc.prems(3) Suc.prems(7) Suc_eq_plus1 Suc_lessI Suc_pred add_diff_inverse_nat dvd_def even_diff_nat gt4 length_greater_0_conv length_tl list.size(3) mult_eq_self_implies_10 mult_pos_pos nat_1_add_1 nat_less_le numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)

					hence neg_y: "hd ?xs = Neg y"
						using eq5expand s Suc.prems(3) by simp

					hence "y \<notin> vars"
						using Suc.prems(3) Suc.prems(7) fresh_notIn neg_y s by auto
					moreover have "Pos y \<in> l ! 0"
						using eq5expand Suc.prems(5) pos_y by force
					moreover have "Neg y \<in> l ! 2"
						using eq5expand Suc.prems(5) neg_y by force
					ultimately show ?thesis
						using nil zero_neq_numeral by blast
				next
					case gt5

					obtain j where j: "j = Suc i"
						by arith

					hence tlexpand: "splc (snd ?p) ?xs init = {hd ?xs, fst (pop (snd ?p)), hd (tl ?xs)}	# splc (snd (pop (snd ?p))) (tl (tl ?xs)) init"
						using Suc.prems gt5 expand splc_gt4 suc_card
						by (smt Suc_diff_le Suc_eq_numeral diff_Suc_1 diff_Suc_eq_diff_pred diff_mult_distrib2 eval_nat_numeral(3) le_numeral_Suc length_tl mult_2 nat_less_le plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))

					hence gt5expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} 
																							# {hd ?xs, fst (pop (snd ?p)), hd (tl ?xs)} 
																							# splc (snd (pop (snd ?p))) (tl (tl ?xs)) init"
						using expand gt5 by simp


					hence s: "s = Neg (fresh vars undefined) # Pos (fresh vars undefined)
											# Neg (fresh (insert (fresh vars undefined) vars) undefined) # tl (tl (tl s))"
						using gt4 stock_eq4 Suc.prems Suc.hyps(2)
						by (metis list.sel(3) nat_less_le old.nat.distinct(1) stock.elims)

					have len: "length s' = length s - 1"
						using Suc.prems(3) Suc.prems(4) by simp
					

					have n_prev: "?n_prev = s' ! 0"
						using Suc.prems(5) expand tlexpand
						by (metis list.exhaust_sel list.sel(2) list.sel(3) not_Cons_self2 nth_Cons_0 splc.simps(1))
					have p_cur: "?p_cur = s' ! 1"
						using Suc.prems(5) expand tlexpand
						by (metis One_nat_def list.exhaust_sel list.sel(2) list.sel(3) not_Cons_self2 nth_Cons_0 nth_Cons_Suc splc.simps(1))
					hence hd_xs: "hd ?xs = s' ! 2"
						using len Suc.prems(3) Suc.prems(4) tlexpand
						by (smt (verit) Nil_tl One_nat_def Suc_1 diff_Suc_1 hd_conv_nth length_Cons list.distinct(1) list.exhaust_sel list.size(3) nth_Cons_Suc splc.elims zero_neq_one)

					obtain x where x: "?n_prev = Neg x"
						using n_prev tl_rev_stock_even_neg[of vars "card c - 3" 0] stock_length
						by (metis One_nat_def Suc.hyps(2) Suc.prems(2) Suc.prems(3) Suc.prems(7) Suc_diff_Suc diff_zero dvd_def even_zero gr0I length_tl mult_pos_pos odd_one zero_less_Suc zero_less_numeral)
					obtain y where pos_y: "?p_cur = Pos y"
						using p_cur tl_rev_stock_odd_pos[of vars "card c - 3" 1] stock_length
						by (metis (no_types, lifting) One_nat_def Suc.hyps(2) Suc.prems(2) Suc.prems(3) Suc.prems(7) Suc_eq_plus1 Suc_lessI Suc_pred add_diff_inverse_nat dvd_def even_diff_nat gt4 length_greater_0_conv length_tl list.size(3) mult_eq_self_implies_10 mult_pos_pos nat_1_add_1 nat_less_le numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)

					hence neg_y: "hd ?xs = Neg y"
						using gt5expand s hd_xs p_cur stock_length_even tl_rev_stock_pair Suc.prems Suc.hyps
						by (metis Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_less_eq even_Suc length_Cons odd_one zero_less_Suc)


					hence "y \<notin> vars"
						using Suc.prems(2) Suc.prems(3) Suc.prems(7) pos_y stock_butlast stock_fresh
						by (metis butlast_rev idset_iff list.sel(2) list.set_sel(1) lit.distinct(1) rev_rev_ident set_rev)
					moreover have "Pos y \<in> l ! 0"
						using gt5expand Suc.prems(5) pos_y by force
					moreover have "Neg y \<in> l ! 1"
						using gt5expand Suc.prems(5) neg_y by force
					ultimately show ?thesis
						using nil zero_neq_numeral by auto
				qed
			next
				case gt0

				hence "l ! i = tl l ! (i-1)"
					using Suc.prems(5) expand by simp

				have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
					by (metis Nil_tl list.set_sel(2) subsetI)
				moreover have snd_p_set: "snd (pop c) \<subseteq> c"
					using c by auto
				ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
					using Suc.prems(9) by auto
	
	
				have n: "n = card ?rest - 3"
					using Suc.hyps suc_card by arith

				thm Suc.hyps
				hence "\<forall>i < length (tl l) - 2. \<exists>j x. i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> (tl l) ! i \<and> Neg x \<in> (tl l) ! j"
					apply (rule Suc.hyps(1)[where ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
					using Suc.prems(1) c finite_insert apply metis
					using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
					using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
					using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
					using Suc.prems(5) expand apply simp
					using gt4 suc_card apply simp
					using Suc.prems(7) apply simp
					using Suc.prems(8) snd_p_set tl_tl_set apply blast
					using disj apply simp
					using Suc.prems(10) apply simp
					using Suc.prems(11) idset_def apply (smt mem_Collect_eq snd_p_set subset_iff)
					done

				hence "\<forall>i < length l - 3. \<exists>j x. i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> (tl l) ! i \<and> Neg x \<in> (tl l) ! j"
					by simp
				hence "\<forall>i < length l - 3. \<exists>j x. i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> l ! Suc i \<and> Neg x \<in> l ! Suc j"
					using Suc.prems(5) expand by simp
				hence "\<forall>i. \<exists>j x. i < length l - 3 \<longrightarrow> i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> l ! Suc i \<and> Neg x \<in> l ! Suc j"
					by simp
				hence "\<forall>i. \<exists>j x. i > 0 \<and> i < length l - 2 \<longrightarrow> i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> l ! i \<and> Neg x \<in> l ! j"
					by (smt One_nat_def Suc_inject Suc_less_eq Suc_pred diff_Suc_eq_diff_pred numeral_3_eq_3 numeral_2_eq_2 zero_less_diff)
				hence "\<exists>j x. i \<noteq> j \<and> x \<notin> vars \<and> Pos x \<in> l ! i \<and> Neg x \<in> l ! j"
					using gt0 i by simp
				thus ?thesis .
			qed
		qed
  qed
qed



lemma splc_aux_clause:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"\<exists>y. init = Pos y" "idset c \<subseteq> vars"
	shows "\<forall>c' \<in> set (butlast (butlast l)). \<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c' \<and> Neg j \<in> c'"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
	thus ?case
	proof cases
		case eq4
		thus ?thesis
			using Suc.prems by (auto simp add: Let_def)
	next
		case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		thus ?thesis
		proof (intro ballI)

			fix c'
			assume c': "c' \<in> set (butlast (butlast l))"
	
			then consider (safe) "c' = hd l"
				| (rest) "c' \<in> set (butlast (butlast (tl l)))"
				using Suc.prems expand c'
				by (smt butlast.simps(1) butlast.simps(2) list.sel(1) list.sel(3) list.set_cases)
			thus "\<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c' \<and> Neg j \<in> c'"
			proof cases
				case safe
	
				hence c': "c' = {?n_prev, fst ?p, ?p_cur}"
					using expand safe by simp
	
				hence n_prev: "?n_prev = s' ! 0"
					using Suc.prems(2) Suc.prems(3) Suc.prems(4) Suc.prems(5) expand
					by (metis hd_conv_nth length_Cons list.sel(2) n_not_Suc_n splc.simps(1))
				moreover have "\<exists>i. tl (rev (stock (card c - 3) vars)) ! 0 = Neg i"
					apply (rule tl_rev_stock_even_neg)
					using Suc.prems(7) apply simp
					using Suc.prems(6) apply simp
					 apply simp
					using Suc.prems Suc.hyps stock_length gt4
					by (smt One_nat_def Suc_1 Suc_eq_plus1 Suc_lessI Suc_pred add_diff_inverse_nat dvd_def even_diff_nat length_greater_0_conv length_tl list.size(3) mult_eq_self_implies_10 mult_pos_pos nat_less_le numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)
	
				ultimately obtain i where i: "?n_prev = Neg i"
					using Suc.prems by metis 
	
				have "?p_cur = hd (tl s')"
					by simp
				hence p_cur: "?p_cur = s' ! 1"
					using Suc.prems(2) Suc.prems(3) Suc.prems(4)
					by (smt (verit, del_insts) Nitpick.size_list_simp(2) Suc.hyps(2) Suc_1 Suc_eq_plus1 add_diff_inverse_nat diff_is_0_eq diff_zero dvd_def gt4 hd_conv_nth less_Suc_eq_0_disj mult_eq_self_implies_10 mult_pos_pos nat_less_le nth_tl numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
				moreover have "\<exists>j. tl (rev (stock (card c - 3) vars)) ! 1 = Pos j"
					apply (rule tl_rev_stock_odd_pos)
					using Suc.prems(7) apply simp
					using Suc.prems(6) apply simp
					 apply simp
					using Suc.prems Suc.hyps stock_length gt4
					by (smt One_nat_def Suc_1 Suc_eq_plus1 Suc_lessI Suc_pred add_diff_inverse_nat dvd_def even_diff_nat length_greater_0_conv length_tl list.size(3) mult_eq_self_implies_10 mult_pos_pos nat_less_le numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)
	
				ultimately obtain j where j: "?p_cur = Pos j"
					using Suc.prems by metis
	
				have "ident (tl (rev (stock (card c - 3) vars)) ! 0) \<noteq> ident (tl (rev (stock (card c - 3) vars)) ! Suc 0)"
					apply (rule tl_rev_stock_neq_ident)
					using Suc.prems(7) apply simp
					using Suc.prems(6) apply simp
					 apply simp
					using Suc.prems Suc.hyps stock_length gt4
					by (smt One_nat_def Suc_1 Suc_eq_plus1 Suc_lessI Suc_pred add_diff_inverse_nat dvd_def even_diff_nat length_greater_0_conv length_tl list.size(3) mult_eq_self_implies_10 mult_pos_pos nat_less_le numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)
	
				hence "i \<noteq> j"
					using Suc.prems i j n_prev p_cur by fastforce
				moreover have "Neg i \<in> c'"
					using c' i by simp
				moreover have "i \<notin> vars"
					using Suc.prems i j idset_iff stock_disj
					by (metis IntI empty_iff list.sel(2) list.set_sel(1) list.set_sel(2) lit.distinct(1) set_rev)
				moreover have "Pos j \<in> c'"
					using c' j by simp
				moreover have "Pos j \<in> set s'"
					using Suc.prems Suc.hyps j
					by (smt Nitpick.size_list_simp(2) One_nat_def Suc_eq_plus1 Suc_pred add_diff_inverse_nat diff_is_0_eq' gt4 list.set_sel(1) list.set_sel(2) list.size(3) mult_eq_self_implies_10 nat_0_less_mult_iff nat_less_le nat_mult_eq_1_iff numeral_eq_Suc one_eq_numeral_iff pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)
				moreover have "j \<notin> vars"
					using Suc.prems calculation idset_iff stock_fresh
					by (metis list.sel(2) list.set_sel(2) set_rev)
				ultimately show ?thesis using safe by metis
			next
				case rest
	
				have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
					by (metis Nil_tl list.set_sel(2) subsetI)
				moreover have snd_p_set: "snd (pop c) \<subseteq> c"
					using c by auto
				ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
					using Suc.prems(9) by auto
	
	
				have n: "n = card ?rest - 3"
					using Suc.hyps suc_card by arith
	
				hence "\<forall>c' \<in> set (butlast (butlast (tl l))). \<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c' \<and> Neg j \<in> c'"
					apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
					using Suc.prems(1) c finite_insert apply metis
					using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
					using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
					using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
					using expand apply simp
					using gt4 suc_card apply simp
					using Suc.prems(7) apply simp
					using Suc.prems(8) snd_p_set tl_tl_set apply blast
					using disj apply simp
					using Suc.prems(10) apply simp
					using Suc.prems(11) idset_def apply (smt mem_Collect_eq snd_p_set subset_iff)
					done

				thus ?thesis using rest by simp
			qed
		qed
	qed
qed


lemma splc_aux_clause_nth:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"\<exists>y. init = Pos y" "idset c \<subseteq> vars" "c' = l ! i" "i < length l - 2"
	shows "\<exists>x y. Neg y = s' ! (2*i) \<and> Pos x = s' ! Suc (2*i) \<and> Neg y \<in> c' \<and> Pos x \<in> c' \<and> y \<notin> vars \<and> x \<notin> vars"
	using assms
proof (induction "card c - 3" arbitrary: c c' l s s' vars init i)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
	thus ?case
	proof cases
		case eq4
		thus ?thesis
			using Suc.prems by (auto simp add: Let_def)
	next
		case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		consider (hd) "i = 0"
			| (tl) "i > 0"
			by arith
		thus ?thesis
		proof cases
			case hd
			hence c'_hd: "c' = hd l"
				using Suc.prems(12) expand by simp

			hence c': "c' = {?n_prev, fst ?p, ?p_cur}"
				using expand by simp

			
			find_theorems "hd ?xs = ?xs ! 0"
			have nil: "s' \<noteq> []"
				using Suc.prems by fastforce
			hence n_prev: "?n_prev = s' ! 0"
				by (rule hd_conv_nth)
			thm tl_rev_stock_even_neg
			moreover have "\<exists>y. tl (rev (stock (card c - 3) vars)) ! 0 = Neg y"
				apply (rule tl_rev_stock_even_neg)
				using Suc.prems gt4 by auto
			ultimately have "\<exists>y. Neg y = s' ! (2 * i) \<and> Neg y \<in> c'"
				using Suc.prems(2) Suc.prems(3) hd c' by force

			then obtain y where neg_y: "Neg y = s' ! (2 * i) \<and> Neg y \<in> c'"
				by blast
			hence "y \<in> idset (set s)"
				using idset_iff Suc.prems hd nil
				by (metis Nil_tl Suc.prems(3) list.set_sel(1) list.set_sel(2) mult_0_right n_prev set_rev)
			hence y_vars: "y \<notin> vars"
				using stock_disj Suc.prems by blast

			hence p_cur: "?p_cur = s' ! 1"
				using Suc.prems expand hd
				by (metis One_nat_def Suc_1 hd_conv_nth length_Cons length_greater_0_conv list.sel(2) list.size(3) nat_less_le nth_tl splc.simps(1) zero_less_diff)

			thm tl_rev_stock_odd_pos
			moreover have "\<exists>x. tl (rev (stock (card c - 3) vars)) ! 1 = Pos x"
				apply (rule tl_rev_stock_odd_pos)
				using Suc.prems gt4 by auto
			ultimately have "\<exists>x. Pos x = s' ! Suc (2 * i) \<and> Pos x \<in> c'"
				using Suc.prems(2) Suc.prems(3) hd c' by force

			then obtain x where pos_x: "Pos x = s' ! Suc (2 * i) \<and> Pos x \<in> c'"
				by blast
			hence "x \<in> idset (set s)"
				using idset_iff Suc.hyps(2) gt4 hd nil Suc.prems(3) Suc.prems(4)
				by (smt Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_eq_plus1 add_diff_inverse_nat diff_is_0_eq length_tl list.set_sel(2) mult_0_right mult_eq_self_implies_10 nat_less_le nth_mem numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) set_rev zero_less_Suc zero_less_diff)
			hence x_vars: "x \<notin> vars"
				using stock_disj Suc.prems by blast

			thus ?thesis using pos_x neg_y x_vars y_vars by blast
		next
			case tl
			hence c': "c' \<in> set (tl l)"
				using Suc.prems(12) Suc.prems(13) expand by simp
	
			have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
				by (metis Nil_tl list.set_sel(2) subsetI)
			moreover have snd_p_set: "snd (pop c) \<subseteq> c"
				using c by auto
			ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
				using Suc.prems(9) by auto


			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by arith

			thm Suc.hyps
			hence "\<exists>x y. Neg y = tl (tl s') ! (2 * (i-1)) \<and> Pos x = tl (tl s') ! Suc (2 * (i-1)) \<and> Neg y \<in> c' \<and> Pos x \<in> c' \<and> y \<notin> vars \<and> x \<notin> vars"
				apply (rule Suc.hyps(1)[where ?c' = c' and ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
				using Suc.prems(1) c finite_insert apply metis
				using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
				using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
				using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
				using expand apply simp
				using gt4 suc_card apply simp
				using Suc.prems(7) apply simp
				using Suc.prems(8) snd_p_set tl_tl_set apply blast
				using disj apply simp
				using Suc.prems(10) apply simp
				using Suc.prems(11) idset_def apply (smt mem_Collect_eq snd_p_set subset_iff)
				using Suc.prems(12) expand tl apply simp
				using Suc.prems(13) expand tl apply simp
				done

			hence "\<exists>x y. Neg y = tl (tl s') ! (2*i - 2) \<and> Pos x = tl (tl s') ! Suc (2*i - 2) \<and> Neg y \<in> c' \<and> Pos x \<in> c' \<and> y \<notin> vars \<and> x \<notin> vars"
				by (simp add: diff_mult_distrib2)
			hence "\<exists>x y. Neg y = tl s' ! (2*i - 1) \<and> Pos x = tl s' ! Suc (2*i - 1) \<and> Neg y \<in> c' \<and> Pos x \<in> c' \<and> y \<notin> vars \<and> x \<notin> vars"
				using Suc.prems Suc.hyps(2) gt4 n suc_card tl
				by (smt (verit) Nitpick.size_list_simp(2) Suc_1 Suc_diff_Suc diff_Suc_1 diff_is_0_eq' dvd_def hd_Cons_tl linordered_nonzero_semiring_class.zero_le_one mult_eq_self_implies_10 nat_less_le not_less_eq_eq nth_Cons_Suc numeral_eq_Suc odd_one one_le_mult_iff pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
			hence "\<exists>x y. Neg y = s' ! (2*i) \<and> Pos x = s' ! Suc (2*i) \<and> Neg y \<in> c' \<and> Pos x \<in> c' \<and> y \<notin> vars \<and> x \<notin> vars"
				using Suc.prems Suc.hyps(2) tl
				by (metis One_nat_def Suc_1 Suc_diff_Suc diff_zero dvd_def hd_Cons_tl list.size(3) mult_pos_pos nth_Cons_Suc odd_one zero_less_Suc)
			thus ?thesis .
		qed
	qed
qed

lemma last_butlast_tl: "length l \<ge> 3 \<Longrightarrow> last (butlast (tl l)) = last (butlast l)"
	apply (induction l)
	 apply auto
	by (metis One_nat_def Suc_diff_le diff_Suc_Suc length_0_conv length_butlast numeral_2_eq_2 old.nat.distinct(1))

lemma splc_length:
	assumes "finite c" "finite vars" "card c \<ge> 4" "length s' = 2 * (card c - 3) - 1"
					"s' = tl (rev s)" "l = splc c s' init"
	shows "2 + length l = card c"
	using assms
proof (induction "card c - 3" arbitrary: c s s' init vars l)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis using Suc.prems apply auto
  		by (metis (no_types, lifting) Nitpick.size_list_simp(2) One_nat_def hd_Cons_tl length_0_conv length_rev length_tl list.distinct(1) list.sel(3) numeral_2_eq_2 splc.simps(2))
  next
  	case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis

		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

  	hence "2 + length (tl l) = card (snd (pop c))"
  		apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
  		using Suc.prems(1) c finite_insert apply metis
  		using Suc.prems(2) apply simp
  		using gt4 suc_card apply simp
  		using Suc.prems(4) Suc.hyps(2) n apply (metis add.commute add_Suc_right diff_Suc_1 length_tl mult_2)
  		using Suc.prems(5) apply (metis butlast_rev rev_swap)
  		using Suc.prems(6) expand apply fastforce
  		done

  	thus ?thesis using expand suc_card by simp
  qed
qed


lemma splc_aux_clause_first:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y"
	shows "\<exists>i. Pos i \<in> last (butlast l) \<and> init = Pos i"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
	thus ?case
	proof cases
		case eq4
		thus ?thesis
			using Suc.prems by (auto simp add: Let_def)
	next
		case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto


		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

		hence "\<exists>i. Pos i \<in> last (butlast (tl l)) \<and> init = Pos i"
			apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using expand apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) snd_p_set tl_tl_set apply blast
			using disj apply simp
			using Suc.prems(10) apply simp
			done

		moreover have "last (butlast (tl l)) = last (butlast l)"
			apply (rule last_butlast_tl)
			using splc_length gt4 Suc.prems
			by (metis One_nat_def Suc_1 leD nat_add_left_cancel_le not_less_eq_eq numeral_3_eq_3 numeral_Bit0)

		ultimately show ?thesis using Suc.prems Suc.hyps stock_length by blast
	qed
qed


lemma splc_aux_clause_first_alt:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y"
	shows "\<exists>x y. x \<in> last (butlast l) \<and> y \<in> last (butlast l) \<and> x \<in> c \<and> y \<in> c \<and> x \<noteq> y \<and> x \<noteq> init \<and> y \<noteq> init"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
	thus ?case
	proof cases
		case eq4
		let ?p = "pop c"
		let ?q = "pop (snd ?p)"

		have eq4expand: "splc c s' init = {fst ?p, fst ?q, init} # insert (hd s') (snd ?q) # []"
			using eq4 Suc.prems unfolding refc_def
			by (auto simp add: Let_def split: if_splits)

		hence "last (butlast l) = {fst ?p, fst ?q, init}"
			using Suc.prems by force
		moreover have "fst ?p \<in> c"
			using eq4 pop_isin
			by (metis card.empty zero_neq_numeral)
		moreover have "fst ?q \<in> c"
			using eq4 pop_card pop_ins pop_isin 
			by (metis One_nat_def card.empty card_gt_0_iff insertCI one_eq_numeral_iff semiring_norm(83) zero_less_numeral)
		moreover have "fst ?p \<noteq> fst ?q"
			using eq4 pop_card pop_ins pop_isin
			by (metis card_gt_0_iff diff_Suc_1 insert_absorb not_less_eq_eq numeral_eq_Suc pred_numeral_simps(2) zero_less_Suc)
		moreover have "fst ?p \<noteq> init"
			using Suc.prems(8) calculation(2) by blast
		moreover have "fst ?q \<noteq> init"
			using Suc.prems(8) calculation(3) by blast
		ultimately show ?thesis
			by blast
	next
		case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto


		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

		thm Suc.hyps
		hence "\<exists>x y. x \<in> last (butlast (tl l)) \<and> y \<in> last (butlast (tl l)) \<and> x \<in> snd (pop c) \<and> y \<in> snd (pop c) \<and> x \<noteq> y \<and> x \<noteq> init \<and> y \<noteq> init"
			apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using expand apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) snd_p_set tl_tl_set apply blast
			using disj apply simp
			using Suc.prems(10) apply simp
			done

		moreover have "last (butlast (tl l)) = last (butlast l)"
			apply (rule last_butlast_tl)
			using splc_length gt4 Suc.prems
			by (metis One_nat_def Suc_1 leD nat_add_left_cancel_le not_less_eq_eq numeral_3_eq_3 numeral_Bit0)

		ultimately show ?thesis
			using Suc.prems Suc.hyps c by (metis insertCI)
	qed
qed


lemma splc_aux_clause_last:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y"
	shows "\<exists>i. Neg i \<in> last l \<and> hd s = Neg i"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
	thus ?case
	proof cases
		case eq4
		thus ?thesis
			using Suc.prems by (auto simp add: Let_def)
	next
		case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto


		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

		hence "\<exists>i. Neg i \<in> last (tl l) \<and> hd (butlast (butlast s)) = Neg i"
			apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using suc_card expand apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) snd_p_set tl_tl_set apply blast
			using disj apply simp
			using Suc.prems(10) apply simp
			done

		moreover have "last (tl l) = last l"
			using Suc.prems Suc.hyps splc_length
			by (metis Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_eq_plus1 last_tl le_imp_less_Suc less_irrefl_nat numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))

		ultimately show ?thesis using Suc.prems Suc.hyps gt4 hd_stock_neg n suc_card stock_butlast
			by (smt (verit, ccfv_threshold) diff_Suc_1 less_Suc_eq less_trans_Suc numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_diff)
	qed
qed

lemma splc_aux_clause_last_alt:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y"
	shows "\<exists>x y. x \<in> last l \<and> y \<in> last l \<and> x \<in> c \<and> y \<in> c \<and> x \<noteq> y \<and> x \<noteq> hd s \<and> y \<noteq> hd s"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
	thus ?case
	proof cases
		case eq4

		let ?p = "pop c"
		let ?q = "pop (snd ?p)"

		have eq4expand: "splc c s' init = {fst ?p, fst ?q, init} # insert (hd s') (snd ?q) # []"
			using eq4 Suc.prems unfolding refc_def
			by (auto simp add: Let_def split: if_splits)

		hence "\<exists>x y. snd ?q = {x, y}"
			using eq4 pop_card pop_ins
			by (smt card_eq_0_iff diff_Suc_1 finite_insert numeral_3_eq_3 numeral_eq_Suc old.nat.distinct(1) pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))

		then obtain x y where x: "x \<in> snd ?q" and y: "y \<in> snd ?q" and neq: "x \<noteq> y"
			using eq4 pop_card
			by (smt Diff_insert_absorb card.empty card_gt_0_iff card_insert_if diff_Suc_1 finite.emptyI insert_Diff_single insert_absorb insert_commute numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_numeral)

		hence last: "last l = insert (hd s') (snd ?q)"
			using eq4expand Suc.prems by force
		moreover have "x \<in> last l"
			using x last by blast
		moreover have "y \<in> last l"
			using y last by blast
		moreover have "x \<in> c"
			using pop_def x
			by (metis DiffD1 snd_conv)
		moreover have "y \<in> c"
			using pop_def y
			by (metis DiffD1 pop_def snd_conv)
		moreover have "x \<noteq> hd s"
			using Suc.prems Suc.hyps
			by (metis One_nat_def Set.set_insert Suc_pred calculation(4) disjoint_insert(1) last_in_set last_rev last_tl list.size(3) nat_0_less_mult_iff nat_mult_eq_1_iff one_eq_numeral_iff semiring_norm(83) zero_less_Suc zero_less_numeral)
		moreover have "y \<noteq> hd s"
			using Suc.prems Suc.hyps
			by (metis One_nat_def Set.set_insert Suc_pred calculation(5) disjoint_insert(1) last_in_set last_rev last_tl list.size(3) nat_0_less_mult_iff nat_mult_eq_1_iff one_eq_numeral_iff semiring_norm(83) zero_less_Suc zero_less_numeral)
		ultimately show ?thesis
			using neq by blast
	next
		case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto


		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

		thm Suc.hyps
		hence "\<exists>x y. x \<in> last (tl l) \<and> y \<in> last (tl l) \<and> x \<in> snd (pop c) \<and> y \<in> snd (pop c) \<and> x \<noteq> y \<and> x \<noteq> hd (butlast (butlast s)) \<and> y \<noteq> hd (butlast (butlast s))"
			apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using suc_card expand apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) snd_p_set tl_tl_set apply blast
			using disj apply simp
			using Suc.prems(10) apply simp
			done

		moreover have "last (tl l) = last l"
			using Suc.prems Suc.hyps splc_length
			by (metis Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_eq_plus1 last_tl le_imp_less_Suc less_irrefl_nat numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))

		ultimately show ?thesis
			using Suc.prems Suc.hyps
			by (smt One_nat_def Set.set_insert Suc_diff_Suc diff_zero disjoint_insert(1) last_in_set last_rev last_tl list.size(3) nat_0_less_mult_iff nat_mult_eq_1_iff one_eq_numeral_iff semiring_norm(83) snd_p_set subset_iff zero_less_Suc zero_less_numeral)
	qed
qed

lemma splc_init_pos:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y"
	shows "init \<in> last (butlast l)"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
	thus ?case
	proof cases
		case eq4
		thus ?thesis
			using Suc.prems by (auto simp add: Let_def)
	next
		case gt4

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using gt4 Suc.prems splc_gt4 by metis
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto


		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

		hence "init \<in> last (butlast (tl l))"
			apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
				using Suc.prems(1) c finite_insert apply metis
				using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
				using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
				using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
				using Suc.prems(5) expand apply fastforce
				using gt4 suc_card apply simp
				using Suc.prems(7) apply simp
				using Suc.prems(8) snd_p_set tl_tl_set apply blast
				using disj apply simp
				using Suc.prems(10) apply simp
				done

		thus ?thesis using Suc.prems splc_length gt4
			by (smt Suc_1 Suc_pred add_diff_cancel_left' card_gt_0_iff diff_Suc_Suc diff_is_0_eq last_butlast_tl less_Suc_eq_le nless_le numeral_3_eq_3 numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
	qed
qed



lemma simple: "i < length l \<Longrightarrow> l ! i \<in> set l"
	by (rule nth_mem)

lemma nth_butlast_set: "i < length l - 2 \<Longrightarrow> l ! i \<in> set (butlast (butlast l))"
	apply (induction l arbitrary: i)
	 apply auto
	apply (metis One_nat_def length_butlast less_nat_zero_code list.size(3))
	by (metis One_nat_def Suc_diff_Suc Suc_less_eq Suc_pred length_butlast length_greater_0_conv not_gr_zero nth_Cons' numeral_2_eq_2)

lemma "(f\<up>) (Pos v) \<Longrightarrow> a \<noteq> v \<Longrightarrow> ((fun_upd f a b)\<up>) (Pos v)"
	unfolding lift_def by auto

value "take 2 [0::nat, 1, 2]"
value "drop 2 [0::nat, 1, 2]"

lemma set_fold_ident_upd: "\<forall>l \<in> set xs. ident l \<noteq> ident t \<Longrightarrow> (fold (\<lambda>x f. f(ident x := a)) xs f) (ident t) = f (ident t)"
	by (induction xs arbitrary: a t f) auto

lemma in_set_fold_upd: "x \<in> set xs \<Longrightarrow> (fold (\<lambda>x f. f(ident x := True)) xs f) (ident x)"
	by (induction xs arbitrary: x f) (auto, metis fun_upd_same set_fold_ident_upd)

lemma in_set_fold_upd_alt: "x \<in> set xs \<Longrightarrow> \<not>(fold (\<lambda>x f. f(ident x := False)) xs f) (ident x)"
	by (induction xs arbitrary: x f) (auto, metis fun_upd_same set_fold_ident_upd)

lemma set_foldr_ident_upd: "\<forall>l \<in> set xs. ident l \<noteq> ident t \<Longrightarrow> (foldr (\<lambda>x f. if f (ident x) = undefined then f(ident x := a) else f) xs f) (ident t) = f (ident t)"
	by (induction xs arbitrary: a t f) auto

lemma nth_set_take: "\<lbrakk> j < i; i \<le> length xs \<rbrakk> \<Longrightarrow> xs ! j \<in> set (take i xs)"
	by (metis in_set_conv_nth length_take min_less_iff_conj nth_take order_less_le_trans)

lemma refc_cases: "x \<in> set xs \<Longrightarrow> x \<in> set (butlast (butlast xs)) \<or> x = last (butlast xs) \<or> x = last xs"
	apply (induction xs arbitrary: x)
	 apply auto
	by (metis append_butlast_last_id empty_iff empty_set self_append_conv2 set_ConsD)

lemma butlast_butlast_pos: "c \<in> set (butlast (butlast l)) \<longleftrightarrow> (\<exists>j < length l - 2. c = l ! j)"
	apply (induction l arbitrary: c)
	 apply auto
	 	 apply (metis One_nat_def length_butlast less_nat_zero_code list.size(3))
	 	apply (metis One_nat_def length_butlast length_greater_0_conv nth_Cons_0)
	 apply (metis Suc_diff_Suc less_Suc_eq_0_disj not_less_eq nth_Cons_Suc numeral_2_eq_2 zero_less_diff)
	apply (metis One_nat_def Suc_diff_Suc Suc_less_eq Suc_pred length_butlast length_greater_0_conv not_gr_zero nth_Cons' numeral_2_eq_2)
	done


lemma vmap_true_pos_lift: "vmap v \<Longrightarrow> l = Pos v \<Longrightarrow> (vmap\<up>) l"
	unfolding lift_def by simp

lemma vmap_false_neg_lift: "\<not>vmap v \<Longrightarrow> l = Neg v \<Longrightarrow> (vmap\<up>) l"
	unfolding lift_def by simp

(*
lemma sat_single: "c \<noteq> {} \<Longrightarrow> sat (c # [])"
	unfolding sat_def models_def 
	by (metis empty_set ex_in_conv lift_def lit.case_distrib set_ConsD)
*)

lemma sat_tl: "sat expr \<Longrightarrow> sat (tl expr)"
	unfolding sat_def models_def
	by (metis list.sel(2) list.set_sel(2))

lemma sat_rev: "sat expr \<Longrightarrow> sat (rev expr)"
	unfolding sat_def models_def by auto 

lemma sat_butlast: "sat expr \<Longrightarrow> sat (butlast expr)"
	using sat_tl sat_rev butlast_rev rev_swap by metis

lemma sat_subset: "sat expr \<Longrightarrow> sat (filter P expr)"
	unfolding sat_def models_def by auto

lemma sat_append: "sat (xs @ ys) \<Longrightarrow> sat xs \<and> sat ys"
	unfolding sat_def models_def by auto

lemma sat_rotate: "sat (x # xs) \<Longrightarrow> sat (xs @ x # [])"
	unfolding sat_def models_def by simp

lemma sat_rotate_append: "sat (xs @ ys) \<Longrightarrow> sat (ys @ xs)"
	unfolding sat_def models_def by auto


lemma update_preserve_lit: "\<lbrakk> vmap \<Turnstile> expr; vnew \<notin> idset (\<Union>(set expr)); l \<in> \<Union>(set expr) \<rbrakk>
															\<Longrightarrow> ((fun_upd vmap vnew b)\<up>) l = (vmap\<up>) l"
	unfolding idset_def apply (auto simp: fun_upd_def lift_def)
	by (smt (z3) ident.elims lit.simps(5) lit.simps(6))+

lemma update_preserve_sat:
	assumes "sat expr" "vmap \<Turnstile> expr" "vnew \<notin> idset (\<Union>(set expr))" 
	shows "(fun_upd vmap vnew b) \<Turnstile> expr"
	unfolding idset_def sat_def models_def
proof (intro ballI)
	fix clause :: "'a lit set"
	assume clause_in_expr: "clause \<in> set expr"

	obtain lit where "lit \<in> clause" and "(fun_upd vmap vnew b\<up>) lit"
		by (meson UnionI assms(2) assms(3) clause_in_expr models_def update_preserve_lit)

	thus "\<exists>lit \<in> clause. (vmap(vnew := b)\<up>) lit"
		by blast
qed

lemma ex_mid_lift: "(vmap\<up>) (Pos x) \<longleftrightarrow> \<not>(vmap\<up>) (Neg x)"
	unfolding lift_def by auto

lemma splc_aux_hd:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 5" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"\<exists>y. init = Pos y" "idset c \<subseteq> vars"
	shows "hd s' \<in> hd l"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq5) "card c = 5"
  	| (gt5) "card c > 5"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq5

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using eq5 Suc.prems splc_gt4 by (metis eval_nat_numeral(3) less_Suc_eq)
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		hence tlexpand: "splc (snd ?p) ?xs init = {fst (pop (snd ?p)), fst (pop (snd (pop (snd ?p)))), init} # insert (hd ?xs) (snd (pop (snd (pop (snd ?p))))) # []"
			by (smt (verit) Nitpick.size_list_simp(2) Suc.prems(4) Suc_1 Suc_diff_le add_diff_cancel_right' diff_Suc_eq_diff_pred diff_is_0_eq eq5 eval_nat_numeral(3) length_tl list.distinct(1) list.sel(1) list.sel(3) mult_2 not_less_eq_eq numeral_3_eq_3 numeral_Bit0 old.nat.distinct(1) splc.elims)

		hence eq5expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # {fst (pop (snd ?p)), fst (pop (snd (pop (snd ?p)))), init} # insert (hd ?xs) (snd (pop (snd (pop (snd ?p))))) # []"
			using expand eq5 Suc.prems by arith

		hence s: "s = Neg (fresh vars undefined) # Pos (fresh vars undefined)
								# Neg (fresh (insert (fresh vars undefined) vars) undefined) # Pos (fresh (insert (fresh vars undefined) vars) undefined)
								# []"
			using eq5 Suc.prems stock_eq4 suc_card
			by (metis Suc.hyps(2) Suc_diff_le diff_Suc_1 diff_is_0_eq eval_nat_numeral(3) not_less_eq_eq old.nat.distinct(1) stock.simps(2))

		moreover have "?n_prev = Neg (fresh (insert (fresh vars undefined) vars) undefined)"
			using s Suc.prems by simp

		ultimately show ?thesis
			using expand by simp
  next
  	case gt5

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto


		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

		hence "hd (tl (tl s')) \<in> hd (tl l)"
			apply (rule Suc.hyps(1)[where ?s = "butlast (butlast s)" and ?vars = vars and ?init = init])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using Suc.prems splc_gt4 suc_card apply (metis le_numeral_Suc less_Suc_eq_le list.sel(3) pred_numeral_simps(3))
			using gt5 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) snd_p_set tl_tl_set apply blast
			using disj apply simp
			using Suc.prems(10) apply simp
			using Suc.prems(11) idset_def apply (smt mem_Collect_eq snd_p_set subset_iff)
			done

		thus ?thesis
  		using Suc.prems splc_gt4 suc_card
  		by (metis insert_iff le_numeral_Suc less_Suc_eq_le list.sel(1) pred_numeral_simps(3))
  qed
qed


lemma vmap_propagate:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 5" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"\<exists>y. init = Pos y" "idset c \<subseteq> vars"
					"\<forall>l \<in> c. \<not>(vmap\<up>) l" "(vmap\<up>) init" "\<not>(vmap\<up>) (hd s')" "\<forall>c \<in> set l. \<exists>l \<in> c. (vmap\<up>) l"
	shows "\<forall>i. i < length s' \<and> odd i \<longrightarrow> (vmap\<up>) (s' ! i)"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init vmap)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq5) "card c = 5"
  	| (gt5) "card c > 5"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq5

		let ?p = "pop c"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?n_prev = "hd s'"
		let ?p_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		have expand: "l = {?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init"
			using eq5 Suc.prems splc_gt4 by (metis eval_nat_numeral(3) less_Suc_eq)
	
		hence setexpand: "set l = set ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init)"
			by simp

		hence tlexpand: "splc (snd ?p) ?xs init = {fst (pop (snd ?p)), fst (pop (snd (pop (snd ?p)))), init} # insert (hd ?xs) (snd (pop (snd (pop (snd ?p))))) # []"
			by (smt (verit) Nitpick.size_list_simp(2) Suc.prems(4) Suc_1 Suc_diff_le add_diff_cancel_right' diff_Suc_eq_diff_pred diff_is_0_eq eq5 eval_nat_numeral(3) length_tl list.distinct(1) list.sel(1) list.sel(3) mult_2 not_less_eq_eq numeral_3_eq_3 numeral_Bit0 old.nat.distinct(1) splc.elims)

		hence eq5expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} # {fst (pop (snd ?p)), fst (pop (snd (pop (snd ?p)))), init} # insert (hd ?xs) (snd (pop (snd (pop (snd ?p))))) # []"
			using expand eq5 Suc.prems by arith

		hence s: "s = Neg (fresh vars undefined) # Pos (fresh vars undefined)
								# Neg (fresh (insert (fresh vars undefined) vars) undefined) # Pos (fresh (insert (fresh vars undefined) vars) undefined)
								# []"
			using eq5 Suc.prems stock_eq4 suc_card
			by (metis Suc.hyps(2) Suc_diff_le diff_Suc_1 diff_is_0_eq eval_nat_numeral(3) not_less_eq_eq old.nat.distinct(1) stock.simps(2))

		hence s': "s' = Neg (fresh (insert (fresh vars undefined) vars) undefined) # Pos (fresh vars undefined) # Neg (fresh vars undefined) # []"
			using Suc.prems by simp

		thus ?thesis
		proof (intro allI impI)
			fix i
			assume a: "i < length s' \<and> odd i"

			hence i1: "i = 1"
				using s' less_Suc_eq by fastforce

			have "\<exists>l \<in> {?n_prev, fst ?p, ?p_cur}. (vmap\<up>) l"
				using Suc.prems(15) expand by fastforce
			moreover have "\<not>(vmap\<up>) ?n_prev"
				using Suc.prems(14) by simp
			moreover have "\<not>(vmap\<up>) (fst ?p)"
				using Suc.prems(12) c by blast
			ultimately have "(vmap\<up>) (?p_cur)"
				by blast

			moreover have "?p_cur = s' ! i"
				using i1 s' by simp

			ultimately show "(vmap\<up>) (s' ! i)" by simp
		qed
  next
  	case gt5

		let ?p = "pop c"
		let ?q = "pop (snd ?p)"
		let ?t = "fst ?p"
		let ?rest = "snd ?p"
	
		have c: "c = insert ?t ?rest"
			using pop_ins Suc.prems Suc.hyps
			by (metis card.empty diff_le_self less_eq_nat.simps(1) not_less_eq_eq)
	
		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto


		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto


		let ?n1_prev = "hd s'"
		let ?p1_cur = "hd (tl s')"
		let ?xs = "tl (tl s')"

		let ?n2_prev = "hd (tl (tl s'))"
		let ?p2_cur = "hd (tl (tl (tl s')))"
		let ?xss = "tl (tl (tl (tl s')))"

		have expand: "l = {?n1_prev, fst ?p, ?p1_cur} # splc (snd ?p) ?xs init"
			using gt5 Suc.prems splc_gt4 suc_card
			by (metis le_numeral_Suc less_Suc_eq_le pred_numeral_simps(3))

		have gt5expand: "l = {?n1_prev, fst ?p, ?p1_cur} # {?n2_prev, fst ?q, ?p2_cur} # splc (snd ?q) ?xss init"
			using Suc.prems Suc.hyps splc_gt4 suc_card expand gt5
			by (smt (verit, ccfv_threshold) Suc_diff_le diff_Suc_1 diff_Suc_eq_diff_pred diff_is_0_eq diff_mult_distrib2 eval_nat_numeral(3) length_tl mult_2 nat_less_le not_less_eq_eq plus_1_eq_Suc)

		
		have "\<exists>l \<in> {?n1_prev, fst ?p, ?p1_cur}. (vmap\<up>) l"
			using Suc.prems(15) expand by fastforce
		moreover have "\<not>(vmap\<up>) ?n1_prev"
			using Suc.prems(14) by simp
		moreover have "\<not>(vmap\<up>) (fst ?p)"
			using Suc.prems(12) c by blast
		ultimately have lift: "(vmap\<up>) (?p1_cur)"
			by blast

		thm tl_rev_stock_odd_pos
		have "\<exists>x. tl (rev (stock (card c - 3) vars)) ! 1 = Pos x"
			apply (rule tl_rev_stock_odd_pos)
			using Suc.prems by auto

		then obtain x where pos_x: "tl (rev (stock (card c - 3) vars)) ! 1 = Pos x"
			by blast

		thm tl_rev_stock_pair
		have neg_x: "tl (rev (stock (card c - 3) vars)) ! Suc 1 = Neg x"
			apply (rule tl_rev_stock_pair)
			using Suc.prems pos_x by auto

		have p1: "tl (rev (stock (card c - 3) vars)) ! 1 = ?p1_cur"
			using Suc.prems Suc.hyps stock_eq4 lift
			by (smt (verit) Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_pred eval_nat_numeral(3) hd_conv_nth le_imp_less_Suc less_Suc_eq_0_disj less_not_refl mult_eq_self_implies_10 mult_pos_pos nth_tl stock.elims)

		moreover have "tl (rev (stock (card c - 3) vars)) ! 2 = ?n2_prev"
			using expand gt5expand Suc.prems
			by (smt (verit) Nil_tl One_nat_def Suc_1 hd_Cons_tl hd_conv_nth list.distinct(1) list.inject nth_Cons_Suc splc.elims)

		ultimately have nolift: "\<not>(vmap\<up>) (?n2_prev)"
			using ex_mid_lift pos_x neg_x lift
			by (metis Suc_1)


		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith

		thm Suc.hyps
		hence "\<forall>i. i < length (tl (tl s')) \<and> odd i \<longrightarrow> (vmap\<up>) ((tl (tl s')) ! i)"
			apply (rule Suc.hyps(1)[where ?s = "butlast (butlast s)" and ?vars = vars and ?init = init and ?l = "tl l"])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using Suc.prems splc_gt4 suc_card apply (metis le_numeral_Suc less_Suc_eq_le list.sel(3) pred_numeral_simps(3))
			using gt5 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) snd_p_set tl_tl_set apply blast
			using disj apply simp
			using Suc.prems(10) apply simp
			using Suc.prems(11) idset_def apply (smt mem_Collect_eq snd_p_set subset_iff)
			using Suc.prems(12) snd_p_set apply blast
			using Suc.prems(13) apply simp
			using nolift apply simp
			using Suc.prems(15) apply (metis list.sel(2) list.set_sel(2))
			done

		hence "\<forall>i. i < length s' - 2 \<and> odd i \<longrightarrow> (vmap\<up>) ((tl (tl s')) ! i)"
			by fastforce
		hence "\<forall>i. i < length s' - 2 \<and> odd i \<longrightarrow> (vmap\<up>) (s' ! (i+2))"
			by (simp add: less_diff_conv nth_tl)
		hence "\<forall>i. i > 1 \<and> i < length s' \<and> odd i \<longrightarrow> (vmap\<up>) (s' ! i)"
			by (metis One_nat_def Suc_diff_Suc Suc_lessD Suc_pred add_2_eq_Suc' less_diff_conv odd_add plus_1_eq_Suc)

		moreover have "\<forall>i. i \<le> 1 \<and> i < length s' \<and> odd i \<longrightarrow> (vmap\<up>) (s' ! i)"
			using Suc.prems lift p1
			by (metis antisym_conv2 less_numeral_extra(3) less_one odd_pos)

  	ultimately show ?thesis
  		by (meson linorder_not_le)
  qed
qed



lemma reverse_checkpoint_aux: "\<not> sat (fst (refc c vars) @ xs)
															\<longleftrightarrow> (\<forall>vmap. \<exists>c' \<in> set (fst (refc c vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l) \<or> \<not>(\<forall>c' \<in> set (fst (refc c vars) @ xs). 0 < card c')"
	unfolding sat_def models_def by simp

lemma reverse_checkpoint_le3_alt:
	assumes "\<not> sat (c # xs)" "card c \<le> 3"
	shows "(\<forall>vmap. \<exists>c' \<in> set (fst (refc c vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l) \<or> \<not>(\<forall>c' \<in> set (fst (refc c vars) @ xs). 0 < card c')"
	using assms unfolding sat_def models_def refc_def
	by (auto simp add: Let_def split: if_splits)

lemma reverse_checkpoint_le3:
	assumes "\<not> sat (c # xs)" "card c \<le> 3"
	shows "\<not> sat (fst (refc c vars) @ xs)"
	using assms reverse_checkpoint_le3_alt reverse_checkpoint_aux
	by metis

lemma reverse_checkpoint_alt:
	assumes "\<not> sat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite c" "finite vars" "card c \<ge> 4"
					"\<forall>c' \<in> set (c # xs). finite c'"
	shows "\<forall>vmap. \<exists>c' \<in> set (fst (refc c vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l"
	using assms unfolding sat_def models_def
proof -
	let ?s = "stock (card c - 3) vars"

	have "\<nexists>vmap. vmap \<Turnstile> c # xs"
		using assms sat_def models_def
		by (metis bot_nat_0.not_eq_extremum card_eq_0_iff empty_iff)
	hence "\<nexists>vmap. \<forall>c' \<in> set (c # xs). \<exists>l \<in> c'. (vmap\<up>) l"
		unfolding models_def by simp
	hence "\<forall>vmap. \<not> (\<forall>c' \<in> set (c # xs). \<exists>l \<in> c'. (vmap\<up>) l)"
		by simp
	hence "\<forall>vmap. \<exists>c' \<in> set (c # xs). \<not> (\<exists>l \<in> c'. (vmap\<up>) l)"
		by simp
	hence a: "\<forall>vmap. \<exists>c' \<in> set (c # xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l"
		by simp

	thus ?thesis
	proof (intro allI)
		fix vmap

		have "(\<forall>l \<in> c. \<not> (vmap\<up>) l) \<or> (\<exists>c' \<in> set xs. \<forall>l \<in> c'. \<not> (vmap\<up>) l)"
			using a by simp
		then consider (hd) "(\<forall>l \<in> c. \<not> (vmap\<up>) l)"
			| (tl) "(\<exists>c' \<in> set xs. \<forall>l \<in> c'. \<not> (vmap\<up>) l)"
			by blast
		thus "\<exists>c' \<in> set (fst (refc c vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l"
		proof cases
			case hd
			show "\<exists>c' \<in> set (fst (refc c vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l"
			proof (rule ccontr)
				assume "\<not> (\<exists>c' \<in> set (fst (refc c vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l)"

				hence "\<forall>c' \<in> set (fst (refc c vars) @ xs). \<not> (\<forall>l \<in> c'. \<not> (vmap\<up>) l)"
					by simp
				hence f: "\<forall>c' \<in> set (fst (refc c vars) @ xs). \<exists>l \<in> c'. (vmap\<up>) l"
					by simp

				have c1: "last (butlast (fst (refc c vars))) \<in> set (fst (refc c vars))"
					unfolding refc_def using assms apply (auto simp add: Let_def split: if_splits)
					using splc_length stock_length
					by (smt One_nat_def Suc_1 Suc_diff_le add_diff_cancel_left' add_is_0 diff_Suc_Suc diff_commute in_set_butlastD last_in_set length_butlast length_rev length_tl list.size(3) numeral_3_eq_3 numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_one)

				have c2: "last (butlast (fst (refc c vars))) \<in> set ((fst (refc c vars)) @ xs)"
					unfolding refc_def using assms apply (auto simp add: Let_def split: if_splits)
					using splc_length stock_length
					by (smt One_nat_def Suc_1 Suc_diff_le add_diff_cancel_left' add_is_0 diff_Suc_Suc diff_commute in_set_butlastD last_in_set length_butlast length_rev length_tl list.size(3) numeral_3_eq_3 numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_one)

		
				have aux1: "set (tl (rev (stock (card c - 3) vars))) \<inter> c = {}"
					apply (rule refc_stock_clause_disj)
					unfolding refc_def apply (simp add: Let_def split: if_splits)
					using assms apply simp
					using assms apply simp
					using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
					done
			
				have aux2: "last (stock (card c - 3) vars) \<notin> set (tl (rev (stock (card c - 3) vars))) \<union> c"
					apply (rule refc_init_uniq)
					unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
					using assms apply simp
					using assms apply simp
					using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
					done
		
				have aux3: "card (last (butlast (fst (refc c vars)))) = 3"
					unfolding refc_def using assms(5) apply (auto simp add: Let_def split: if_splits)
					apply (rule splc_card_3[of c "stock (card c - 3) vars" vars "tl (rev (stock (card c - 3) vars))" _ "last (stock (card c - 3) vars)"])
					prefer 5 using c1 refc_def stock_le3 apply (metis (no_types, lifting) Nil_is_rev_conv fst_conv list.distinct(1) splc.elims tl_Nil)
					using assms stock_length aux1 aux2 apply fastforce+
					done

				thm last_stock_pos
				have aux4: "\<exists>v. v \<notin> vars \<and> last (stock (card c - 3) vars) = Pos v"
					apply (rule last_stock_pos)
					using assms by simp+
		
				thm splc_aux_clause_first
				have "\<exists>v. Pos v \<in> last (butlast (fst (refc c vars))) \<and> last ?s = Pos v"
					apply (rule splc_aux_clause_first[of c ?s vars "tl (rev ?s)" _ "last ?s"])
					unfolding refc_def using assms(5) apply (auto simp add: Let_def split: if_splits)
					using assms stock_length aux1 aux2 aux4 apply fastforce+
					done
		
				then obtain v where v1: "Pos v \<in> last (butlast (fst (refc c vars)))" and v2: "last ?s = Pos v"
					by blast
		
				thm splc_aux_clause_first_alt
				have "\<exists>x y. x \<in> last (butlast (fst (refc c vars))) \<and> y \<in> last (butlast (fst (refc c vars))) \<and> x \<in> c \<and> y \<in> c \<and> x \<noteq> y \<and> x \<noteq> last ?s \<and> y \<noteq> last ?s"
					apply (rule splc_aux_clause_first_alt[of c ?s vars "tl (rev ?s)" _ "last ?s"])
					unfolding refc_def using assms(5) apply (auto simp add: Let_def split: if_splits)
					using assms stock_length aux1 aux2 aux4 apply fastforce+
					done
		
				then obtain x y where x: "x \<in> last (butlast (fst (refc c vars)))" and y: "y \<in> last (butlast (fst (refc c vars)))"
													and x_c: "x \<in> c" and y_c: "y \<in> c" and xy: "x \<noteq> y" and x_last: "x \<noteq> last ?s" and y_last: "y \<noteq> last ?s"
					by blast
		
				have "\<exists>x y z. last (butlast (fst (refc c vars))) = {x, y, z}"
					using aux3 by (meson card_3_iff)
				hence "\<exists>x y. last (butlast (fst (refc c vars))) = {x, y, Pos v}"
					using v1 by fastforce
				hence first_set: "last (butlast (fst (refc c vars))) = {x, y, Pos v}"
					using x x_last xy y y_last v2 by auto
				
				hence "\<not>(vmap\<up>) x" and "\<not>(vmap\<up>) y"
					using f x_c y_c hd by simp+
				hence lift_pos: "(vmap\<up>) (Pos v)"
					using f first_set c2 by fastforce
		
				hence nolift: "\<not>(vmap\<up>) (Neg v)"
					using ex_mid_lift by metis
		
				thm splc_aux_clause
				moreover have "\<forall>c \<in> set (butlast (butlast (fst (refc c vars)))). \<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c \<and> Neg j \<in> c"
					apply (rule splc_aux_clause[of c ?s vars "tl (rev ?s)" _ "last ?s"])
					prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
					using assms stock_length aux1 aux2 aux4 unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+
		
				consider (eq4) "card c = 4"
					| (gt4) "card c > 4"
					using assms by arith
				thus "False"
				proof cases
					case eq4
		
					let ?p = "pop c"
					let ?q = "pop (snd ?p)"
		
					have expand: "fst (refc c vars) = {fst ?p, fst ?q, Pos v} # insert (Neg v) (snd ?q) # []"
						unfolding refc_def using eq4 stock_eq4 v2
						by (simp add: Let_def split: if_splits)
		
					hence "\<forall>l \<in> insert (Neg v) (snd ?q). \<not> (vmap\<up>) l"
						using assms calculation hd pop_ins  x_c xy y_c
						by (metis empty_iff finite_insert insertCI insertE)
		
					thus ?thesis using f expand by simp
				next
					case gt4
		
					thm splc_aux_hd
					moreover have "hd (tl (rev ?s)) \<in> hd (fst (refc c vars))"
						apply (rule splc_aux_hd[of c ?s vars "tl (rev ?s)" _ "last ?s"])
						prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
						using assms stock_length aux1 aux2 aux4 gt4 unfolding refc_def
						by (fastforce simp add: Let_def split: if_splits)+
		
					thm tl_rev_stock_even_neg
					have "\<exists>x. tl (rev ?s) ! 0 = Neg x"
						apply (rule tl_rev_stock_even_neg)
						using assms apply simp
						using gt4 apply simp
						 apply simp
						using assms stock_le3 stock_length_even
						by (metis Nitpick.size_list_simp(2) One_nat_def gr0I not_less_eq_eq numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
		
					then obtain x where tl_rev_neg_x: "tl (rev ?s) ! 0 = Neg x"
						by blast
		
					hence nth_neg_x: "?s ! (length ?s - 2) = Neg x"
						using assms stock_length_even
						by (smt (verit) Nitpick.size_list_simp(2) One_nat_def Suc_1 diff_0_eq_0 length_greater_0_conv length_rev length_tl nth_tl odd_one rev_nth zero_less_diff)
		
					thm stock_pair
					have "?s ! Suc (length ?s - 2) = Pos x"
						apply (rule stock_pair)
						using assms apply simp
						using gt4 apply simp
						using stock_length_even assms apply fastforce
						using assms stock_gt0 stock_length_even
						apply (smt (verit) Suc_lessI Suc_less_eq diff_less dvd_minus_self even_Suc le_imp_less_Suc numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_diff zero_less_numeral)
						using nth_neg_x by blast
		
					hence pos_x: "?s ! (length ?s - 1) = Pos x"
						using assms stock_le3 stock_length_even
						by (metis One_nat_def Suc_1 Suc_diff_Suc Suc_lessI length_greater_0_conv not_less_eq_eq numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
					moreover have stock_not_nil: "?s \<noteq> []"
						using assms stock_gt0 by fastforce
					find_theorems "last ?l = ?l ! ?i"
					ultimately have "last ?s = Pos x"
						by (simp add: last_conv_nth)
		
					hence xv: "x = v"
						using v2 by simp
		
					hence neg_v: "(hd (tl (rev ?s))) = Neg v"
						using nth_neg_x tl_rev_neg_x pos_x
						by (metis Suc_1 diff_Suc_eq_diff_pred hd_conv_nth length_rev length_tl list.sel(2) lit.distinct(1))
		
					hence nolift_aux: "\<not> (vmap\<up>) (hd (tl (rev ?s)))"
						using nolift by simp
		
		
		
					have "even (length ?s)"
						using assms stock_length_even by blast
					hence "even (length (rev ?s))"
						by simp
					hence odd_len: "odd (length (tl (rev ?s)))"
						using stock_not_nil by simp
		
					have "length ?s \<ge> 3"
						using gt4 stock_length assms by fastforce
					hence len_ge2: "length (tl (rev ?s)) \<ge> 2"
						by simp
		
					thm vmap_propagate
					have "\<forall>i. i < length (tl (rev ?s)) \<and> odd i \<longrightarrow> (vmap\<up>) ((tl (rev ?s)) ! i)"
						apply (rule vmap_propagate[of c ?s vars "tl (rev ?s)" "fst (refc c vars)" "last ?s"])
						prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
						using assms stock_length aux1 aux2 aux4 gt4 hd lift_pos v2 nolift_aux f unfolding refc_def
						by (fastforce simp add: Let_def split: if_splits)+
		
					moreover have odd_q: "odd (length (tl (rev ?s)) - 2)"
						using odd_len len_ge2 by simp
						
					ultimately have lift_pos: "(vmap\<up>) ((tl (rev ?s)) ! (length (tl (rev ?s)) - 2))"
						by auto
		
					thm splc_aux_clause_last
					have "\<exists>i. Neg i \<in> last (fst (refc c vars)) \<and> hd ?s = Neg i"
						apply (rule splc_aux_clause_last[of c ?s vars "tl (rev ?s)" "fst (refc c vars)" "last ?s"])
						using assms stock_length aux1 aux2 aux4 unfolding refc_def
						by (fastforce simp add: Let_def split: if_splits)+
		
					then obtain q where q1: "Neg q \<in> last (fst (refc c vars))" and q2: "hd ?s = Neg q"
						by blast
		
					hence "Neg q = last (tl (rev ?s))"
						using stock_not_nil pos_x
						by (metis hd_conv_nth last_rev last_tl length_rev length_tl list.size(3) lit.distinct(1))
		
					hence "Neg q = tl (rev ?s) ! (length (tl (rev ?s)) - 1)"
						using stock_not_nil tl_rev_neg_x neg_v xv
						by (metis hd_Nil_eq_last last_conv_nth length_tl list.sel(2) list.size(3))
		
					hence "Pos q = (tl (rev ?s)) ! (length (tl (rev ?s)) - 2)"
						using assms odd_len len_ge2 odd_q stock_not_nil tl_rev_stock_pair_alt
						by (smt (verit) One_nat_def Suc_1 Suc_diff_le Suc_pred diff_Suc_eq_diff_pred length_greater_0_conv length_rev length_tl lessI less_Suc_eq_0_disj odd_Suc_minus_one stock.elims)
		
					hence "(vmap\<up>) (Pos q)"
						using lift_pos by arith
		
					hence nolift_q: "\<not>(vmap\<up>) (Neg q)"
						using ex_mid_lift by metis
		
		
					thm splc_aux_clause_last_alt
					have "\<exists>x y. x \<in> last (fst (refc c vars)) \<and> y \<in> last (fst (refc c vars)) \<and> x \<in> c \<and> y \<in> c \<and> x \<noteq> y \<and> x \<noteq> hd ?s \<and> y \<noteq> hd ?s"
						apply (rule splc_aux_clause_last_alt[of c ?s vars "tl (rev ?s)" "fst (refc c vars)" "last ?s"])
						using assms stock_length aux1 aux2 aux4 unfolding refc_def
						by (fastforce simp add: Let_def split: if_splits)+
		
					then obtain l1 l2 where l1_last: "l1 \<in> last (fst (refc c vars))" and l2_last: "l2 \<in> last (fst (refc c vars))"
															and l1_c: "l1 \<in> c" and l2_c: "l2 \<in> c" and l1_l2: "l1 \<noteq> l2" and l1_hd: "l1 \<noteq> hd ?s" and l2_hd: "l2 \<noteq> hd ?s"
						by blast
		
					thm splc_card_3
					have "card (last (fst (refc c vars))) = 3"
						unfolding refc_def using assms(5) apply (auto simp add: Let_def split: if_splits)
						apply (rule splc_card_3[of c "stock (card c - 3) vars" vars "tl (rev (stock (card c - 3) vars))" _ "last (stock (card c - 3) vars)"])
						prefer 5 using c1 refc_def stock_le3 stock_not_nil apply (metis empty_iff empty_set fst_conv last_in_set stock_not_nil)
						using assms stock_length aux1 aux2 apply fastforce+
						done
		
					hence "\<exists>x y z. last (fst (refc c vars)) = {x, y, z}"
						by (meson card_3_iff)
					hence "\<exists>z. last (fst (refc c vars)) = {l1, l2, z}"
						using l1_last l2_last l1_l2 by auto
					moreover have "l1 \<noteq> Neg q"
						using q2 l1_hd by arith
					moreover have "l2 \<noteq> Neg q"
						using q2 l2_hd by arith
					ultimately have "last (fst (refc c vars)) = {l1, l2, Neg q}"
						using q1 by fastforce
		
					moreover have "\<not>(vmap\<up>) l1"
						using l1_c hd by simp
					moreover have "\<not>(vmap\<up>) l2"
						using l2_c hd by simp
					ultimately have "\<forall>l \<in> last (fst (refc c vars)). \<not>(vmap\<up>) l"
						using nolift_q by simp
		
					thus ?thesis using f c1 c2
						by (metis Un_iff empty_iff empty_set last_in_set set_append)
				qed
			qed
		next
			case tl
			thus ?thesis by auto
		qed
	qed
qed

lemma reverse_checkpoint:
	assumes "\<not> sat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite c" "finite vars" "card c \<ge> 4"
					"\<forall>c' \<in> set (c # xs). finite c'"
	shows "\<not> sat (fst (refc c vars) @ xs)"
	using assms reverse_checkpoint_alt reverse_checkpoint_aux
	by fast


lemma checkpoint_le3:
	assumes "sat (c # xs)" "card c \<le> 3"
	shows "sat (fst (refc c vars) @ xs)"
	using assms unfolding refc_def
	by (auto simp add: Let_def split: if_splits)


lemma checkpoint1:
	assumes "sat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite c" "finite vars" "card c \<ge> 4"
	shows "\<exists>vmap_new. \<forall>c' \<in> set (fst (refc c vars) @ xs). \<exists>l \<in> c'. (vmap_new\<up>) l"
	using assms unfolding sat_def models_def
proof -
	let ?s = "stock (card c - 3) vars"

	have "sat (fst (refc c vars) @ xs) = sat (splc c (tl (rev ?s)) (last ?s) @ xs)"
		unfolding refc_def by (auto simp add: Let_def split: if_splits)

	hence "\<exists>vmap. vmap \<Turnstile> c # xs"
		using sat_def assms by blast

	then obtain vmap_orig where vmap_orig: "\<forall>c' \<in> set (c # xs). \<exists>l \<in> c'. (vmap_orig\<up>) l"
		using models_def by blast



	have "\<forall>c' \<in> set (c # xs). \<exists>l \<in> c'. (vmap_orig\<up>) l"
		using vmap_orig by simp

	hence "\<exists>l \<in> c. (vmap_orig\<up>) l"
		by simp

	then obtain tgt where tgt1: "tgt \<in> c" and tgt2: "(vmap_orig\<up>) tgt"
		by blast

	have aux1: "set (tl (rev (stock (card c - 3) vars))) \<inter> c = {}"
		apply (rule refc_stock_clause_disj)
		unfolding refc_def apply (simp add: Let_def split: if_splits)
		using assms apply simp
		using assms apply simp
		using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
		done

	have aux2: "last (stock (card c - 3) vars) \<notin> set (tl (rev (stock (card c - 3) vars))) \<union> c"
		apply (rule refc_init_uniq)
		unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
		using assms apply simp
		using assms apply simp
		using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
		done

	have aux3: "\<exists>x. last (stock (card c - 3) vars) = Pos x \<and> hd (tl (rev (stock (card c - 3) vars))) = Neg x"
		apply (rule refc_init_pos)
		unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
		using assms apply simp
		using assms apply simp
		using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
		done


	have tgt: "\<exists>c' \<in> set (fst (refc c vars)). tgt \<in> c'"
		unfolding refc_def
		apply (rule splc_preserve_lit[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
		using assms aux1 aux2 tgt1 stock_length by (fastforce simp add: Let_def split: if_splits)+

	then consider (middle) "\<exists>i. tgt \<in> fst (refc c vars) ! i \<and> i < length (fst (refc c vars)) - 2"
		| (first) "tgt \<in> fst (refc c vars) ! (length (fst (refc c vars)) - 2)"
		| (last) "tgt \<in> fst (refc c vars) ! (length (fst (refc c vars)) - 1)"
		by (smt (verit, best) One_nat_def Suc_pred diff_Suc_eq_diff_pred diff_is_0_eq in_set_conv_nth length_pos_if_in_set less_SucE less_Suc_eq_le numeral_2_eq_2 zero_less_numeral)
	thus "\<exists>vmap_new. \<forall>c' \<in> set (fst (refc c vars) @ xs). \<exists>l \<in> c'. (vmap_new\<up>) l"
	proof cases
		case middle

		then obtain i where i: "tgt \<in> fst (refc c vars) ! i" and i_hi: "i < (length (fst (refc c vars)) - 2)"
			by blast
		moreover obtain c_tgt where c_tgt: "c_tgt = fst (refc c vars) ! i"
			by simp
		ultimately have tgt: "tgt \<in> c_tgt"
			by simp

		have c_tgt_refc: "c_tgt \<in> set (fst (refc c vars))"
			using c_tgt assms(5) unfolding refc_def apply (auto simp add: Let_def split: if_splits)
			apply (rule nth_mem)
			using i_hi unfolding refc_def apply (auto simp add: Let_def split: if_splits)
			done
		hence aux: "c_tgt \<in> set (splc c (tl (rev (stock (card c - 3) vars))) (last (stock (card c - 3) vars)))"
			unfolding refc_def by (auto simp add: Let_def split: if_splits)

		have card3: "card c_tgt = 3"
			apply (rule splc_card_3[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
			using assms aux aux1 aux2 tgt1 stock_length by (fastforce simp add: Let_def split: if_splits)+

		have idset_subs_vars: "idset c \<subseteq> vars"
			using assms idset_iff by (meson UnionI list.set_intros(1) subset_iff)

		have aux_c: "\<forall>c' \<in> set (butlast (butlast (fst (refc c vars)))). \<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c' \<and> Neg j \<in> c'"
			apply (rule splc_aux_clause[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
			using assms aux1 aux2 aux3 stock_length idset_subs_vars unfolding refc_def
			by (fastforce simp add: Let_def split: if_splits)+



		moreover have c_tgt_set: "c_tgt \<in> set (butlast (butlast (fst (refc c vars))))"
			using c_tgt i_hi nth_butlast_set by simp

		ultimately obtain lv rv where lv: "Neg lv \<in> c_tgt" and rv: "Pos rv \<in> c_tgt"
			and lv_vars: "lv \<notin> vars" and rv_vars: "rv \<notin> vars" and lv_rv: "lv \<noteq> rv"
			by blast

		have "\<exists>x y z. x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z \<and> c_tgt = {x, y, z}"
			using card3 by (meson card_3_iff)

		moreover have tgt_lv: "tgt \<noteq> Neg lv"
			using tgt1 assms(2) lv_vars idset_iff by (meson UnionI list.set_intros(1) subset_iff)

		moreover have tgt_rv: "tgt \<noteq> Pos rv"
			using tgt1 assms(2) rv_vars idset_iff by (meson UnionI list.set_intros(1) subset_iff)

		ultimately have "c_tgt = {Neg lv, tgt, Pos rv}"
			using lv rv tgt by auto

		(* initially set all stock variable mappings in current clause to false -- lifts for negatives *)
		obtain vmap_n0 where vmap_n0: "vmap_n0 = (\<lambda>v. if v \<in> idset (set ?s) then False else vmap_orig v)"
			by auto
		then obtain vmap_n1 where vmap_n1: "vmap_n1 = vmap_n0(ident tgt := case tgt of Pos x \<Rightarrow> True | Neg x \<Rightarrow> False)"
			using tgt2 by blast
		hence vmap_lift_tgt: "(vmap_n1\<up>) tgt"
			using lift_def by (smt (verit) fun_upd_apply ident.elims lit.simps(5) lit.simps(6))
		then obtain vmap_n2 where vmap_n2: "vmap_n2 = fun_upd vmap_n1 lv True"
			by auto
		then obtain vmap_tgt where vmap_tgt: "vmap_tgt = fun_upd vmap_n2 rv False"
			by auto

		hence "\<not>(vmap_tgt\<up>) (Neg lv)"
			using lv_rv vmap_n2 unfolding lift_def by simp
		hence "\<not>(vmap_tgt\<up>) (Pos rv)"
			using vmap_tgt unfolding lift_def by simp
		hence vmap_tgt_carry: "(vmap_tgt\<up>) tgt"
			using tgt_lv tgt_rv vmap_n1 vmap_n2 vmap_tgt lift_def vmap_lift_tgt
			by (smt fun_upd_apply lit.exhaust lit.simps(5) lit.simps(6))

		let ?front = "take (2*i) (tl (rev ?s))"
		let ?rear = "drop (2*(Suc i)) (tl (rev ?s))"

		obtain vmap_tgt_front where vmap_tgt_front:
			"vmap_tgt_front = fold (\<lambda>x f. f(ident x := True)) ?front vmap_tgt"
			by blast

		find_theorems "fun_upd"
		thm "fun_upd_other"
		thm "set_fold_ident_upd"

		have stock_clause_disj: "\<forall>l \<in> set (tl (rev ?s)). ident l \<notin> idset c"
			using assms unfolding idset_def apply auto
			by (smt butlast_rev idset_def in_set_butlastD mem_Collect_eq set_rev stock_fresh)
		moreover have front_stock: "set ?front \<subseteq> set (tl (rev ?s))" and rear_stock: "set ?rear \<subseteq> set (tl (rev ?s))"
			by (meson set_take_subset, meson set_drop_subset)
		ultimately have front_ident: "\<forall>l \<in> set ?front. ident l \<notin> idset c" and rear_ident: "\<forall>l \<in> set ?rear. ident l \<notin> idset c"
			by blast+

		have tgt_in_c: "ident tgt \<in> idset c"
			using tgt1 unfolding idset_def by auto
		hence "\<forall>l \<in> set ?front. ident l \<noteq> ident tgt"
			using front_ident by metis
		hence "(fold (\<lambda>x f. f(ident x := True)) ?front vmap_tgt) (ident tgt) = vmap_tgt (ident tgt)"
			by (rule set_fold_ident_upd)
		hence "vmap_tgt_front (ident tgt) = vmap_tgt (ident tgt)"
			using vmap_tgt_front by simp
		hence vmap_tgt_front_carry: "(vmap_tgt_front\<up>) tgt"
			using vmap_tgt_carry lift_def by (smt ident.elims lit.simps(5) lit.simps(6))

		then obtain vmap_new where vmap_new:
			"vmap_new = vmap_tgt_front(ident (last ?s) := True)"
			by blast

		hence "ident (last ?s) \<noteq> ident tgt"
			using assms stock_clause_disj tgt_in_c aux2 aux3 stock_length_even tgt1
			by (metis Nil_is_rev_conv Nitpick.size_list_simp(2) One_nat_def Un_iff ident.elims ident.simps(1) last_rev length_rev list.set_sel(1) odd_one)
		hence "vmap_new (ident tgt) = vmap_tgt_front (ident tgt)"
			using vmap_new by simp
		hence vmap_new_lift_tgt: "(vmap_new\<up>) tgt"
			using vmap_tgt_front_carry lift_def by (smt ident.elims lit.simps(5) lit.simps(6))


		have "2 * i < 2*length (fst (refc c vars)) - 4"
			using i_hi by simp
		also have twice_i_bound_alt: "... = 2*(card c - 2) - 4"
			unfolding refc_def using assms aux3 splc_length stock_le3 stock_length
			by (smt add_diff_cancel_left' fst_conv last_rev length_rev length_tl list.sel(2) lit.distinct(1) rev.simps(1))
		also have "... = 2*(card c - 3) - 2"
			by simp
		also have "... = length (stock (card c - 3) vars) - 2"
			using stock_length assms by metis
		also have "... = length (tl (rev (stock (card c - 3) vars))) - 1"
			by simp
		finally have twice_i_bound: "2 * i \<le> length (tl (rev (stock (card c - 3) vars)))"
			by simp

		show ?thesis
		proof (intro exI ballI)
			fix c'
			assume c': "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (update) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			hence "\<exists>l \<in> c'. (vmap_new\<up>) l"
			proof cases
				case update
	
				then consider (tgt) "c' = fst (refc c vars) ! i"
					| (front) "\<exists>j. j < i \<and> c' = fst (refc c vars) ! j"
					| (rear) "\<exists>j. j > i \<and> j < length (fst (refc c vars)) \<and> c' = fst (refc c vars) ! j"
					by (metis in_set_conv_nth nat_neq_iff)
				thus ?thesis
				proof cases
					case tgt
					thus ?thesis using vmap_new_lift_tgt i by blast
				next
					case front
					then obtain j where j: "j < i" and c': "c' = fst (refc c vars) ! j"
						by blast
	
					thm splc_aux_clause_nth
					have "\<exists>x y. Neg y = tl (rev ?s) ! (2 * j) \<and> Pos x = tl (rev ?s) ! Suc (2 * j) \<and> Neg y \<in> c' \<and> Pos x \<in> c' \<and> y \<notin> vars \<and> x \<notin> vars"
						apply (rule splc_aux_clause_nth[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"
									and ?l = "splc c (tl (rev (stock (card c - 3) vars))) (last (stock (card c - 3) vars))" and ?c' = c'])
						prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
						using assms stock_length aux1 aux2 aux3 c' j i_hi unfolding refc_def
						by (fastforce simp add: Let_def split: if_splits)+
	
					hence "\<exists>x. Pos x = tl (rev ?s) ! Suc (2 * j) \<and> Pos x \<in> c'"
						by blast
					then obtain x where x: "Pos x = tl (rev ?s) ! Suc (2 * j) \<and> Pos x \<in> c'"
						by blast
	
					have x_front: "tl (rev ?s) ! Suc (2*j) \<in> set ?front"
						apply (rule nth_set_take)
						using j twice_i_bound by simp+
	
					thm in_set_fold_upd
					have "fold (\<lambda>x f. f(ident x := True)) ?front vmap_tgt (ident (Pos x))"
						apply (rule in_set_fold_upd)
						using x x_front by simp
	
					hence "vmap_tgt_front x"
						using vmap_tgt_front by simp
	
					hence tgt_front_lift: "(vmap_tgt_front\<up>) (Pos x)"
						unfolding lift_def by simp
	
					have "Pos x \<noteq> last ?s"
						using front_stock aux2 x x_front by auto
					hence "(vmap_new\<up>) (Pos x)"
						using vmap_new tgt_front_lift unfolding lift_def by simp
	
					then show ?thesis using x by blast
				next
					case rear
					then consider (normal) "\<exists>j. c' = fst (refc c vars) ! j \<and> j < length (fst (refc c vars)) - 2"
						| (first) "c' = fst (refc c vars) ! (length (fst (refc c vars)) - 2)"
						| (last) "c' = fst (refc c vars) ! (length (fst (refc c vars)) - 1)"
						by (smt One_nat_def Suc_pred diff_Suc_eq_diff_pred diff_is_0_eq length_pos_if_in_set less_SucE less_Suc_eq_le numeral_2_eq_2 update zero_less_numeral)
					thus ?thesis
					proof cases
						case normal
	
						then obtain j where j_lo: "j > i" and j_hi: "j < length (fst (refc c vars)) - 2" and c': "c' = fst (refc c vars) ! j"
							using assms aux1 aux2 aux3 rear refc_def splc_clause_uniq stock_le3 stock_length
							by (smt diff_le_self dual_order.strict_trans1 fst_conv last_rev length_rev length_tl list.sel(2) lit.distinct(1) rev.simps(1))
	
						thm splc_aux_clause_nth
						have aug_aux_c: "\<exists>x y. Neg y = tl (rev ?s) ! (2 * j) \<and> Pos x = tl (rev ?s) ! Suc (2 * j) \<and> Neg y \<in> c' \<and> Pos x \<in> c' \<and> y \<notin> vars \<and> x \<notin> vars"
							apply (rule splc_aux_clause_nth[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"
										and ?l = "splc c (tl (rev (stock (card c - 3) vars))) (last (stock (card c - 3) vars))" and ?c' = c'])
							prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
							using assms stock_length aux1 aux2 aux3 c' j_hi i_hi unfolding refc_def
							by (fastforce simp add: Let_def split: if_splits)+
	
						then obtain l x where l: "l = Neg x" and neg_x: "Neg x \<in> c'" and x_vars: "x \<notin> vars" and x_pos: "Neg x = tl (rev ?s) ! (2 * j)"
							by blast
	
						have x_idset: "x \<in> idset (set ?s)"
							using assms update splc_set stock_le3 stock_length l neg_x x_vars
							by (smt Set.set_insert Sup_insert Un_iff append_butlast_last_id aux1 aux2 aux3 butlast_rev empty_set fst_conv idset_iff last_rev length_rev length_tl list.sel(2) list.simps(15) lit.distinct(1) refc_def rev.simps(1) rev_rev_ident set_append set_rev sup_commute)
	
						hence n0_lift: "(vmap_n0\<up>) l"
							using vmap_n0 vmap_false_neg_lift l by metis
	
						hence "Neg x \<noteq> tgt"
							using assms idset_iff tgt1 x_vars
							by (metis UnionI insert_iff list.simps(15))
						hence n1_lift: "(vmap_n1\<up>) l"
							using vmap_n0 vmap_n1 vmap_false_neg_lift assms aux3 idset_iff l tgt_in_c x_vars x_idset
							by (smt UnionI fun_upd_other list.set_intros(1))
	
						thm splc_lit_uniq
						have lv_uniq: "\<forall>cc \<in> set (fst (refc c vars)). cc = c_tgt \<or> Neg lv \<notin> cc"
							apply (rule splc_lit_uniq[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
							using assms aux1 aux2 stock_length lv c_tgt_refc unfolding refc_def
							by (fastforce simp add: Let_def split: if_splits)+
	
						thm splc_clause_uniq
						have clause_uniq: "\<forall>i j. i < length (fst (refc c vars)) \<and> j < length (fst (refc c vars)) \<and> i \<noteq> j \<longrightarrow> (fst (refc c vars)) ! i \<noteq> (fst (refc c vars)) ! j"
							apply (rule splc_clause_uniq[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
							using assms aux1 aux2 stock_length lv c_tgt_refc unfolding refc_def
							by (fastforce simp add: Let_def split: if_splits)+
						moreover have "i \<noteq> length (fst (refc c vars)) - 1"
							using i_hi by simp
						ultimately have "(fst (refc c vars)) ! i \<noteq> (fst (refc c vars)) ! (length (fst (refc c vars)) - 1)"
							using rear by fastforce
							
						hence "c_tgt \<noteq> last (fst (refc c vars))"
							using c_tgt c_tgt_set
							by (metis empty_iff empty_set in_set_butlastD last_conv_nth)
						hence "x \<noteq> lv"
							using neg_x lv lv_uniq rear clause_uniq c_tgt update
							by fastforce
	
						hence n2_lift: "(vmap_n2\<up>) l"
							using vmap_n2 n1_lift l lift_def
							by (metis fun_upd_other lit.simps(6))
	
						hence tgt_lift: "(vmap_tgt\<up>) l"
							using vmap_tgt n2_lift l lift_def
							by (metis fun_upd_apply lit.simps(6))
	
	
						thm stock_length
						hence "j < card c - 4"
							using j_hi twice_i_bound_alt by arith
						hence "2*j < 2*(card c - 4)"
							by simp
						hence "2*j < 2*(card c - 3) - 2"
							by simp
						hence "2*j < length (stock (card c - 3) vars) - 2"
							using stock_length assms by metis
						hence twice_j: "2*j < length (stock (card c - 3) vars) - 1"
							by simp
	
						thm tl_rev_stock_uniq
						have "\<forall>k < 2*i. tl (rev ?s) ! k \<noteq> tl (rev ?s) ! (2*j)"
						proof (intro allI impI)
							fix k
							assume a: "k < 2*i"
	
							hence "k < length (tl (rev (stock (card c - 3) vars)))"
								using twice_i_bound by simp
							hence k: "k < length (stock (card c - 3) vars) - 1"
								by simp
	
							show "tl (rev ?s) ! k \<noteq> tl (rev ?s) ! (2*j)"
								apply (rule tl_rev_stock_uniq[where ?vars = vars])
								using assms apply simp
								using k apply simp
								using twice_j apply simp
								using a j_lo apply simp
								done
						qed
	
						hence "\<forall>k < 2*i. tl (rev ?s) ! k \<noteq> l"
							using l x_pos by arith
	
						hence neg_front: "l \<notin> set ?front"
							by (simp add: in_set_conv_nth)
	
	
						hence x_pos_alt: "Pos x = tl (rev ?s) ! ((2*j) - 1)"
							using x_pos tl_rev_stock_pair_alt assms j_lo stock_length twice_j
							by (smt (verit) Nat.lessE add_diff_inverse_nat dvd_triv_left even_Suc length_tl less_one less_zeroE nat_0_less_mult_iff nat_diff_split plus_1_eq_Suc zero_less_Suc)
	
	
						thm tl_rev_stock_uniq
						have "\<forall>k < 2*i. tl (rev ?s) ! k \<noteq> tl (rev ?s) ! ((2*j) - 1)"
						proof (intro allI impI)
							fix k
							assume a: "k < 2*i"
	
							hence "k < length (tl (rev (stock (card c - 3) vars)))"
								using twice_i_bound by simp
							hence k: "k < length (stock (card c - 3) vars) - 1"
								by simp
	
							show "tl (rev ?s) ! k \<noteq> tl (rev ?s) ! ((2*j) - 1)"
								apply (rule tl_rev_stock_uniq[where ?vars = vars])
								using assms apply simp
								using k apply simp
								using twice_j apply simp
								using a j_lo apply simp
								done
						qed
	
						hence "\<forall>k < 2*i. tl (rev ?s) ! k \<noteq> Pos x"
							using x_pos_alt by arith
	
						hence pos_front: "Pos x \<notin> set ?front"
							by (simp add: in_set_conv_nth)
	
	
						hence "\<forall>lit \<in> set ?front. ident lit \<noteq> ident l"
							using pos_front neg_front l
							by (metis ident.elims ident.simps(2))
						hence "vmap_tgt_front (ident l) = vmap_tgt (ident l)"
							using vmap_tgt_front set_fold_ident_upd by metis
						hence tgt_front_lift: "(vmap_tgt_front\<up>) l"
							using vmap_tgt_front tgt_lift l lift_def
							by (metis ident.simps(2) lit.simps(6))
	
						hence "ident l \<noteq> ident (last ?s)"
							using x_pos_alt l twice_j aux2 aux3
							by (metis UnI1 diff_le_self dual_order.strict_trans1 ident.simps(1) ident.simps(2) leD length_rev length_tl not_le_imp_less nth_mem)
						hence "(vmap_new\<up>) l"
							using vmap_new tgt_front_lift lift_def l
							by (metis fun_upd_apply ident.simps(2) lit.simps(6))
	
						thus ?thesis using l neg_x by blast
					next
						case first
	
						hence "last ?s \<in> last (butlast (fst (refc c vars)))"
							using assms aux1 aux2 aux3 refc_def splc_aux_clause_first stock_le3 stock_length
							by (metis (no_types, lifting) fst_conv last_rev length_rev length_tl list.sel(2) lit.distinct(1) rev.simps(1))
						moreover have "c' = last (butlast (fst (refc c vars)))"
							using first assms refc_def c_tgt_set nth_butlast
							by (smt One_nat_def butlast.simps(1) diff_Suc_eq_diff_pred diff_less dual_order.trans last_conv_nth le_eq_less_or_eq length_butlast length_pos_if_in_set list.size(3) n_not_Suc_n not_less_iff_gr_or_eq numeral_2_eq_2 zero_less_diff)
						ultimately have "last ?s \<in> c'"
							by simp
	
						thus ?thesis using vmap_new aux3 vmap_true_pos_lift
							by (metis fun_upd_same ident.simps(1))
					next
						case last
	
						thm splc_aux_clause_last
						have "\<exists>i. Neg i \<in> last (fst (refc c vars)) \<and> hd ?s = Neg i"
							apply (rule splc_aux_clause_last[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
							using assms aux1 aux2 aux3 stock_length unfolding refc_def 
							by (fastforce simp add: Let_def split: if_splits)+
	
						then obtain l v where l: "l = Neg v" and v1: "Neg v \<in> last (fst (refc c vars))" and v2: "hd ?s = Neg v"
							by blast
	
						hence n0_lift: "(vmap_n0\<up>) l"
							using vmap_n0 vmap_false_neg_lift aux3 idset_iff
							by (metis last_rev list.set_sel(1) lit.distinct(1) rev.simps(1))
	
						hence "Neg v \<noteq> tgt"
							using assms aux3 idset_iff stock_fresh tgt1 v2
							by (metis UnionI insert_iff last_rev list.set_sel(1) list.simps(15) lit.distinct(1) rev.simps(1))
						hence n1_lift: "(vmap_n1\<up>) l"
							using vmap_n0 vmap_n1 n0_lift vmap_false_neg_lift aux3 idset_iff l stock_clause_disj tgt_in_c v2
							by (smt (verit, del_insts) Nitpick.size_list_simp(2) fun_upd_apply hd_conv_nth ident.simps(2) last_conv_nth last_in_set last_rev last_tl length_rev length_tl list.set_sel(1) lit.distinct(1) rev.simps(1))
	
	
	
						thm splc_lit_uniq
						have lv_uniq: "\<forall>cc \<in> set (fst (refc c vars)). cc = c_tgt \<or> Neg lv \<notin> cc"
							apply (rule splc_lit_uniq[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
							using assms aux1 aux2 stock_length lv c_tgt_refc unfolding refc_def
							by (fastforce simp add: Let_def split: if_splits)+
	
						thm splc_clause_uniq
						have "\<forall>i j. i < length (fst (refc c vars)) \<and> j < length (fst (refc c vars)) \<and> i \<noteq> j \<longrightarrow> (fst (refc c vars)) ! i \<noteq> (fst (refc c vars)) ! j"
							apply (rule splc_clause_uniq[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
							using assms aux1 aux2 stock_length lv c_tgt_refc unfolding refc_def
							by (fastforce simp add: Let_def split: if_splits)+
						moreover have "i \<noteq> length (fst (refc c vars)) - 1"
							using i_hi by simp
						ultimately have "(fst (refc c vars)) ! i \<noteq> (fst (refc c vars)) ! (length (fst (refc c vars)) - 1)"
							using rear by fastforce
							
						hence "c_tgt \<noteq> last (fst (refc c vars))"
							using c_tgt c_tgt_set
							by (metis empty_iff empty_set in_set_butlastD last_conv_nth)
						hence "v \<noteq> lv"
							using v1 lv lv_uniq rear
							by (metis last_in_set less_zeroE list.size(3))
	
						hence n2_lift: "(vmap_n2\<up>) l"
							using vmap_n2 n1_lift l lift_def
							by (metis fun_upd_other lit.simps(6))
	
						hence tgt_lift: "(vmap_tgt\<up>) l"
							using vmap_tgt n2_lift l lift_def
							by (metis fun_upd_apply lit.simps(6))
	
						have step0: "min (length (tl (rev ?s))) (2*(length (fst (refc c vars)) - 2)) = min (length (rev (?s)) - 1) (2*(length (fst (refc c vars))) - 4)"
							by simp
						moreover have step1: "... = min (length ?s - 1) (2*(length (fst (refc c vars))) - 4)"
							by simp
						moreover have step2: "... = min (2 * (card c - 3) - 1) (2*(length (fst (refc c vars))) - 4)"
							using stock_length assms by metis
						moreover have step3: "... = min (2 * ((2 + length (fst (refc c vars))) - 3) - 1) (2*(length (fst (refc c vars))) - 4)"
							using splc_length assms refc_def aux3 stock_le3 stock_length v2
							by (smt fst_conv last_rev length_rev length_tl lit.distinct(1) rev.simps(1))
						moreover have step4: "... = min (2 * (length (fst (refc c vars)) - 1) - 1) (2*(length (fst (refc c vars))) - 4)"
							by simp
						moreover have step5: "... = min (2 * length (fst (refc c vars)) - 3) (2*(length (fst (refc c vars))) - 4)"
							by simp
						moreover have step6: "... = 2 * (length (fst (refc c vars))) - 4"
							by simp
	
						moreover have twice_i: "2*i < 2 * (length (fst (refc c vars))) - 4"
							using i_hi by simp
						ultimately have length_front: "length ?front = 2*i"
							using i_hi length_take
							by (smt min.absorb4 min.strict_boundedE)
	
						hence length_front_bound: "length ?front < 2 * (length (fst (refc c vars))) - 4"
							using twice_i by simp
	
						have hd_0: "l = ?s ! 0"
							using l v1 v2 aux3
							by (metis hd_conv_nth last_rev lit.distinct(1) rev.simps(1))
						hence "l = rev ?s ! (length ?s - 1)"
							using v2 aux3
							by (metis One_nat_def last_rev length_greater_0_conv length_rev lit.distinct(1) rev_nth rev_rev_ident)
						hence step: "l = tl (rev ?s) ! (length ?s - 2)"
							using assms stock_length_even
							by (smt One_nat_def Suc_1 Suc_pred diff_Suc_eq_diff_pred diff_Suc_less length_greater_0_conv length_rev length_tl list.size(3) nth_tl odd_one)
						hence "l = tl (rev ?s) ! (2 * (card c - 3) - 2)"
							using stock_length assms by metis
						hence "l = tl (rev ?s) ! (2 * ((2 + length (fst (refc c vars))) - 3) - 2)"
							using splc_length assms refc_def aux3 stock_le3 stock_length v2
							by (smt fst_conv last_rev length_rev length_tl lit.distinct(1) rev.simps(1))
						hence "l = tl (rev ?s) ! (2 * ((length (fst (refc c vars))) - 1) - 2)"
							by simp
						hence "l = tl (rev ?s) ! (2 * (length (fst (refc c vars))) - 4)"
							by (simp add: right_diff_distrib')
	
						have i_card: "i < card c - 4"
							using i_hi splc_length assms refc_def aux3 stock_le3 stock_length v2
							by (smt add_diff_cancel_left' diff_diff_left fst_conv last_rev length_rev length_tl lit.distinct(1) numeral_Bit0 rev.simps(1))
	
						thm tl_rev_stock_uniq
						have "\<forall>j < 2*i. tl (rev ?s) ! (length ?s - 2) \<noteq> tl (rev ?s) ! j"
						proof (intro allI impI)
							fix j
							assume a: "j < 2*i"
							show "tl (rev ?s) ! (length ?s - 2) \<noteq> tl (rev ?s) ! j"
								apply (rule tl_rev_stock_uniq[where ?vars = vars])
								using assms apply simp
								using a i_hi length_front apply simp
								using a i_hi length_front apply simp
								using a assms(4) length_front length_front_bound stock_length step0 step1 step2 step3 step4 step5 step6
								apply (metis Suc_1 Suc_diff_Suc length_greater_0_conv length_tl less_zeroE list.size(3) min.strict_boundedE not_less_eq zero_less_diff)
								done
						qed
	
						hence "\<forall>j < 2*i. tl (rev ?s) ! j \<noteq> l"
							using step by metis
	
						hence neg_front: "l \<notin> set ?front"
							by (simp add: in_set_conv_nth)
	
						have "?s ! Suc 0 = Pos v"
							apply (rule stock_pair)
							using assms stock_length hd_0 l by fastforce+
						hence "Pos v = ?s ! 1"
							by simp
						hence "Pos v = rev ?s ! (length ?s - 2)"
							using assms(4) aux3 stock_length_even v2
							by (metis One_nat_def Suc_1 Suc_pred bot_nat_0.not_eq_extremum last_rev length_greater_0_conv length_rev lit.distinct(1) odd_one rev_nth rev_rev_ident zero_less_diff)
						hence pos_v: "Pos v = tl (rev ?s) ! (length ?s - 3)"
							using i_card assms stock_length
							by (smt (verit, best) One_nat_def Suc_1 Suc_pred bot_nat_0.not_eq_extremum diff_Suc_eq_diff_pred diff_Suc_less diff_diff_left dvd_def length_0_conv length_rev length_tl mult_eq_self_implies_10 not_less_eq nth_tl numeral_3_eq_3 numeral_Bit0 odd_one)
	
						have "\<forall>j < 2*i. tl (rev ?s) ! (length ?s - 3) \<noteq> tl (rev ?s) ! j"
						proof (intro allI impI)
							fix j
							assume a: "j < 2*i"
							show "tl (rev ?s) ! (length ?s - 3) \<noteq> tl (rev ?s) ! j"
								apply (rule tl_rev_stock_uniq[where ?vars = vars])
								using assms apply simp
								using a i_hi length_front apply simp
								using a i_hi length_front apply simp
								using assms length_front length_front_bound refc_def splc_length stock_length
								apply (smt (verit) Suc_diff_Suc a add_diff_cancel_left' diff_diff_left dual_order.strict_trans fst_conv length_greater_0_conv length_rev length_tl list.size(3) mult_2 not_less_eq not_less_eq_eq numeral_3_eq_3 numeral_Bit0 numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(2) right_diff_distrib' semiring_norm(26) semiring_norm(27))
								done
						qed
	
						hence "\<forall>j < 2*i. tl (rev ?s) ! j \<noteq> Pos v"
							using pos_v by metis
						hence pos_front: "Pos v \<notin> set ?front"
							by (simp add: in_set_conv_nth)
	
	
						hence "\<forall>lit \<in> set ?front. ident lit \<noteq> ident l"
							using pos_front neg_front l
							by (metis ident.elims ident.simps(2))
						hence "vmap_tgt_front (ident l) = vmap_tgt (ident l)"
							using vmap_tgt_front set_fold_ident_upd by metis
						hence tgt_front_lift: "(vmap_tgt_front\<up>) l"
							using vmap_tgt_front tgt_lift l lift_def
							by (metis ident.simps(2) lit.simps(6))
	
						hence "ident l \<noteq> ident (last ?s)"
							using assms aux2 aux3 l v1 stock_length_even pos_v stock_gt0
							by (smt Nitpick.size_list_simp(2) One_nat_def UnCI diff_Suc_eq_diff_pred diff_Suc_less ident.simps(1) ident.simps(2) leD length_greater_0_conv length_rev not_less_eq nth_mem numeral_3_eq_3 numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_diff)
						hence "(vmap_new\<up>) l"
							using vmap_new tgt_front_lift lift_def l
							by (metis fun_upd_apply ident.simps(2) lit.simps(6))
	
						thus ?thesis using l v1 update
							by (metis empty_iff empty_set last last_conv_nth)
					qed
				qed
			next
				case rest
	
				hence "sat xs"
					using assms sat_tl by fastforce
				hence orig_lift: "\<exists>l \<in> c'. (vmap_orig\<up>) l"
					unfolding sat_def models_def using rest vmap_orig by simp
				then obtain l where l1: "l \<in> c'" and l2: "(vmap_orig\<up>) l"
					by blast
	
				have v_xs: "\<forall>v \<in> idset (\<Union>(set xs)). v \<notin> idset (set ?s)"
					using assms idset_iff stock_fresh
					by (metis Sup_insert UnCI list.simps(15))
				hence v_stock: "\<forall>v \<in> idset c'. v \<notin> idset (set ?s)"
					using rest idset_iff
					by (metis UnionI)
	
				have "c' \<in> set xs"
					using rest by simp
				hence "\<forall>l \<in> c'. l \<in> \<Union>(set xs)"
					by blast
				hence notin_stock: "\<forall>l \<in> c'. l \<notin> set ?s"
					using assms v_stock idset_iff
					by (metis ident.elims)
				hence ident_orig_n0: "\<forall>l \<in> c'. vmap_orig (ident l) = vmap_n0 (ident l)"
					by (metis ident.elims idset_iff v_stock vmap_n0)
				hence "\<forall>l \<in> c'. (vmap_orig\<up>) l = (vmap_n0\<up>) l"
					using lift_def
					by (smt ident.elims lit.simps(5) lit.simps(6))
					
				hence "(vmap_n0\<up>) l"
					using orig_lift l1 l2 by blast
	
				hence n1_lift: "(vmap_n1\<up>) l"
					using vmap_n1 tgt2 ident_orig_n0 lift_def l1 l2	
					by (smt fun_upd_apply ident.elims lit.simps(5) lit.simps(6))
	
				hence "ident l \<noteq> lv"
					using assms idset_iff lv_vars rest l1 l2
					by (smt (verit) UnionI ident.elims insert_iff list.simps(15))
				hence n2_lift: "(vmap_n2\<up>) l"
					using vmap_n2 n1_lift assms lift_def idset_iff lv_vars rest
					by (smt fun_upd_apply ident.elims lit.simps(5) lit.simps(6))
	
				hence "ident l \<noteq> rv"
					using assms idset_iff rv_vars rest l1 l2
					by (smt (verit) UnionI ident.elims insert_iff list.simps(15))
				hence tgt_lift: "(vmap_tgt\<up>) l"
					using vmap_tgt n2_lift assms lift_def idset_iff rv_vars rest
					by (smt fun_upd_apply ident.elims lit.simps(5) lit.simps(6))
	
				hence "l \<notin> set ?front"
					using notin_stock l1 l2
					by (metis in_set_takeD list.sel(2) list.set_sel(2) set_rev)
				hence "\<forall>lit \<in> set ?front. ident lit \<noteq> ident l"
					using v_stock idset_iff l1 l2
					by (smt (verit) butlast_rev ident.elims in_set_butlastD in_set_takeD set_rev)
				hence "vmap_tgt_front (ident l) = vmap_tgt (ident l)"
					using vmap_tgt_front set_fold_ident_upd by metis
				hence tgt_front_lift: "(vmap_tgt_front\<up>) l"
					using vmap_tgt_front tgt_lift lift_def
					by (metis (no_types, lifting) ident.elims lit.simps(5) lit.simps(6))
	
				hence "ident l \<noteq> ident (last ?s)"
					using assms aux3 l1 l2 notin_stock stock_length_even
					by (metis (no_types, lifting) Nil_is_rev_conv Nitpick.size_list_simp(2) One_nat_def ident.elims ident.simps(1) last_in_set last_rev length_rev list.sel(2) list.set_sel(2) lit.distinct(1) odd_one set_rev)
				hence "(vmap_new\<up>) l"
					using vmap_new tgt_front_lift lift_def
					by (smt fun_upd_apply ident.elims lit.simps(5) lit.simps(6))
	
				thus ?thesis using l1 l2 by blast
			qed
	
	
				 
			(* 
				stock: n1 p1 n2 p2 ... nx px
				rev stock: px nx ... p2 n2 p1 n1
				tl rev stock: nx ... p2 n2 p1 n1  (init = px)
	
				after refc: {nx _ p(x-1)}, {n(x-1) _ p(x-2)}, ..., {n2 _ p1}, {_ _ px}, {n1 _ _}
												i = 0            i = 1
											s' ! 0, 1				 s' ! 2, 3
	
				> partition s'
				> map to ident
				> mass update vmap
			*)
			term "fold (\<lambda>x f. f(x := True)) l f"
			(*
				hence each clause has something set to true
				thus ?thesis
			*)
	
			thus "\<exists>l\<in>c'. (vmap_new\<up>) l" .
		qed
	next
		case first

		have first_pos: "last (butlast (fst (refc c vars))) = fst (refc c vars) ! (length (fst (refc c vars)) - 2)"
			using tgt assms aux3 refc_def splc_length stock_le3 stock_length
			by (smt One_nat_def Suc_pred add.commute cancel_comm_monoid_add_class.diff_cancel diff_Suc_eq_diff_pred diff_is_0_eq fst_conv last_conv_nth last_in_set last_rev length_butlast length_pos_if_in_set length_rev length_tl lessI list.sel(2) list.size(3) lit.distinct(1) nth_butlast numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc rev.simps(1))

		thm splc_aux_clause_first
		moreover have "\<exists>v. Pos v \<in> last (butlast (fst (refc c vars))) \<and> last ?s = Pos v"
			apply (rule splc_aux_clause_first[where ?c = c and ?s = "stock (card c - 3) vars" and ?vars = vars and ?s' = "tl (rev ?s)"])
			using assms stock_length aux1 aux2 aux3 unfolding refc_def by (fastforce simp add: Let_def split: if_splits)+

		ultimately obtain v where v_set: "Pos v \<in> last (butlast (fst (refc c vars)))" and v_init: "last ?s = Pos v"
			and v_pos: "Pos v \<in> fst (refc c vars) ! (length (fst (refc c vars)) - 2)"
			by blast

		hence v_vars: "v \<notin> vars"
			using assms aux3 idset_iff stock_fresh
			by (metis last_in_set last_rev list.sel(2) lit.simps(4) rev.simps(1))

		(* lift negatives *)
		then obtain vmap_new where vmap_new: "vmap_new = fold (\<lambda>x f. f(ident x := False)) ?s vmap_orig"
			by blast

		thm in_set_fold_upd_alt
		hence "\<forall>v \<in> set ?s. \<not> fold (\<lambda>x f. f(ident x := False)) ?s vmap_orig (ident v)"
			using in_set_fold_upd_alt by blast
		hence "\<forall>v \<in> set ?s. \<not> vmap_new (ident v)"
			using vmap_new by simp
		hence lift_neg: "\<forall>v \<in> idset (set ?s). (vmap_new\<up>) (Neg v)"
			using idset_iff unfolding lift_def by fastforce		

		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume c': "c' \<in> set (fst (refc c vars) @ xs)"

			then consider (ult) "c' = last (fst (refc c vars))"
				| (prim) "c' = last (butlast (fst (refc c vars)))"
				| (mid) "c' \<in> set (butlast (butlast (fst (refc c vars))))"
				| (xs) "c' \<in> set xs"
				using refc_cases by fastforce
			thus "\<exists>l\<in>c'. (vmap_new\<up>) l"
			proof cases
				case prim

				hence "(vmap_orig\<up>) tgt"
					using tgt2 by simp

				have "tgt \<notin> set ?s"
					using aux1 aux2 tgt1
					by (metis Int_iff Nitpick.size_list_simp(2) UnCI empty_iff hd_Cons_tl hd_rev length_pos_if_in_set less_numeral_extra(3) set_ConsD set_rev)
				hence "\<forall>lit \<in> set ?s. ident lit \<noteq> ident tgt"
					using assms idset_iff stock_fresh tgt1
					by (smt (verit) UnionI ident.elims list.set_intros(1))
				hence "vmap_new (ident tgt) = vmap_orig (ident tgt)"
					using vmap_new set_fold_ident_upd by metis
				hence "(vmap_new\<up>) tgt"
					using vmap_new tgt2 lift_def
					by (metis (no_types, lifting) ident.elims lit.simps(5) lit.simps(6))

				thus ?thesis using first first_pos prim by blast
			next
				case ult

				thm splc_aux_clause_last
				have "\<exists>v. Neg v \<in> last (fst (refc c vars)) \<and> hd ?s = Neg v"
					apply (rule splc_aux_clause_last[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
					using assms aux1 aux2 aux3 stock_length unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+

				then obtain x where x_pos: "Neg x \<in> last (fst (refc c vars))" and "hd ?s = Neg x"
					by blast

				hence "Neg x \<in> set ?s"
					using v_init
					by (metis last_rev list.set_sel(1) lit.distinct(1) rev.simps(1))
				hence "x \<in> idset (set ?s)"
					using idset_iff by metis
				hence "(vmap_new\<up>) (Neg x)"
					using lift_neg by simp

				thus ?thesis using x_pos ult by blast
			next
				case mid

				have set: "\<Union> (set (fst (refc c vars))) = {last ?s} \<union> set (tl (rev ?s)) \<union> c"
					apply (rule splc_set[where ?c = c and ?s = ?s and ?vars = vars])
					using assms aux1 aux2 aux3 stock_length unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+

				have aux_c: "\<forall>c' \<in> set (butlast (butlast (fst (refc c vars)))). \<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c' \<and> Neg j \<in> c'"
					apply (rule splc_aux_clause[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
					prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
					using assms aux1 aux2 aux3 stock_length unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+

				then obtain x where neg_x: "Neg x \<in> c'" and x_vars: "x \<notin> vars"
					using mid by blast

				hence "Neg x \<noteq> last ?s"
					using aux3 by force
				moreover have "Neg x \<notin> c"
					using assms idset_iff x_vars
					by (metis UnionI list.set_intros(1))
				moreover have "Neg x \<in> \<Union> (set (fst (refc c vars)))"
					using neg_x mid
					by (meson Union_iff in_set_butlastD)
				ultimately have "Neg x \<in> set (tl (rev ?s))"
					using set by blast

				hence "Neg x \<in> set ?s"
					by (metis list.sel(2) list.set_sel(2) set_rev)
				hence "x \<in> idset (set ?s)"
					using idset_iff by metis
				hence "(vmap_new\<up>) (Neg x)"
					using lift_neg by simp

				then show ?thesis using neg_x by blast
			next
				case xs

				hence "sat xs"
					using assms sat_tl by fastforce
				hence orig_lift: "\<exists>l \<in> c'. (vmap_orig\<up>) l"
					unfolding sat_def models_def using xs vmap_orig by simp
				then obtain l where l1: "l \<in> c'" and l2: "(vmap_orig\<up>) l"
					by blast
	
				have v_xs: "\<forall>v \<in> idset (\<Union>(set xs)). v \<notin> idset (set ?s)"
					using assms idset_iff stock_fresh
					by (metis Sup_insert UnCI list.simps(15))
				hence v_stock: "\<forall>v \<in> idset c'. v \<notin> idset (set ?s)"
					using xs idset_iff
					by (metis UnionI)

				hence "\<forall>lit \<in> set ?s. ident lit \<noteq> ident l"
					using idset_iff l1
					by (metis ident.elims)
				hence "vmap_new (ident l) = vmap_orig (ident l)"
					using vmap_new set_fold_ident_upd by metis
				hence "(vmap_new\<up>) l"
					using vmap_new l2 lift_def
					by (metis (no_types, lifting) ident.elims lit.simps(5) lit.simps(6))
				
				then show ?thesis using l1 by blast
			qed
		qed
	next
		case last

		have last_pos: "last (fst (refc c vars)) = fst (refc c vars) ! (length (fst (refc c vars)) - 1)"
			using tgt assms aux3 refc_def splc_length stock_le3 stock_length
			by (smt One_nat_def Suc_pred add.commute cancel_comm_monoid_add_class.diff_cancel diff_Suc_eq_diff_pred diff_is_0_eq fst_conv last_conv_nth last_in_set last_rev length_butlast length_pos_if_in_set length_rev length_tl lessI list.sel(2) list.size(3) lit.distinct(1) nth_butlast numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc rev.simps(1))

		thm splc_aux_clause_last
		moreover have "\<exists>v. Neg v \<in> last (fst (refc c vars)) \<and> hd ?s = Neg v"
			apply (rule splc_aux_clause_last[where ?c = c and ?s = "stock (card c - 3) vars" and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
			using assms stock_length aux1 aux2 aux3 unfolding refc_def by (fastforce simp add: Let_def split: if_splits)+

		ultimately obtain v where v_set: "Neg v \<in> last (fst (refc c vars))" and v_init: "hd ?s = Neg v"
			and v_pos: "Neg v \<in> fst (refc c vars) ! (length (fst (refc c vars)) - 1)"
			by blast

		hence v_vars: "v \<notin> vars"
			using assms aux3 idset_iff stock_fresh
			by (metis last_rev list.set_sel(1) lit.distinct(1) rev.simps(1))

		(* lift positives *)
		then obtain vmap_new where vmap_new: "vmap_new = fold (\<lambda>x f. f(ident x := True)) ?s vmap_orig"
			by blast

		thm in_set_fold_upd_alt
		hence "\<forall>v \<in> set ?s. fold (\<lambda>x f. f(ident x := True)) ?s vmap_orig (ident v)"
			using in_set_fold_upd by blast
		hence "\<forall>v \<in> set ?s. vmap_new (ident v)"
			using vmap_new by simp
		hence lift_pos: "\<forall>v \<in> idset (set ?s). (vmap_new\<up>) (Pos v)"
			using idset_iff unfolding lift_def by fastforce

		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume c': "c' \<in> set (fst (refc c vars) @ xs)"

			then consider (ult) "c' = last (fst (refc c vars))"
				| (prim) "c' = last (butlast (fst (refc c vars)))"
				| (mid) "c' \<in> set (butlast (butlast (fst (refc c vars))))"
				| (xs) "c' \<in> set xs"
				using refc_cases by fastforce
			thus "\<exists>l\<in>c'. (vmap_new\<up>) l"
			proof cases
				case ult

				hence "(vmap_orig\<up>) tgt"
					using tgt2 by simp

				have "tgt \<notin> set ?s"
					using aux1 aux2 tgt1
					by (metis Int_iff Nitpick.size_list_simp(2) UnCI empty_iff hd_Cons_tl hd_rev length_pos_if_in_set less_numeral_extra(3) set_ConsD set_rev)
				hence "\<forall>lit \<in> set ?s. ident lit \<noteq> ident tgt"
					using assms idset_iff stock_fresh tgt1
					by (smt (verit) UnionI ident.elims list.set_intros(1))
				hence "vmap_new (ident tgt) = vmap_orig (ident tgt)"
					using vmap_new set_fold_ident_upd by metis
				hence "(vmap_new\<up>) tgt"
					using vmap_new tgt2 lift_def
					by (metis (no_types, lifting) ident.elims lit.simps(5) lit.simps(6))

				thus ?thesis using last last_pos ult by blast
			next
				case prim
				thm splc_aux_clause_first
				have "\<exists>v. Pos v \<in> last (butlast (fst (refc c vars))) \<and> last ?s = Pos v"
					apply (rule splc_aux_clause_first[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
					using assms aux1 aux2 aux3 stock_length unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+

				then obtain x where x_pos: "Pos x \<in> last (butlast (fst (refc c vars)))" and "last ?s = Pos x"
					by blast

				hence "Pos x \<in> set ?s"
					using v_init
					by (metis last_in_set last_rev lit.distinct(1) rev.simps(1))
				hence "x \<in> idset (set ?s)"
					using idset_iff by metis
				hence "(vmap_new\<up>) (Pos x)"
					using lift_pos by simp

				thus ?thesis using x_pos prim by blast
			next
				case mid

				have set: "\<Union> (set (fst (refc c vars))) = {last ?s} \<union> set (tl (rev ?s)) \<union> c"
					apply (rule splc_set[where ?c = c and ?s = ?s and ?vars = vars])
					using assms aux1 aux2 aux3 stock_length unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+

				have aux_c: "\<forall>c' \<in> set (butlast (butlast (fst (refc c vars)))). \<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c' \<and> Neg j \<in> c'"
					apply (rule splc_aux_clause[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
					prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
					using assms aux1 aux2 aux3 stock_length unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+

				then obtain x where pos_x: "Pos x \<in> c'" and x_vars: "x \<notin> vars"
					using mid by blast

				have "tgt \<in> last (fst (refc c vars))"
					using last last_pos by blast

				thm splc_clause_uniq
				have "\<forall>i j. i < length (fst (refc c vars)) \<and> j < length (fst (refc c vars)) \<and> i \<noteq> j \<longrightarrow> (fst (refc c vars)) ! i \<noteq> (fst (refc c vars)) ! j"
					apply (rule splc_clause_uniq[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
					using assms aux1 aux2 stock_length unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+
				moreover have last_butlast_pos: "last (butlast (fst (refc c vars))) = fst (refc c vars) ! (length (fst (refc c vars)) - 2)"
					using mid
					by (smt (verit) One_nat_def Suc_pred diff_diff_left last_conv_nth last_in_set length_butlast length_pos_if_in_set length_tl list.sel(2) not_less_eq nth_butlast numeral_2_eq_2 plus_1_eq_Suc verit_comp_simplify1(1))
				moreover have "\<exists>j < length (fst (refc c vars)) - 2. c' = fst (refc c vars) ! j"
					using butlast_butlast_pos mid by metis
				ultimately have "c' \<noteq> last (butlast (fst (refc c vars)))"
					using mid tgt
					by (smt diff_less dual_order.strict_trans length_pos_if_in_set nat_neq_iff zero_less_numeral)

				thm splc_lit_uniq
				moreover have "\<forall>cc \<in> set (fst (refc c vars)). cc = c' \<or> Pos x \<notin> cc"
					apply (rule splc_lit_uniq[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
					prefer 10 using mid refc_def apply (smt (verit) in_set_butlastD)
					using assms stock_length aux1 aux2 mid pos_x unfolding refc_def
					by (fastforce simp add: Let_def split: if_splits)+
				moreover have "last ?s \<in> last (butlast (fst (refc c vars)))"
					using assms aux1 aux2 aux3 refc_def splc_aux_clause_first stock_le3 stock_length v_init
					by (metis (no_types, lifting) fst_conv last_rev length_rev length_tl lit.distinct(1) rev.simps(1))

				ultimately have "Pos x \<noteq> last ?s"
					using last_butlast_pos tgt
					by (metis diff_less length_pos_if_in_set nth_mem zero_less_numeral)
				moreover have "Pos x \<notin> c"
					using assms idset_iff x_vars
					by (metis UnionI list.set_intros(1))
				moreover have "Pos x \<in> \<Union> (set (fst (refc c vars)))"
					using pos_x mid
					by (meson Union_iff in_set_butlastD)
				ultimately have "Pos x \<in> set (tl (rev ?s))"
					using set by blast

				hence "Pos x \<in> set ?s"
					by (metis list.sel(2) list.set_sel(2) set_rev)
				hence "x \<in> idset (set ?s)"
					using idset_iff by metis
				hence "(vmap_new\<up>) (Pos x)"
					using lift_pos by metis

				then show ?thesis using pos_x by blast
			next
				case xs

				hence "sat xs"
					using assms sat_tl by fastforce
				hence orig_lift: "\<exists>l \<in> c'. (vmap_orig\<up>) l"
					unfolding sat_def models_def using xs vmap_orig by simp
				then obtain l where l1: "l \<in> c'" and l2: "(vmap_orig\<up>) l"
					by blast
	
				have v_xs: "\<forall>v \<in> idset (\<Union>(set xs)). v \<notin> idset (set ?s)"
					using assms idset_iff stock_fresh
					by (metis Sup_insert UnCI list.simps(15))
				hence v_stock: "\<forall>v \<in> idset c'. v \<notin> idset (set ?s)"
					using xs idset_iff
					by (metis UnionI)

				hence "\<forall>lit \<in> set ?s. ident lit \<noteq> ident l"
					using idset_iff l1
					by (metis ident.elims)
				hence "vmap_new (ident l) = vmap_orig (ident l)"
					using vmap_new set_fold_ident_upd by metis
				hence "(vmap_new\<up>) l"
					using vmap_new l2 lift_def
					by (metis (no_types, lifting) ident.elims lit.simps(5) lit.simps(6))
				
				then show ?thesis using l1 by blast
			qed
		qed
	qed
qed

lemma checkpoint2:
	assumes "sat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite c" "finite vars" "card c \<ge> 4"
	shows "\<forall>c' \<in> set (fst (refc c vars) @ xs). card c' > 0"
	using assms unfolding sat_def models_def
proof (intro ballI)
	fix c'
	assume "c' \<in> set (fst (refc c vars) @ xs)"

	then consider (front) "c' \<in> set (fst (refc c vars))"
		| (rear) "c' \<in> set xs"
		by fastforce
	thus "card c' > 0"
	proof cases
		case front
		let ?s = "(stock (card c - 3) vars)"

		have aux1: "set (tl (rev ?s)) \<inter> c = {}"
			apply (rule refc_stock_clause_disj)
			unfolding refc_def apply (simp add: Let_def split: if_splits)
			using assms apply simp
			using assms apply simp
			using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
			done
	
		have aux2: "last ?s \<notin> set (tl (rev ?s)) \<union> c"
			apply (rule refc_init_uniq)
			unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
			using assms apply simp
			using assms apply simp
			using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
			done

		thm splc_card_3
		have "card c' = 3"
			apply (rule splc_card_3[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
			prefer 5 using assms front refc_def apply (metis fst_conv not_less_eq_eq numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
			using assms stock_length aux1 aux2 unfolding refc_def
			by (fastforce simp add: Let_def split: if_splits)+

		thus ?thesis by simp
	next
		case rear
		thus ?thesis
			using assms sat_tl unfolding sat_def by fastforce
	qed

	have "\<forall>c' \<in> set (c # xs). card c' > 0"
		using assms unfolding sat_def by simp
qed


lemma checkpoint:
	assumes "sat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite c" "finite vars" "card c \<ge> 4"
	shows "sat (fst (refc c vars) @ xs)"
	using assms checkpoint1 checkpoint2 unfolding sat_def models_def
	by fast

fun refc_rotate
	where "refc_rotate [] = []"
	| "refc_rotate (x # xs) = xs @ (fst (refc x (idset (\<Union>(set (x # xs))))))"

lemma
	assumes "sat (x # xs)" "finite x" "finite (idset (\<Union>(set (x # xs))))" "card x \<ge> 4"
	shows "sat (refc_rotate (x # xs))"
	using assms checkpoint sat_rotate_append
	by fastforce

lemma "\<lbrakk> finite c; finite vars \<rbrakk> \<Longrightarrow> finite (snd (refc c vars) \<union> vars)"
	by (metis card_eq_0_iff diff_is_0_eq finite_UnI refc_def snd_conv stock_idset_card)

lemma finite_expr: "\<forall>c \<in> set xs. finite c \<Longrightarrow> finite (\<Union>(set xs))"
	by blast

lemma finite_idset: "finite (\<Union>(set xs)) \<Longrightarrow> finite (idset (\<Union>(set xs)))"
	by (induction xs) (auto simp add: idset_def Union_eq)

lemma finite_expr_idset: "\<forall>c \<in> set xs. finite c \<Longrightarrow> finite (idset (\<Union>(set xs)))"
	using finite_expr finite_idset by blast

lemma
	assumes "sat (x # xs)" "\<forall>c \<in> set (x # xs). finite c \<and> card c \<ge> 4"
	shows "sat (refc_rotate (x # xs))"
	using assms checkpoint sat_rotate_append finite_expr_idset
	by (metis list.set_intros(1) refc_rotate.simps(2))


lemma n_comp_refc_rotate: "(refc_rotate ^^ Suc n) (x # xs) = (refc_rotate ^^ n) (xs @ (fst (refc x (idset (\<Union>(set (x # xs)))))))"
	by (induction n arbitrary: x xs) auto

lemma l: "(refc_rotate ^^ Suc n) xs = refc_rotate ((refc_rotate ^^ n) xs)"
	by simp

lemma ys_drop: "n \<le> length xs \<Longrightarrow> \<exists>ys. (refc_rotate ^^ n) xs = (drop n xs) @ ys"
	apply (induction n arbitrary: xs)
	 apply auto
	by (smt (verit) append.assoc drop_Suc drop_eq_Nil less_Suc_eq_le linorder_not_le list.sel(3) not_less_iff_gr_or_eq refc_rotate.elims tl_append2 tl_drop)

lemma ys_drop_suc: "\<lbrakk> n < length xs; (refc_rotate ^^ n) xs = (drop n xs) @ ys \<rbrakk>
					\<Longrightarrow> (refc_rotate ^^ Suc n) xs = drop (Suc n) xs @ ys @ fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys)))))"
	apply (induction n arbitrary: xs ys)
	 apply auto
	 apply (metis drop0 drop_Suc list.exhaust_sel refc_rotate.simps(2))
	by (smt Union_Un_distrib append.assoc append_Cons drop_Suc drop_eq_Nil list.collapse nat_less_le not_less_iff_gr_or_eq refc_rotate.simps(2) set_append tl_drop)

lemma refc_rotate_finite:
	assumes "\<forall>c \<in> set xs. finite c" "n \<le> length xs"
	shows "\<forall>c \<in> set ((refc_rotate ^^ n) xs). finite c"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  hence "n \<le> length xs"
  	by arith
  hence "\<exists>ys. (refc_rotate ^^ n) xs = (drop n xs) @ ys"
  	using ys_drop by blast
  then obtain ys where ys: "(refc_rotate ^^ n) xs = (drop n xs) @ ys"
  	by blast

  hence expand_suc: "(refc_rotate ^^ Suc n) xs = drop (Suc n) xs @ ys @ fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys)))))"
  	using Suc.prems(2) Suc_le_lessD ys_drop_suc by blast

  thus ?case
  proof (intro ballI)
  	fix c
  	assume c: "c \<in> set ((refc_rotate ^^ Suc n) xs)"

  	then consider (front) "c \<in> set (drop (Suc n) xs @ ys)"
			| (rear) "c \<in> set (fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys))))))"
			using expand_suc by fastforce
		thus "finite c"
		proof cases
			case front
			thm Suc.IH
			have "\<forall>c \<in> set ((refc_rotate ^^ n) xs). finite c"
				apply (rule Suc.IH)
				using Suc.prems by auto

			thus ?thesis
				using ys Suc.prems(1) front set_drop_subset by fastforce
		next
			case rear

			then consider (gt4) "card (hd (drop n xs)) \<ge> 4"
				| (le3) "card (hd (drop n xs)) \<le> 3"
				by arith
			thus ?thesis
			proof cases
				case gt4

				let ?vars = "idset (\<Union> (set (drop n xs @ ys)))"
				let ?s = "stock (card (hd (drop n xs)) - 3) ?vars"
	
				have aux1: "set (tl (rev ?s)) \<inter> hd (drop n xs) = {}"
					apply (rule refc_stock_clause_disj)
						unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
							apply (metis Suc.IH Suc.prems(1) \<open>n \<le> length xs\<close> finite_expr_idset ys)
						using gt4 apply simp
						using idset_iff apply (smt (verit) Suc.prems(2) UnionI append_is_Nil_conv drop_eq_Nil hd_append2 list.set_sel(1) not_less_eq_eq subset_iff)
					done
	
				have aux2: "last ?s \<notin> set (tl (rev ?s)) \<union> hd (drop n xs)"
					apply (rule refc_init_uniq)
					unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
						apply (metis Suc.IH Suc.prems(1) \<open>n \<le> length xs\<close> finite_expr_idset ys)
					using gt4 apply simp
					using idset_iff apply (smt (verit) Suc.prems(2) UnionI append_is_Nil_conv drop_eq_Nil hd_append2 list.set_sel(1) not_less_eq_eq subset_iff)
					done
	
				thm stock_length
				have stock_len: "length (stock (card (hd (drop n xs)) - 3) ?vars) = 2 * (card (hd (drop n xs)) - 3)"
					apply (rule stock_length)
					by (metis Suc.IH Suc.prems(1) \<open>n \<le> length xs\<close> finite_expr_idset ys)
	
				thm splc_card_3
				have "card c = 3"
					apply (rule splc_card_3[where ?c' = c and ?vars = ?vars and ?c = "hd (drop n xs)"
									and ?s = ?s and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
									apply (meson Suc.prems(1) Suc.prems(2) drop_eq_Nil hd_in_set in_set_dropD not_less_eq_eq)
								 apply simp
								apply simp
					using stock_len apply simp
							apply (metis fst_conv list.sel(2) rear refc_def rev.simps(1) splc.simps(1) stock_le3)
					using gt4 apply simp
						apply (metis Suc.IH Suc.prems(1) \<open>n \<le> length xs\<close> finite_expr_idset ys)
					using aux2 apply simp
					using aux1 apply simp
					done
	
				thus ?thesis
					using card.infinite by fastforce
			next
				case le3
				thus ?thesis using Suc.prems rear refc_def
					by (metis drop_eq_Nil empty_iff empty_set fst_conv list.set_sel(1) not_less_eq_eq set_ConsD set_drop_subset subsetD)
			qed
		qed
	qed
qed


lemma refc_rotate_sat:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c" "n \<le> length xs"
	shows "sat ((refc_rotate ^^ n) xs)"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have sat_n: "sat ((refc_rotate ^^ n) xs)"
  	apply (rule Suc.IH)
  	using Suc.prems by auto

  then obtain ys where ys: "(refc_rotate ^^ n) xs = (drop n xs) @ ys"
  	by (metis drop_all nle_le self_append_conv2 ys_drop)

  hence "sat ((refc_rotate ^^ n) xs) = sat (drop n xs @ ys)"
  	by simp

	let ?vars = "idset (\<Union>(set (drop n xs @ ys)))"
	consider (gt4) "card (hd (drop n xs)) \<ge> 4"
		| (le3) "card (hd (drop n xs)) \<le> 3"
		by arith
	thus "sat ((refc_rotate ^^ Suc n) xs)"
	proof cases
		case gt4

		have sat_cp: "sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			apply (rule checkpoint)
			using Suc.prems sat_n ys apply (metis Cons_eq_appendI drop_eq_Nil2 list.exhaust_sel not_less_eq_eq)
			using Suc.prems apply (metis append_Cons drop_eq_Nil list.collapse not_less_eq_eq)
			using Suc.prems apply (meson drop_eq_Nil in_set_dropD list.set_sel(1) not_less_eq_eq)
			using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
			using gt4 apply simp
			done
	
		have sat_ys: "sat ((refc_rotate ^^ n) xs) \<longleftrightarrow> sat (drop n xs @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using sat_rotate_append by fastforce
		also have step4: "... \<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> sat ((refc_rotate ^^ Suc n) xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "sat ((refc_rotate ^^ Suc n) xs)"
			using sat_n sat_ys by blast
	next
		case le3
		have sat_cp: "sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			apply (rule checkpoint_le3)
			using Suc.prems sat_n ys apply (metis Cons_eq_appendI drop_eq_Nil2 list.exhaust_sel not_less_eq_eq)
			using le3 apply simp
			done
	
		have sat_ys: "sat ((refc_rotate ^^ n) xs) \<longleftrightarrow> sat (drop n xs @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using sat_rotate_append by fastforce
		also have step4: "... \<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> sat ((refc_rotate ^^ Suc n) xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "sat ((refc_rotate ^^ Suc n) xs)"
			using sat_n sat_ys by blast
	qed
qed


lemma refc_rotate_nsat:
	assumes "\<not> sat xs" "\<forall>c \<in> set xs. finite c" "n \<le> length xs"
	shows "\<not> sat ((refc_rotate ^^ n) xs)"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have sat_n: "\<not> sat ((refc_rotate ^^ n) xs)"
  	apply (rule Suc.IH)
  	using Suc.prems by auto

  then obtain ys where ys: "(refc_rotate ^^ n) xs = drop n xs @ ys"
  	by (metis drop_all nle_le self_append_conv2 ys_drop)

  hence "sat ((refc_rotate ^^ n) xs) \<longleftrightarrow> sat (drop n xs @ ys)"
  	by simp

	let ?vars = "idset (\<Union>(set (drop n xs @ ys)))"
	consider (gt4) "card (hd (drop n xs)) \<ge> 4"
		| (le3) "card (hd (drop n xs)) \<le> 3"
		by arith
	thus "\<not> sat ((refc_rotate ^^ Suc n) xs)"
	proof cases
		case gt4

		have sat_cp: "\<not> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			apply (rule reverse_checkpoint)
			using Suc.prems sat_n ys apply (metis Cons_eq_appendI drop_eq_Nil2 list.exhaust_sel not_less_eq_eq)
			using Suc.prems apply (metis append_Cons drop_eq_Nil list.collapse not_less_eq_eq)
			using Suc.prems apply (meson drop_eq_Nil in_set_dropD list.set_sel(1) not_less_eq_eq)
			using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
			using gt4 apply simp
			using Suc.prems refc_rotate_finite ys apply (metis Suc_n_not_le_n append_Cons drop_eq_Nil2 le_SucI list.exhaust_sel nle_le)
			done

		have sat_ys: "sat ((refc_rotate ^^ n) xs) \<longleftrightarrow> sat (drop n xs @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using sat_rotate_append by fastforce
		also have step4: "... \<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> sat ((refc_rotate ^^ Suc n) xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "\<not> sat ((refc_rotate ^^ Suc n) xs)"
			using sat_n sat_ys by blast
	next
		case le3
		have sat_cp: "\<not> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			apply (rule reverse_checkpoint_le3)
			using Suc.prems sat_n ys apply (metis Cons_eq_appendI drop_eq_Nil2 list.exhaust_sel not_less_eq_eq)
			using le3 apply simp
			done
	
		have sat_ys: "sat ((refc_rotate ^^ n) xs) \<longleftrightarrow> sat (drop n xs @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using sat_rotate_append by fastforce
		also have step4: "... \<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> sat ((refc_rotate ^^ Suc n) xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "\<not> sat ((refc_rotate ^^ Suc n) xs)"
			using sat_n sat_ys by blast
	qed
qed




find_theorems "length (drop ?n ?xs)"

lemma refc_rotate_card_3:
	assumes "\<forall>c \<in> set xs. finite c" "n \<le> length xs"
	shows "\<forall>c \<in> set (drop (length xs - n) ((refc_rotate ^^ n) xs)). card c \<le> 3"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have "\<exists>ys. (refc_rotate ^^ n) xs = drop n xs @ ys"
  	using ys_drop Suc.prems Suc_leD by blast

  then obtain ys where ys: "(refc_rotate ^^ n) xs = drop n xs @ ys"
  	by blast

  have expand_suc: "(refc_rotate ^^ Suc n) xs = (drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys)))))"
  	apply (rule ys_drop_suc)
  	using Suc.prems ys by arith+

  thus ?case
  proof (intro ballI)
  	fix c
  	assume c: "c \<in> set (drop (length xs - (Suc n)) ((refc_rotate ^^ Suc n) xs))"

		hence ys_alt: "ys = (drop (length xs - n) ((refc_rotate ^^ n) xs))"
			using ys by simp

		hence "c \<in> set (ys @ fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys))))))"
			using expand_suc ys c by simp

  	then consider (set_ys) "c \<in> set ys"
			| (rear) "c \<in> set (fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys))))))"
			using expand_suc by fastforce
		thus "card c \<le> 3"
		proof cases
			case set_ys
			thm Suc.IH
			have "\<forall>c \<in> set (drop (length xs - n) ((refc_rotate ^^ n) xs)). card c \<le> 3"
				apply (rule Suc.IH)
				using Suc.prems by simp+

			moreover have "c \<in> set (drop (length xs - n) ((refc_rotate ^^ n) xs))"
				using set_ys ys_alt by blast

			ultimately show ?thesis by blast
		next
			case rear

			let ?vars = "idset (\<Union> (set (drop n xs @ ys)))"
			let ?s = "stock (card (hd (drop n xs)) - 3) ?vars"

			consider (gt4) "card (hd (drop n xs)) \<ge> 4"
				| (le3) "card (hd (drop n xs)) \<le> 3"
				by arith
			thus ?thesis
			proof cases
				case gt4

				have aux1: "set (tl (rev ?s)) \<inter> hd (drop n xs) = {}"
					apply (rule refc_stock_clause_disj)
					unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
					using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
					using gt4 apply simp
					using idset_iff Suc.prems apply (smt (verit) UnionI append_is_Nil_conv drop_eq_Nil hd_append2 list.set_sel(1) not_less_eq_eq subset_iff)
					done
		
				have aux2: "last ?s \<notin> set (tl (rev ?s)) \<union> hd (drop n xs)"
					apply (rule refc_init_uniq)
					unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
					using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
					using gt4 apply simp
					using idset_iff Suc.prems apply (smt (verit) UnionI append_is_Nil_conv drop_eq_Nil hd_append2 list.set_sel(1) not_less_eq_eq subset_iff)
					done
		
				thm stock_length
				have stock_len: "length (stock (card (hd (drop n xs)) - 3) ?vars) = 2 * (card (hd (drop n xs)) - 3)"
					by (rule stock_length) (metis Suc.prems Suc_leD finite_expr_idset refc_rotate_finite ys)

				thm splc_card_3
				have "card c = 3"
					apply (rule splc_card_3[where ?c' = c and ?vars = ?vars and ?c = "hd (drop n xs)"
									and ?s = ?s and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
					using Suc.prems apply (meson drop_eq_Nil hd_in_set in_set_dropD not_less_eq_eq)
					apply simp
					apply simp
					using stock_len apply simp
					using rear refc_def stock_le3 apply (metis fst_conv list.sel(2) rev.simps(1) splc.simps(1))
					using gt4 apply simp
					using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
					using aux2 apply simp
					using aux1 apply simp
					done
	
				thus ?thesis
					using card.infinite by fastforce
			next
				case le3
				thus ?thesis using rear refc_def
					by (metis empty_iff empty_set fst_conv set_ConsD)
			qed
		qed
	qed
qed



lemma transform_sat:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c"
	shows "sat ((refc_rotate ^^ length xs) xs)"
	using assms refc_rotate_sat by blast

lemma transform_nsat:
	assumes "\<not> sat xs" "\<forall>c \<in> set xs. finite c"
	shows "\<not> sat ((refc_rotate ^^ length xs) xs)"
	using assms refc_rotate_nsat by blast

find_theorems drop 0
lemma transform_le3:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c"
	shows "\<forall>c \<in> set ((refc_rotate ^^ length xs) xs). card c \<le> 3"
	using assms refc_rotate_card_3 drop_0 by force

lemma sat_to_le3sat:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c"
	shows "le3sat ((refc_rotate ^^ length xs) xs)"
	using assms transform_sat transform_le3 unfolding le3sat_def by blast

lemma le3sat_to_sat:
	assumes "\<not> sat xs" "\<forall>c \<in> set xs. finite c"
	shows "\<not> le3sat ((refc_rotate ^^ length xs) xs)"
	using assms transform_nsat transform_le3 unfolding le3sat_def by blast

lemma sat_iff_le3sat:
	assumes "\<forall>c \<in> set xs. finite c"
	shows "sat xs \<longleftrightarrow> le3sat ((refc_rotate ^^ length xs) xs)"
	using assms sat_to_le3sat le3sat_to_sat by blast

definition to_le3sat :: "('a :: fresh) lit set list \<Rightarrow> 'a lit set list"
	where "to_le3sat xs = (refc_rotate ^^ length xs) xs"

definition sat_pset :: "('a :: fresh) lit set list set"
	where "sat_pset = {expr. sat expr}"

definition le3sat_pset :: "('a :: fresh) lit set list set"
	where "le3sat_pset = {expr. le3sat expr}"


fun has_empty :: "'a lit set list \<Rightarrow> bool"
	where "has_empty [] = False"
	| "has_empty (x # xs) = (if card x = 0 then True else has_empty xs)"

lemma has_empty: "has_empty xs \<longleftrightarrow> (\<exists>c \<in> set xs. card c = 0)"
	by (induction xs) auto

lemma has_empty_sat: "has_empty expr \<Longrightarrow> \<not> sat expr"
proof -
	assume "has_empty expr"
	hence "\<exists>c \<in> set expr. card c = 0"
		using has_empty by blast

	then obtain c where c_expr: "c \<in> set expr" and c_card: "card c = 0"
		by blast

	find_theorems "card ?A = 0"
	hence "infinite c \<or> (c = {})"
		using c_card card_eq_0_iff by meson
		
	thus "\<not> sat expr"
	proof (elim disjE)
		assume "infinite c"
		thus "\<not> sat expr"
			unfolding sat_def using c_expr by fastforce
	next
		assume "c = {}"
		thus "\<not> sat expr"
			unfolding sat_def using c_expr by fastforce
	qed
qed

lemma has_empty_le3sat: "has_empty expr \<Longrightarrow> \<not> le3sat expr"
proof -
	assume "has_empty expr"
	hence "\<exists>c \<in> set expr. card c = 0"
		using has_empty by blast

	then obtain c where c_expr: "c \<in> set expr" and c_card: "card c = 0"
		by blast

	find_theorems "card ?A = 0"
	hence "infinite c \<or> (c = {})"
		using c_card card_eq_0_iff by meson
		
	thus "\<not> le3sat expr"
	proof (elim disjE)
		assume "infinite c"
		thus "\<not> le3sat expr"
			unfolding le3sat_def sat_def using c_expr by fastforce
	next
		assume "c = {}"
		thus "\<not> le3sat expr"
			unfolding le3sat_def sat_def using c_expr by fastforce
	qed
qed


definition preproc :: "('a :: fresh) lit set list \<Rightarrow> 'a lit set list"
	where "preproc expr = (if has_empty expr then [{}] else to_le3sat expr)"

lemma SAT_to_le3SAT:
	assumes "sat xs"
	shows "le3sat (preproc xs)"
	using assms unfolding preproc_def
	apply (auto simp add: Let_def has_empty_sat split: if_splits)
	using sat_def sat_to_le3sat to_le3sat_def
	by (metis card_gt_0_iff)

lemma le3SAT_to_SAT:
	assumes "\<not> sat xs"
	shows "\<not> le3sat (preproc xs)"
	using assms unfolding preproc_def
	apply (auto simp add: Let_def split: if_splits)
	apply (simp add: le3sat_def sat_def)
	using has_empty le3sat_to_sat to_le3sat_def
	by (metis card.infinite)

lemma SAT_iff_le3SAT: "sat xs \<longleftrightarrow> le3sat (preproc xs)"
	using SAT_to_le3SAT le3SAT_to_SAT by blast

lemma sat_reduce_le3sat: "is_reduction preproc sat_pset le3sat_pset"
	unfolding is_reduction_def preproc_def sat_pset_def le3sat_pset_def to_le3sat_def
	apply (auto simp add: Let_def has_empty_sat has_empty_le3sat split: if_splits)
	using SAT_iff_le3SAT preproc_def to_le3sat_def by metis+




fun augc :: "('a :: fresh) lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit set list * 'a set"
	where "augc c vars = (
		if card c = 1 then
			let x = fst (pop c) in
			let v1 = fresh vars undefined in
			let v2 = fresh (insert v1 vars) undefined in
			({Pos v1, Pos v2, x} # {Pos v1, Neg v2, x} # {Neg v1, Pos v2, x} # {Neg v1, Neg v2, x} # [], {v1, v2} \<union> vars)
		else if card c = 2 then
			let v = fresh vars undefined in
			let p = pop c in
			let q = pop (snd p) in
			({Pos v, fst p, fst q} # {Neg v, fst p, fst q} # [], insert v vars)
		else
			(c # [], vars)
	)"

fun refine_le3 :: "('a :: fresh) lit set list \<Rightarrow> 'a set \<Rightarrow> 'a lit set list"
	where "refine_le3 [] vars = []"
	| "refine_le3 (x # xs) vars = (
			let aug = augc x vars in
				fst aug @ refine_le3 xs (snd aug)
	)"

definition to_3sat :: "('a :: fresh) lit set list \<Rightarrow> 'a lit set list"
	where "to_3sat expr = refine_le3 expr (idset (\<Union>(set expr)))"


lemma augc_card_3:
	assumes "card c \<le> 3" "card c \<noteq> 0" "finite vars" "c' \<in> set (fst (augc c vars))" "idset c \<subseteq> vars"
	shows "card c' = 3"
	using assms
proof (induction "card c" arbitrary: c c' vars)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (card1) "card c = 1"
  	| (card2) "card c = 2"
		| (card3) "card c = 3"
		using Suc.prems by arith
	thus ?case
	proof cases
		case card1

		let ?x = "fst (pop c)"
		let ?v1 = "fresh vars undefined"
		let ?v2 = "fresh (insert ?v1 vars) undefined"

		have expand: "fst (augc c vars) = {Pos ?v1, Pos ?v2, ?x} # {Pos ?v1, Neg ?v2, ?x}
																		# {Neg ?v1, Pos ?v2, ?x} # {Neg ?v1, Neg ?v2, ?x} # []"
			using card1 by (metis One_nat_def augc.simps fst_conv)

		hence setexpand: "set (fst (augc c vars)) = {{Pos ?v1, Pos ?v2, ?x}, {Pos ?v1, Neg ?v2, ?x},
																								{Neg ?v1, Pos ?v2, ?x}, {Neg ?v1, Neg ?v2, ?x}}"
			by simp

		moreover have "card {Pos ?v1, Pos ?v2, ?x} = 3" and "card {Pos ?v1, Neg ?v2, ?x} = 3"
							and "card {Neg ?v1, Pos ?v2, ?x} = 3" and "card {Neg ?v1, Neg ?v2, ?x} = 3"
		proof -
			have "?v1 \<noteq> ?v2"
				using Suc.prems fresh_notIn by (metis finite_insert insertCI)
			moreover have "?v1 \<noteq> ident ?x"
				using Suc.prems fresh_notIn idset_iff pop_isin
				by (smt card_eq_0_iff ident.elims subsetD)
			moreover have "?v2 \<noteq> ident ?x"
				using Suc.prems fresh_notIn idset_iff pop_isin
				by (smt (verit) card_eq_0_iff finite.insertI ident.elims insertCI subset_iff)
			ultimately show "card {Pos ?v1, Pos ?v2, ?x} = 3" and "card {Pos ?v1, Neg ?v2, ?x} = 3"
									and "card {Neg ?v1, Pos ?v2, ?x} = 3" and "card {Neg ?v1, Neg ?v2, ?x} = 3"
				by (metis card_3_iff ident.simps)+
		qed

		ultimately show ?thesis
			using Suc.prems by fastforce
	next
		case card2

		let ?v = "fresh vars undefined"
		let ?p = "pop c"
		let ?q = "pop (snd ?p)"

		have expand: "fst (augc c vars) = {Pos ?v, fst ?p, fst ?q} # {Neg ?v, fst ?p, fst ?q} # []"
			using card2 by (metis One_nat_def augc.simps fst_conv not_less_eq_eq numeral_2_eq_2)

		hence setexpand: "set (fst (augc c vars)) = {{Pos ?v, fst ?p, fst ?q}, {Neg ?v, fst ?p, fst ?q}}"
			by simp

		moreover have "card {Pos ?v, fst ?p, fst ?q} = 3" and "card {Neg ?v, fst ?p, fst ?q} = 3"
		proof -
			have "Pos ?v \<noteq> fst ?p" and "Neg ?v \<noteq> fst ?p"
				using Suc.prems fresh_notIn idset_iff pop_isin 
				by (metis card_eq_0_iff subsetD)+
			moreover have "Pos ?v \<noteq> fst ?q" and "Neg ?v \<noteq> fst ?q"
				using Suc.prems fresh_notIn idset_iff pop_card pop_ins card2
				by (smt card.empty card.infinite diff_Suc_1 insertCI numeral_2_eq_2 subsetD)+
			moreover have "fst ?p \<noteq> fst ?q"
				using Suc.prems pop_card pop_ins card2
				by (metis Suc_inject card_eq_0_iff insert_absorb2 numeral_2_eq_2)
			ultimately show "card {Pos ?v, fst ?p, fst ?q} = 3" and "card {Neg ?v, fst ?p, fst ?q} = 3"
				by simp+
		qed

		ultimately show ?thesis
			using Suc.prems by fastforce
	next
		case card3
		hence "fst (augc c vars) = c # []"
			by simp
		hence "set (fst (augc c vars)) = {c}"
			by simp
		thus ?thesis
			using card3 Suc.prems by simp
	qed
qed


lemma checkpoint_augc:
	assumes "le3sat (c # xs)"
	shows "le3sat (fst (augc c (idset (\<Union>(set (c # xs))))) @ xs)"
	using assms unfolding le3sat_def sat_def
proof (intro conjI)
	assume a: "((\<exists>\<sigma>. \<sigma> \<Turnstile> c # xs) \<and> (\<forall>c' \<in> set (c # xs). 0 < card c')) \<and> (\<forall>c' \<in> set (c # xs). card c' \<le> 3)"
	let ?vars = "idset (\<Union> (set (c # xs)))"
	
	have lo: "\<forall>c' \<in> set (c # xs). card c' > 0"
		using a by simp
	have hi: "\<forall>c' \<in> set (c # xs). card c' \<le> 3"
		using a by simp
	have "\<exists>vmap. vmap \<Turnstile> c # xs"
		using a by simp

	then obtain vmap where vmap: "vmap \<Turnstile> c # xs"
		by blast

	hence vmap_c: "\<exists>l \<in> c. (vmap\<up>) l"
		unfolding models_def by simp
	
	have "card c > 0" and "card c \<le> 3"
		using lo hi by simp+
	then consider (card1) "card c = 1"
		| (card2) "card c = 2"
		| (card3) "card c = 3"
		by arith
	thus "\<exists>vmap_new. vmap_new \<Turnstile> fst (augc c ?vars) @ xs"
	proof cases
		case card1
		thus ?thesis
		proof (intro exI)
			obtain x where x: "c = {x}"
				using card1 card_1_singletonE by blast
	
			hence vmap_x: "(vmap\<up>) x"
				using vmap_c by simp
	
			let ?x = "fst (pop c)"
			let ?v1 = "fresh ?vars undefined"
			let ?v2 = "fresh (insert ?v1 ?vars) undefined"
	
			have expand: "fst (augc c ?vars) = {Pos ?v1, Pos ?v2, x} # {Pos ?v1, Neg ?v2, x}
																				# {Neg ?v1, Pos ?v2, x} # {Neg ?v1, Neg ?v2, x} # []"
				using card1 x pop_isin
				by (smt (verit) augc.simps fst_conv insert_not_empty insert_subset subset_insertI subset_singletonD)
	
			hence "\<forall>c' \<in> set (fst (augc c ?vars)). x \<in> c'"
				by simp
	
			hence "\<forall>c' \<in> set (fst (augc c ?vars)). \<exists>l \<in> c'. (vmap\<up>) l"
				using vmap_x by blast

			thus "vmap \<Turnstile> fst (augc c ?vars) @ xs"
				using vmap
				by (smt UnE models_def set_append set_subset_Cons subset_iff)
		qed
	next
		case card2
		thus ?thesis
		proof (intro exI)
			obtain x y where xy: "c = {x, y}" and x: "fst (pop c) = x"
				using card2 pop_card pop_ins
				by (metis One_nat_def Suc_1 card_eq_0_iff diff_Suc_1 finite_insert old.nat.distinct(1))

			hence y: "fst (pop (snd (pop c))) = y"
				using card2 pop_card pop_ins
				by (metis Diff_insert_absorb One_nat_def Suc_1 card_eq_0_iff card_insert_if finite.emptyI finite_insert insert_not_empty n_not_Suc_n singleton_insert_inj_eq)

			hence vmap_xy: "(vmap\<up>) x \<or> (vmap\<up>) y"
				using vmap_c xy by simp

			let ?v = "fresh ?vars undefined"
			have expand: "fst (augc c ?vars) = {Pos ?v, x, y} # {Neg ?v, x, y} # []"
				using card2 x y by (metis Suc_1 augc.simps fst_conv n_not_Suc_n)

			hence "\<forall>c' \<in> set (fst (augc c ?vars)). x \<in> c' \<and> y \<in> c'"
				by simp

			hence "\<forall>c' \<in> set (fst (augc c ?vars)). \<exists>l \<in> c'. (vmap\<up>) l"
				using vmap_xy by blast

			thus "vmap \<Turnstile> fst (augc c ?vars) @ xs"
				using vmap
				by (smt UnE models_def set_append set_subset_Cons subset_iff)
		qed
	next
		case card3
		thus ?thesis using a by simp
	qed
next
	assume a: "((\<exists>\<sigma>. \<sigma> \<Turnstile> c # xs) \<and> (\<forall>c' \<in> set (c # xs). 0 < card c')) \<and> (\<forall>c' \<in> set (c # xs). card c' \<le> 3)"

	let ?vars = "idset (\<Union> (set (c # xs)))"
	have lo: "\<forall>c' \<in> set (c # xs). card c' > 0"
		using a by simp
	have hi: "\<forall>c' \<in> set (c # xs). card c' \<le> 3"
		using a by simp
	have "\<exists>vmap. vmap \<Turnstile> c # xs"
		using a by simp

	then obtain vmap where vmap: "vmap \<Turnstile> c # xs"
		by blast

	hence vmap_c: "\<exists>l \<in> c. (vmap\<up>) l"
		unfolding models_def by simp
	
	have "card c > 0" and "card c \<le> 3"
		using lo hi by simp+
	then consider (card1) "card c = 1"
		| (card2) "card c = 2"
		| (card3) "card c = 3"
		by arith
	thus "\<forall>c' \<in> set (fst (augc c ?vars) @ xs). 0 < card c'"
	proof cases
		case card1
		thus ?thesis
		proof (intro ballI)
			fix c'
			assume "c' \<in> set (fst (augc c ?vars) @ xs)"

			then consider (xs) "c' \<in> set xs"
				| (augc) "c' \<in> set (fst (augc c ?vars))"
				by fastforce
			thus "card c' > 0"
			proof cases
				case xs
				thus ?thesis by (simp add: lo)
			next
				case augc
	
				obtain x where x: "c = {x}"
					using card1 card_1_singletonE by blast
		
				let ?x = "fst (pop c)"
				let ?v1 = "fresh ?vars undefined"
				let ?v2 = "fresh (insert ?v1 ?vars) undefined"
		
				have expand: "fst (augc c ?vars) = {Pos ?v1, Pos ?v2, x} # {Pos ?v1, Neg ?v2, x}
																					# {Neg ?v1, Pos ?v2, x} # {Neg ?v1, Neg ?v2, x} # []"
					using card1 x pop_isin
					by (smt (verit) augc.simps fst_conv insert_not_empty insert_subset subset_insertI subset_singletonD)
	
				hence "\<forall>c' \<in> set (fst (augc c ?vars)). x \<in> c'"
					by simp
				moreover have "\<forall>c' \<in> set (fst (augc c ?vars)). finite c'"
					using expand by simp
				ultimately have "\<forall>c' \<in> set (fst (augc c ?vars)). card c' > 0"
					by (metis card_gt_0_iff empty_iff)

				thus ?thesis using augc by blast
			qed
		qed
	next
		case card2
		thus ?thesis
		proof (intro ballI)
			fix c'
			assume "c' \<in> set (fst (augc c ?vars) @ xs)"

			then consider (xs) "c' \<in> set xs"
				| (augc) "c' \<in> set (fst (augc c ?vars))"
				by fastforce
			thus "card c' > 0"
			proof cases
				case xs
				thus ?thesis by (simp add: lo)
			next
				case augc
	
				obtain x y where xy: "c = {x, y}" and x: "fst (pop c) = x"
					using card2 pop_card pop_ins
					by (metis One_nat_def Suc_1 card_eq_0_iff diff_Suc_1 finite_insert old.nat.distinct(1))

				hence y: "fst (pop (snd (pop c))) = y"
					using card2 pop_card pop_ins
					by (metis Diff_insert_absorb One_nat_def Suc_1 card_eq_0_iff card_insert_if finite.emptyI finite_insert insert_not_empty n_not_Suc_n singleton_insert_inj_eq)

				let ?v = "fresh ?vars undefined"		
				have expand: "fst (augc c ?vars) = {Pos ?v, x, y} # {Neg ?v, x, y} # []"
					using card2 x y
					by (metis One_nat_def augc.simps fst_conv n_not_Suc_n numeral_2_eq_2)
	
				hence "\<forall>c' \<in> set (fst (augc c ?vars)). x \<in> c'"
					by simp
				moreover have "\<forall>c' \<in> set (fst (augc c ?vars)). finite c'"
					using expand by simp
				ultimately have "\<forall>c' \<in> set (fst (augc c ?vars)). card c' > 0"
					by (metis card_gt_0_iff empty_iff)

				thus ?thesis using augc by blast
			qed
		qed
	next
		case card3
		thus ?thesis by (simp add: a)
	qed
next
	assume a: "((\<exists>\<sigma>. \<sigma> \<Turnstile> c # xs) \<and> (\<forall>c' \<in> set (c # xs). 0 < card c')) \<and> (\<forall>c' \<in> set (c # xs). card c' \<le> 3)"

	let ?vars = "idset (\<Union> (set (c # xs)))"
	have lo: "\<forall>c' \<in> set (c # xs). card c' > 0"
		using a by simp
	have hi: "\<forall>c' \<in> set (c # xs). card c' \<le> 3"
		using a by simp
	have "\<exists>vmap. vmap \<Turnstile> c # xs"
		using a by simp

	then obtain vmap where vmap: "vmap \<Turnstile> c # xs"
		by blast

	hence vmap_c: "\<exists>l \<in> c. (vmap\<up>) l"
		unfolding models_def by simp
	
	have "card c > 0" and "card c \<le> 3"
		using lo hi by simp+

	thus "\<forall>c' \<in> set (fst (augc c ?vars) @ xs). card c' \<le> 3"
	proof (intro ballI)
		fix c'
		assume "c' \<in> set (fst (augc c ?vars) @ xs)"

		then consider (xs) "c' \<in> set xs"
			| (augc) "c' \<in> set (fst (augc c ?vars))"
			by fastforce
		thus "card c' \<le> 3"
		proof cases
			case xs
			thus ?thesis by (simp add: hi)
		next
			case augc

			thm augc_card_3
			have "card c' = 3"
				apply (rule augc_card_3[where ?c = c and ?vars = ?vars])
				apply (simp add: lo hi)+
				using a finite_expr finite_idset apply (metis Sup_insert card_ge_0_finite list.simps(15))
				using augc apply blast
				apply (meson UnionI idset_iff list.set_intros(1) subset_iff)
				done

			thus ?thesis by simp
		qed
	qed
qed


lemma reverse_checkpoint_augc_aux:
	assumes "\<forall>vmap. \<exists>c' \<in> set (c # xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l" "card c > 0" "card c \<le> 3"
	shows "\<forall>vmap. \<exists>c' \<in> set (fst (augc c (idset (\<Union>(set (c # xs))))) @ xs). \<forall>l \<in> c'. \<not>(vmap\<up>) l"
	using assms
proof (intro allI)
	let ?vars = "idset (\<Union>(set (c # xs)))"

	fix vmap
	have "(\<forall>l \<in> c. \<not>(vmap\<up>) l) \<or> (\<exists>c' \<in> set xs. \<forall>l \<in> c'. \<not>(vmap\<up>) l)"
		using assms by simp
	then consider (hd) "(\<forall>l \<in> c. \<not>(vmap\<up>) l)"
		| (tl) "(\<exists>c' \<in> set xs. \<forall>l \<in> c'. \<not>(vmap\<up>) l)"
		by blast
	thus "\<exists>c' \<in> set (fst (augc c ?vars) @ xs). \<forall>l \<in> c'. \<not>(vmap\<up>) l"
	proof cases
		case hd
		show "\<exists>c' \<in> set (fst (augc c ?vars) @ xs). \<forall>l \<in> c'. \<not>(vmap\<up>) l"
		proof (rule ccontr)
			assume a: "\<not>(\<exists>c' \<in> set (fst (augc c ?vars) @ xs). \<forall>l \<in> c'. \<not>(vmap\<up>) l)"

			hence "\<forall>c' \<in> set (fst (augc c ?vars) @ xs). \<not>(\<forall>l \<in> c'. \<not>(vmap\<up>) l)"
				by simp
			hence f: "\<forall>c' \<in> set (fst (augc c ?vars) @ xs). \<exists>l \<in> c'. (vmap\<up>) l"
				by simp

			then consider (card1) "card c = 1"
				| (card2) "card c = 2"
				| (card3) "card c = 3"
				using assms by arith
			thus "False"
			proof cases
				case card1
				obtain x where x: "c = {x}"
					using card1 card_1_singletonE by blast
		
				let ?x = "fst (pop c)"
				let ?v1 = "fresh ?vars undefined"
				let ?v2 = "fresh (insert ?v1 ?vars) undefined"
		
				have expand: "fst (augc c ?vars) = {Pos ?v1, Pos ?v2, x} # {Pos ?v1, Neg ?v2, x}
																					# {Neg ?v1, Pos ?v2, x} # {Neg ?v1, Neg ?v2, x} # []"
					using card1 x pop_isin
					by (smt (verit) augc.simps fst_conv insert_not_empty insert_subset subset_insertI subset_singletonD)

				moreover have "\<not>(vmap\<up>) x"
					using x hd by blast

				ultimately show ?thesis
					using a ex_mid_lift by fastforce
			next
				case card2
				obtain x y where xy: "c = {x, y}" and x: "fst (pop c) = x"
					using card2 pop_card pop_ins
					by (metis One_nat_def Suc_1 card_eq_0_iff diff_Suc_1 finite_insert old.nat.distinct(1))
	
				hence y: "fst (pop (snd (pop c))) = y"
					using card2 pop_card pop_ins
					by (metis Diff_insert_absorb One_nat_def Suc_1 card_eq_0_iff card_insert_if finite.emptyI finite_insert insert_not_empty n_not_Suc_n singleton_insert_inj_eq)
	
				let ?v = "fresh ?vars undefined"
				have expand: "fst (augc c ?vars) = {Pos ?v, x, y} # {Neg ?v, x, y} # []"
					using card2 x y
					by (metis One_nat_def augc.simps fst_conv n_not_Suc_n numeral_2_eq_2)

				moreover have "\<not>(vmap\<up>) x \<and> \<not>(vmap\<up>) y"
					using xy hd by blast

				ultimately show ?thesis
					using a ex_mid_lift by fastforce
			next
				case card3
				hence "fst (augc c ?vars) = c # []"
					by simp
				hence "\<exists>l \<in> c. (vmap\<up>) l"
					using f by simp
				thus ?thesis
					using hd by simp
			qed
		qed
	next
		case tl
		thus ?thesis by auto
	qed
qed

lemma reverse_checkpoint_augc:
	assumes "\<not> le3sat (c # xs)"
	shows "\<not> le3sat (fst (augc c (idset (\<Union>(set (c # xs))))) @ xs)"
	using assms
proof (intro notI conjI)
	let ?vars = "idset (\<Union>(set (c # xs)))"
	assume a: "\<not> le3sat (c # xs)"
	assume f: "le3sat (fst (augc c ?vars) @ xs)"

	hence vmap_f_conj: "(\<exists>vmap. \<forall>c' \<in> set (fst (augc c ?vars) @ xs). \<exists>l \<in> c'. (vmap\<up>) l)
										\<and> (\<forall>c' \<in> set (fst (augc c ?vars) @ xs). card c > 0)
										\<and> (\<forall>c' \<in> set (fst (augc c ?vars) @ xs). card c \<le> 3)"
		unfolding le3sat_def sat_def models_def by simp
	hence vmap_f: "\<exists>vmap. \<forall>c' \<in> set (fst (augc c ?vars) @ xs). \<exists>l \<in> c'. (vmap\<up>) l"
			and lo_f: "\<forall>c' \<in> set (fst (augc c ?vars) @ xs). card c > 0"
			and hi_f: "\<forall>c' \<in> set (fst (augc c ?vars) @ xs). card c \<le> 3"
		by blast+

	have "\<not>(\<exists>vmap. \<forall>c' \<in> set (c # xs). \<exists>l \<in> c'. (vmap\<up>) l)
			\<or> \<not>(\<forall>c' \<in> set (c # xs). card c > 0)
			\<or> \<not>(\<forall>c' \<in> set (c # xs). card c \<le> 3)"
		using a f unfolding le3sat_def sat_def models_def by auto
	hence "(\<forall>vmap. \<exists>c' \<in> set (c # xs). \<forall>l \<in> c'. \<not>(vmap\<up>) l)
			\<or> (\<exists>c' \<in> set (c # xs). card c = 0)
			\<or> (\<exists>c' \<in> set (c # xs). card c > 3)"
		by fastforce
	then consider (vmap) "\<forall>vmap. \<exists>c' \<in> set (c # xs). \<forall>l \<in> c'. \<not>(vmap\<up>) l"
		| (lo) "\<exists>c' \<in> set (c # xs). card c = 0"
		| (hi) "\<exists>c' \<in> set (c # xs). card c > 3"
		by blast
	thus "False"
	proof cases
		case vmap
		thm reverse_checkpoint_augc_aux
		have "\<forall>vmap. \<exists>c' \<in> set (fst (augc c ?vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l"
			apply (rule reverse_checkpoint_augc_aux)
			using vmap lo_f hi_f by fastforce+

		thus ?thesis using vmap_f by meson
	next
		case lo
		then obtain c' where c': "c' \<in> set (c # xs)"
			by blast
		then consider (hd) "c' = c"
			| (tl) "c' \<in> set xs"
			by fastforce
		thus ?thesis
		proof cases
			case hd
			hence expand: "fst (augc c ?vars) = c # []"
				using lo by simp

			hence "c \<in> set (fst (augc c ?vars) @ xs)"
				by simp
			hence "\<not>(\<forall>c' \<in> set (fst (augc c ?vars) @ xs). card c > 0)"
				using lo by simp
			thus ?thesis 
				using lo_f by blast
		next
			case tl
			thus ?thesis 
				using lo lo_f by fastforce
		qed
	next
		case hi
		then obtain c' where c': "c' \<in> set (c # xs)"
			by blast
		then consider (hd) "c' = c"
			| (tl) "c' \<in> set xs"
			by fastforce
		thus ?thesis
		proof cases
			case hd
			hence expand: "fst (augc c ?vars) = c # []"
				using hi by simp

			hence "c \<in> set (fst (augc c ?vars) @ xs)"
				by simp
			hence "\<not>(\<forall>c' \<in> set (fst (augc c ?vars) @ xs). card c \<le> 3)"
				using hi by simp
			thus ?thesis 
				using hi_f by blast
		next
			case tl
			thus ?thesis 
				using hi hi_f by fastforce
		qed
	qed
qed







lemma
	assumes "le3sat expr"
	shows "eq3sat (to_3sat expr)"
	using assms unfolding to_3sat_def
proof (induction expr rule: rev_induct)
  case Nil
  thus ?case by (simp add: eq3sat_def le3sat_def)
next
  case (snoc c expr)
  thm snoc.prems
  thm snoc.IH

  let ?xs = "refine_le3 (expr) (idset (\<Union>(set (expr @ [c]))))"
  have "refine_le3 (expr @ [c]) (idset (\<Union>(set (expr @ [c])))) = ?xs @ fst (augc c (idset (\<Union>(set ?xs))))"
  	apply (induction "length expr" arbitrary: c)
  	 apply (auto simp add: Let_def split: if_splits)
  	oops

  then consider (card1) "card c = 1"
  	| (card2) "card c = 2"
  	| (card3) "card c = 3"
  	unfolding le3sat_def sat_def using set_append
  	by (metis One_nat_def Suc_le_eq Un_iff le_Suc_eq le_less_Suc_eq list.set_intros(1) numeral_2_eq_2 numeral_3_eq_3)
  thus ?case
  proof cases
  	case card1
  	show ?thesis unfolding eq3sat_def sat_def
  	proof (intro conjI)

  next
  	case card2
  	then show ?thesis sorry
  next
  	case card3
  	then show ?thesis sorry
  qed
qed






	


lemma "sum card (set l) = (\<Sum>s\<in>set l . card s)"
	by (rule refl)

lemma "Ball (set l) P = (\<forall>x\<in>set l . P x)"
	by rule

lemma splc_card_un:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
	shows "card (\<Union>(set l)) = fold (\<lambda>c' carry. carry + card c') l 0"
	using assms
proof (induction "card c - 3" arbitrary: c l s s' vars init)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis using Suc.prems apply (auto simp add: Let_def)
  		using splc_card_3 pop_card pop_ins
  		by (smt One_nat_def add_numeral_left card_eq_0_iff card_insert_if finite.emptyI finite.insertI insert_iff insert_not_empty nat.inject numeral_3_eq_3 numeral_eq_Suc numeral_plus_numeral one_eq_numeral_iff plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(2) semiring_norm(27) zero_neq_numeral)
  next
  	case gt4

  	thm Suc.hyps(1)
  	then show ?thesis sorry
  qed
qed

end