theory SAT_3SAT
	imports Main "Poly_Reductions_Lib.SAT_Definition" "../Reductions" Fresh_Identifiers.Fresh_String "HOL-Library.Multiset"
begin

definition le3sat :: "'a three_sat \<Rightarrow> bool"
	where "le3sat expr = (sat expr \<and> (\<forall>clause \<in> set expr. card clause \<le> 3))"

lemma "sat Nil"
	unfolding sat_def models_def 
	by simp

fun ident :: "'a lit \<Rightarrow> 'a"
	where "ident (Pos x) = x"
	| "ident (Neg x) = x"

definition idset :: "'a lit set \<Rightarrow> 'a set"
	where "idset clause = {ident x | x. x \<in> clause}"

fun varset :: "'a set list \<Rightarrow> 'a set"
	where "varset [] = {}"
	| "varset (c # cs) = c \<union> (varset cs)"

definition gen_uniq :: "'a set \<Rightarrow> 'a"
	where "gen_uniq var_set = (SOME x. x \<notin> var_set)"


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

(*
fun splc :: "('a :: fresh) lit set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a lit set list"
	where "splc c [] carry init = (
		let p = pop c in
		let q = pop (snd p) in
			{fst p, fst q, Pos init} # insert (Neg carry) (snd q) # []
	)"
	| "splc c (x # xs) carry init = (
		let p = pop c in
			{Neg carry, fst p, Pos x} # splc (snd p) xs x init
	)"

definition refc :: "('a :: fresh) lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit set list * 'a set"
	where "refc c vars = (
		let s = stock (card c - 3) vars in 
			if s = [] then 
				(c # [], vars)
			else if length s = 1 then
				(splc c [] (hd s) (hd s), vars \<union> set s)
			else 
				(splc c s (hd s) (hd s), vars \<union> set s)
	)"
*)

(*
lemma splc_card:
	assumes "finite c" "card c > 3" "c' \<in> set (splc c s carry init)" "length s = card c - 3"
	shows "card c' \<le> 3"
	using assms
proof (induction "card c" arbitrary: c s carry init c')
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis
  		using Suc.prems by auto
  next
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  		using Suc.prems(2) splc_4 
  			apply (simp add: card_insert_if)
  		 apply (simp add: card_insert_if) oops
  		by (smt (verit, best) One_nat_def card.empty card.infinite card_gt_0_iff card_insert_if diff_Suc_1 finite_insert less_or_eq_imp_le numeral_eq_Suc one_eq_numeral_iff order.strict_trans pop_card pop_card_less pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) semiring_norm(86) zero_less_Suc)
  next
  	case gt4

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

  	have "c' \<in> set (splc ?rest s carry init) \<Longrightarrow> card c' \<le> 3"
  		apply (rule Suc.hyps(1)[where ?c = ?rest])
  		using suc_card Suc.hyps(2) apply auto[1]
  		using Suc.prems(1) c apply (metis finite_insert)
  		using gt4 suc_card apply arith
  				apply auto[1]
  			 defer
  		using Suc.prems(5) apply simp
  		using Suc.prems(6) apply simp

  		
  		apply (simp add: Suc.prems(5))
  	  using Suc.prems(3) apply simp
  	  done

		let ?f = "fresh vars undefined"

  	have expand: "fst (split_clause c vars carry) = {hd carry, ?x, Pos ?f} # (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry)))"
  		apply auto
  		apply (auto simp add: Let_def)[1]
  		using c gt4 apply auto
  		by (meson fst_conv)+

  	consider (safe) "c' = {hd carry, ?x, Pos ?f}"
  		| (rest) "c' \<in> set (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry)))"
  		using Suc.prems expand by auto
  	thus ?thesis
  	proof cases
  		case safe
  		thus ?thesis
  			by (simp add: card_insert_le_m1)
  	next
  		case rest
  		thm Suc.prems
  		thm Suc.hyps

  		have "n = card ?rest"
  			using Suc.hyps suc_card by simp

  		thus ?thesis
  			apply (rule Suc.hyps(1))
  			using Suc.prems(1) c apply (metis finite_insert)
  			using rest apply simp
  			using Suc.prems(3) apply simp
  			done
  	qed
  qed
qed
  then show ?case sorry
qed


proof (induction c s carry init arbitrary: c' vars rule: splc.induct)
  case (1 c carry init)
  then show ?case
  	apply (auto simp add: Let_def card_insert_if)
  	by (metis diff_is_0_eq leD list.distinct(1) stock.elims)
next
  case (2 c x xs carry init)

  let ?p = "pop c"
  have expand: "splc c (x # xs) carry init = {Neg carry, fst ?p, Pos x} # splc (snd ?p) xs x init"
  	by (meson splc.simps(2))

  consider (safe) "c' = {Neg carry, fst ?p, Pos x}"
  	| (rest) "c' \<in> set (splc (snd ?p) xs x init)"
  	using expand 2 by auto
  thus ?case
  proof cases
  	case safe
  	thus ?thesis by (simp add: card_insert_if)
  next
  	case rest

  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins 2
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using 2 c pop_card by blast

(*
		have "n = card ?rest"
			using Suc.hyps suc_card by simp
*)

  	show ?thesis apply (rule "2.IH"[where ?xa = "?p" and ?vars = vars])
  					 apply simp
  		using "2.prems"(1) "2.prems"(2)
  					apply (metis c finite_insert snd_conv
  qed
qed
*)

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

(*
lemma stock_perm_2: "length s = 2 \<Longrightarrow> rev (last s # butlast s) = s"
	by (smt add_diff_cancel_right' append_butlast_last_id cancel_comm_monoid_add_class.diff_cancel length_0_conv length_butlast one_add_one rev.simps rev_singleton_conv zero_neq_numeral)
*)
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


(*
lemma
	assumes "finite c" "finite vars" "s = rev (stock (card c - 3) vars)" "l = splc c (tl s) carry" 
					"idset (set carry) \<subseteq> set s" "length carry = 2" "card c \<ge> 4"
	shows "idset (\<Union>(set l)) = idset c \<union> set s \<union> {ident (hd carry)}"
	using assms
proof (induction c "tl s" carry arbitrary: l s vars rule: splc.induct)
  case (1 c carry)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	using 1
  	by (metis Nitpick.size_list_simp(2) One_nat_def Suc_nat_number_of_add Suc_numeral add_diff_inverse_nat length_rev less_or_eq_imp_le numeral_3_eq_3 numeral_eq_Suc numerals(1) plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) stock_length)
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using 1 by simp
  next
  	case eq4

		let ?p = "pop c"
		let ?q = "pop (snd ?p)"
		
		have expand: "l = {fst ?p, fst ?q, hd (tl carry)} # insert (hd carry) (snd ?q) # []"
			using eq4 1 by (simp add: Let_def)

		hence "card (snd ?q) = 2"
			using eq4 1
			by (metis (no_types, lifting) "1.prems"(1) add_left_cancel bot_nat_0.extremum_unique card.empty eq4 finite_insert not_numeral_le_zero numeral_2_eq_2 numeral_3_eq_3 numeral_eq_Suc plus_1_eq_Suc pop_card pop_ins pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
		then obtain x y where xy: "snd ?q = {x, y}" 
			by (meson card_2_iff)

		hence un: "\<Union>(set l) = {fst ?p, fst ?q, hd (tl carry), hd carry, x, y}"
			using expand by auto

		have "ident (hd carry) \<in> set s"
			using "1.prems"(5) "1.prems"(6) idset_def eq4
			by (metis (mono_tags, lifting) Nitpick.size_list_simp(2) le_refl list.set_sel(1) mem_Collect_eq subset_eq zero_neq_numeral)
		moreover have "ident (hd (tl carry)) \<in> set s"
			using "1.prems"(5) "1.prems"(6) idset_def
			by (metis (mono_tags, lifting) diff_Suc_1 eq4 length_0_conv length_tl list.set_sel(1) list.set_sel(2) mem_Collect_eq nle_le numeral_2_eq_2 old.nat.distinct(1) subset_iff)
		moreover have "x \<in> c" and "y \<in> c" and "fst ?p \<in> c" and "fst ?q \<in> c"
			using eq4 xy pop_ins pop_card
			by (metis One_nat_def card.empty card_gt_0_iff finite_insert insertCI one_eq_numeral_iff semiring_norm(83) zero_less_numeral)+
		ultimately have sub1: "idset (\<Union>(set l)) \<subseteq> idset c \<union> set s \<union> {ident (hd carry)}"
			using un apply auto
			by (smt (verit, ccfv_SIG) empty_iff idset_def insert_iff mem_Collect_eq)

		have "idset (\<Union>(set l)) = {ident (fst ?p), ident (fst ?q), ident (hd (tl carry)), ident (hd carry), ident x, ident y}"
			using un idset_def[of "\<Union>(set l)"] by auto

		moreover have "c = {fst ?p, fst ?q, x, y}"
			using 1 eq4 xy
			by (metis One_nat_def card.empty card_gt_0_iff finite_insert pop_card pop_ins rel_simps(74) semiring_norm(83) zero_less_numeral) 
		moreover have "set carry = {hd (tl carry), hd carry}"
			using 1
			by (metis (no_types, opaque_lifting) Suc_1 diff_Suc_1 diff_is_0_eq dual_order.refl empty_set insert_commute length_0_conv length_tl list.exhaust_sel list.simps(15) old.nat.distinct(1) zero_neq_one)
		ultimately have sub2: "idset c \<union> set s \<union> {ident (hd carry)} \<subseteq> idset (\<Union>(set l))"
			using un apply auto
			 apply (smt (verit, ccfv_SIG) empty_iff idset_def insert_iff mem_Collect_eq)
			using un by (metis "1.hyps" \<open>ident (hd (tl carry)) \<in> set s\<close> empty_iff empty_set hd_Cons_tl set_ConsD)

  	then show ?thesis using sub1 sub2 by auto
  qed

(*
  	apply (smt (verit, best) card.empty finite_insert idset_def insert_iff le_SucI mem_Collect_eq not_less_eq_eq numeral_3_eq_3 pop_card pop_ins subset_iff)
  	 apply (smt (verit, best) card.empty finite_insert idset_def insert_iff le_SucI mem_Collect_eq not_less_eq_eq numeral_3_eq_3 pop_card pop_ins subset_iff)
  	by (smt (z3) "1.prems"(5) empty_iff empty_set hd_Cons_tl idset_def insert_iff list.simps(15) mem_Collect_eq rev_singleton_conv subset_iff)
*)
next
  case (2 c x xs carry)

	let ?p = "pop c"
	have expand: "l = {hd carry, fst ?p, Pos x} # splc (snd ?p) xs (Neg x # tl carry)"
		using 2 by (metis splc.simps(2))

	consider (edge) "card (snd ?p) = 4"
		| (safe) "card (snd ?p) > 4"
		using 2 pop_card stock_length
		by (metis (no_types, opaque_lifting) Suc_leI cancel_comm_monoid_add_class.diff_cancel card.empty diff_Suc_eq_diff_pred diff_commute le_antisym length_0_conv length_rev length_tl list.distinct(1) nat_neq_iff not_numeral_le_zero one_plus_numeral plus_1_eq_Suc semiring_norm(2) semiring_norm(4))
	thus ?case
	proof cases
		case edge

		have "idset (set (Neg x # tl carry)) \<subseteq> set (tl s)"
			oops

		have t: "idset (\<Union>(set (tl l))) = idset (snd (pop c)) \<union> set (tl s) \<union> {ident (hd (Neg x # tl carry))}"
			apply (rule "2.hyps"(1)[where ?vars = vars])
						 apply simp
			using "2.hyps"(2) apply (metis list.sel(3))
			using 2 pop_card apply (metis Nil_tl One_nat_def card_eq_0_iff diff_is_0_eq less_Suc_eq_0_disj less_numeral_extra(3) list.distinct(1) one_le_numeral rev.simps(1) stock.elims zero_le_numeral)
			using 2 apply simp
			using "2.prems"(3) pop_card stock_butlast apply (smt (verit, ccfv_threshold) "2.hyps"(2) "2.prems"(1) Nitpick.size_list_simp(2) One_nat_def Suc_diff_diff butlast_rev card.empty diff_zero dual_order.strict_trans length_rev less_numeral_extra(3) list.distinct(1) numeral_3_eq_3 rev_swap stock_length zero_less_Suc zero_less_diff)
			using "2.prems"(4) apply (metis "2.hyps"(2) list.sel(3) splc.simps(2))
				defer
			using "2.prems"(6) apply simp
			using edge apply simp

		then show ?thesis sorry
	next
		case safe

		hence id: "idset (\<Union>(set l)) - idset (\<Union>(set (tl l))) = {ident (fst ?p), x}"
			sorry

		have t: "idset (\<Union>(set (tl l))) = idset (snd (pop c)) \<union> set (tl s) \<union> {ident (hd (Neg x # tl carry))}"
			apply (rule "2.hyps"(1)[where ?vars = vars])
						 apply simp
			using "2.hyps"(2) apply (metis list.sel(3))
			using 2 pop_card apply (metis Nil_tl One_nat_def card_eq_0_iff diff_is_0_eq less_Suc_eq_0_disj less_numeral_extra(3) list.distinct(1) one_le_numeral rev.simps(1) stock.elims zero_le_numeral)
			using 2 apply simp
			using "2.prems"(3) pop_card stock_butlast apply (smt (verit, ccfv_threshold) "2.hyps"(2) "2.prems"(1) Nitpick.size_list_simp(2) One_nat_def Suc_diff_diff butlast_rev card.empty diff_zero dual_order.strict_trans length_rev less_numeral_extra(3) list.distinct(1) numeral_3_eq_3 rev_swap stock_length zero_less_Suc zero_less_diff)
			using "2.prems"(4) apply (metis "2.hyps"(2) list.sel(3) splc.simps(2))
			using safe apply simp
			using "2.prems"(6) apply simp
			using safe apply simp
			done
		then show ?thesis using id t by auto
	qed

	hence hd: "hd l = {hd carry, fst ?p, Pos x}"
		by simp

	hence id: "idset (\<Union>(set l)) - idset (\<Union>(set (tl l))) = {ident (fst ?p), ident (hd carry)}" sorry

	hence t1: "ident (hd carry) \<in> set s" sorry
	have t2: "fst ?p \<in> c" sorry
	have t3: "x \<in> set s" sorry


(* idset hd = idset fst + hd s *)
(* idset hd \u idset tl = idset fst \u idset snd + ins hd tl *)

  have t: "idset (\<Union>(set (tl l))) = idset (snd (pop c)) \<union> set (tl s) \<union> {ident (hd (Neg x # tl carry))}"
  	apply (rule "2.hyps"(1)[where ?vars = vars])
  				 apply simp
  	using "2.hyps"(2) apply (metis list.sel(3))
  	using 2 pop_card apply (metis Nil_tl One_nat_def card_eq_0_iff diff_is_0_eq less_Suc_eq_0_disj less_numeral_extra(3) list.distinct(1) one_le_numeral rev.simps(1) stock.elims zero_le_numeral)
  	using 2 apply simp
  	using "2.prems"(3) pop_card stock_butlast apply (smt (verit, ccfv_threshold) "2.hyps"(2) "2.prems"(1) Nitpick.size_list_simp(2) One_nat_def Suc_diff_diff butlast_rev card.empty diff_zero dual_order.strict_trans length_rev less_numeral_extra(3) list.distinct(1) numeral_3_eq_3 rev_swap stock_length zero_less_Suc zero_less_diff)
  	using "2.prems"(4) apply (metis "2.hyps"(2) list.sel(3) splc.simps(2))
  	defer
  	using "2.prems"(6) apply simp
  	sorry 

  thus ?case using t1 t2 t3 t hd id 

qed



lemma splc_card_3:
	assumes "finite c" "card c \<ge> 3" "s = stock (card c - 3) vars" "c' \<in> set (splc c (tl s) carry)"
					"idset c \<subseteq> vars" "finite vars" "carry = Neg (hd s) # Pos (hd s) # []"
	shows "card c' = 3"
	using assms
proof (induction "card c - 3" arbitrary: c c' s carry vars)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4
  	then show ?thesis using Suc.prems sorry
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

		let ?x = "hd (tl s)"
		let ?xs = "tl (tl s)"
		have expand: "splc c (?x # ?xs) carry = {hd carry, fst ?p, Pos ?x} # splc (snd ?p) ?xs (Neg ?x # tl carry)"
			using gt4 by (meson splc.simps(2))
	
		hence setexpand: "set (splc c (?x # ?xs) carry) = set ({hd carry, fst ?p, Pos ?x} # splc (snd ?p) ?xs (Neg ?x # tl carry))"
			by simp

		consider (safe) "c' = {hd carry, fst ?p, Pos ?x}"
			| (rest) "c' \<in> set (splc (snd ?p) ?xs (Neg ?x # tl carry))"
			using gt4 setexpand Suc.prems apply (simp add: Let_def)
			using Suc.prems Suc.hyps setexpand stock_length suc_card
			by (smt (verit) Suc_diff_Suc diff_Suc_1 diff_is_0_eq hd_Cons_tl insert_iff list.distinct(1) list.sel(3) list.simps(15) nat_less_le not_less_eq_eq numeral_eq_Suc pred_numeral_simps(2) safe semiring_norm(26) semiring_norm(27) stock.elims)
		thus ?thesis
		proof cases
			case safe

			have carry: "hd carry \<in> set carry"
				using Suc.prems(7) by simp
			moreover have ref: "fst (pop c) \<in> c"
				using pop_ins c by auto
			moreover have "idset (set carry) \<subseteq> set s"
				using Suc.prems(7) unfolding idset_def apply auto
				using stock_length Suc.prems Suc.hyps
				by (metis less_zeroE list.set_sel(1) list.size(3) zero_less_Suc)+
			moreover have "fst (pop c) \<notin> set carry"
				using carry_disj calculation Suc.prems by blast
  		ultimately have neq1: "hd carry \<noteq> fst (pop c)"
				by metis

			have id: "ident (fst (pop c)) \<in> idset c"
				using idset_def by (metis (mono_tags, lifting) ref mem_Collect_eq)

			have fresh: "fresh vars undefined \<notin> idset c"
				using fresh_notIn Suc.prems by blast

			have "Pos (hd (tl s)) \<in> set carry"

			hence neq2: "fst (pop c) \<noteq> Pos (hd (tl s))"
				using Suc.prems(6) id by auto
			oops
			hence neq3: "hd carry \<noteq> Pos (fresh vars undefined)"
				using idset_def Suc.prems fresh carry fresh_notIn by simp
				
			hence "card {hd carry, fst ?p, Pos (fresh vars undefined)} = 3"
				using neq1 neq2 neq3 by simp

			thus ?thesis using safe by simp
		next
			case rest
			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by arith
			thus ?thesis
				apply (rule Suc.hyps(1)[where ?c = ?rest and ?s = "tl s"
							and ?vars = "insert (fresh vars undefined) vars" and ?carry = "Neg (hd (tl s)) # tl carry"])
				using Suc.prems(1) c apply (metis finite_insert)
				using gt4 suc_card apply simp
				using n Suc.prems Suc.hyps apply (metis diff_Suc_1 list.sel(3) stock.simps(2))
				using rest apply simp
				using Suc.prems(5) c idset_def apply (smt mem_Collect_eq subset_iff subset_insertI)
				using Suc.prems(6) apply (metis finite_insert)
				done
		qed
  qed
qed
*)

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


(*
lemma splc_lit_uniq:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"v \<in> c'" "c' = l ! i" "i \<noteq> j" "i < card c - 2" "j < card c - 2" "init = Pos y" "last (tl (rev s)) = Neg y"
	shows "v \<notin> l ! j"
	using assms
proof (induction "card c - 3" arbitrary: c c' l s s' vars init v i j y)
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
		let ?nx = "hd s'"

		have expand: "l = {fst ?p, fst ?q, init} # insert ?nx (snd ?q) # []"
			using eq4 Suc.prems Suc.hyps
			by (smt One_nat_def Suc_1 Suc_diff_Suc Suc_length_conv diff_Suc_1 diff_is_0_eq' length_0_conv list.sel(1) nat_mult_1_right numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) splc.simps(2) zero_less_Suc zero_less_diff)

		have s': "hd s' \<in> set s'"
			using expand Suc.prems(5)
			by (metis list.distinct(1) list.sel(3) list.set_sel(1) splc.simps(1))

		obtain x y where xy: "snd ?q = {x, y}"
			using eq4 pop_card pop_ins
			by (smt (verit) card_eq_0_iff finite_insert leD not_less_eq_eq numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)

		hence c: "c = {fst ?p, fst ?q, x, y}"
			using eq4 Suc.prems pop_card pop_ins
			by (metis card_gt_0_iff diff_Suc_1 numeral_eq_Suc pred_numeral_simps(2) zero_less_numeral)

		hence "fst ?p \<noteq> x" and "fst ?q \<noteq> x" and "fst ?p \<noteq> y" and "fst ?q \<noteq> y"
			using Suc.prems eq4 pop_card pop_ins xy
			by (smt Suc_eq_numeral card_gt_0_iff insert_absorb insert_subset leD le_imp_less_Suc pred_numeral_simps(2) subset_insertI zero_less_numeral)+
		moreover have "fst ?p \<noteq> ?nx" and "fst ?q \<noteq> ?nx"
			using c s' Suc.prems(9) by force+
		moreover have "init \<noteq> ?nx" and "init \<noteq> x" and "init \<noteq> y"
			using c s' Suc.prems(8) by force+
		moreover have nth_defs: "l ! 0 = {fst ?p, fst ?q, init}" and "l ! 1 = insert ?nx (snd ?q)"
			using expand by simp+
		moreover have "i < 2" and "j < 2"
			using eq4 Suc.prems(13) Suc.prems(14) by simp+
		moreover have "i = 0 \<and> j = 1 \<or> i = 1 \<and> j = 0"
			using eq4 Suc.prems by force
		ultimately show ?thesis
			using Suc.prems(10) Suc.prems(11) xy by auto
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

		have n: "n = card ?rest - 3"
			using Suc.hyps suc_card by arith
		hence "v \<notin> tl l ! (j-1)"
			apply (rule Suc.hyps(1)[where ?i = "i-1" and ?c' = "tl l ! (i-1)" and ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
			using Suc.prems(1) c finite_insert apply metis
			using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
			using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
			using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
			using Suc.prems(5) expand apply simp
			using gt4 suc_card apply simp
			using Suc.prems(7) apply simp
			using Suc.prems(8) c apply (metis Nil_tl Un_iff insert_iff list.set_sel(2))
			using disj apply simp
			subgoal sorry
					 apply simp
			using Suc.prems(12) 

			oops

		then consider (hd) "c' = hd l"
			| (tl) "c' = tl l ! (i-1)"
			using Suc.prems expand
			by (metis list.sel(1) list.sel(3) nth_non_equal_first_eq)
		thus ?thesis
		proof cases
			case hd
			then show ?thesis 
		next
			case tl
			oops
			have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
				by (metis Nil_tl list.set_sel(2) subsetI)
			moreover have snd_p_set: "snd (pop c) \<subseteq> c"
				using c by auto
			ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
				using Suc.prems(9) by auto

			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by arith
			then show ?thesis sorry
		qed

qed


lemma splc_lit_uniq:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"v \<in> c" "v \<in> c'" "c' \<in> set l" 
	shows "\<forall>cc. cc \<notin> set l \<or> cc = c' \<or> v \<notin> cc"
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
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  		using pop_card pop_def pop_ins
  		by (metis Diff_insert_absorb One_nat_def card_eq_0_iff empty_iff fst_conv insertCI mk_disjoint_insert one_eq_numeral_iff semiring_norm(83) snd_conv)+
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

		then consider (safe) "c' = hd l"
			| (rest) "c' \<in> set (tl l)"
			using Suc.prems expand by force
		thus ?thesis
		proof cases
			case safe
			then show ?thesis using Suc.prems sorry
		next
			case rest

			have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
				by (metis Nil_tl list.set_sel(2) subsetI)
			moreover have snd_p_set: "snd (pop c) \<subseteq> c"
				using c by auto
			ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
				using Suc.prems(9) by auto

			obtain v' where v': "v' \<in> c'"
				using Suc.prems(11) by blast
			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by arith
			hence "\<forall>cc. cc \<notin> set (tl l) \<or> cc = c' \<or> v' \<notin> cc"
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
				(* using rest apply simp *)
				subgoal  oops
				using v' apply simp
				using Suc.prems Suc.hyps expand gt4 c n rest
				apply (smt (verit) IntI Nitpick.size_list_simp(2) One_nat_def Suc_mult_less_cancel1 Suc_pred' add_2_eq_Suc' card_insert_if diff_Suc_Suc emptyE finite_subset insertE less_Suc_eq_0_disj list.sel(3) list.set_sel(1) list.set_sel(2) mult.right_neutral n_not_Suc_n nat_0_less_mult_iff nat_mult_eq_1_iff numeral_3_eq_3 numeral_Bit0 numerals(2) rel_simps(71) set_ConsD snd_p_set zero_less_diff)
				done

			moreover have "\<nexists>cc. cc = hd l \<and> cc \<noteq> c' \<and> v \<in> cc"

			thus ?thesis 
		qed
qed
*)

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

(* try with list nth else might need to invoke refc here *)
lemma splc_aux_pair:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y \<and> Neg y = hd (tl (rev s))"
	shows "\<forall>c1 \<in> set l. \<exists>c2 \<in> set l. \<exists>x \<in> idset (set s). c1 \<noteq> c2 \<and> (Pos x \<in> c1 \<and> Neg x \<in> c2 \<or> Pos x \<in> c2 \<and> Neg x \<in> c1)"
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
  		using Suc.prems apply (auto simp add: Let_def idset_def)
  		by (metis (no_types, lifting) One_nat_def Suc.prems(6) card_eq_0_iff card_insert_if insertCI insertE not_less_eq_eq one_eq_numeral_iff pop_card pop_ins semiring_norm(83) zero_neq_numeral)+
  		
(*
		let ?p = "pop c"
		let ?q = "pop (snd ?p)"

  	have eq4expand: "splc c s' init = {fst ?p, fst ?q, init} # insert (hd s') (snd ?q) # []"
  		using eq4 Suc.prems(4)
  		by (metis (no_types, lifting) One_nat_def Suc_length_conv add_diff_cancel_right' diff_numeral_Suc length_0_conv list.sel(1) mult_2 numeral_3_eq_3 plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) splc.simps(2))

  	then obtain y where y: "init = Pos y"
  		using Suc.prems(10) by blast

  	have "rev (stock (card c - 3) vars) ! Suc 0 = Neg y"
  		using Suc.prems(10) Suc.prems(2) Suc.prems(3)
  		by (metis One_nat_def Suc.prems(4) Suc_1 add_diff_cancel_right' diff_numeral_Suc eq4 hd_conv_nth length_0_conv lit.inject(1) mult.right_neutral nth_tl numeral_3_eq_3 old.nat.distinct(1) plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) y zero_less_one)
  		oops

  	have "\<exists>x. tl (rev (stock (card c - 3) vars)) ! 0 = Neg x"
  		apply (rule tl_rev_stock_even_neg)
  		using Suc.prems by auto
  	hence "\<exists>x. hd s' = Neg x"
  		using Suc.prems(2) Suc.prems(3) Suc.prems(4)
  		by (metis One_nat_def Suc_1 add_diff_cancel_right' diff_numeral_Suc eq4 hd_conv_nth list.size(3) mult.right_neutral numeral_3_eq_3 old.nat.distinct(1) plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
  	then obtain x where x: "hd s' = Neg x"
  		by blast

  	hence "x = y"
  		using x y tl_rev_stock_pair


  	thus ?thesis 
  		oops
  		by (metis One_nat_def card_eq_0_iff insert_absorb insert_iff not_less_eq_eq one_eq_numeral_iff semiring_norm(83) zero_neq_numeral)+
*)
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
			fix c1
			assume c1: "c1 \<in> set l"

			obtain c2 where c2: "c2 \<in> set l"
				using c1 by simp

			then consider (edge) "c1 = hd l"
				| (rest) "c1 \<in> set (tl l)"
				using expand Suc.prems c1 by force
			thus "\<exists>c2 \<in> set l. \<exists>x \<in> idset (set s). c1 \<noteq> c2 \<and> (Pos x \<in> c1 \<and> Neg x \<in> c2 \<or> Pos x \<in> c2 \<and> Neg x \<in> c1)"
			proof cases
				case edge
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
					
					then obtain y where init: "init = Pos y"
						using Suc.prems(10) by force
(*
					hence y: "y = (fresh (insert (fresh vars undefined) vars) undefined)"
						using eq5 s Suc.prems(2) Suc.prems(3) Suc.prems(8) Suc.prems(10)
						sorry
						by (metis UnI1 hd_Cons_tl hd_rev last.simps length_Cons length_rev list.distinct(1) list.size(3) lit.inject(1) numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) set_ConsD set_rev zero_neq_numeral)
*)
					then obtain c2 where c2: "c2 = {fst (pop (snd ?p)), fst (pop (snd (pop (snd ?p)))), init}"
						by simp
(*
					have "l = Neg (fresh (insert (fresh vars undefined) vars) undefined) # Pos (fresh vars undefined) # Neg (fresh vars undefined) # []"
						using Suc.prems
*)
					hence n_prev: "Neg y = ?n_prev"
						using Suc.prems s eq5expand
						by (metis init lit.inject(1))

					hence "c1 \<noteq> c2"
						using splc_hd_tl_disj Suc.prems expand tlexpand edge c2
						by (smt IntI UnionI empty_iff insert_subset list.sel(3) list.set_intros(1) subset_insertI)
					moreover have "Neg y \<in> hd l"
						using edge n_prev Suc.prems(5) eq5expand by simp
					moreover have "Pos y \<in> c2"
						using c2 init by simp
					moreover have "y \<in> idset (set s)"
						using s init n_prev Suc.prems(3) unfolding idset_def
						by (smt Nil_is_rev_conv hd_Cons_tl ident.simps(2) list.distinct(1) list.sel(3) list.set_sel(1) list.set_sel(2) mem_Collect_eq rev_singleton_conv set_rev)
					ultimately show ?thesis
						using Suc.prems(5) c2 edge expand tlexpand
						by (metis insertCI list.simps(15))

				next
					case gt5

					hence tlexpand: "splc (snd ?p) ?xs init = {hd ?xs, fst (pop (snd ?p)), hd (tl ?xs)}	# splc (snd (pop (snd ?p))) (tl (tl ?xs)) init"
						using Suc.prems gt4 splc_gt4 suc_card
						by (smt Suc_diff_le diff_Suc_1 diff_diff_left diff_mult_distrib2 eval_nat_numeral(3) le_numeral_Suc length_tl less_Suc_eq mult_2 nat_less_le pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))

					hence gt5expand: "splc c s' init = {?n_prev, fst ?p, ?p_cur} 
																							# {hd ?xs, fst (pop (snd ?p)), hd (tl ?xs)} 
																							# splc (snd (pop (snd ?p))) (tl (tl ?xs)) init"
						using expand gt5 by simp
(*
					hence s: "s = Neg (fresh vars undefined) # Pos (fresh vars undefined)
											# Neg (fresh (insert (fresh vars undefined) vars) undefined) # tl (tl (tl s))"
						using gt5 Suc.prems suc_card
						by (smt Suc_diff_le diff_Suc_1 diff_Suc_eq_diff_pred eval_nat_numeral(3) list.sel(3) nat_less_le numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) stock.simps(2))
*)

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
						using n_prev tl_rev_stock_even_neg Suc.prems Suc.hyps
						by (metis even_zero length_0_conv list.distinct(1) list.sel(3) stock.elims zero_less_Suc)
					obtain y where pos_y: "?p_cur = Pos y"
						using p_cur tl_rev_stock_odd_pos[of vars "card c - 3" 1] stock_length
						by (metis (no_types, lifting) One_nat_def Suc.hyps(2) Suc.prems(2) Suc.prems(3) Suc.prems(7) Suc_eq_plus1 Suc_lessI Suc_pred add_diff_inverse_nat dvd_def even_diff_nat gt4 length_greater_0_conv length_tl list.size(3) mult_eq_self_implies_10 mult_pos_pos nat_1_add_1 nat_less_le numeral_eq_Suc odd_one pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)
					have "tl (rev (stock (card c - 3) vars)) ! Suc 1 = Neg y"
						apply (rule tl_rev_stock_pair)
						using Suc.prems(7) apply simp
						using Suc.prems(6) apply simp
						apply simp
						using Suc.prems(2) Suc.prems(3) Suc.prems(4) stock_length gt5 apply simp
						using pos_y p_cur Suc.prems(2) Suc.prems(3) Suc.prems(4) apply simp
						done
					moreover have "tl (rev (stock (card c - 3) vars)) ! Suc 1 = hd (tl (tl s'))"
						using Suc.prems(2) Suc.prems(3) Suc.prems(4) hd_xs Suc_1 by arith
					ultimately have neg_y: "hd ?xs = Neg y"
						by simp

					have "Pos y \<in> set s'"
						using pos_y neg_y
						by (metis Nil_tl hd_in_set list.set_sel(2) lit.distinct(1))
					moreover have "Neg y \<in> set s'"
						using pos_y neg_y Suc.prems Suc.hyps p_cur
						by (metis (no_types, lifting) Suc_1 diff_Suc_eq_diff_pred hd_xs length_greater_0_conv length_rev length_tl list.size(3) lit.distinct(1) nth_Cons_0 nth_mem nth_tl rev_nth stock.simps(2) zero_less_diff)
					moreover have "set s' \<subseteq> set s"
						using Suc.prems(3)
						by (metis list.sel(2) list.set_sel(2) set_rev subsetI)
					ultimately have idy: "y \<in> idset (set s)"
						using idset_iff by force

(*
					have "fst ?p \<noteq> fst (pop (snd ?p))"
						using gt5 c pop_isin suc_card
						by (metis One_nat_def card.empty insert_absorb less_one n_not_Suc_n zero_neq_numeral)
*)

					hence "{?n_prev, fst ?p, ?p_cur} \<noteq> {hd ?xs, fst (pop (snd ?p)), hd (tl ?xs)}"
						using splc_hd_tl_disj Suc.prems(1-9) gt5expand by fastforce


					thus ?thesis using pos_y neg_y idy edge gt5expand Suc.prems
						by (metis insertCI list.sel(1) list.simps(15))
				qed
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

				hence "\<forall>c1 \<in> set (tl l). \<exists>c2 \<in> set (tl l). \<exists>x \<in> idset (set (butlast (butlast s))). c1 \<noteq> c2 \<and> (Pos x \<in> c1 \<and> Neg x \<in> c2 \<or> Pos x \<in> c2 \<and> Neg x \<in> c1)"
					apply (rule Suc.hyps(1)[where ?vars = vars and ?s = "butlast (butlast s)" and ?s' = "tl (tl s')" and ?init = init])
					using Suc.prems(1) c finite_insert apply metis
					using Suc.prems(2) suc_card Suc.hyps stock_butlast apply (metis diff_Suc_1 diff_commute)
					using Suc.prems(3) apply (metis butlast_rev rev_rev_ident)
					using Suc.prems(4) suc_card apply (metis Suc_1 diff_Suc_1 diff_commute diff_diff_left diff_mult_distrib2 length_tl mult.right_neutral plus_1_eq_Suc)
					using Suc.prems(5) expand apply simp
					using gt4 suc_card apply simp
					using Suc.prems(7) apply simp
					using Suc.prems(8) snd_p_set tl_tl_set apply blast
					using disj apply simp
					using Suc.prems(10)  oops
					done

				then show ?thesis using rest Suc.prems(5) expand
					by (metis idset_iff in_set_butlastD insertCI list.sel(3) list.simps(15))
			qed
		qed
	qed
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

lemma splc_init_neighbour:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 5" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y"
	shows "Neg (ident init) \<in> hd l"
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


		hence "?n_prev = Neg (fresh (insert (fresh vars undefined) vars) undefined)"
			using Suc.prems by simp

		then show ?thesis 
	next
		case gt5
		then show ?thesis sorry
	qed
qed




lemma splc_aux_clause_neighbour:
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = last (butlast (splc c s' init)) # butlast (butlast (splc c s' init)) @ last (splc c s' init) # []"
					"card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}"
					"\<exists>y. init = Pos y"
	shows "\<forall>i < length l - 2. \<exists>x. Pos x \<in> l ! i \<and> Neg x \<in> l ! Suc i"
	using assms
	sorry
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

		have "l = last (butlast (splc c s' init))
										# butlast (butlast (splc c s' init))
										@ last (splc c s' init) # []"
			using Suc.prems(5) by simp
		hence expand: "l = last (butlast (splc c s' init))
										# butlast (butlast ({?n_prev, fst ?p, ?p_cur} # splc (snd ?p) ?xs init))
										@ last (splc c s' init) # []"
			using gt4 splc_gt4 Suc.prems(4) by metis

		have "card (last (butlast (splc c s' init))) = 3"
			apply (rule splc_card_3[where ?c = c and ?s = s and ?vars = vars and ?s' = s' and ?init = init])
			using Suc.prems apply auto
			using gt4 Suc.prems(4) splc_gt4
			by (smt (verit) append_butlast_last_id in_set_butlastD last_in_set list.distinct(1) list.inject self_append_conv2 splc.elims)

		hence "\<exists>x y z. x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z \<and> last (butlast (splc c s' init)) = {x, y, z}"
			by (meson card_3_iff)

		moreover have "\<exists>i. Pos i \<in> last (butlast (splc c s' init)) \<and> init = Pos i"
			apply (rule splc_aux_clause_first[where ?c = c and ?s = s and ?vars = vars and ?s' = s' and ?init = init])
			using Suc.prems by blast+

		ultimately obtain l1 l2 v where "l1 \<noteq> l2" and "l1 \<noteq> Pos v" and "l2 \<noteq> Pos v"
			and "last (butlast (splc c s' init)) = {l1, l2, Pos v}" and "Pos v = init"
			by (smt insert_commute insert_iff singletonD)

		have tl_tl_set: "set (tl (tl s')) \<subseteq> set s'"
			by (metis Nil_tl list.set_sel(2) subsetI)
		moreover have snd_p_set: "snd (pop c) \<subseteq> c"
			using c by auto
		ultimately have disj: "set (tl (tl s')) \<inter> snd (pop c) = {}"
			using Suc.prems(9) by auto

		thus ?thesis
		proof (intro allI impI)

		fix i
		assume i: "i < length l - 2"

		consider (nil) "i = 0"
			| (gt0) "i > 0"
			by arith
		thus "\<exists>x. Pos x \<in> l ! i \<and> Neg x \<in> l ! Suc i"
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
					using expand tlexpand Suc.prems(5) by simp

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
					using nil zero_neq_numeral
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
		next
			case gt0

			have n: "n = card ?rest - 3"
				using Suc.hyps suc_card by arith

			thm Suc.hyps
			hence "\<forall>i < length (tl l) - 2. \<exists>x. Pos x \<in> tl l ! i \<and> Neg x \<in> tl l ! Suc i"
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

			hence "\<forall>i < length l - 3. \<exists>x. Pos x \<in> tl l ! i \<and> Neg x \<in> tl l ! Suc i"
				by simp
			hence "\<forall>i < length l - 3. \<exists>x. Pos x \<in> l ! Suc i \<and> Neg x \<in> l ! Suc (Suc i)"
				using Suc.prems(5) expand by fastforce
			hence "\<forall>i. \<exists>x. i < length l - 3 \<longrightarrow> Pos x \<in> l ! Suc i \<and> Neg x \<in> l ! Suc (Suc i)"
				by simp
			hence "\<forall>i. \<exists>x. i > 0 \<and> i < length l - 2 \<longrightarrow> Pos x \<in> l ! i \<and> Neg x \<in> l ! Suc i"
				by (smt One_nat_def Suc_inject Suc_less_eq Suc_pred diff_Suc_eq_diff_pred numeral_3_eq_3 numeral_2_eq_2 zero_less_diff)
			hence "\<exists>x. Pos x \<in> l ! i \<and> Neg x \<in> l ! Suc i"
				using gt0 i by simp
			thus ?thesis by simp
		qed
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



lemma
	assumes "vmap = (\<lambda>x. undefined)" "finite vars"
					"vmap_new = fold (\<lambda>x f. if f (ident x) = undefined then f(ident x := False) else f) (stock n vars) vmap"
	shows "\<forall>x. Pos x \<in> set (stock n vars) \<longrightarrow> vmap_new x"
	using assms
proof (induction n arbitrary: vars vmap vmap_new)
  case 0
  thus ?case by simp
next
  case (Suc n)

  hence "butlast (butlast (stock (Suc n) vars)) = stock n vars"
  	by (metis diff_Suc_1 stock_butlast)
  hence stock_extend: "stock (Suc n) vars = stock n vars @ [last (butlast (stock (Suc n) vars)), last (stock (Suc n) vars)]"
  	by (metis (no_types, lifting) append.assoc append_butlast_last_id butlast.simps(2) last.simps less_numeral_extra(3) list.distinct(1) stock.elims zero_less_Suc)

  have "\<exists>x. x \<notin> vars \<and> last (stock (Suc n) vars) = Pos x"
  	by (rule last_stock_pos) (auto simp add: Suc.prems)
  then obtain x where x: "last (stock (Suc n) vars) = Pos x"
  	by blast

  have "\<exists>y. stock (Suc n) vars ! (length (stock (Suc n) vars) - 2) = Neg y"
  	apply (rule stock_even_neg)
  	using Suc.prems apply simp
  	using Suc.prems apply simp
  	using stock_length_even Suc.prems dvd_minus_self apply blast
  	using Suc.prems stock_gt0 apply (meson diff_less zero_less_Suc zero_less_numeral)
  	done
  moreover have nth_last_butlast: "stock (Suc n) vars ! (length (stock (Suc n) vars) - 2) = last (butlast (stock (Suc n) vars))"
  	using Suc.prems stock_gt0 stock_length_even
  	by (metis (no_types, lifting) One_nat_def Suc_1 Suc_pred diff_Suc_eq_diff_pred diff_less last_conv_nth length_butlast length_greater_0_conv list.size(3) nth_butlast odd_one zero_less_Suc)
  ultimately obtain y where y: "last (butlast (stock (Suc n) vars)) = Neg y"
  	by force

  hence xy: "x = y"
  	using stock_pair Suc.prems x nth_last_butlast stock_gt0 stock_length_even 
  	by (smt One_nat_def Suc_1 Suc_diff_Suc diff_less dvd_diff_nat even_numeral last_conv_nth length_0_conv less_Suc0 linorder_neqE_nat lit.inject(1) odd_one zero_less_Suc)
  hence pos_notin: "Pos x \<notin> set (stock n vars)"
  	using x stock_suc_last Suc.prems by metis
  hence neg_notin: "Neg x \<notin> set (stock n vars)"
  	using y xy stock_suc_butlast Suc.prems by metis

  have "\<forall>x. Pos x \<in> set (stock n vars) \<longrightarrow> fold (\<lambda>x f. if f (ident x) = undefined then f(ident x := False) else f) (stock n vars) vmap x"
  	by (rule Suc.IH) (auto simp add: Suc.prems)

  let ?vmap' = "fold (\<lambda>x f. if f (ident x) = undefined then f(ident x := False) else f) (stock n vars) vmap"
  have "\<forall>l. l \<in> set (stock n vars) \<longrightarrow> ?vmap' (ident l) = False"
  	apply (induction n vars rule: stock.induct)
  	 apply auto
  	apply (simp add: Let_def split: if_splits)

  have "\<forall>l. l \<notin> set (stock n vars) \<longrightarrow> ?vmap' (ident l) = undefined"
  	using Suc.prems 

  have "vmap_new = fold (\<lambda>x f. if f (ident x) = undefined then f(ident x := False) else f) [Neg y, Pos x] ?vmap'"
  	using stock_extend Suc.prems x y by simp
  hence "vmap_new = fold (\<lambda>x f. if f (ident x) = undefined then f(ident x := False) else f) [Neg x, Pos x] ?vmap'"
  	using xy by simp
  moreover have "?vmap' x = undefined"
  	using pos_notin neg_notin
  hence "\<not>vmap_new x"
  	using Suc.prems 

  then show ?case sorry
qed

lemma 
	assumes "vmap_new = fold (\<lambda>x f. if f (ident x) = undefined then f(ident x := False) else f) (stock (card (c :: 'a lit set) - 3) vars) vmap"
					"\<forall>l. l \<in> set (stock (card c - 3) vars) \<longrightarrow> vmap (ident l) = undefined" "l \<in> set (stock (card c - 3) vars)" "l = Pos x"
	shows "vmap_new x"
	using assms
proof (induction "card c - 3" arbitrary: c vars vmap vmap_new l x)
  case 0
  thus ?case by simp
next
  case (Suc n)

	let ?p = "pop c"
	let ?t = "fst ?p"
	let ?rest = "snd ?p"

	have c: "c = insert ?t ?rest"
		using pop_ins Suc.prems Suc.hyps
		by (metis card_eq_0_iff diff_0_eq_0 old.nat.distinct(1))

	have suc_card: "Suc (card ?rest) = card c"
		using Suc.prems Suc.hyps c pop_card
		by (metis card_eq_0_iff diff_0_eq_0 old.nat.distinct(1))

	have n: "n = card ?rest - 3"
		using Suc.hyps suc_card by arith

  hence "vmap_new x"
		apply (rule "Suc.hyps")
			 prefer 4 apply simp
		

  then show ?case sorry
qed


lemma vmap_true_pos_lift: "vmap v \<Longrightarrow> l = Pos v \<Longrightarrow> (vmap\<up>) l"
	unfolding lift_def by simp

lemma vmap_false_neg_lift: "\<not>vmap v \<Longrightarrow> l = Neg v \<Longrightarrow> (vmap\<up>) l"
	unfolding lift_def by simp

lemma 
	assumes "finite c" "s = stock (card c - 3) vars" "s' = tl (rev s)" "length s' = 2 * (card c - 3) - 1"
					"l = splc c s' init" "card c \<ge> 4" "finite vars" "init \<notin> set s' \<union> c" "set s' \<inter> c = {}" "\<exists>y. init = Pos y"
					"i \<le> length l - 2"
	shows "\<forall>x \<in> idset (set s'). Neg x \<in> l ! i \<longrightarrow> Neg x = s' ! (2*i)"
	using assms
	proof (induction "card c - 3" arbitrary: c l s s' vars init i)
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
				using Suc.prems idset_iff by (fastforce simp add: Let_def)
		next
			case gt4

			let ?p = "pop c"
			let ?t = "fst ?p"
			let ?rest = "snd ?p"
		
			have c: "c = insert ?t ?rest"
				using pop_ins Suc.prems Suc.hyps
				by (metis card_eq_0_iff diff_0_eq_0 old.nat.distinct(1))
		
			have suc_card: "Suc (card ?rest) = card c"
				using Suc.prems Suc.hyps c pop_card
				by (metis card_eq_0_iff diff_0_eq_0 old.nat.distinct(1))

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

			hence "\<forall>x \<in> idset (set (tl (tl s'))). Neg x \<in> (tl l) ! (i-1) \<longrightarrow> Neg x = (tl (tl s')) ! (2*(i-1))"
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
				using Suc.prems(11) apply simp
				done

			thus ?thesis
		qed
	qed




lemma sat_single: "c \<noteq> {} \<Longrightarrow> sat (c # [])"
	unfolding sat_def models_def 
	by (metis empty_set ex_in_conv lift_def lit.case_distrib set_ConsD)

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

lemma test__:
	assumes "\<exists>l \<in> c. (vmap\<up>) l" "finite c" "finite vars" "vars \<subseteq> idset c"
	shows "\<not> vmap \<Turnstile> fst (refc c vars)"
	using assms unfolding models_def refc_def
	oops


lemma test_:
	assumes "vmap \<Turnstile> fst (refc c vars)" "finite c" "finite vars" "vars \<subseteq> idset c"
	shows "\<exists>l \<in> c. (vmap\<up>) l"
	using assms
	oops

lemma test:
	assumes "vmap \<Turnstile> fst (refc c vars)"
	shows "vmap \<Turnstile> c # []"
	using assms unfolding models_def refc_def
	oops

lemma ex_mid_lift: "(vmap\<up>) (Pos x) \<longleftrightarrow> \<not>(vmap\<up>) (Neg x)"
	unfolding lift_def by auto


lemma "(\<not> vmap \<Turnstile> c # [] \<Longrightarrow> \<not> vmap \<Turnstile> fst (refc c vars)) \<Longrightarrow> \<nexists>vmap. vmap \<Turnstile> c # xs \<Longrightarrow> \<nexists>vmap. vmap \<Turnstile> fst (refc c vars) @ xs"
	apply (induction xs arbitrary: vmap c vars)
	unfolding refc_def apply (auto simp add: Let_def split: if_splits)
	 apply (metis card.empty sat_def sat_single zero_le)

lemma inv_test:
	assumes ""


thm splc.induct
lemma inv:
	assumes "\<not> sat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite c" "finite vars" "card c \<ge> 4"
	shows "\<not> sat (fst (refc c vars) @ xs)"
	using assms unfolding sat_def models_def
proof -
(*
	assume "\<not>\<not>sat (fst (refc c vars) @ xs)"

	hence "\<exists>vmap. vmap \<Turnstile> (fst (refc c vars)) @ xs"
		unfolding sat_def by simp

	hence "\<exists>vmap. \<forall>c \<in> set ((fst (refc c vars)) @ xs). \<exists>l \<in> c. (vmap\<up>) l"
		unfolding models_def by simp
*)
	have "\<nexists>vmap. vmap \<Turnstile> c # xs"
		using assms(1) unfolding sat_def by simp
	hence "\<nexists>vmap. \<forall>c' \<in> set (c # xs). \<exists>l \<in> c'. (vmap\<up>) l"
		unfolding models_def by simp
	hence "\<forall>vmap. \<not> (\<forall>c' \<in> set (c # xs). \<exists>l \<in> c'. (vmap\<up>) l)"
		by simp
	hence "\<forall>vmap. \<exists>c' \<in> set (c # xs). \<not> (\<exists>l \<in> c'. (vmap\<up>) l)"
		by simp
	hence a: "\<forall>vmap. \<exists>c' \<in> set (c # xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l"
		by simp

	fix vmap
	have "(\<forall>l \<in> c. \<not> (vmap\<up>) l) \<or> (\<exists>c' \<in> set xs. \<forall>l \<in> c'. \<not> (vmap\<up>) l)"
		using a by simp
	then consider (hd) "(\<forall>l \<in> c. \<not> (vmap\<up>) l)"
		| (tl) "(\<exists>c' \<in> set xs. \<forall>l \<in> c'. \<not> (vmap\<up>) l)"
		by blast
	hence "\<exists>c' \<in> set (fst (refc c vars) @ xs). \<forall>l \<in> c'. \<not> (vmap\<up>) l"
	proof cases
		case hd
		thus ?thesis
		proof -
			assume "\<forall>c' \<in> set (fst (refc c vars)). \<exists>l \<in> c'. (vmap\<up>) l"

			have c1: "last (butlast (fst (refc c vars))) \<in> set (fst (refc c vars))"
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
			have "\<exists>v. Pos v \<in> last (butlast (fst (refc c vars))) \<and> last (stock (card c - 3) vars) = Pos v"
				apply (rule splc_aux_clause_first[of c "stock (card c - 3) vars" vars "tl (rev (stock (card c - 3) vars))" _ "last (stock (card c - 3) vars)"])
				unfolding refc_def using assms(5) apply (auto simp add: Let_def split: if_splits)
				using assms stock_length aux1 aux2 aux4 apply fastforce+
				done




		hence "\<exists>subc \<in> set (fst (refc c vars)). \<forall>l \<in> subc. \<not> (vmap\<up>) l"

			oops

		proof (induction "card c - 3" arbitrary: c vars)
			case 0
			thus ?case
				unfolding refc_def by (auto simp add: Let_def split: if_splits)
		next
			case (Suc n)
			consider (eq4) "card c = 4"
				| (gt4) "card c > 4"
				using Suc.hyps by arith
			thus ?case
			proof cases
				case eq4

				let ?p = "pop c"
				let ?q = "pop (snd ?p)"

				let ?init = "last (stock (card c - 3) vars)"
				let ?other = "(hd (tl (rev (stock (card c - 3) vars))))"
		
				have eq4expand: "fst (refc c vars) = {fst ?p, fst ?q, last (stock (card c - 3) vars)} # insert (hd (tl (rev (stock (card c - 3) vars)))) (snd ?q) # []"
					using eq4 Suc.prems unfolding refc_def
					by (auto simp add: Let_def split: if_splits)

				have fst_p: "fst ?p \<in> c"
					using pop_isin eq4
					by (metis card.empty zero_neq_numeral)
				have fst_q: "fst ?q \<in> c"
					using assms pop_isin pop_card pop_ins eq4
					by (metis One_nat_def card.empty card_gt_0_iff insertCI one_eq_numeral_iff semiring_norm(83) zero_less_numeral)
				have snd_q: "snd ?q \<subseteq> c"
					using assms pop_card pop_ins eq4
					by (smt One_nat_def card.empty card_gt_0_iff dual_order.trans finite_insert one_eq_numeral_iff semiring_norm(83) subset_insertI zero_less_numeral)

				have "ident ?init = ident ?other"
					using eq4expand hd_stock_neg stock_0
					by (smt One_nat_def add_diff_cancel_right' diff_numeral_Suc eq4 hd_conv_nth ident.simps(1) ident.simps(2) last.simps last_conv_nth last_rev length_Cons length_rev length_tl list.sel(3) list.size(3) nth_tl numeral_3_eq_3 old.nat.distinct(1) plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) stock.simps(2) zero_less_one)
				
				have "stock (card c - 3) vars = [Neg (fresh vars undefined), Pos (fresh vars undefined)]"
					using eq4 stock_eq4 by blast
				hence x: "?init = Pos (fresh vars undefined) \<and> ?other = Neg (fresh vars undefined)"
					by simp

				hence one: "(vmap\<up>) ?init \<Longrightarrow> \<not>(vmap\<up>) ?other"
					using ex_mid_lift by metis
				hence two: "(vmap\<up>) ?other \<Longrightarrow> \<not>(vmap\<up>) ?init"
					using x by metis

				then consider (vmap_init) "(vmap\<up>) ?init"
					| (vmap_other) "(vmap\<up>) ?other"
					using ex_mid_lift x by metis
				thus ?thesis
				proof cases
					case vmap_init
					then obtain subc where subc: "subc = insert ?other (snd ?q)"
						by blast

					hence "\<not>(vmap\<up>) ?other"
						using one vmap_init by blast
					moreover have "\<forall>l \<in> snd ?q. \<not>(vmap\<up>) l"
						using snd_q hd Suc.prems by blast
					ultimately show ?thesis
						using eq4expand Suc.prems by simp
				next
					case vmap_other
					then obtain subc where subc: "subc = {fst ?p, fst ?q, last (stock (card c - 3) vars)}"
						by blast

					hence "\<not>(vmap\<up>) ?init"
						using two vmap_other by blast
					moreover have "\<not>(vmap\<up>) (fst ?p)"
						using fst_p hd Suc.prems by blast
					moreover have "\<not>(vmap\<up>) (fst ?q)"
						using fst_q hd Suc.prems by blast
					ultimately show ?thesis
						using eq4expand Suc.prems by simp
				qed
			next
				case gt4

				let ?p = "pop c"
				let ?t = "fst ?p"
				let ?rest = "snd ?p"
			
				have c: "c = insert ?t ?rest"
					using pop_ins Suc.prems Suc.hyps
					by (metis card_eq_0_iff diff_0_eq_0 old.nat.distinct(1))
	
				have suc_card: "Suc (card ?rest) = card c"
					using Suc.prems Suc.hyps c pop_card
					by (metis card_eq_0_iff diff_0_eq_0 old.nat.distinct(1))

				have n: "n = card ?rest - 3"
					using Suc.hyps suc_card by arith

				thm Suc.hyps
				hence "\<exists>subc \<in> set (fst (refc ?rest vars)). \<forall>l \<in> subc. \<not> (vmap\<up>) l"
					apply (rule Suc.hyps(1))
					using c Suc.prems by blast

				then show ?thesis 
			qed
		qed
	next
		case tl
		then show ?thesis sorry
	qed

		oops
	obtain c' where "c' \<in> set (c # xs)"
		by fastforce
	then consider (hd) "c' = c"
		| (tl) "c' \<in> set xs"
		by fastforce
	hence "\<forall>l \<in> c'. \<not> (vmap\<up>) l"
	proof cases
		case hd
		thus ?thesis
		proof (induction "card c - 3" arbitrary: c)
			case 0
			thus ?case
				using assms(5) hd by auto
		next
			case (Suc n)
			consider (eq4) "card c = 4"
				| (gt4) "card c > 4"
				using Suc.prems assms(5) hd by fastforce
			thus ?case
			proof cases
				case eq4
				then show ?thesis 
			next
				case gt4
				then show ?thesis sorry
			qed
		qed
	next
		case tl

		then show ?thesis sorry
	qed



	show "False" sorry
qed

lemma checkpoint_le3:
	assumes "sat (c # xs)" "card c \<le> 3"
	shows "sat (fst (refc c vars) @ xs)"
	using assms unfolding refc_def
	by (auto simp add: Let_def split: if_splits)


lemma checkpoint:
	assumes "sat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite c" "finite vars" "card c \<ge> 4"
	shows "sat (fst (refc c vars) @ xs)"
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

		have aux_c: "\<forall>c' \<in> set (butlast (butlast (fst (refc c vars)))). \<exists>i j. i \<notin> vars \<and> j \<notin> vars \<and> i \<noteq> j \<and> Pos i \<in> c' \<and> Neg j \<in> c'"
			apply (rule splc_aux_clause[where ?c = c and ?s = ?s and ?vars = vars and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
			prefer 11 using assms idset_iff apply (meson UnionI list.set_intros(1) subset_iff)
			using assms aux1 aux2 aux3 stock_length unfolding refc_def
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
				then show ?thesis sorry
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

fun fold_rotate :: "nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b"
	where "fold_rotate 0 f (x # xs) init = init"
	| "fold_rotate (Suc n) f (x # xs) init = fold_rotate n f xs (f x init)"

fun map_rotate_carry :: "nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a list * 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'a list"
	where "map_rotate_carry 0 f (x # xs) carry = x # xs"
	| "map_rotate_carry (Suc n) f (x # xs) carry = map_rotate_carry n f (xs @ x # []) (snd (f x carry)) @ fst (f x carry)"

fun n_comp :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
	where "n_comp 0 f = id"
	| "n_comp (Suc n) f = f \<circ> n_comp n f"

fun refc_rotate
	where "refc_rotate [] = []"
	| "refc_rotate (x # xs) = xs @ (fst (refc x (idset (\<Union>(set (x # xs))))))"

lemma "card x \<ge> 4 \<Longrightarrow> \<forall>c \<in> set (fst (refc x (idset (\<Union>(set (x # xs)))))). card c = 3"
proof -
	assume "card x \<ge> 4"
	show "\<forall>c \<in> set (fst (refc x (idset (\<Union>(set (x # xs)))))). card c = 3"
	proof (intro ballI)
		fix c
		assume c: "c \<in> set (fst (refc x (idset (\<Union>(set (x # xs))))))"

		have "finite (idset (\<Union> (set (x # xs))))"
			oops

		let ?s = "stock (card x - 3) (idset (\<Union> (set (x # xs))))"
		show "card c = 3"
			apply (rule splc_card_3[where ?c = x and ?vars = "idset (\<Union>(set (x # xs)))" and ?s = ?s and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
			using \<open>4 \<le> card x\<close> card.infinite apply fastforce
						 apply simp
						apply simp
			using stock_length
		qed

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

lemma n_comp_refc_rotate: "(n_comp (Suc n) refc_rotate) (x # xs) = (n_comp n refc_rotate) (xs @ (fst (refc x (idset (\<Union>(set (x # xs)))))))"
	by (induction n refc_rotate arbitrary: x xs rule: n_comp.induct) auto

lemma l: "(n_comp (Suc n) refc_rotate) xs = refc_rotate (n_comp n refc_rotate xs)"
	by simp

lemma "\<lbrakk> hd xs = hd ys; idset (\<Union>(set xs)) = idset (\<Union>(set ys)) \<rbrakk> \<Longrightarrow> refc_rotate xs = refc_rotate ys"
	apply (induction xs arbitrary: ys rule: refc_rotate.induct)
	 apply (auto simp add: idset_def)
                               
lemma "(n_comp n refc_rotate) (xs @ (fst (refc x (idset (\<Union>(set (x # xs))))))) = (n_comp n refc_rotate) xs @ (fst (refc x (idset (\<Union>(set (x # xs))))))"
	apply (induction n arbitrary: x xs)
	 apply auto

lemma ys_drop: "n \<le> length xs \<Longrightarrow> \<exists>ys. n_comp n refc_rotate xs = (drop n xs) @ ys"
	apply (induction n arbitrary: xs)
	 apply auto
	by (smt (verit) append.assoc drop_Suc drop_eq_Nil less_Suc_eq_le linorder_not_le list.sel(3) not_less_iff_gr_or_eq refc_rotate.elims tl_append2 tl_drop)

lemma "\<forall>c \<in> set xs. finite c \<Longrightarrow> n \<le> length xs \<Longrightarrow> ((n_comp n refc_rotate) xs = (drop n xs) @ ys) \<Longrightarrow> (\<forall>c \<in> set ys. card c = 3)"
	apply (induction n arbitrary: xs ys)
	 apply auto


lemma ys_drop_suc: "\<lbrakk> n < length xs; n_comp n refc_rotate xs = (drop n xs) @ ys \<rbrakk>
					\<Longrightarrow> n_comp (Suc n) refc_rotate xs = (drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys)))))"
	apply (induction n arbitrary: xs ys)
	 apply auto
	 apply (metis drop0 drop_Suc list.exhaust_sel refc_rotate.simps(2))
	by (smt Union_Un_distrib append.assoc append_Cons drop_Suc drop_eq_Nil list.collapse nat_less_le not_less_iff_gr_or_eq refc_rotate.simps(2) set_append tl_drop)

lemma refc_rotate_finite:
	assumes "\<forall>c \<in> set xs. finite c" "n \<le> length xs"
	shows "\<forall>c \<in> set (n_comp n refc_rotate xs). finite c"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  hence "n \<le> length xs"
  	by arith
  hence "\<exists>ys. n_comp n refc_rotate xs = (drop n xs) @ ys"
  	using ys_drop by blast
  then obtain ys where ys: "n_comp n refc_rotate xs = (drop n xs) @ ys"
  	by blast

  hence expand_suc: "n_comp (Suc n) refc_rotate xs = (drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys)))))"
  	using Suc.prems(2) Suc_le_lessD ys_drop_suc by blast

  thus ?case
  proof (intro ballI)
  	fix c
  	assume c: "c \<in> set (n_comp (Suc n) refc_rotate xs)"

  	then consider (front) "c \<in> set (drop (Suc n) xs @ ys)"
			| (rear) "c \<in> set (fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys))))))"
			using expand_suc by fastforce
		thus "finite c"
		proof cases
			case front
			thm Suc.IH
			have "\<forall>c \<in> set (n_comp n refc_rotate xs). finite c"
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



lemma
	assumes "sat xs" "\<forall>c \<in> set xs. finite c \<and> card c \<ge> 4"
	shows "sat (n_comp (length xs) refc_rotate xs)"
	using assms
proof (induction "length xs" refc_rotate arbitrary: xs rule: n_comp.induct)
  case 1
  then show ?case by simp
next
  case (2 n)

  have "sat (fst (refc (hd xs) (idset (\<Union> (set (hd xs # tl xs))))) @ (tl xs))"
  	apply (rule checkpoint)
  	using "2.prems"(1) "2.hyps"(2) apply (metis list.collapse list.size(3) old.nat.distinct(1))
  		 apply simp
  	using 2 apply (metis Zero_neq_Suc hd_in_set list.size(3))
  	using 2 finite_expr_idset apply (metis list.collapse list.size(3) old.nat.distinct(1))
  	using 2 apply (metis length_0_conv list.set_sel(1) old.nat.distinct(1))
  	done

  hence "sat ((tl xs) @ (fst (refc (hd xs) (idset (\<Union> (set (hd xs # tl xs)))))))"
  	using sat_rotate_append by blast

  thm "2.hyps"(1)
  have "sat (n_comp (length (tl xs)) refc_rotate (tl xs))"
  	using 2 by (metis diff_Suc_1 length_0_conv length_tl list.set_sel(2) old.nat.distinct(1) sat_tl)

  hence "sat ((n_comp (length (tl xs)) refc_rotate (tl xs)) @ (fst (refc (hd xs) (idset (\<Union> (set (hd xs # tl xs)))))))"
  	

  thm n_comp_refc_rotate
  moreover have "n_comp (Suc (length (tl xs))) refc_rotate (hd xs # tl xs)
										= n_comp (length (tl xs)) refc_rotate ((tl xs) @ fst (refc (hd xs) (idset (\<Union> (set (hd xs # tl xs))))))"
  	sorry

  ultimately show ?case 
qed


lemma "\<forall>c \<in> set xs. finite c \<Longrightarrow> \<forall>c \<in> set (n_comp n refc_rotate xs). finite c"
	apply (induction n arbitrary: xs)
	 apply auto


lemma refc_rotate_sat:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c" "n \<le> length xs"
	shows "sat (n_comp n refc_rotate xs)"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have sat_n: "sat ((n_comp n refc_rotate) xs)"
  	apply (rule Suc.IH)
  	using Suc.prems by auto

  then obtain ys where ys: "n_comp n refc_rotate xs = (drop n xs) @ ys"
  	by (metis drop_all nle_le self_append_conv2 ys_drop)

  hence "sat (n_comp n refc_rotate xs) = sat ((drop n xs) @ ys)"
  	by simp

	let ?vars = "idset (\<Union>(set (drop n xs @ ys)))"
	consider (gt4) "card (hd (drop n xs)) \<ge> 4"
		| (le3) "card (hd (drop n xs)) \<le> 3"
		by arith
	thus "sat (n_comp (Suc n) refc_rotate xs)"
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
	
	(*
		sat (n_comp n refc_rotate xs)
			\<longleftrightarrow> sat ((drop n xs) @ ys)
			\<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))
			\<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))
			\<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))
			\<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))
			\<longleftrightarrow> sat (n_comp (Suc n) refc_rotate xs)
	*)
	
		have sat_ys: "sat (n_comp n refc_rotate xs) \<longleftrightarrow> sat ((drop n xs) @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using sat_rotate_append by fastforce
		also have step4: "... \<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> sat (n_comp (Suc n) refc_rotate xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "sat (n_comp (Suc n) refc_rotate xs)"
			using sat_n sat_ys by blast
	next
		case le3
		have sat_cp: "sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			apply (rule checkpoint_le3)
			using Suc.prems sat_n ys apply (metis Cons_eq_appendI drop_eq_Nil2 list.exhaust_sel not_less_eq_eq)
			using le3 apply simp
			done
	
	(*
		sat (n_comp n refc_rotate xs)
			\<longleftrightarrow> sat ((drop n xs) @ ys)
			\<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))
			\<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))
			\<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))
			\<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))
			\<longleftrightarrow> sat (n_comp (Suc n) refc_rotate xs)
	*)
	
		have sat_ys: "sat (n_comp n refc_rotate xs) \<longleftrightarrow> sat ((drop n xs) @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> sat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> sat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> sat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using sat_rotate_append by fastforce
		also have step4: "... \<longleftrightarrow> sat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> sat (n_comp (Suc n) refc_rotate xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "sat (n_comp (Suc n) refc_rotate xs)"
			using sat_n sat_ys by blast
	qed
qed

find_theorems "length (drop ?n ?xs)"

lemma refc_rotate_card_3:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c" "n \<le> length xs"
	shows "\<forall>c \<in> set (drop (length xs - n) (n_comp n refc_rotate xs)). card c \<le> 3"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have "\<exists>ys. n_comp n refc_rotate xs = (drop n xs) @ ys"
  	using ys_drop Suc.prems(3) Suc_leD by blast

  then obtain ys where ys: "n_comp n refc_rotate xs = (drop n xs) @ ys"
  	by blast

  have expand_suc: "n_comp (Suc n) refc_rotate xs = (drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) (idset (\<Union>(set (drop n xs @ ys)))))"
  	apply (rule ys_drop_suc)
  	using Suc.prems ys by arith+

  thus ?case
  proof (intro ballI)
  	fix c
  	assume c: "c \<in> set (drop (length xs - (Suc n)) (n_comp (Suc n) refc_rotate xs))"

		hence ys_alt: "ys = (drop (length xs - n) (n_comp n refc_rotate xs))"
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
			have "\<forall>c \<in> set (drop (length xs - n) (n_comp n refc_rotate xs)). card c \<le> 3"
				apply (rule Suc.IH)
				using Suc.prems by simp+

			moreover have "c \<in> set (drop (length xs - n) (n_comp n refc_rotate xs))"
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
						apply (metis Suc.prems(2) Suc.prems(3) Suc_leD finite_expr_idset refc_rotate_finite ys)
					using gt4 apply simp
					using idset_iff apply (smt (verit) Suc.prems(3) UnionI append_is_Nil_conv drop_eq_Nil hd_append2 list.set_sel(1) not_less_eq_eq subset_iff)
					done
		
				have aux2: "last ?s \<notin> set (tl (rev ?s)) \<union> hd (drop n xs)"
					apply (rule refc_init_uniq)
					unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
						apply (metis Suc.prems(2) Suc.prems(3) Suc_leD finite_expr_idset refc_rotate_finite ys)
					using gt4 apply simp
					using idset_iff apply (smt (verit) Suc.prems(3) UnionI append_is_Nil_conv drop_eq_Nil hd_append2 list.set_sel(1) not_less_eq_eq subset_iff)
					done
		
				thm stock_length
				have stock_len: "length (stock (card (hd (drop n xs)) - 3) ?vars) = 2 * (card (hd (drop n xs)) - 3)"
					by (rule stock_length) (metis Suc.prems(2) Suc.prems(3) Suc_leD finite_expr_idset refc_rotate_finite ys)

				thm splc_card_3
				have "card c = 3"
					apply (rule splc_card_3[where ?c' = c and ?vars = ?vars and ?c = "hd (drop n xs)"
									and ?s = ?s and ?s' = "tl (rev ?s)" and ?init = "last ?s"])
									apply (meson Suc.prems(2) Suc.prems(3) drop_eq_Nil hd_in_set in_set_dropD not_less_eq_eq)
								 apply simp
								apply simp
					using stock_len apply simp
							apply (metis fst_conv list.sel(2) rear refc_def rev.simps(1) splc.simps(1) stock_le3)
					using gt4 apply simp
						apply (metis Suc.prems(2) Suc.prems(3) Suc_leD finite_expr_idset refc_rotate_finite ys)
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
	shows "sat (n_comp (length xs) refc_rotate xs)"
	using assms refc_rotate_sat by blast

find_theorems drop 0
lemma transform_le3:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c"
	shows "\<forall>c \<in> set (n_comp (length xs) refc_rotate xs). card c \<le> 3"
	using assms refc_rotate_card_3 drop_0 by force

lemma sat_to_le3sat:
	assumes "sat xs" "\<forall>c \<in> set xs. finite c"
	shows "le3sat (n_comp (length xs) refc_rotate xs)"
	using assms transform_sat transform_le3 unfolding le3sat_def by blast




lemma
	assumes "sat xs"
	shows "sat (map_rotate_carry (length xs) refc xs (idset (\<Union>(set xs))))"
	using assms unfolding refc_def
	apply (induction "length xs" "refc :: 'a lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit set list \<times> 'a set" xs "idset (\<Union>(set xs))" rule: map_rotate_carry.induct)
		 apply (auto simp add: Let_def split: if_splits)
	oops

term rotate

lemma
	assumes "sat xs" "\<forall>c \<in> set xs. finite c \<and> card c \<ge> 4"
	shows "sat (fst (fold (\<lambda>c (ret, vars). (ret @ fst (refc c vars), snd (refc c vars) \<union> vars)) xs ([], idset (\<Union>(set xs)))))"
	using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)

  hence "sat (a # (fst (fold (\<lambda>c (ret, vars). (ret @ fst (refc c vars), snd (refc c vars) \<union> vars)) xs ([], idset (\<Union>(set xs))))))"
  	

  then show ?case sorry
qed
	
	oops


proof (induction "length xs" arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  thm Suc.hyps
  have "sat (fst (fold (\<lambda>c (ret, vars). (ret @ fst (refc c vars), snd (refc c vars) \<union> vars)) (tl xs) ([], idset (\<Union> (set (tl xs))))))"
  	apply (rule Suc.hyps(1))
  	using Suc.hyps apply simp
  	using Suc.prems(1) sat_tl apply blast
  	using Suc.prems(2) apply (metis list.set_sel(2) tl_Nil)
  	done

  let ?rest = "fst (fold (\<lambda>c (ret, vars). (ret @ fst (refc c vars), snd (refc c vars) \<union> vars)) (tl xs) ([], idset (\<Union>(set (tl xs)))))"
  let ?vars = "snd (fold (\<lambda>c (ret, vars). (ret @ fst (refc c vars), snd (refc c vars) \<union> vars)) xs ([], idset (\<Union>(set xs))))"


  have "fst (fold (\<lambda>c (ret, vars). (ret @ fst (refc c vars), snd (refc c vars) \<union> vars)) xs ([], idset (\<Union>(set xs))))
						= fst (refc (hd xs) (snd (refc (hd xs) ?vars) \<union> ?vars)) @ ?rest"

  	oops

  have "sat xs"
  	using Suc.prems by simp
  hence "sat (butlast xs @ (last xs # []))"
  	by (metis Suc.hyps(2) append_butlast_last_id list.size(3) old.nat.distinct(1))
  hence tmp: "sat (last xs # butlast xs)"
  	sorry

  have "sat (fst (refc (last xs) ?vars) @ butlast xs)"
  	apply (rule checkpoint)
  	using tmp apply simp
  		 defer
  		 apply (metis Suc.hyps(2) Suc.prems(2) last_in_set list.size(3) old.nat.distinct(1))
  	using Suc.prems(2)

  	oops



  then show ?case sorry
qed


proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons c xs)

  thm Cons.IH
  have rest: "sat (fst (fold (\<lambda>c (ret, vars). (fst (refc c vars) @ ret, snd (refc c vars) \<union> vars)) xs ([], idset (\<Union>(set xs)))))"
  	apply (rule Cons.IH)
  	using Cons.prems sat_tl apply fastforce
  	using Cons.prems apply simp
  	done

  let ?rest = "fst (fold (\<lambda>c (ret, vars). (fst (refc c vars) @ ret, snd (refc c vars) \<union> vars)) xs ([], idset (\<Union>(set xs))))"
  let ?vars = "snd (fold (\<lambda>c (ret, vars). (fst (refc c vars) @ ret, snd (refc c vars) \<union> vars)) xs ([], idset (\<Union>(set xs))))"
  
  have "sat (fst (refc c ?vars) @ ?rest)"
  	apply (rule checkpoint)

  then show ?case 
qed






(*
		fix c'
		assume c': "c' \<in> set (c # xs)"

		then consider (safe) "c' \<in> set xs"
			| (split) "c' = c"
			by fastforce
		hence "\<exists>l \<in> c'. (vmap_orig\<up>) l"
*)

		fix c'
		assume c': "c' \<in> set (fst (refc c vars) @ xs)"

		then consider (safe) "c' \<in> set xs"
			| (split) "c' \<in> set (fst (refc c vars))"
			by fastforce
		thus "\<exists>l\<in>c'. (vmap_new\<up>) l"



		obtain vmap_new where "vmap_new = vmap_orig"
			by simp

		then consider (safe) "c' \<in> set xs"
			| (split) "c' \<in> set (fst (refc c vars))"
			by fastforce
	thus "\<exists>l\<in>c'. (vmap\<up>) l"
	proof 


	


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

lemma split_clause_card:
	assumes "finite c" "c' \<in> set (fst (split_clause c vars carry))" "length carry \<le> 2"
	shows "card c' \<le> 3"
	using assms
proof (induction "card c" arbitrary: c vars carry)
  case 0
  thus ?case by simp
next
  case (Suc n)
  thm Suc.hyps
  thm Suc.prems
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis
  		using Suc.prems by auto
  next
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  		using Suc.prems(2) split_cls_4 by blast+
  next
  	case gt4

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

  	have "c' \<in> set (fst (split_clause ?rest vars carry)) \<Longrightarrow> card c' \<le> 3"
  		apply (rule Suc.hyps(1)[of ?rest])
  		using suc_card Suc.hyps(2) apply auto[1]
  		using Suc.prems(1) c apply (metis finite_insert)
  		apply auto[1]
  	  using Suc.prems(3) apply simp
  	  done

		let ?f = "fresh vars undefined"

  	have expand: "fst (split_clause c vars carry) = {hd carry, ?x, Pos ?f} # (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry)))"
  		apply auto
  		apply (auto simp add: Let_def)[1]
  		using c gt4 apply auto
  		by (meson fst_conv)+

  	consider (safe) "c' = {hd carry, ?x, Pos ?f}"
  		| (rest) "c' \<in> set (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry)))"
  		using Suc.prems expand by auto
  	thus ?thesis
  	proof cases
  		case safe
  		thus ?thesis
  			by (simp add: card_insert_le_m1)
  	next
  		case rest
  		thm Suc.prems
  		thm Suc.hyps

  		have "n = card ?rest"
  			using Suc.hyps suc_card by simp

  		thus ?thesis
  			apply (rule Suc.hyps(1))
  			using Suc.prems(1) c apply (metis finite_insert)
  			using rest apply simp
  			using Suc.prems(3) apply simp
  			done
  	qed
  qed
qed








lemma refine_clause_card:
	assumes "finite c" "c' \<in> set (fst (refine_clause c vars))"
	shows "card c' \<le> 3"
	using assms split_clause_card unfolding refine_clause_def
	by (metis le_Suc_eq length_0_conv length_Cons numeral_2_eq_2)

lemma fresh: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> fresh B x \<notin> A"
	using fresh_notIn by blast

lemma split_clause_card_3:
	assumes "finite c" "card c \<ge> 3" "c' \<in> set (fst (split_clause c vars carry))" "length carry = 2"
					"\<forall>l \<in> set carry. l \<notin> c" "idset c \<subseteq> vars" "finite vars" "idset (set carry) \<subseteq> vars"
	shows "card c' = 3"
	using assms
proof (induction "card c" arbitrary: c vars carry)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis
  		using Suc.prems by simp
  next
  	case eq4
  	hence neq1: "fst (pop c) \<noteq> fst (pop (snd (pop c)))"
  		using pop_card pop_ins pop_isin
  		by (metis card_gt_0_iff diff_Suc_1 insert_absorb n_not_Suc_n numeral_eq_Suc pred_numeral_simps(2) zero_less_Suc)

  	have one: "ident (fst (pop (snd (pop c)))) \<in> idset c"
  		unfolding idset_def using eq4 pop_card pop_ins
  		by (smt (verit) card_gt_0_iff insertCI mem_Collect_eq nat.inject numeral_eq_Suc pred_numeral_simps(2) zero_less_Suc)
  	have two: "hd (tl carry) \<in> set carry"
  		by (metis Suc.prems(4) length_Cons list.collapse list.set_sel(1) list.set_sel(2) list.size(3) n_not_Suc_n numeral_2_eq_2 old.nat.distinct(1))
  		
  	hence neq2: "fst (pop (snd (pop c))) \<noteq> hd (tl carry)"
  		using Suc.prems(5) one two
  		by (metis One_nat_def Suc.hyps(2) card.empty card_gt_0_iff eq4 insertCI numeral_One numeral_eq_iff pop_card pop_ins pop_isin semiring_norm(83) zero_less_Suc)

  	hence neq3: "fst (pop c) \<noteq> hd (tl carry)"
  		using idset_def Suc.hyps Suc.prems pop_isin two
  		by (smt card.empty mem_Collect_eq old.nat.distinct(1))

  	hence first: "card {fst (pop c), fst (pop (snd (pop c))), hd (tl carry)} = 3"
  		using neq1 neq2 neq3 by simp

		have card2: "card (snd (pop (snd (pop c)))) = 2"
			using eq4 pop_card
			by (metis card_gt_0_iff diff_Suc_1 numeral_2_eq_2 numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_less_Suc)
		have "hd carry \<notin> snd (pop (snd (pop c)))"
			apply auto using Suc.prems(5) pop_card pop_ins
			by (metis (mono_tags, lifting) Suc.hyps(2) Suc.prems(2) Suc.prems(4) Suc_n_not_le_n card.empty card_gt_0_iff finite_insert insertCI le_SucI list.set_sel(1) list.size(3) numeral_2_eq_2 numeral_3_eq_3 zero_less_Suc)

		hence second: "card (insert (hd carry) (snd (pop (snd (pop c))))) = 3"
			using card2
			by (metis card_Suc_eq eval_nat_numeral(3) zero_neq_numeral)

		thus ?thesis 
			using Suc.prems apply (auto simp add: Let_def)
			using eq4 first second by (smt fst_conv list.set(1) list.simps(15) set_ConsD singletonD)
  next
  	case gt4

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

  	let ?f = "fresh vars undefined"
  	let ?p = "pop c"

  	have split: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
			using gt4 by (metis (no_types, lifting) fst_conv le_imp_less_Suc numeral_eq_Suc order_less_imp_triv pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) split_clause.simps)
		consider (safe) "c' = {hd carry, fst ?p, Pos ?f}"
			| (rest) "c' \<in> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
			using split Suc.prems(3) by auto
		thus ?thesis
		proof cases
			case safe

			have carry: "hd carry \<in> set carry"
				by (metis Suc.prems(4) list.set_sel(1) list.size(3) numeral_2_eq_2 old.nat.distinct(1))
  		
  		hence neq1: "hd carry \<noteq> fst (pop c)"
				using idset_def Suc.hyps Suc.prems pop_isin
				by (smt card.empty mem_Collect_eq old.nat.distinct(1))

			have id: "ident (fst (pop c)) \<in> idset c"
				using idset_def Suc.prems Suc.hyps pop_isin
				by (metis (mono_tags, lifting) card_gt_0_iff mem_Collect_eq zero_less_Suc)

			have fresh: "fresh vars undefined \<notin> idset c"
				using fresh_notIn Suc.prems by blast

			hence neq2: "fst (pop c) \<noteq> Pos (fresh vars undefined)"
				using Suc.prems(6) id by auto

			hence neq3: "hd carry \<noteq> Pos (fresh vars undefined)"
				using idset_def Suc.prems fresh carry fresh_notIn
				by (smt ident.simps(1) mem_Collect_eq subset_iff)
				
			hence "card {hd carry, fst ?p, Pos ?f} = 3"
				using neq1 neq2 neq3 by simp

			thus ?thesis using safe by simp
		next
			case rest
			hence "n = card ?rest"
				using Suc.hyps suc_card by simp
			thus ?thesis
				apply (rule Suc.hyps(1))
				using Suc.prems(1) c apply (metis finite_insert)
				using gt4 suc_card apply arith
				using rest apply simp
				using Suc.prems(4) apply simp
				subgoal using Suc.prems(5) Suc.prems(6) apply auto[1]
					apply (metis (mono_tags, lifting) Suc.prems(7) c fresh ident.simps(2) idset_def insertCI mem_Collect_eq)
				 apply (smt (verit) c idset_def insertCI list.sel(2) list.set_sel(2) mem_Collect_eq)
				done
				using Suc.prems(6) c idset_def apply (smt (verit) insertCI mem_Collect_eq subset_iff)
				using Suc.prems(7) apply simp
				using Suc.prems(6) Suc.prems(8) apply auto 
				by (smt (verit, del_insts) ident.simps(2) idset_def insert_iff list.sel(2) list.set_sel(2) mem_Collect_eq subset_iff)
		qed
	qed
qed

lemma list_permute: "length l \<ge> 2 \<Longrightarrow> set l = set ((last (butlast l)) # (butlast (butlast l)) @ (last l # []))"
	apply auto apply (metis Un_iff append_butlast_last_id insert_iff list.set(2) set_append)
	by (metis Suc_n_not_le_n append.simps(1) append_butlast_last_id in_set_butlastD last_in_set le_SucI length_0_conv length_Cons numeral_2_eq_2)+

lemma vmap_set: "\<lbrakk> l1 \<noteq> l2; set l1 = set l2; vmap \<Turnstile> l1 \<rbrakk> \<Longrightarrow> vmap \<Turnstile> l2"
	using models_def by metis

lemma sat_permute: "length l \<ge> 2 \<Longrightarrow> sat l = sat ((last (butlast l)) # (butlast (butlast l)) @ (last l # []))"
	unfolding sat_def	using list_permute vmap_set by (metis (no_types, lifting))

lemma split_clause_lit:
	assumes "finite c" "lit \<in> c" "length carry \<le> 2"
	shows "lit \<in> \<Union> (set (fst (split_clause c vars carry)))"
	using assms
proof (induction "card c" arbitrary: c vars carry)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis
  		using Suc.prems by auto
  next
  	case eq4
  	then show ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  		by (metis emptyE finite_insert insertE pop_ins)
  next
  	case gt4

  	thm Suc.prems
  	thm Suc.hyps

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

		let ?f = "fresh vars undefined"

  	have expand: "fst (split_clause c vars carry) = {hd carry, ?x, Pos ?f} # (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry)))"
  		apply auto
  		apply (auto simp add: Let_def)[1]
  		using c gt4 apply auto
  		by (meson fst_conv)+

  	consider (safe) "lit \<in> {hd carry, ?x, Pos ?f}"
  		| (rest) "lit \<in> \<Union> (set (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry))))"
  		using Suc.prems Suc.hyps c pop_card
  		by (metis (no_types, lifting) One_nat_def finite_insert insertCI insertE length_Cons list.exhaust_sel list.sel(2) list.size(3) nat.inject one_le_numeral)

  	thus ?thesis
  	proof cases
  		case safe
  		thus ?thesis
  			using expand by auto
  	next
  		case rest
  		thus ?thesis using Suc.hyps Suc.prems expand
  			by (smt (z3) Union_iff le_Suc_eq list.distinct(1) list.sel(3) list.set_sel(2) not_less_eq_eq numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) split_clause.simps)
  	qed
  qed
qed

lemma refine_clause_lit:
	assumes "finite c" "lit \<in> c" "length carry \<le> 2"
	shows "lit \<in> \<Union> (set (fst (refine_clause c vars)))"
	using assms split_clause_lit unfolding refine_clause_def
	by (metis le_Suc_eq length_0_conv length_Cons numeral_2_eq_2)


lemma split_clause_carry:
	assumes "finite c" "l = fst (split_clause c vars carry)"


lemma split_clause_ex:
	assumes "finite c" "c' \<in> set (fst (split_clause c vars carry))" "length carry \<le> 2" "card c > 0"
	shows "\<exists>l \<in> c'. l \<in> c"
	using assms
proof (induction "card c" arbitrary: c vars carry)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	hence "c' = c"
  		using Suc.prems by simp
  	obtain l where "l \<in> c'" and "l \<in> c"
  		using le3 Suc.prems by fastforce
  	thus ?thesis by auto
  next
  	case eq4
  	thus ?thesis 
  		using Suc.prems apply (auto simp add: Let_def)
  		using Suc.prems(4) card_gt_0_iff pop_isin apply blast
  		using pop_card pop_ins
  		by (metis card_eq_0_iff diff_Suc_1 insertCI numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)
  next
  	case gt4

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

		let ?f = "fresh vars undefined"

  	have expand: "fst (split_clause c vars carry) = {hd carry, ?x, Pos ?f} # (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry)))"
  		apply auto
  		apply (auto simp add: Let_def)[1]
  		using c gt4 apply auto
  		by (meson fst_conv)+

  	consider (safe) "c' = {hd carry, ?x, Pos ?f}"
  		| (rest) "c' \<in> set (fst (split_clause ?rest (insert ?f vars) (Neg ?f # tl carry)))"
  		using Suc.prems Suc.hyps c expand	by (metis set_ConsD)
  	thus ?thesis
  	proof cases
  		case safe
  		thus ?thesis
  			apply (auto simp add: Let_def split: if_splits)
  			using c by blast
  	next
  		case rest
  		thus ?thesis using Suc.hyps Suc.prems expand c gt4 pop_def suc_card
  			by (smt (verit, best) Diff_iff Nitpick.size_list_simp(2) One_nat_def Suc_le_eq add_left_cancel finite_insert le_trans length_Cons less_Suc_eq_le list.sel(2) one_le_numeral plus_1_eq_Suc prod.sel(2))
  	qed
  qed
qed

lemma refine_clause_ex:
	assumes "finite c" "c' \<in> set (fst (refine_clause c vars))" "card c > 0"
	shows "\<exists>l \<in> c'. l \<in> c"
	using assms split_clause_ex unfolding refine_clause_def
	by (metis le_Suc_eq length_0_conv length_Cons numeral_2_eq_2)

lemma split_clause_carry_disj:
	assumes "finite c" "l = fst (split_clause c vars carry)" "idset c \<subseteq> vars"
					"carry = Neg g # Pos f # []" "Neg g \<notin> c" "Pos f \<notin> c"
	shows "\<forall>lit \<in> c. lit \<notin> set carry"
	using assms by auto

lemma split_clause_carry_disj_alt:
	assumes "finite c" "l = fst (split_clause c vars carry)" "idset c \<subseteq> vars"
					"carry = Neg g # Pos f # []" "Neg g \<notin> c" "Pos f \<notin> c"
	shows "\<forall>lit \<in> set carry. lit \<notin> c"
	using assms by auto


lemma split_clause_subset:
	assumes "l = fst (split_clause c vars carry)" "finite c" "finite vars" "card c \<ge> 4"
					"carry = Neg g # Pos f # []" "c' \<subseteq> set l"
	shows "\<Union>c' \<union> set carry \<subseteq> \<Union>(set l)"
	using assms
proof (induction "card c" arbitrary: c c' vars carry l g f)
  case 0
  then show ?case by simp
next
  case (Suc n)
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	thus ?thesis using Suc.prems by (auto simp add: Let_def)
  next
  	case gt4

		let ?p = "pop c"
		let ?f = "fresh vars undefined"
  	have expand: "l = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
  		using gt4 Suc.prems by (simp add: Let_def)

  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card_eq_0_iff less_nat_zero_code)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems c pop_card by auto

  	have asdf: "c' \<subseteq> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))
						\<Longrightarrow> \<Union>c' \<union> set (Neg ?f # tl carry) \<subseteq> \<Union>(set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"
			apply (rule Suc.hyps(1)[where ?c = ?rest and ?vars = "insert ?f vars" and ?g = ?f and ?f = f])
			using Suc.hyps(2) suc_card apply arith
					 apply simp
			using c gt4 Suc.prems apply (metis finite_insert)
			using c gt4 Suc.prems apply (metis finite_insert)
			using gt4 suc_card apply arith
			using Suc.prems(5) apply simp
			apply simp
  		done

  	consider (safe) "{hd carry, fst ?p, Pos ?f} \<notin> c'"
  		| (rest) "{hd carry, fst ?p, Pos ?f} \<in> c'"
  		by blast
  	thus ?thesis
  	proof cases
  		case safe
  		thus ?thesis using asdf Suc.prems
  			by (smt Sup_insert Sup_subset_mono Un_subset_iff expand insert_subset list.sel(1) list.sel(3) list.simps(15) subset_insert subset_refl subset_trans)
  	next
  		case rest

  		obtain rem where c': "c' = insert {hd carry, fst ?p, Pos ?f} rem" and rem: "rem \<subseteq> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
  			using rest Suc.prems expand
  			by (smt insert_subset list.simps(15) mk_disjoint_insert subset_insert)

  		have "\<Union>rem \<union> set (Neg ?f # tl carry) \<subseteq> \<Union>(set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"
  			using asdf Suc.prems Suc.hyps rem c gt4 suc_card
  			by (metis finite_insert less_Suc_eq_le list.sel(3) nat.inject)

  		hence "\<Union>c' \<union> set (Neg ?f # tl carry) \<subseteq> \<Union>(set l)"
  			using rem c' expand Suc.prems
  			by (smt Un_insert_right Union_Un_distrib list.simps(15) sup.absorb_iff1 sup_assoc sup_commute)

  		thus ?thesis
  			using rest Suc.prems(5) by auto
  	qed

  qed
qed

lemma
	assumes "l = fst (split_clause c vars carry)" "finite c" "finite vars" "card c \<ge> 4"
					"carry = Neg g # Pos f # []" "c' \<subseteq> set l" "\<Union>c' \<union> set carry \<union> compl = \<Union>(set l)" "v \<in> compl"
	shows "ident v \<notin> vars"
	using assms
proof (induction "card c" arbitrary: c vars carry c' l g f compl v)
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
		have expand: "l = {fst ?p, fst ?q, hd (tl carry)} # (insert (hd carry) (snd ?q)) # []"
			using eq4 Suc.prems by (simp add: Let_def)

		hence "compl = {}"


  	then show ?thesis
  next
  	case gt4
  	then show ?thesis sorry
  qed
qed

lemma
	assumes "finite c" "l \<in> {hd carry, fst (pop c), Pos (fresh vars undefined)}" "idset c \<union> idset (set carry) \<subseteq> vars" "finite vars"
					"cc = \<Union>(set (fst (split_clause (snd (pop c)) (insert (fresh vars undefined) vars) (Neg (fresh vars undefined) # tl carry))))" 
					"carry = Neg g # Pos f # []" "Neg g \<notin> c" "Pos f \<notin> c" "card c > 4"
	shows "l \<notin> cc"
	using assms
proof (induction "card c" arbitrary: c vars carry l cc g f)
  case 0
  thus ?case by simp
next
  case (Suc n)

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"
  	let ?f = "fresh vars undefined"

		have "hd carry = Neg g"
			using Suc.prems by simp
		moreover have "Neg g \<in> set carry"
			using Suc.prems by simp
		moreover have "g \<in> vars"
			using Suc.prems idset_def calculation 
			by (smt Un_subset_iff ident.simps(2) mem_Collect_eq subset_iff)
		ultimately have "Neg g \<noteq> Neg (fresh vars undefined)"
			using fresh_notIn Suc.prems by auto

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) Suc.prems(9)
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

		hence "n = card ?rest"
			using Suc.hyps suc_card by simp

		hence "Neg g \<notin> \<Union>(set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"
			apply (rule Suc.hyps(1)[where ?vars = "vars" and ?carry = "Neg g # Pos f # []"])
			using Suc.prems c apply (metis finite_insert)
						 apply simp
						defer
			using Suc.prems apply simp
			oops
	
  then show ?case sorry
qed

lemma
	assumes "lit \<in> \<Union>(set (fst (split_clause c vars carry)))" "finite c" "finite vars" "length carry = 2"
	shows "ident lit \<notin> vars \<or> lit \<in> set carry \<or> lit \<in> c"
	using assms
proof (induction c vars carry arbitrary: c vars carry lit rule: split_clause.induct)
  case (1 c vars carry)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using "1.prems" by simp
  next
  	case eq4
  	then show ?thesis using "1.prems" apply (auto simp add: Let_def)
  				apply (metis hd_in_set length_0_conv zero_neq_numeral)
  			 apply (metis card_eq_0_iff pop_isin zero_neq_numeral)
  		sorry
  next
  	case gt4

		let ?p = "pop c"
		let ?f = "fresh vars undefined"
  	have expand: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
  		using gt4 "1.prems" by (simp add: Let_def)

  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins "1.prems" gt4
  		by (metis card_eq_0_iff less_nat_zero_code)

  	have suc_card: "Suc (card ?rest) = card c"
  		using "1.prems" c pop_card by auto

  	consider (safe) "lit \<in> {hd carry, fst ?p, Pos ?f}"
  		| (rest) "lit \<in> \<Union>(set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"
  		using expand "1.prems" by fastforce
  	thus ?thesis
  	proof cases
  		case safe
  		then show ?thesis sorry
  	next
  		case rest
  		show ?thesis apply (rule "1.IH")
  			
  	qed

  qed
qed


proof (induction "card c" arbitrary: lit)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems
  next
  	case eq4
  	thus ?thesis
  		using Suc.prems apply (auto simp add: Let_def)
  		oops
  				apply (metis hd_in_set length_0_conv zero_neq_numeral)
  			 apply (metis card_eq_0_iff pop_isin zero_neq_numeral)
  			apply (metis One_nat_def Suc.hyps(2) card.empty insertCI numeral_eq_one_iff old.nat.distinct(1) pop_card pop_ins pop_isin semiring_norm(83))
  		 apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_n_not_n hd_in_set list.set_sel(2) zero_neq_numeral)
  		by (metis Diff_iff pop_def snd_conv)
  next
  	case gt4
		let ?p = "pop c"
		let ?f = "fresh vars undefined"
  	have expand: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
  		using gt4 Suc.prems by (simp add: Let_def)

  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card_eq_0_iff less_nat_zero_code)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems c pop_card by auto

  	consider (safe) "lit \<in> {hd carry, fst ?p, Pos ?f}"
  		| (rest) "lit \<in> \<Union>(set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"
  		using expand Suc.prems gt4 by fastforce
  	thus ?thesis
  	proof cases
  		case safe
  		then show ?thesis using Suc.prems c fresh_notIn
  			by (metis empty_iff ident.simps(1) insert_iff length_0_conv list.set_sel(1) numeral_2_eq_2 old.nat.distinct(1))
  	next
  		case rest
  		hence "n = card ?rest"
  			using Suc.hyps suc_card by simp
  		show ?thesis apply (rule Suc.hyps(1))
  	qed

  qed
qed

lemma split_clause_uniq:
	assumes "finite c" "c' \<in> set (fst (split_clause c vars carry))" "cc \<in> set (fst (split_clause c vars carry))" 
					"cc \<noteq> c'" "carry = Neg g # Pos f # []" "Neg g \<notin> c" "Pos f \<notin> c" "card c > 0" 
					"idset c \<union> idset (set carry) \<subseteq> vars" "l \<in> c'" "finite vars" 
	shows "l \<notin> cc"
	using assms
proof (induction "card c" arbitrary: c c' cc l vars carry g f)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis 
  		using le3 Suc.prems by auto
  next
  	case eq4

		let ?p = "pop c"
		let ?q = "pop (snd ?p)"

  	let ?one = "{fst ?p, fst ?q, hd (tl carry)}"
  	let ?two = "(insert (hd carry) (snd ?q))"

  	have expand: "fst (split_clause c vars carry) = ?one # ?two # []"
  		using eq4 Suc.prems by (simp add: Let_def)

  	have 11: "fst ?p \<notin> ?two"
			using Suc.prems pop_card pop_def pop_ins
  		by (metis DiffD1 card_gt_0_iff card_insert_if finite_insert insert_iff list.sel(1) n_not_Suc_n snd_conv)
  	have 12: "fst ?q \<notin> ?two"
			using Suc.prems eq4 pop_card pop_card_less pop_ins
			by (metis (no_types, lifting) One_nat_def card.empty finite_insert insert_absorb insert_iff list.sel(1) nat_less_le one_eq_numeral_iff semiring_norm(83))
		have 13: "hd (tl carry) \<notin> ?two"
			using Suc.prems pop_def
			by (metis DiffD1 insert_iff list.sel(1) list.sel(3) lit.simps(4) snd_conv)

		have card3: "card ?two = 3"
			apply (rule split_clause_card_3[where ?c = c and ?vars = vars and ?carry = carry])
			using eq4 expand Suc.prems split_clause_carry_disj_alt by auto
		obtain x y where q: "snd ?q = {x, y}"
			using expand card3 eq4 pop_card pop_ins
			by (metis (no_types, lifting) card_eq_0_iff diff_Suc_1 finite_insert numeral_3_eq_3 numeral_eq_Suc old.nat.distinct(1) pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))

		have 21: "x \<notin> ?one"
			using 11 12 13 q by auto
		have 22: "y \<notin> ?one"
			using 11 12 13 q by auto
		have 23: "hd carry \<notin> ?one"
			using 11 12 13 by auto

  	thus ?thesis
  		using 11 12 13 21 22 23 Suc.prems expand Diff_iff Diff_insert_absorb
  		by auto
  next
  	case gt4

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

  	let ?p = "pop c"
  	let ?f = "fresh vars undefined"

  	let ?one = "{hd carry, fst ?p, Pos ?f}"
  	let ?two = "fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))"

  	have expand: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
  		using gt4 Suc.prems by (simp add: Let_def)

  	hence setexpand: "set (fst (split_clause c vars carry)) = set (?one # ?two)"
  		by simp

  	consider (one_two) "c' = ?one \<and> cc \<in> set ?two"
  		| (two_one) "c' \<in> set ?two \<and> cc = ?one"
  		| (rest) "c' \<in> set ?two \<and> cc \<in> set ?two"
  		using Suc.prems(2) Suc.prems(3) Suc.prems(4) setexpand by force
  	thus ?thesis
  	proof cases
  		case one_two

  		have "hd carry = Neg g"
  			using Suc.prems by simp
  		moreover have "Neg g \<in> set carry"
  			using Suc.prems by simp
  		moreover have "g \<in> vars"
  			using Suc.prems idset_def calculation 
  			by (smt Un_subset_iff ident.simps(2) mem_Collect_eq subset_iff)
  		ultimately have "Neg g \<noteq> Neg (fresh vars undefined)"
  			using fresh_notIn Suc.prems by auto

			hence "n = card ?rest"
				using Suc.hyps suc_card by simp

  		hence "Neg g \<notin> \<Union>(set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"

  		then show ?thesis sorry
  	next
  		case two_one
  		then show ?thesis sorry
  	next
  		case rest

  		have "fresh vars undefined \<notin> idset c"
  			using Suc.prems fresh_notIn idset_def by blast
  		hence "Neg (fresh vars undefined) \<notin> c"
  			by (simp add: idset_def)
  		hence neg: "Neg (fresh vars undefined) \<notin> snd (pop c)"
  			using pop_ins c by auto

  		have "snd (pop c) \<subseteq> c"
  			using pop_ins c by auto
  		hence "idset (snd (pop c)) \<subseteq> idset c"
  			using idset_def c by (smt mem_Collect_eq subset_iff)
  		hence subs: "idset (snd (pop c)) \<subseteq> vars"
  			using Suc.prems by auto

  		have tl: "set (tl carry) \<subseteq> set carry"
  			using Suc.prems by simp

  		hence "idset (set (Neg (fresh vars undefined) # [])) = insert (fresh vars undefined) {}"
  			unfolding idset_def by simp
  		hence id: "idset (set (Neg (fresh vars undefined) # [])) \<subseteq> insert (fresh vars undefined) vars"
  			using idset_def by simp
  			

  		hence "n = card ?rest"
  			using Suc.hyps suc_card by simp

			thus ?thesis
				apply (rule Suc.hyps(1)[where ?c' = c' and ?vars = "insert ?f vars" and ?carry = "Neg ?f # tl carry"
							and ?g = "fresh vars undefined" and ?f = f])
				using Suc.prems(1) c apply (metis finite_insert)
				using rest apply simp
				using rest apply simp
				using Suc.prems(4) apply simp
				using Suc.prems(5) apply simp
				using neg apply simp
				using Suc.prems(7) c pop_ins apply blast
				using gt4 suc_card apply arith
				using Suc.prems(9) tl id idset_def subs
					apply (smt Un_subset_iff insert_iff list.simps(15) mem_Collect_eq subset_iff)
				using Suc.prems(10) apply simp
				using Suc.prems(11) apply (metis finite_insert)
				done
  	qed
  qed
qed

lemma split_clause_distinct:
	assumes "l = fst (split_clause c vars carry)" "c1 = l ! i" "c2 = l ! j" "i \<noteq> j"
					"i < length l - 1" "j < length l - 1" "idset c \<union> idset (set carry) \<subseteq> vars"
					"carry = Neg g # Pos f # []" "finite c"
	shows "c1 \<noteq> c2"
	using assms
proof (induction "card c" arbitrary: c i j vars carry c1 c2)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4

		let ?p = "pop c"
		let ?q = "pop (snd ?p)"
				
  	have "l = {fst ?p, fst ?q, hd (tl carry)} # (insert (hd carry) (snd ?q)) # []"
  		using Suc.prems eq4 by (simp add: Let_def)

  	hence "c1 = {fst ?p, fst ?q, hd (tl carry)}" and "c2 = (insert (hd carry) (snd ?q))"
  		using Suc.prems by simp+

  	thus ?thesis using pop_card pop_ins
  		by (smt Suc_eq_numeral card_eq_0_iff card_insert_if eq4 insertE insert_absorb insert_absorb2 insert_commute n_not_Suc_n old.nat.distinct(1) pred_numeral_simps(2))
  next
  	case gt4

		let ?p = "pop c"
		let ?f = "fresh vars undefined"

		have expand: "l = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
			using Suc.prems gt4 by (simp add: Let_def)

		consider (hd) "c1 = {hd carry, fst ?p, Pos ?f}"
			| (tl) "c1 \<in> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
			using expand gt4 Suc.prems
			by (metis (no_types, lifting) length_Cons length_tl less_Suc_eq_le less_or_eq_imp_le list.sel(3) nth_mem set_ConsD)
		thus ?thesis
		proof cases
			case hd
(*
			hence "c2 \<in> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
				using expand gt4 Suc.prems
				by (metis insertE length_tl less_imp_diff_less less_zeroE list.sel(3) list.simps(15) nat_neq_iff nth_Cons_pos nth_mem)

			have "fst ?p \<notin> snd ?p"
				by (metis Diff_iff fst_conv insertI1 pop_def snd_conv)

			have "\<forall>c' \<in> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))). \<exists>lit \<in> c'. lit \<in> snd ?p"
				using split_clause_ex Suc.prems gt4 pop_card
				by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_n_not_le_n card_gt_0_iff dual_order.strict_trans2 length_Cons list.sel(3) list.size(3) not_less_eq_eq numeral_2_eq_2 one_le_numeral)
*)
		next
			case tl
			then show ?thesis sorry
		qed


		obtain c' where "c' \<in> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))) \<Longrightarrow> fst ?p \<notin> c'"
			by blast


		have "fst ?p \<notin> set carry"
			

		have "fst ?p \<notin> set (Neg ?f # tl carry)"

		hence "\<forall>c' \<in> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))). fst ?p \<notin> c'"
			

		hence "{hd carry, fst ?p, Pos ?f} \<notin> set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"

  	then show ?thesis sorry
  qed
qed




lemma split_clause_len:
	assumes "finite c" "l = fst (split_clause c vars carry)" "card c \<ge> 4"
	shows "length l = card c - 2"
	using assms
proof (induction "card c" arbitrary: c vars carry l)
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
  	let ?f = "fresh vars undefined"

  	have expand: "l = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
  		using gt4 Suc.prems by (simp add: Let_def)
  	hence "length l = Suc (length (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"
  		by simp
  	also have "... = Suc (card (snd ?p) - 2)"
  		using Suc.hyps Suc.prems gt4 pop_card
  		by (metis card.infinite card_0_eq le_SucE nat.inject nat_neq_iff not_numeral_le_zero)
  	finally show ?thesis using Suc.prems pop_card
  		by (metis (no_types, lifting) Suc_diff_le card.empty less_or_eq_imp_le not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) verit_comp_simplify1(3))
  qed
qed

lemma refine_clause_len:
	assumes "finite c" "l = fst (refine_clause c vars)" "card c \<ge> 4"
	shows "length l = card c - 2"
	using assms unfolding refine_clause_def by (simp add: split_clause_len Let_def)

thm split_clause_card_3
lemma
	assumes "finite c" "card c \<ge> 4" "c' \<in> set (fst (split_clause c vars carry))" "length carry = 2"
					"\<forall>l\<in>set carry. l \<notin> c" "idset c \<subseteq> vars" "finite vars" "idset (set carry) \<subseteq> vars" "card c' = 3"
	shows "card (\<Union>(set (fst (split_clause c vars carry)))) = 3 * (card c - 2)"
	using assms
proof (induction "card c" arbitrary: c c' vars carry)
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
  	then show ?thesis using Suc.prems apply (auto simp add: Let_def)
  		using split_clause_card_3 
  next
  	case gt4
  	then show ?thesis sorry
  qed
qed


lemma split_clause_len_card:
	assumes "l = fst (split_clause c vars carry)" "finite c" "finite vars" "carry = Neg g # Pos f # []"
					"Neg g \<notin> c" "Pos f \<notin> c" "idset c \<union> idset (set carry) \<subseteq> vars"
	shows "length l = card (set l)"
	using assms
proof (induction "card c" arbitrary: c vars carry l f g)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4
		let ?p = "pop c"
		let ?q = "pop (snd ?p)"
  	have expand: "l = {fst ?p, fst ?q, hd (tl carry)} # (insert (hd carry) (snd ?q)) # []"
  		using eq4 Suc.prems by (simp add: Let_def)
  	hence "set l = {{fst ?p, fst ?q, hd (tl carry)}, (insert (hd carry) (snd ?q))}"
  		by simp
  	hence r: "hd (tl carry) \<noteq> hd carry \<Longrightarrow> card (set l) = 2"
  		using Suc.hyps Suc.prems eq4 pop_card_less pop_ins
  		by (smt (verit, ccfv_SIG) One_nat_def card.empty card_insert_disjoint finite.emptyI finite_insert insertCI insertE insert_absorb nat_less_le numeral_2_eq_2 one_eq_numeral_iff semiring_norm(83) singletonD zero_less_Suc)

  	hence pos: "hd (tl carry) = Pos f"
  		using Suc.prems by simp
  	hence neg: "hd carry = Neg g"
  		using Suc.prems by simp

  	have "length l = 2"
  		using expand by simp
  	moreover have "Pos f \<noteq> Neg g"
  		by simp
  	moreover have "hd (tl carry) \<noteq> hd carry"
  		using pos neg by simp
  	ultimately show ?thesis 
  		using r by simp
  next
  	case gt4
		let ?p = "pop c"
		let ?f = "fresh vars undefined"
		have expand: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?f} # (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry)))"
			using gt4 Suc.prems by (simp add: Let_def)

		have "fst ?p \<notin> snd ?p"
			using pop_def
			by (metis Diff_iff fst_conv insertI1 snd_conv)
		moreover have "fst ?p \<notin> set (Neg ?f # tl carry)"
			using Suc.prems Suc.hyps(2) idset_def pop_isin fresh
			by (smt Un_subset_iff card_gt_0_iff empty_set ident.simps(2) list.sel(3) list.simps(15) mem_Collect_eq set_ConsD singletonD zero_less_Suc)
		ultimately have "fst ?p \<notin> snd ?p \<union> set (Neg ?f # tl carry)"
			by simp

		hence "fst ?p \<notin> \<Union>(set (fst (split_clause (snd ?p) (insert ?f vars) (Neg ?f # tl carry))))"
			using split_clause_subset

  	then show ?thesis
  		using Suc.prems oops by (auto simp add: Let_def)
  qed
qed

lemma refine_clause_len_card:
	assumes "l = fst (refine_clause c vars)" "finite c" "idset (\<Union>(set l)) \<subseteq> vars" "finite vars"
	shows "length l = card (set l)"
	using assms unfolding refine_clause_def
proof (induction "card c" arbitrary: c vars l)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4
  	hence expand: "l = fst (split_clause c (insert (fresh vars undefined) vars) [Neg (fresh vars undefined), Pos (fresh vars undefined)])"
  		using eq4 Suc.prems by (simp add: Let_def)

  	have "fresh vars undefined \<notin> idset (\<Union>(set l))"
  		apply (rule fresh)
  		using Suc.prems by auto

  	hence neg: "Neg (fresh vars undefined) \<notin> \<Union> (set l)" and pos: "Pos (fresh vars undefined) \<notin> \<Union> (set l)"
  		unfolding idset_def by simp+

  	show ?thesis 
  		apply (rule split_clause_len_card[where ?c = c and ?vars = "insert (fresh vars undefined) vars"
  					and ?g = "fresh vars undefined" and ?f = "fresh vars undefined"
  					and ?carry = "Neg (fresh vars undefined) # Pos (fresh vars undefined) # []"
  					])
  		using expand Suc.prems neg pos by auto
  next
  	case gt4
  	hence expand: "l = fst (split_clause c (insert (fresh vars undefined) vars) [Neg (fresh vars undefined), Pos (fresh vars undefined)])"
  		using gt4 Suc.prems by (simp add: Let_def)

  	have "fresh vars undefined \<notin> idset (\<Union>(set l))"
  		apply (rule fresh)
  		using Suc.prems by auto

  	hence neg: "Neg (fresh vars undefined) \<notin> \<Union> (set l)" and pos: "Pos (fresh vars undefined) \<notin> \<Union> (set l)"
  		unfolding idset_def by simp+

  	show ?thesis 
  		apply (rule split_clause_len_card[where ?c = c and ?vars = "insert (fresh vars undefined) vars"
  					and ?g = "fresh vars undefined" and ?f = "fresh vars undefined"
  					and ?carry = "Neg (fresh vars undefined) # Pos (fresh vars undefined) # []"
  					])
  		using expand Suc.prems neg pos by auto
  qed
qed

lemma split_clause_distinct:
	assumes "l = fst (split_clause c vars carry)" "finite c" "carry = Neg g # Pos f # []"
					"Neg g \<notin> \<Union>(set l)" "Pos f \<notin> \<Union>(set l)" "i \<noteq> j" "i < length l - 1" "j < length l - 1"
	shows "l ! i \<noteq> l ! j"
	using assms
proof (induction "card c" arbitrary: c vars carry l g f i j)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4
  	thus ?thesis using Suc.prems by (auto simp add: Let_def)
  next
  	case gt4
  	thus ?thesis using Suc.prems by (auto simp add: Let_def)
  qed
qed

lemma refine_clause_distinct:
	assumes "l = fst (refine_clause c vars)" "finite c" "i \<noteq> j" "i < length l - 1" "j < length l - 1"
					"finite vars" "idset (\<Union> (set l)) \<subseteq> vars"
	shows "l ! i \<noteq> l ! j"
	using assms unfolding refine_clause_def
proof (induction "card c" arbitrary: c vars l)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4

  	have "fresh vars undefined \<notin> idset (\<Union>(set l))"
  		apply (rule fresh)
  		using Suc.prems by auto

  	hence neg: "Neg (fresh vars undefined) \<notin> \<Union> (set l)" and pos: "Pos (fresh vars undefined) \<notin> \<Union> (set l)"
  		unfolding idset_def by simp+

  	hence expand: "l = fst (split_clause c (insert (fresh vars undefined) vars) [Neg (fresh vars undefined), Pos (fresh vars undefined)])"
  		using eq4 Suc.prems by (simp add: Let_def)

  	thus ?thesis
  		apply (rule split_clause_distinct[where ?g = "fresh vars undefined" and ?f = "fresh vars undefined"])
  		using Suc.prems expand neg pos by auto
  next
  	case gt4

  	have "fresh vars undefined \<notin> idset (\<Union>(set l))"
  		apply (rule fresh)
  		using Suc.prems by auto

  	hence neg: "Neg (fresh vars undefined) \<notin> \<Union> (set l)" and pos: "Pos (fresh vars undefined) \<notin> \<Union> (set l)"
  		unfolding idset_def by simp+

  	hence expand: "l = fst (split_clause c (insert (fresh vars undefined) vars) [Neg (fresh vars undefined), Pos (fresh vars undefined)])"
  		using gt4 Suc.prems by (simp add: Let_def)

  	thus ?thesis
  		apply (rule split_clause_distinct[where ?g = "fresh vars undefined" and ?f = "fresh vars undefined"])
  		using Suc.prems expand neg pos by auto
  qed
qed


lemma split_clause_struct:
	assumes "finite c" "l = fst (split_clause c vars (Neg g # Pos f # []))"
					"c' \<in> set (butlast (butlast l))"	"finite vars" "card c \<ge> 5"
					"Neg g \<notin> \<Union>(set l)" "Pos f \<notin> \<Union>(set l)"
	shows "(\<exists>i j. Pos i \<in> c' \<and> i \<noteq> j \<and> Neg j \<in> c')"
	using assms
proof (induction "card c" arbitrary: c c' l vars g f)
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
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) eq5
  		by (metis card.empty le_numeral_extra(3) not_numeral_le_zero)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

  	let ?p = "pop c"

  	obtain carry where carry2: "carry = Neg g # Pos f # []"
  		using refine_clause_def by (smt split_clause.simps)

		let ?gg = "fresh vars undefined"

  	have clause: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?gg} # (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
  		using eq5 carry2 by (simp add: Let_def)

  	have len1: "length (fst (split_clause c vars carry)) = 3"
  		using eq5 Suc.prems split_clause_len[where ?c = c and ?l = l and ?vars = vars and ?carry = carry]
  		by (metis Suc_1 carry2 diff_Suc_1 diff_Suc_Suc eval_nat_numeral(2) eval_nat_numeral(3) lessI nat_less_le semiring_norm(26) semiring_norm(27))

  	have len2: "length (fst (split_clause c vars carry)) = card (set (fst (split_clause c vars carry)))"
  		apply (rule split_clause_len_card[where ?c = c and ?vars = vars and ?carry = carry and ?g = g and ?f = f])
  		using Suc.prems carry2 by simp+

  	hence "card (set (fst (split_clause c vars carry))) = 3"
  		using len1 len2 by simp

  	show ?thesis apply (rule Suc.hyps(1)[where ?c = c and ?l = l and ?vars = vars and ?g = g and ?f = f])
  		using Suc.prems(2) Suc.prems(6) carry2 clause by auto
  next
  	case gt5

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt5
  		by (metis card.empty not_less_zero)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

  	(*let ?g = "fresh vars undefined"*)
  	let ?p = "pop c"

  	obtain carry where carry2: "carry = Neg g # Pos f # []"
  		using refine_clause_def by (smt split_clause.simps)

(*  	
		let ?v = "insert f vars"
		let ?gg = "fresh ?v undefined"
*)
		let ?gg = "fresh vars undefined"

  	have clause: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?gg} # (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
  		using gt5 carry2 by (simp add: Let_def)

  	hence "tl l = tl (fst (split_clause c vars carry))"
  		using Suc.prems(2) carry2 by simp
  	also have "... = (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
  		using clause by simp
  	hence tl: "tl l = (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
  		using calculation by simp
  	hence hd: "hd l = {hd carry, fst ?p, Pos ?gg}"
  		using clause Suc.prems(2) carry2 by simp

		hence c': "c' \<in> set l"
			using Suc.prems	by (meson in_set_butlastD)

		hence cases: "c' = hd l \<or> c' \<in> set (tl l)"
			by (metis Nil_tl c' list.collapse set_ConsD)

		value "(butlast (butlast ([0::nat, 1, 2, 3])))"

		consider (safe) "c' = {hd carry, fst ?p, Pos ?gg}"
			| (rest) "c' \<in> set (tl (butlast (butlast l)))"
			| (edge) "c = last l \<or> c = last (butlast l)"
			using Suc.prems tl carry2 clause
			by (metis (no_types, lifting) butlast.simps(2) butlast_tl cases empty_iff empty_set hd set_ConsD)
			(* by (smt butlast.simps(1) butlast.simps(2) set_ConsD) *)
  	thus ?thesis
  	proof cases
  		case safe
  		obtain j where j: "hd carry = Neg j"
  			using carry2 by simp
  		hence j': "Neg j = Neg g"
  			by (simp add: carry2)
  		hence cond1: "Neg j \<in> c'"
  			using safe j by simp
  		obtain i where i: "Pos ?gg = Pos i"
  			using carry2 by simp
  		hence i': "Pos i = Pos (fresh vars undefined)"
  			by simp
  		hence cond2: "Pos i \<in> c'"
  			using safe by simp
  		hence cond3: "i \<noteq> j"
  			using i' j' fresh_notIn Suc.prems(4) Suc.prems(6) c' cond1 by blast
  		thus ?thesis
  			using cond1 cond2 cond3 by blast
  	next
  		case rest

  		have len: "length l \<ge> 3"
  			using Suc.prems by (auto simp add: Let_def)

			hence len_perm: "length l = length (last (butlast l) # butlast (butlast l) @ [last l])"
				using Suc.prems by auto

			hence "n = card ?rest"
				using Suc.hyps suc_card by simp

			thus ?thesis
				apply (rule Suc.hyps(1)[where ?l = "tl l" and ?vars = "insert (fresh vars undefined) vars"
							and ?g = "fresh vars undefined" and ?f = f])
				using Suc.prems(1) c apply (metis finite_insert)
				using tl apply simp
				using rest butlast_tl apply metis
				using Suc.prems(4) apply simp
				using gt5 suc_card apply arith
				using Suc.prems(2) Suc.prems(6) carry2 clause apply simp
				using Suc.prems(2) Suc.prems(7) carry2 clause apply simp
				done
		next
			case edge

  		have len: "length l \<ge> 3"
  			using Suc.prems by (auto simp add: Let_def)

			thus ?thesis using edge Suc.prems list_permute split_clause_card
				by (metis Suc_leD butlast.simps(1) butlast.simps(2) last_in_set length_Cons length_greater_0_conv length_pos_if_in_set less_or_eq_imp_le list.set_intros(1) list.size(3) numeral_2_eq_2 numeral_3_eq_3 prod.sel(1) split_clause.simps)
		qed
	qed
qed


lemma refine_clause_struct:
	assumes "finite c" "l = fst (refine_clause c vars)" "idset c \<subseteq> vars"
					"c' \<in> set (butlast (butlast l))"	"finite vars" "card c \<ge> 5"
	shows "(\<exists>i j. Pos i \<in> c' \<and> i \<noteq> j \<and> Neg j \<in> c')"
	using assms unfolding refine_clause_def
proof (induction "card c" arbitrary: c c' vars l)
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

  	hence expand: "l = fst (split_clause c (insert (fresh vars undefined) vars) [Neg (fresh vars undefined), Pos (fresh vars undefined)])"
  		using Suc.prems by (simp add: Let_def)

  	have "fresh vars undefined \<notin> idset (\<Union>(set l))"
  		apply (rule fresh)
  		using Suc.prems by auto

  	hence neg: "Neg (fresh vars undefined) \<notin> \<Union> (set l)" and pos: "Pos (fresh vars undefined) \<notin> \<Union> (set l)"
  		unfolding idset_def by simp+

  	show ?thesis
  		apply (rule split_clause_struct[where ?c = c and ?l = l and ?vars = "insert (fresh vars undefined) vars"
  					and ?g = "fresh vars undefined" and ?f = "fresh vars undefined"])
  		using Suc.prems expand neg pos by blast+
  next
  	case gt5

  	hence expand: "l = fst (split_clause c (insert (fresh vars undefined) vars) [Neg (fresh vars undefined), Pos (fresh vars undefined)])"
  		using Suc.prems by (simp add: Let_def)

  	have "fresh vars undefined \<notin> idset (\<Union>(set l))"
  		apply (rule fresh)
  		using Suc.prems by auto

  	hence neg: "Neg (fresh vars undefined) \<notin> \<Union> (set l)" and pos: "Pos (fresh vars undefined) \<notin> \<Union> (set l)"
  		unfolding idset_def by simp+

  	show ?thesis
  		apply (rule split_clause_struct[where ?c = c and ?l = l and ?vars = "insert (fresh vars undefined) vars"
  					and ?g = "fresh vars undefined" and ?f = "fresh vars undefined"])
  		using Suc.prems expand neg pos by blast+
  qed
qed


lemma split_clause_neighbour:
	assumes "finite c" "l = fst (split_clause c vars (Neg g # Pos f # []))"
					"i < length l - 2" "Neg g \<notin> \<Union>(set l)" "Pos f \<notin> \<Union>(set l)"
	shows "\<exists>id \<in> l ! i. id \<in> l ! Suc i"
	using assms
proof (induction "length l" arbitrary: c vars g f l i)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	thus ?thesis using Suc.prems by simp
  next
  	case eq4
  	thus ?thesis
  		using Suc.prems by (auto simp add: Let_def)
  next
  	case gt4

  	obtain carry where carry2: "carry = Neg g # Pos f # []"
  		using refine_clause_def by (smt split_clause.simps)

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

		have c: "c = insert ?x ?rest"
			using pop_ins Suc.prems(1) gt4
			by (metis card.empty not_less_zero)

		have suc_card: "Suc (card ?rest) = card c"
			using Suc.prems(1) c pop_card by auto

		let ?gg = "fresh vars undefined"
  	have clause: "l = {hd carry, fst ?p, Pos ?gg} # (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # tl carry)))"
  		using gt4 carry2 Suc.prems by (simp add: Let_def)

  	hence len: "length l = Suc (length (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # tl carry))))"
  		by simp

  	thus ?thesis
  		using Suc.prems len carry2 clause by fastforce
  qed
qed


lemma refine_clause_neighbour:
	assumes "finite c" "l = fst (refine_clause c vars)"
					"i < length l - 2" "finite vars" "idset \<Union>(set l) \<subseteq> vars"
	shows "\<exists>id \<in> l ! i. id \<in> l ! Suc i"



(*
lemma
	assumes "finite c" "l = fst (split_clause c vars (Neg g # Pos f # []))" "k > 0"
					"k \<le> length l - 3" "c' = l ! k"	"finite vars" "card c > 4" "g \<in> vars" "f \<in> vars"
					(* "lp = (last (butlast l)) # (butlast (butlast l)) @ (last l # [])" *)
	shows "(\<exists>i j. Pos i \<in> c' \<and> i \<noteq> j \<and> Neg j \<in> c')"
	using assms
proof (induction "card c" arbitrary: c c' l vars g f)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case gt4

  	let ?p = "pop c"
  	let ?x = "fst ?p"
  	let ?rest = "snd ?p"

  	have c: "c = insert ?x ?rest"
  		using pop_ins Suc.prems(1) gt4
  		by (metis card.empty less_zeroE)

  	have suc_card: "Suc (card ?rest) = card c"
  		using Suc.prems(1) c pop_card by auto

  	(*let ?g = "fresh vars undefined"*)
  	let ?p = "pop c"

  	obtain carry where carry2: "carry = Neg g # Pos f # []"
  		using refine_clause_def by (smt split_clause.simps)

(*  	
		let ?v = "insert f vars"
		let ?gg = "fresh ?v undefined"
*)
		let ?gg = "fresh vars undefined"

  	have clause: "fst (split_clause c vars carry) = {hd carry, fst ?p, Pos ?gg} # (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
  		using gt4 carry2 by (simp add: Let_def)

  	hence "tl l = tl (fst (split_clause c vars carry))"
  		using Suc.prems(2) carry2 by simp
  	also have "... = (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
  		using clause by simp
  	hence tl: "tl l = (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
  		using calculation by simp
  	hence hd: "hd l = {hd carry, fst ?p, Pos ?gg}"
  		using clause Suc.prems(2) carry2 by simp

		hence c': "c' \<in> set l"
			using Suc.prems
			sorry
			by (metis (no_types, opaque_lifting) carry2 clause diff_Suc_Suc diff_less_Suc in_set_conv_nth leD length_Cons less_imp_diff_less not_less_iff_gr_or_eq numeral_2_eq_2)
			
		hence cases: "c' = hd l \<or> c' \<in> set (tl l)"
			by (metis Nil_tl c' list.collapse set_ConsD)

		consider (safe) "c' = {hd carry, fst ?p, Pos ?gg}"
			| (rest) "c' \<in> set (fst (split_clause (snd ?p) (insert ?gg vars) (Neg ?gg # Pos f # [])))"
			using hd tl cases by arith
  	thus ?thesis
  	proof cases
  		case safe
  		obtain j where j: "hd carry = Neg j"
  			using carry2 by simp
  		hence j': "Neg j = Neg g"
  			by (simp add: carry2)
  		hence cond1: "Neg j \<in> c'"
  			using safe j by simp
  		obtain i where i: "Pos ?gg = Pos i"
  			using carry2 by simp
  		hence i': "Pos i = Pos (fresh vars undefined)"
  			by simp
  		hence cond2: "Pos i \<in> c'"
  			using safe by simp
  		hence cond3: "i \<noteq> j"
  			using i' j' fresh_notIn Suc.prems(6) Suc.prems(8) sorry (* by force *)
  		thus ?thesis
  			using cond1 cond2 cond3 by blast
  	next
  		case rest

  		have len: "length l \<ge> 3"
  			using Suc.prems apply (auto simp add: Let_def)
  			using suc_card by arith+

  		have len_tl: "k - 1 < length (tl l)"
  			sorry

			hence len_perm: "length l = length (last (butlast l) # butlast (butlast l) @ [last l])"
				using Suc.prems by auto

			hence "n = card ?rest"
				using Suc.hyps suc_card by simp

			thus ?thesis
				apply (rule Suc.hyps(1)[where ?l = "tl l" and ?vars = "insert (fresh vars undefined) vars"
							and ?g = "fresh vars undefined" and ?f = f])
				using Suc.prems(1) c apply (metis finite_insert)
				using tl apply simp
				using Suc.prems(3) apply simp
				using Suc.prems(4) nth_tl[of "k - 1" "l"] len_tl apply simp
				
				find_theorems "tl ?l ! _"
				find_theorems "Suc (?k - 1)"
				
				using Suc.prems(4) Suc.prems(8) apply simp
				using Suc.prems(5) Suc.prems(9) apply simp
				using Suc.prems(6) apply simp
				subgoal sorry
				using Suc.prems(8) apply simp
				using Suc.prems(9) apply simp
				using Suc.prems(10) apply simp






		let ?v = "insert f vars"
		let ?gg = "fresh ?v undefined"

		have carry3: "fst (split_clause c ?v carry) = {hd carry, fst ?p, Pos ?g} # (fst (split_clause (snd ?p) (insert ?gg ?v) (Neg ?gg # Pos f # [])))"
			using gt4 carry2 by (simp add: Let_def)

		hence tl: "tl l = (fst (split_clause (snd ?p) (insert ?gg ?v) (Neg ?gg # Pos f # [])))"
			using Suc.prems apply (simp split: if_splits)
			by (simp add: Let_def)+
		oops
		have c': "c' \<in> set l"
			using Suc.prems list_permute
			by (smt (verit, ccfv_threshold) One_nat_def Suc_pred butlast_snoc diff_is_0_eq le_imp_less_Suc length_Cons length_butlast less_numeral_extra(4) less_or_eq_imp_le not_less_eq_eq nth_mem numeral_2_eq_2 order.strict_trans)

		hence "c' \<in> set lp"
			using Suc.prems
			by (metis less_imp_diff_less not_less_iff_gr_or_eq nth_mem)
			
		hence "c' = hd l \<or> c' \<in> set (tl l)"
			by (metis Nil_tl c' list.collapse set_ConsD)



(*
		hence "c' = {hd carry, fst ?p, Pos ?ff}"
			using carry1 carry2 carry3 Suc.prems oops
*)

		have c': "c' \<in> set l"
			using Suc.prems list_permute
			by (smt (verit, ccfv_threshold) One_nat_def Suc_pred butlast_snoc diff_is_0_eq le_imp_less_Suc length_Cons length_butlast less_numeral_extra(4) less_or_eq_imp_le not_less_eq_eq nth_mem numeral_2_eq_2 order.strict_trans)

		hence "c' \<in> set lp"
			using Suc.prems
			by (metis less_imp_diff_less not_less_iff_gr_or_eq nth_mem)
			
		hence "c' = hd l \<or> c' \<in> set (tl l)"
			by (metis Nil_tl c' list.collapse set_ConsD)

		have "hd l = {hd carry, fst ?p, Pos ?gg}"
			apply (subst Suc.prems(2))
			apply (subst split_clause.simps)
			apply (subst if_not_P)
			using Suc.prems(7) apply simp
			apply (subst if_not_P)
			using Suc.prems(7) apply simp
			apply (simp add: Let_def carry2)

			using carry3 apply (auto)
			subgoal using Suc.prems(7) apply ( simp add: Let_def)

		have "c' = {hd carry, fst ?p, Pos ?gg} \<or> c' \<in> set (fst (split_clause (snd ?p) (insert ?gg ?v) (Neg ?gg # Pos f # [])))"
			apply (subst Suc.prems(5))
			apply (subst Suc.prems(9))
			apply (subst Suc.prems(2))
			apply (subst Suc.prems(2))
			apply (subst Suc.prems(2))
			apply (simp del: split_clause.simps)
			
			using carry2 carry3 list_permute c' Suc.prems(2) Suc.prems(8) apply (auto) apply (simp add: Let_def split: if_splits)
			apply (elim disjE) using fresh 
(*
		consider (safe) "c' = {hd carry, fst ?p, Pos ?gg}"
			| (rest) "c' \<in> set (fst (split_clause (snd ?p) (insert ?gg ?v) (Neg ?gg # Pos f # [])))"
			using carry2 carry3 list_permute c' Suc.prems(2) Suc.prems(8) apply (auto split: if_splits) apply (simp add: Let_def)
*)
  	thus ?thesis
  	proof cases
  		case safe
  		obtain i where i: "hd carry = Neg i"
  			using carry2 by simp
  		obtain j where j: "Pos ?ff = Pos j"
  			using carry2 by simp
  		thus ?thesis 
  			using safe i j Suc.prems carry2
  			by (metis finite.insertI fresh_notIn insertCI list.sel(1))
  	next
  		case rest

			hence "n = card ?rest"
				using Suc.hyps suc_card by simp

			thus ?thesis
				apply (rule Suc.hyps(1)[where ?l = "tl l" and ?lp = "(last (butlast l)) # (butlast (butlast l)) @ (last l # [])" and ?f = ?ff and ?vars = ?v and ?k = k])
				using Suc.prems(1) c apply (metis finite_insert)
				using tl
				using Suc.prems(3) apply simp
				using Suc.prems(4) apply simp
				using Suc.prems(5) apply simp
				using Suc.prems(6) apply simp
				subgoal sorry
				using Suc.prems(8) apply simp
  	qed
  qed
qed
*)


(*
fun gen_map :: "'a lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
	where "gen_map c vars target f = (
		if vars = {} then
			f
		else
			let p = pop c in
				if target \<in> fst p then
					let  in
					case target
					of Pos t \<Rightarrow> gen_map (snd p) target (fun_upd f t True)
					| Neg t \<Rightarrow> gen_map (snd p) target (fun_upd f t False)
				
	)"
*)

lemma 
	assumes "card {l1, l2, l3, l4} = 4" "sat [{l1, l2, l3, l4}]" "i = fresh (idset {l1, l2, l3, l4}) undefined"
	shows "sat [{l1, l2, Pos i}, {Neg i, l3, l4}]"
	unfolding sat_def models_def lift_def using assms
proof (intro exI)
	fix cls :: "'a lit set"
	assume c: "cls \<in> {{l1, l2, Pos i}, {Neg i, l3, l4}}"

	obtain vmap where vmap: "vmap \<Turnstile> [{l1, l2, l3, l4}]"
		using assms sat_def by blast
	consider (l1) "(vmap\<up>) l1"
		| (l2) "(vmap\<up>) l2"
		| (l3) "(vmap\<up>) l3"
		| (l4) "(vmap\<up>) l4"
		using assms sat_def models_def lift_def vmap
		by (smt (verit) empty_iff insert_iff list.simps(15))
	hence "sat [{l1, l2, Pos i}, {Neg i, l3, l4}]"
	proof cases
		case l1
		hence vmap: "vmap \<Turnstile> ({l1, l2, Pos i} # [])"
			unfolding models_def by simp

(*
		have "l1 \<noteq> l2" using assms
			by (metis (no_types, lifting) One_nat_def card.empty card_insert_if empty_not_insert finite.emptyI finite_insert insert_absorb insert_absorb2 num.simps(4) numeral_2_eq_2 numeral_3_eq_3 numeral_eq_iff numeral_eq_one_iff semiring_norm(89) verit_eq_simplify(8))
*)
			have "l1 \<noteq> l2" using \<open>card {l1, l2, l3, l4} = 4\<close>

		let ?updmap = "fun_upd vmap (ident l3) (case l3 of Pos x \<Rightarrow> True | Neg x \<Rightarrow> False)"
		have "?updmap \<Turnstile> [{l1, l2, Pos i}, {Neg i, l3, l4}]"
			using vmap assms update_preserve_sat update_preserve_lit
			unfolding models_def lift_def

		then show ?thesis sorry
	next
		case l2
		then show ?thesis sorry
	next
		case l3
		then show ?thesis sorry
	next
		case l4
		then show ?thesis sorry
	qed
qed


lemma
	assumes "card c > 3" "l = fst (split_clause c vars (Pos (fresh vars undefined) # []))" 
					"j < length l - 1" "cur = l ! j" "k < length l - 1" "nxt = l ! k" "j \<noteq> k"
	shows "\<exists>l \<in> cur. l = Pos i \<and> (Neg i) \<in> nxt"
	using assms
proof (induction "card c" arbitrary: c vars j k cur nxt)
  case 0
  thus ?case by simp
next
  case (Suc n)
  thm Suc.prems
  thm Suc.hyps
  consider (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	using Suc.prems by arith
  thus ?case
  proof cases
  	case eq4
  	hence len: "length l = 2"
  		by (auto simp add: Let_def Suc.prems)
  	hence j: "j = 0"
  		using Suc.prems(3) by simp
		hence k: "k = 1"
			using Suc.prems(5) Suc.prems(7) len by simp
  	thus ?thesis using Suc.prems(5) len by simp
  next
  	case gt4
  	consider (safe) "j < length l - 2"
  		| (penult) "j = length l - 2"
  		| (last) "j = length l - 1"
  		using Suc.prems by arith
  	thus ?thesis
  	proof cases
  		case safe

  		obtain l1 l2 i where "cur = {l1, l2, Pos i}"
  			using Suc.prems split_clause_card gt4

  		then show ?thesis sorry
  	next
  		case penult
  		then show ?thesis sorry
  	next
  		case last
  		then show ?thesis sorry
  	qed
  qed
qed

lemma split_clause_sat:
	assumes "finite c" "c \<noteq> {}" "c' = fst (split_clause c vars carry)" "length carry = 2" "sat (c # [])"
					"\<forall>l \<in> set carry. ident l \<notin> idset c" "idset c \<subseteq> vars" "finite vars" "idset (set carry) \<subseteq> vars"
	shows "sat c'"
	using assms
proof (induction "card c" arbitrary: c vars carry)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	hence "c' = c # []"
  		using Suc.prems by simp
  	thus ?thesis 
  		using Suc.prems sat_single by simp
  next
  	case eq4

  	hence single: "card (set (c # [])) = 1"
  		by simp

  	obtain vmap where vmap: "vmap \<Turnstile> c # []"
  		using Suc.prems(5) unfolding sat_def by blast
  	obtain lit where lit: "\<forall>c' \<in> set (c # []). (vmap\<up>) lit"
  		using vmap unfolding models_def by blast

		let ?p = "pop c"
		let ?q = "pop (snd ?p)"

		have "c' = {fst ?p, fst ?q, hd (tl carry)} # (insert (hd carry) (snd ?q)) # []"
			using eq4 Suc.prems
			by (metis Suc_n_not_le_n fst_conv numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) split_clause.simps)

		hence "lit \<in> {fst ?p, fst ?q, hd (tl carry)} \<or> lit \<in> (insert (hd carry) (snd ?q))"
			apply auto

		oops
		have "card {fst ?p, fst ?q, hd (tl carry)} = 3"
			apply (rule split_clause_card_3[of c _ vars carry])
			using Suc.prems apply simp
			using eq4 apply simp
			using eq4 apply (auto simp add: Let_def)[1]
			using Suc.prems by simp+

		have "card (insert (hd carry) (snd ?q)) = 3"
			apply (rule split_clause_card_3[of c _ vars carry])
			using Suc.prems apply simp
			using eq4 apply simp
			using eq4 apply (auto simp add: Let_def)[1]
			using Suc.prems by simp+


  	then show ?thesis sorry
  next
  	case gt4
  	then show ?thesis sorry
  qed
qed



lemma split_clause_sat:
	assumes "finite c" "c' \<in> set (fst (split_clause c vars carry))" "length carry \<le> 2" "sat (c # [])"
	shows "sat (c' # [])"
	using assms
proof (induction "card c" arbitrary: c vars carry)
  case 0
  thus ?case unfolding sat_def models_def lift_def
  	by simp
next
  case (Suc n)
  consider (le3) "card c \<le> 3"
  	| (eq4) "card c = 4"
  	| (gt4) "card c > 4"
  	by arith
  thus ?case
  proof cases
  	case le3
  	let ?split = "(fst (split_clause c vars carry))"

  	have "c # [] = ?split"
  		using le3 by simp
  	hence "sat (c # []) = sat ?split"
  		by simp

  	have "c' \<in> set ?split \<Longrightarrow> c' = c"
  		using le3 by simp

  	hence "sat (c' # [])"
  		using Suc.prems(2) Suc.prems(4) by simp
  	thus ?thesis .
  next
  	case eq4

  	let ?split = "(fst (split_clause c vars carry))"

  	let ?p = "pop c"
		let ?q = "pop (snd ?p)"
		let ?expand = "{fst ?p, fst ?q, hd (tl carry)} # (insert (hd carry) (snd ?q)) # []"

  	have eq4_fn: "?expand = ?split"
  		using eq4 Suc_n_not_le_n fst_conv numeral_eq_Suc
  		by (metis pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) split_clause.simps)

  	hence "sat ?expand = sat ?split"
  		by simp

  	consider (split) "c' = {fst ?p, fst ?q, hd (tl carry)}"
  		| (rest) "c' = insert (hd carry) (snd ?q)"
  		by (metis Suc.prems(2) eq4_fn equals0D list.set(1) set_ConsD)
  	thus ?thesis
  	proof cases
  		case split
			hence "card {fst ?p, fst ?q, hd (tl carry)} > 0"
				by (simp add: card_gt_0_iff)
  		hence "sat ({fst ?p, fst ?q, hd (tl carry)} # [])"
  			using sat_single by (metis empty_not_insert)
  		hence "sat (c' # [])"
  			using split by simp
  		thus ?thesis .
  	next
  		case rest
  		hence "card (insert (hd carry) (snd ?q)) > 0"
  			using eq4 Suc.hyps pop_card pop_ins finite_insert
  			by (metis One_nat_def card_eq_0_iff insert_not_empty numeral_One numeral_eq_iff verit_eq_simplify(10) zero_less_Suc)
  		hence "sat ((insert (hd carry) (snd ?q)) # [])"
  			using sat_single by (metis empty_not_insert)
  		hence "sat (c' # [])"
  			using rest by simp
  		thus ?thesis .
  	qed
  next
  	case gt4
  	hence "card c' \<le> 3"
  		using split_clause_card assms by simp
  	hence "c' = {}"
  	then show ?thesis sorry
  qed
qed


fun sat_le3sat_aux :: "('a :: fresh) lit set list \<Rightarrow> 'a set \<Rightarrow> 'a lit set list"
	where "sat_le3sat_aux [] vars = []"
	| "sat_le3sat_aux (c # cs) vars = (
			let c = refine_clause c vars in
				(fst c) @ sat_le3sat_aux cs (snd c)
	)"

definition sat_le3sat :: "('a :: fresh) lit set list \<Rightarrow> 'a lit set list"
	where "sat_le3sat expr = sat_le3sat_aux expr (idset (\<Union>(set expr)))"


lemma
	assumes "finite (set expr)" "sat expr"
	shows "sat (sat_le3sat expr)"
	using assms unfolding sat_def models_def
proof -
	fix c :: "'a lit set"
	assume c: "c \<in> set expr"

	obtain vmap where vmap: "vmap \<Turnstile> expr"
		using assms sat_def by blast

	obtain l where l1: "l \<in> c" and l2: "(vmap\<up>) l"
		using models_def c vmap by blast

	consider (le3) "card c \<le> 3"
		| (eq4) "card c = 4"
		| (gt4) "card c > 4"
		by arith
	hence "\<exists>nmap. nmap \<Turnstile> fst (refine_clause c (idset (\<Union>(set expr))))"
	proof cases
		case le3
		thus ?thesis using refine_clause_def sat_def sat_single
			by (metis l1 empty_iff fst_conv split_clause.simps)
	next
		case eq4
		hence "\<exists>subc \<in> set (fst (refine_clause c (idset (\<Union>(set expr))))). l \<in> subc"
			using refine_clause_def 

		then show ?thesis sorry
	next
		case gt4
		then show ?thesis sorry
	qed



lemma transform_preserve_le3_single: "card c \<le> 3 \<longleftrightarrow> sat_le3sat (c # []) = c # []"
	unfolding sat_le3sat_def apply auto oops
	by (smt (verit) list.distinct(1) list.inject)

lemma transform_preserve_le3_single_alt: "card c \<le> 3 \<longleftrightarrow> sat_le3sat_aux (c # []) vars carry = c # []"
	apply auto oops
	by (smt (verit) list.distinct(1) list.inject)

lemma transform_preserve_le3_alt: 
"card c \<le> 3 \<longleftrightarrow> sat_le3sat_aux (c # cs) vars carry = c # sat_le3sat_aux cs vars carry"
	apply auto oops by (smt (verit) card.empty card_insert_disjoint finite.emptyI finite.insertI 
			insert_absorb le_SucI list.inject nle_le numeral_3_eq_3)

lemma transform_preserve_le3: "card c \<le> 3 \<longleftrightarrow> sat_le3sat (c # cs) = 
		c # sat_le3sat_aux cs (idset (\<Union>(set (c # cs)))) (fresh (idset (\<Union>(set (c # cs)))) undefined)"
	unfolding sat_le3sat_def using transform_preserve_le3_alt
	apply auto oops by (smt (verit) card.empty card_insert_disjoint finite.emptyI finite.insertI 
			insert_absorb le_SucI list.inject nle_le numeral_3_eq_3)

lemma len_csplit_gt_0: "finite c \<Longrightarrow> length (fst (clause_splitter c vars carry)) > 0"
	apply (induction c arbitrary: vars carry rule: finite_induct)
	by (auto simp add: Let_def)

lemma "\<lbrakk> finite c; finite vars \<rbrakk> \<Longrightarrow> finite (snd (clause_splitter c vars carry))"
	apply (induction c arbitrary: vars carry rule: finite_induct)
	 apply auto

lemma len_inv: "length (sat_le3sat_aux cs vars1 carry1) = length (sat_le3sat_aux cs vars2 carry2)"
	apply (induction cs vars1 carry1 arbitrary: vars2 carry2 rule: sat_le3sat_aux.induct)
	 apply (auto split: if_splits simp add: Let_def simp del: sat_le3sat_aux.simps)
	 apply auto[1]
	apply (subst(2) sat_le3sat_aux.simps)
	apply (subst sat_le3sat_aux.simps)
	oops
	by (smt (verit, best) list.size(4) pop_def)


lemma "length (sat_le3sat_aux cs vars1 carry1) < length (sat_le3sat_aux (c # cs) vars2 carry2)"
	apply (induction cs vars1 carry1 arbitrary: c vars2 carry2 rule: sat_le3sat_aux.induct)
	 apply (auto split: if_splits simp add: Let_def simp del: sat_le3sat_aux.simps)
	apply (auto simp add: Let_def)[1]
	apply (subst(2) sat_le3sat_aux.simps)
	apply (subst sat_le3sat_aux.simps)
	oops
	apply (auto split: if_splits simp add: Let_def simp del: sat_le3sat_aux.simps)




lemma "length cs \<le> length (sat_le3sat_aux cs vars carry)"
proof (induction cs arbitrary: vars carry)
  case Nil
  thus ?case by simp
next
  case (Cons c cs)
  consider (le3) "card c \<le> 3" | (gt3) "card c > 3"
  	by arith
	thus ?case
	proof cases
		case le3
		let ?rest = "sat_le3sat_aux cs vars carry"

		have "sat_le3sat_aux (c # cs) vars carry = c # ?rest"
			using le3 transform_preserve_le3_alt by simp

		hence "length (sat_le3sat_aux (c # cs) vars carry) = length (c # ?rest)"
			by simp
		also have "... = Suc (length ?rest)"
			by simp
		also have "... \<ge> Suc (length cs)"
			using Cons.IH by simp
		finally show ?thesis 
			by simp
	next
		case gt3
		let ?p = "pop c"
		let ?next = "fresh vars (ident (fst ?p))"
		let ?rest = "{Neg carry, fst ?p, Pos ?next} # (sat_le3sat_aux (snd ?p # cs) (insert ?next vars) ?next)"
								
		have "sat_le3sat_aux (c # cs) vars carry = ?rest"
			using gt3	by (meson linorder_not_le sat_le3sat_aux.simps(2))

		hence "length (sat_le3sat_aux (c # cs) vars carry) = length ?rest"
			by simp
		also have "... = Suc (length (sat_le3sat_aux (snd ?p # cs) (insert ?next vars) ?next))"
			by simp
		also have "... \<ge> length (sat_le3sat_aux (snd ?p # cs) (insert ?next vars) ?next)"
			by simp
		also have "... \<ge> length (snd ?p # cs)"
			using Cons.IH len_inv 
	 apply (auto split: if_splits simp add: Let_def simp del: sat_le3sat_aux.simps)
			

		then show ?thesis
	qed
qed
	


lemma "\<forall>c \<in> set (sat_le3sat cs). card c \<le> 3"
proof (intro ballI)
	fix c :: "'a lit set"
	assume c: "c \<in> set (sat_le3sat cs)"

	


lemma "\<forall>c \<in> set cs. card c \<le> 3 \<longrightarrow> sat_le3sat cs = cs"
proof (intro ballI)
	fix c :: "'a lit set"
	assume c: "c \<in> set cs"
	assume card: "card c \<le> 3"


lemma 
	assumes "\<forall>c \<in> set cs. card c \<le> 3"
	shows "sat_le3sat cs = cs"
	using assms
proof 
	fix c :: "'a lit set"

	show ?thesis



fun vmap_upd :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> bool)"
	where "vmap_upd vmap var b = (
		let new_vmap = (\<lambda>v. if v = var then b else vmap v) in (
			new_vmap
		)
	)"



lemma le3:
	assumes "c \<in> set (sat_le3sat_aux expr vars carry)"
	shows "card c \<le> 3"
	using assms unfolding sat_le3sat_def



definition "sat_pset = {expr | expr. sat expr}"
definition "le3sat_pset = {expr | expr. le3sat expr}"


lemma reduct_scheme: "is_reduction sat_le3sat sat_pset le3sat_pset"
	unfolding is_reduction_def

proof (intro allI iffI)
	fix expr :: "('a :: fresh) lit set list"
	assume expr_in_sat: "expr \<in> sat_pset"

	obtain vmap where vmap: "vmap \<Turnstile> expr"
		using expr_in_sat unfolding sat_def sat_pset_def by blast

	hence "vmap \<Turnstile> sat_le3sat expr"
		unfolding models_def
	proof -
		assume sat_expand: "\<forall>clause \<in> set expr. \<exists>lit \<in> clause. (vmap\<up>) lit"
		show "\<forall>clause \<in> set (sat_le3sat expr). \<exists>lit \<in> clause. (vmap\<up>) lit"
		proof
			fix clause :: "'a lit set"
			assume a: "clause \<in> set (sat_le3sat expr)"

(*
			let ?l = "\<lambda>i. SOME l. (vmap\<up>) l \<and> l \<in> expr ! i"
			have select: "i < length expr \<Longrightarrow> (vmap\<up>) (?l i) \<and> (?l i) \<in> expr ! i"
				unfolding models_def using vmap sat_expand by - (rule someI2_ex, auto)
*)

			consider (le3) "card clause \<le> 3" | (gt3) "card clause > 3"
				by arith
			thus "\<exists>lit \<in> clause. (vmap\<up>) lit"
			proof cases
				case le3
				hence "\<forall>cs. sat_le3sat (clause # cs) = clause # cs"
					sorry
				then show ?thesis using vmap models_def sat_def
			next
				case gt3
				then show ?thesis sorry
			qed
	qed

	thus "sat_le3sat expr \<in> le3sat_pset"
qed

lemma
	assumes "sat expr"
	shows "sat3 expr"
	using assms
proof -
	consider (safe) "\<forall>clause \<in> set expr. card clause > 0 \<and> card clause \<le> 3"
		| (rewrite) "\<exists>clause \<in> set expr. card clause > 0 \<and> card clause > 3"
		| (null) "\<exists>clause \<in> set expr. card clause = 0"
		by fastforce
	thus ?thesis
	proof cases
		case safe
		thus ?thesis
			unfolding sat3_def using assms by simp
	next
		case rewrite
		obtain c where obt_c: "c \<in> set expr \<and> card c > 3"
			using rewrite by blast
		thus ?thesis
		proof (induction "card c")
			case 0
			thus ?case by simp
		next
			case (Suc n)
			hence "card c = Suc n"
				by simp
			hence ""
			thus ?case
		qed
	next
		case null
		thus ?thesis sorry
	qed




lemma "sat expr \<Longrightarrow> expr \<in> sat3"
proof (induction expr)
  case Nil
  thus ?case using sat_3sat_induct
  	by simp
next
  case (Cons a expr)
  consider (safe) "card a \<le> 3" | (rewrite) "card a > 3"
  	by arith
  thus ?case
  proof (cases)
  	case safe
  	hence "sat (a # expr)"
  		using Cons.prems by simp
  	thm "Cons.IH"

  	then show ?thesis sorry
  next
  	case rewrite
  	then show ?thesis sorry
  qed
qed

end