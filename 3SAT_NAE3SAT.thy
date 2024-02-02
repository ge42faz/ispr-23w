theory "3SAT_NAE3SAT"
	imports Main SAT_3SAT
begin

definition nae_models :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lit set list \<Rightarrow> bool" (infixl "\<turnstile>" 55)
	where "vmap \<turnstile> expr \<equiv> \<forall>c \<in> set expr. \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f"

lemma nae_models_strict: "vmap \<turnstile> expr \<Longrightarrow> vmap \<Turnstile> expr"
	unfolding models_def nae_models_def by fast

definition naesat :: "'a lit set list \<Rightarrow> bool"
	where "naesat expr \<equiv> (\<exists>vmap. vmap \<turnstile> expr) \<and> (\<forall>c \<in> set expr. card c > 0)"

definition nae4sat :: "'a lit set list \<Rightarrow> bool"
	where "nae4sat expr = (naesat expr \<and> (\<forall>clause \<in> set expr. card clause = 4))"

definition nae3sat :: "'a lit set list \<Rightarrow> bool"
	where "nae3sat expr = (naesat expr \<and> (\<forall>clause \<in> set expr. card clause = 3))"


definition augment :: "('a::fresh) lit set list \<Rightarrow> 'a lit set list" ("_+" 60)
	where "augment expr = (
		let f = fresh (idset (\<Union>(set expr))) undefined in
			map (\<lambda>c. insert (Pos f) c) expr
)"

lemma eq3sat_var_finite: "eq3sat expr \<Longrightarrow> finite (idset (\<Union>(set expr)))"
	unfolding eq3sat_def sat_def
	using card_ge_0_finite finite_expr_idset by blast

lemma augment_notin: "eq3sat expr \<Longrightarrow> c \<in> set expr \<Longrightarrow> Pos (fresh (idset (\<Union>(set expr))) undefined) \<notin> c"
	using eq3sat_var_finite fresh_notIn idset_iff by (meson UnionI)

lemma augment_insert: "c \<in> set expr \<Longrightarrow> insert (Pos (fresh (idset (\<Union>(set expr))) undefined)) c \<in> set (expr+)"
	unfolding augment_def by simp

lemma augment_card: "eq3sat expr \<Longrightarrow> c \<in> set (expr+) \<Longrightarrow> card c = 4"
	unfolding eq3sat_def sat_def augment_def 
	using augment_notin augment_insert apply auto
	using finite_expr_idset fresh_notIn idset_iff
	by (smt UnionI card_eq_0_iff card_insert_disjoint numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)

lemma augment_common: "\<exists>s. \<forall>c \<in> set (expr+). s \<in> c"
	unfolding augment_def by fastforce


definition flip :: "'a lit \<Rightarrow> 'a lit" ("\<updown>")
	where "flip l = (case l of Pos v \<Rightarrow> Neg v | Neg v \<Rightarrow> Pos v)"

lemma double_flip: "\<updown>(\<updown>l) = l"
	unfolding flip_def
	by (metis ident.cases lit.simps(5) lit.simps(6))

lemma flip_id: "\<updown> \<circ> \<updown> = id"
	using double_flip by fastforce

lemma image_comp_id: "f \<circ> f = id \<Longrightarrow> f ` f ` A = A"
	by (simp add: image_comp)

(*
definition duplicate_aux :: "'a lit set list \<Rightarrow> 'a lit set list \<Rightarrow> 'a lit set list" (infix "^" 60)
	where "duplicate_aux expr any = fold (\<lambda>c res. c # flip`c # res) expr any"
*)

lemma inj_flip: "inj \<updown>"
	unfolding inj_def flip_def
	by (smt ident.elims lit.simps(5) lit.simps(6))

find_theorems inj_on card
lemma flip_card: "card (\<updown> ` c) = card c"
	apply (rule card_image)
	using inj_on_subset inj_flip subset_UNIV
	by auto

definition duplicate :: "'a lit set list \<Rightarrow> 'a lit set list" ("_^2")
	where "duplicate expr = expr @ map (\<lambda>c. \<updown>`c) expr"

lemma dupl_len: "length (expr^2) = 2 * length expr"
	unfolding duplicate_def by simp

lemma dupl_imp: "c \<in> set (expr^2) \<Longrightarrow> \<updown>`c \<in> set (expr^2)"
	unfolding duplicate_def by (auto simp add: image_comp_id flip_id)

lemma dupl_rev: "\<updown>`c \<in> set (expr^2) \<Longrightarrow> c \<in> set (expr^2)"
	unfolding duplicate_def apply auto
	using flip_id image_comp_id apply blast
	by (metis flip_id image_comp_id)

lemma dupl_sym: "c \<in> set (expr^2) \<longleftrightarrow> \<updown>`c \<in> set (expr^2)"
	using dupl_imp dupl_rev by metis

lemma dupl_card: "\<forall>c \<in> set expr. card c = n \<Longrightarrow> \<forall>c \<in> set (expr^2). card c = n"
	unfolding duplicate_def lift_def by (auto simp add: flip_card)


(*
definition duplicate_aux :: "'a lit set list \<Rightarrow> 'a lit set list \<Rightarrow> 'a lit set list" (infix "^" 60)
	where "duplicate_aux expr any = fold (\<lambda>c res. c # flip`c # res) expr any"

definition duplicate :: "'a lit set list \<Rightarrow> 'a lit set list" ("_^2")
	where "duplicate expr = expr^[]"

lemma dupl_cons: "((a # expr)^any) = fold (\<lambda>c res. c # flip ` c # res) expr (a # flip`a # any)"
	by (simp add: duplicate_aux_def)

lemma dupl_aux_len: "length (expr^any) = 2 * length expr + length any"
	unfolding duplicate_aux_def duplicate_def flip_def
	by (induction expr arbitrary: any) (auto simp add: dupl_cons)

lemma dupl_len: "length (expr^2) = 2 * length expr"
	unfolding duplicate_def using dupl_aux_len
	oops
	by (metis add.right_neutral list.size(3))


lemma "fold (\<lambda>c res. c # \<updown> ` c # res) (a # expr) [] = fold (\<lambda>c res. c # \<updown> ` c # res) (expr) [a, \<updown>`a]"
	by (rule List.fold_simps(2))

term Set.image

	

lemma "\<forall>c \<in> set expr. card c = n \<Longrightarrow> \<forall>c \<in> set (expr^2). card c = n"
	unfolding duplicate_def duplicate_aux_def
proof (induction expr arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons a expr)
  hence "card a = n"
  	by simp
  moreover have "card (\<updown>`a) = n"
  	using flip_card calculation by blast
  moreover have "\<forall>c \<in> set expr. card c = n"
  	using Cons by simp
  moreover have ""

  moreover have "fold (\<lambda>c res. c # \<updown> ` c # res) (a # expr) [] = fold (\<lambda>c res. c # \<updown> ` c # res) expr [a, \<updown>`a]"
  	by (rule List.fold_simps(2))
  ultimately show ?case


  then show ?case sorry
qed
*)

lemma obtain_aux: "\<lbrakk> card c > 1; e \<in> c \<rbrakk> \<Longrightarrow> \<exists>f. f \<noteq> e \<and> f \<in> c"
	by (metis One_nat_def card_eq_0_iff card_le_Suc0_iff_eq nat_less_le not_one_less_zero order.asym)

lemma lift_flip: "(vmap\<up>) l \<longleftrightarrow> \<not>(vmap\<up>) (\<updown>l)"
	using ex_mid_lift double_flip flip_def
	by (metis ident.elims lit.simps(5))

definition invert :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("\<Updown>")
	where "invert vmap = (\<lambda>x. \<not>vmap x)"

lemma double_invert: "\<Updown>(\<Updown>vmap :: 'a \<Rightarrow> bool) = vmap"
	unfolding invert_def by simp

lemma invert_id: "\<Updown> \<circ> \<Updown> = id"
	using double_invert by fastforce

lemma invert_nae: "vmap \<turnstile> expr \<longleftrightarrow> \<Updown>vmap \<turnstile> expr"
	unfolding invert_def nae_models_def
	by (auto, (metis ident.cases vmap_false_neg_lift vmap_true_pos_lift ex_mid_lift)+)

lemma eq3sat_to_nae4sat:
	assumes "eq3sat expr"
	shows "nae4sat (expr+)"
	using assms
proof -
	have a: "sat expr \<and> (\<forall>clause \<in> set expr. card clause = 3)"
		using assms by (simp add: eq3sat_def)
	hence b: "(\<exists>vmap. vmap \<Turnstile> expr) \<and> (\<forall>clause \<in> set expr. card clause > 0)"
		unfolding sat_def by simp
	hence "\<exists>vmap. \<forall>clause \<in> set expr. \<exists>lit \<in> clause. (vmap\<up>) lit"
		unfolding models_def by simp

	then obtain vmap where vmap: "\<forall>clause \<in> set expr. \<exists>lit \<in> clause. (vmap\<up>) lit"
		by blast

	define f where f: "f = fresh (idset (\<Union>(set expr))) undefined"

	obtain s where dummy: "\<forall>clause \<in> set (expr+). s \<in> clause"
						and s: "s = Pos f"
		unfolding augment_def using f by fastforce

	define vmap_f where vmap_f: "vmap_f = vmap(f := False)"

	have card4: "\<forall>clause \<in> set (expr+). card clause = 4"
		using augment_card assms by blast

	have "\<forall>c \<in> set (expr+). \<exists>f \<in> c. \<not>(vmap_f\<up>) f"
		using s dummy vmap_f ex_mid_lift vmap_false_neg_lift
		by (metis fun_upd_apply)

	moreover have models_aug_expand: "\<forall>c \<in> set (expr+). \<exists>t \<in> c. (vmap_f\<up>) t"
	proof (intro ballI)
		fix c
		assume "c \<in> set (expr+)"

		hence "c - {s} \<in> set expr"
			unfolding augment_def
			by (simp add: assms augment_insert augment_notin f in_image_insert_iff s)

		then obtain t where t: "t \<in> c - {s}" and t_lift: "(vmap\<up>) t"
			using vmap by fastforce

		thus "\<exists>t \<in> c. (vmap_f\<up>) t"
		proof (intro bexI)
			have "t \<noteq> s"
				using t s by simp
			thus "(vmap_f\<up>) t"
				using vmap_f t_lift fun_upd_apply ex_mid_lift s
				by (smt vmap_false_neg_lift vmap_true_pos_lift ident.cases)
		next
			show "t \<in> c"
				using augment_insert t by blast
		qed
	qed

	ultimately have models_aug: "vmap_f \<turnstile> expr+"
		unfolding nae_models_def by fast

	hence "nae4sat (expr+)"
		unfolding nae4sat_def sat_def naesat_def using card4 by auto

	thus ?thesis .
qed

lemma nae4sat_to_eq3sat:
	assumes "nae4sat (expr+)"
	shows "eq3sat expr"
	using assms
proof -
	have a: "naesat (expr+) \<and> (\<forall>clause \<in> set (expr+). card clause = 4)"
		using assms by (simp add: nae4sat_def)
	hence b: "(\<exists>vmap. vmap \<turnstile> expr+) \<and> (\<forall>clause \<in> set (expr+). card clause > 0)"
		unfolding naesat_def by simp
	hence "\<exists>vmap. \<forall>c \<in> set (expr+). \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f"
		unfolding nae_models_def by simp

	then obtain vmap where vmap: "\<forall>c \<in> set (expr+). \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f"
		by blast

	have card4: "\<forall>c \<in> set (expr+). card c = 4"
		using a by simp

	have "\<exists>s. \<forall>c \<in> set (expr+). s \<in> c"
		by (rule augment_common)
	then obtain s where s_common: "\<forall>c \<in> set (expr+). s \<in> c"
								and s_pos: "s = Pos (fresh (idset (\<Union>(set expr))) undefined)"
		unfolding augment_def by simp

	hence s_notin: "\<forall>c \<in> set expr. s \<notin> c"
		using s_pos b augment_insert fresh_notIn idset_iff
		by (metis UnionI card_ge_0_finite finite_idset finite_expr finite_insert)

	hence card3: "\<forall>c \<in> set expr. card c = 3"
		using card4 s_pos b augment_insert
		by (metis Suc_numeral card_ge_0_finite card_insert_disjoint diff_Suc_1 finite_insert semiring_norm(2) semiring_norm(8))

	then consider (truthy) "(vmap\<up>) s"
		| (falsy) "\<not>(vmap\<up>) s"
		by arith
	thus ?thesis
	proof cases
		case truthy
		hence "\<forall>c \<in> set expr. \<exists>t \<in> c. (\<Updown>vmap\<up>) t"
		proof (intro ballI)
			fix c
			assume a': "c \<in> set expr"
			hence "s \<notin> c"
				using s_notin by simp

			thus "\<exists>t \<in> c. (\<Updown>vmap\<up>) t"
				unfolding invert_def using vmap s_pos truthy a' augment_insert
				by (metis insertE lit.exhaust vmap_false_neg_lift vmap_true_pos_lift)
		qed

		hence "\<exists>vmap. \<forall>c \<in> set expr. \<exists>t \<in> c. (vmap\<up>) t"
			by meson
		thus ?thesis unfolding eq3sat_def sat_def models_def
			using card3 by simp
	next
		case falsy
		hence "\<forall>c \<in> set expr. \<exists>t \<in> c. (vmap\<up>) t"
		proof (intro ballI)
			fix c
			assume a': "c \<in> set expr"
			hence "s \<notin> c"
				using s_notin by simp

			thus "\<exists>t \<in> c. (vmap\<up>) t"
				using vmap s_pos falsy a' augment_insert by fast
		qed

		hence "\<exists>vmap. \<forall>c \<in> set expr. \<exists>t \<in> c. (vmap\<up>) t"
			by meson
		thus ?thesis unfolding eq3sat_def sat_def models_def
			using card3 by simp
	qed
qed


definition nae4sat_pset :: "('a :: fresh) lit set list set"
	where "nae4sat_pset = {expr. nae4sat expr}"

lemma eq3sat_reduce_nae4sat: "is_reduction augment eq3sat_pset nae4sat_pset"
	unfolding is_reduction_def eq3sat_pset_def nae4sat_pset_def
	using eq3sat_to_nae4sat nae4sat_to_eq3sat
	by blast


lemma card4_items: "finite c \<Longrightarrow> card c = 4 \<Longrightarrow> \<exists>l1 l2 l3 l4. c = {l1, l2, l3, l4}"
	apply (induction c rule: finite_induct)
	 apply auto
	by (metis card_3_iff)


lemma naesat_falsy_checkpoint:
	assumes "\<not> naesat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite vars" "card c = 4"
					"\<forall>c' \<in> set (c # xs). finite c'"
	shows "\<not> naesat (fst (refc c vars) @ xs)"
	unfolding naesat_def nae_models_def using assms
proof -
	have a1: "(\<forall>vmap. \<exists>c \<in> set (c # xs). \<forall>t \<in> c. \<forall>f \<in> c. \<not>(vmap\<up>) t \<or> (vmap\<up>) f) \<or> (\<exists>c \<in> set (c # xs). card c \<le> 0)"
		using assms(1) unfolding naesat_def nae_models_def
		by (metis gr0I le_numeral_extra(3))
	then consider (cond) "\<forall>vmap. \<exists>c \<in> set (c # xs). \<forall>t \<in> c. \<forall>f \<in> c. \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
		| (infty) "\<exists>c \<in> set (c # xs). card c \<le> 0"
		by blast
	thus "\<not>((\<exists>vmap. \<forall>c\<in>set (fst (refc c vars) @ xs). \<exists>t\<in>c. \<exists>f\<in>c. (vmap\<up>) t \<and> \<not> (vmap\<up>) f) \<and> (\<forall>c\<in>set (fst (refc c vars) @ xs). 0 < card c))"
	proof cases
		case cond                                                          
		hence "\<forall>vmap. \<exists>c \<in> set (fst (refc c vars) @ xs). \<forall>t \<in> c. \<forall>f \<in> c. \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
		proof (intro allI)
			fix vmap
			obtain c' where c': "c' \<in> set (c # xs)" and c'_lift: "\<forall>t \<in> c'. \<forall>f \<in> c'. \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
				using cond by blast
	
			then consider (fst) "c' = c"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>c \<in> set (fst (refc c vars) @ xs). \<forall>t \<in> c. \<forall>f \<in> c. \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
			proof cases
				case fst

				have "\<exists>l1 l2 l3 l4. c = {l1, l2, l3, l4}"
					apply (rule card4_items)
					using assms(4) card.infinite by fastforce+
				then obtain l1 l2 l3 l4 where c_elem: "c = {l1, l2, l3, l4}"
					by blast

				let ?p = "pop c"
				let ?q = "pop (snd ?p)"
				let ?v = "fresh vars undefined"
	
				have expand: "fst (refc c vars) = {fst ?p, fst ?q, Pos ?v} # insert (Neg ?v) (snd ?q) # []"
					unfolding refc_def using assms(4)
					by (simp add: Let_def split: if_splits)

				have cases: "(vmap\<up>) l1 \<and> (vmap\<up>) l2 \<and> (vmap\<up>) l3 \<and> (vmap\<up>) l4
						\<or> \<not>(vmap\<up>) l1 \<and> \<not>(vmap\<up>) l2 \<and> \<not>(vmap\<up>) l3 \<and> \<not>(vmap\<up>) l4"
					using c'_lift c_elem fst by blast

				moreover have c_elem_alt: "c = {fst ?p, fst ?q, fst (pop (snd ?q)), fst (pop (snd (pop (snd ?q))))}"
					using assms(4) pop_card pop_ins
					by (smt Suc_eq_numeral card_eq_0_iff finite_insert numeral_2_eq_2 numeral_3_eq_3 pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)

				ultimately have "(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst (pop (snd ?q))) \<and> (vmap\<up>) (fst (pop (snd (pop (snd ?q)))))
						\<or> \<not>(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst (pop (snd ?q))) \<and> \<not>(vmap\<up>) (fst (pop (snd (pop (snd ?q)))))"
					using c_elem c'_lift fst by blast

				then consider (truthy) "vmap ?v"
					| (falsy) "\<not>vmap ?v"
					by arith
				thus ?thesis
				proof cases
					case truthy
					then consider (allT) "(vmap\<up>) l1 \<and> (vmap\<up>) l2 \<and> (vmap\<up>) l3 \<and> (vmap\<up>) l4"
						| (allF) "\<not>(vmap\<up>) l1 \<and> \<not>(vmap\<up>) l2 \<and> \<not>(vmap\<up>) l3 \<and> \<not>(vmap\<up>) l4"
						using cases by arith
					thus ?thesis
					proof cases
						case allT
						hence "\<forall>t \<in> {fst ?p, fst ?q, Pos ?v}. \<forall>f \<in> {fst ?p, fst ?q, Pos ?v}. \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
							using truthy c_elem_alt c'_lift c_elem fst vmap_true_pos_lift by (metis insert_iff)
						moreover have "{fst ?p, fst ?q, Pos ?v} \<in> set (fst (refc c vars) @ xs)"
							using expand by simp
						ultimately show ?thesis by blast
					next
						case allF
						hence "\<not>(vmap\<up>) (Neg ?v)"
							using truthy ex_mid_lift vmap_true_pos_lift by metis

						hence "\<forall>t \<in> insert (Neg ?v) (snd ?q). \<forall>f \<in> insert (Neg ?v) (snd ?q). \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
							using allF fst assms c'_lift c_elem pop_card pop_ins
							by (metis One_nat_def card.empty empty_not_insert finite_insert insert_iff list.simps(15) one_eq_numeral_iff semiring_norm(83))
						moreover have "insert (Neg ?v) (snd ?q) \<in> set (fst (refc c vars) @ xs)"
							using expand by simp
						ultimately show ?thesis by blast
					qed
				next
					case falsy
					then consider (allT) "(vmap\<up>) l1 \<and> (vmap\<up>) l2 \<and> (vmap\<up>) l3 \<and> (vmap\<up>) l4"
						| (allF) "\<not>(vmap\<up>) l1 \<and> \<not>(vmap\<up>) l2 \<and> \<not>(vmap\<up>) l3 \<and> \<not>(vmap\<up>) l4"
						using cases by arith
					thus ?thesis
					proof cases
						case allT
						hence "(vmap\<up>) (Neg ?v)"
							using falsy vmap_false_neg_lift by metis
						hence "\<forall>t \<in> insert (Neg ?v) (snd ?q). \<forall>f \<in> insert (Neg ?v) (snd ?q). \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
							using allT assms falsy c_elem_alt c'_lift c_elem fst pop_card pop_ins
							by (metis One_nat_def card.empty empty_not_insert finite_insert insert_iff list.simps(15) numeral_eq_one_iff semiring_norm(83))
						moreover have "insert (Neg ?v) (snd ?q) \<in> set (fst (refc c vars) @ xs)"
							using expand by simp
						ultimately show ?thesis by blast
					next
						case allF
						hence "\<not>(vmap\<up>) (Pos ?v)"
							using falsy ex_mid_lift vmap_false_neg_lift by metis

						hence "\<forall>t \<in> {fst ?p, fst ?q, Pos ?v}. \<forall>f \<in> {fst ?p, fst ?q, Pos ?v}. \<not>(vmap\<up>) t \<or> (vmap\<up>) f"
							using allF falsy c_elem_alt c'_lift c_elem fst by blast
						moreover have "{fst ?p, fst ?q, Pos ?v} \<in> set (fst (refc c vars) @ xs)"
							using expand by simp
						ultimately show ?thesis by blast
					qed
				qed
			next
				case rest
				thus ?thesis using c'_lift
					by (metis Un_iff set_append)
			qed
		qed
		thus ?thesis by fast
	next
		case infty
		thus ?thesis using assms(4)
			by (metis Un_iff bot_nat_0.extremum_uniqueI card_eq_0_iff card_gt_0_iff set_ConsD set_append zero_neq_numeral)
	qed
qed


lemma naesat_truthy_card:
	assumes "naesat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite vars" "card c = 4"
					"\<forall>c' \<in> set (c # xs). finite c'"
	shows "\<forall>c' \<in> set (fst (refc c vars) @ xs). 0 < card c'"
	using assms
proof (intro ballI)
	fix c'
	assume "c' \<in> set (fst (refc c vars) @ xs)"
	then consider (fst) "c' \<in> set (fst (refc c vars))"
		| (rest) "c' \<in> set xs"
		by auto
	thus "0 < card c'"
	proof cases
		case fst
			
		let ?p = "pop c"
		let ?q = "pop (snd ?p)"
		let ?v = "fresh vars undefined"

		have expand: "fst (refc c vars) = {fst ?p, fst ?q, Pos ?v} # insert (Neg ?v) (snd ?q) # []"
			unfolding refc_def using assms(4)
			by (simp add: Let_def split: if_splits)

		thus ?thesis using fst assms(4) pop_card pop_ins 
			by (metis One_nat_def card_eq_0_iff emptyE empty_set finite.emptyI finite_insert gr0I insert_not_empty one_eq_numeral_iff semiring_norm(83) set_ConsD zero_neq_numeral)
	next
		case rest
		thus ?thesis using assms(1) naesat_def
			by (meson list.set_intros(2))
	qed
qed


lemma naesat_extend:
	assumes "\<forall>c \<in> set (c # xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f" "vars = idset (\<Union>(set (c # xs)))" "finite vars" "\<forall>c' \<in> set (c # xs). finite c'"
	shows "(\<forall>c \<in> set (c # xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap(fresh vars undefined := True)\<up>) t \<and> \<not>(vmap(fresh vars undefined := True)\<up>) f)
				\<and> (\<forall>c \<in> set (c # xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap(fresh vars undefined := False)\<up>) t \<and> \<not>(vmap(fresh vars undefined := False)\<up>) f)"
	using assms
proof (intro conjI)
	let ?v = "fresh vars undefined"
	define vmap' where vmap': "vmap' = vmap(?v := True)"

	thus "\<forall>c' \<in> set (c # xs). \<exists>t \<in> c'. \<exists>f \<in> c'. (vmap'\<up>) t \<and> \<not> (vmap'\<up>) f"
	proof (intro ballI)
		fix c'
		assume c': "c' \<in> set (c # xs)"
		then obtain t f where t: "t \<in> c'" and t_lift: "(vmap\<up>) t"
										and f: "f \<in> c'" and f_lift: "\<not>(vmap\<up>) f"
			using assms by meson

		hence "(vmap'\<up>) t" and "\<not>(vmap'\<up>) f"
			using vmap' assms c' ex_mid_lift fresh_notIn fun_upd_apply idset_iff vmap_true_pos_lift vmap_false_neg_lift
			by (smt (verit) UnionI ident.cases)+

		thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap'\<up>) t \<and> \<not>(vmap'\<up>) f"
			using t f by blast
	qed
next
	let ?v = "fresh vars undefined"
	define vmap' where vmap': "vmap' = vmap(?v := False)"

	thus "\<forall>c' \<in> set (c # xs). \<exists>t \<in> c'. \<exists>f \<in> c'. (vmap'\<up>) t \<and> \<not> (vmap'\<up>) f"
	proof (intro ballI)
		fix c'
		assume c': "c' \<in> set (c # xs)"
		then obtain t f where t: "t \<in> c'" and t_lift: "(vmap\<up>) t"
										and f: "f \<in> c'" and f_lift: "\<not>(vmap\<up>) f"
			using assms by meson

		hence "(vmap'\<up>) t" and "\<not>(vmap'\<up>) f"
			using vmap' assms c' ex_mid_lift fresh_notIn fun_upd_apply idset_iff vmap_true_pos_lift vmap_false_neg_lift
			by (smt (verit) UnionI ident.cases)+

		thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap'\<up>) t \<and> \<not>(vmap'\<up>) f"
			using t f by blast
	qed
qed


lemma naesat_truthy_checkpoint_aux:
	assumes "naesat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite vars" "card c = 4"
					"\<forall>c' \<in> set (c # xs). finite c'"
	shows "\<exists>vmap. \<forall>c \<in> set (fst (refc c vars) @ xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not>(vmap\<up>) f"
	unfolding naesat_def nae_models_def using assms
proof -
	have a1: "(\<exists>vmap. \<forall>c \<in> set (c # xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not> (vmap\<up>) f)"
		using assms(1) unfolding naesat_def nae_models_def by blast

	then obtain vmap where vmap: "\<forall>c \<in> set (c # xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap\<up>) t \<and> \<not> (vmap\<up>) f"
		by blast

	let ?v = "fresh vars undefined"
	define vmap_l vmap_r where vmap_l: "vmap_l = vmap(?v := True)"
												and vmap_r: "vmap_r = vmap(?v := False)"

	have vmap_extend: "(\<forall>c \<in> set (c # xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap_l\<up>) t \<and> \<not>(vmap_l\<up>) f)
				\<and> (\<forall>c \<in> set (c # xs). \<exists>t \<in> c. \<exists>f \<in> c. (vmap_r\<up>) t \<and> \<not>(vmap_r\<up>) f)"
		apply (subst vmap_l, subst vmap_r)+
		apply (rule naesat_extend)
		using assms vmap unfolding naesat_def nae_models_def
		by auto

	then obtain t f where t: "t \<in> c" and t_lift: "(vmap\<up>) t"
									and f: "f \<in> c" and f_lift: "\<not>(vmap\<up>) f"
		using vmap by auto

	let ?p = "pop c"
	let ?q = "pop (snd ?p)"
	let ?r = "pop (snd ?q)"
	let ?s = "pop (snd ?r)"

	have c_elem_alt: "c = {fst ?p, fst ?q, fst ?r, fst ?s}"
		using assms(4) pop_card pop_ins
		by (smt Suc_eq_numeral card_eq_0_iff finite_insert numeral_2_eq_2 numeral_3_eq_3 pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)

	have v: "Pos ?v \<notin> c \<and> Neg ?v \<notin> c"
		using assms fresh_notIn idset_iff
		by (metis UnionI list.set_intros(1))

	have expand: "fst (refc c vars) = {fst ?p, fst ?q, Pos ?v} # insert (Neg ?v) (snd ?q) # []"
		unfolding refc_def using assms(4)
		by (simp add: Let_def split: if_splits)

	have q: "snd ?q = {fst ?r, fst ?s}"
		using assms(4) pop_card pop_ins 
		by (smt Suc_eq_numeral card_eq_0_iff finite_insert numeral_2_eq_2 numeral_3_eq_3 pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)	

	then consider (0000) "\<not>(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (0001) "\<not>(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		| (0010) "\<not>(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (0011) "\<not>(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		| (0100) "\<not>(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (0101) "\<not>(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		| (0110) "\<not>(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (0111) "\<not>(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		| (1000) "(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (1001) "(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		| (1010) "(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (1011) "(vmap\<up>) (fst ?p) \<and> \<not>(vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		| (1100) "(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (1101) "(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> \<not>(vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		| (1110) "(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> \<not>(vmap\<up>) (fst ?s)"
		| (1111) "(vmap\<up>) (fst ?p) \<and> (vmap\<up>) (fst ?q) \<and> (vmap\<up>) (fst ?r) \<and> (vmap\<up>) (fst ?s)"
		by metis
	thus "\<exists>vmap. \<forall>c\<in>set (fst (refc c vars) @ xs). \<exists>t\<in>c. \<exists>f\<in>c. (vmap\<up>) t \<and> \<not> (vmap\<up>) f"
	proof cases
		case 0000
		thus ?thesis using c_elem_alt t t_lift
			by (metis emptyE insert_iff)
	next
		case 0001
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
			proof cases
				case fst
				hence "\<not>(vmap_l\<up>) (fst ?p)"
					using 0001 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_l\<up>) (Pos ?v)"
					using vmap_l vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					by blast

				have "(vmap_l\<up>) (fst ?s)"
					using 0001 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_l\<up>) (Neg ?v)"
					using vmap_l ex_mid_lift vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 0010
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
			proof cases
				case fst
				hence "\<not>(vmap_l\<up>) (fst ?p)"
					using 0010 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_l\<up>) (Pos ?v)"
					using vmap_l vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					by blast

				have "(vmap_l\<up>) (fst ?r)"
					using 0010 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_l\<up>) (Neg ?v)"
					using vmap_l ex_mid_lift vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 0011
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
			proof cases
				case fst
				hence "\<not>(vmap_l\<up>) (fst ?p)"
					using 0011 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_not_empty)
				moreover have "(vmap_l\<up>) (Pos ?v)"
					using vmap_l vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					by blast

				have "(vmap_l\<up>) (fst ?s)"
					using 0011 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_l\<up>) (Neg ?v)"
					using vmap_l ex_mid_lift vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 0100
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?q)"
					using 0100 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?s)"
					using 0100 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 0101
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?q)"
					using 0101 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?r)"
					using 0101 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 0110
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?q)"
					using 0110 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?s)"
					using 0110 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 0111
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
			proof cases
				case fst
				hence "\<not>(vmap_l\<up>) (fst ?p)"
					using 0111 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_l\<up>) (Pos ?v)"
					using vmap_l vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					by blast

				have "(vmap_l\<up>) (fst ?r)"
					using 0111 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_l\<up>) (Neg ?v)"
					using vmap_l ex_mid_lift vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1000
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?p)"
					using 1000 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?r)"
					using 1000 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1001
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?p)"
					using 1001 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?r)"
					using 1001 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1010
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?p)"
					using 1010 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?s)"
					using 1010 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1011
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
			proof cases
				case fst
				hence "\<not>(vmap_l\<up>) (fst ?q)"
					using 1011 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_l\<up>) (Pos ?v)"
					using vmap_l vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					by blast

				have "(vmap_l\<up>) (fst ?r)"
					using 1011 v c_elem_alt ex_mid_lift fun_upd_apply vmap_l vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_l\<up>) (Neg ?v)"
					using vmap_l ex_mid_lift vmap_true_pos_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_l\<up>) t \<and> \<not> (vmap_l\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1100
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?q)"
					using 1100 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit, del_insts) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?r)"
					using 1100 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1101
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?q)"
					using 1101 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?r)"
					using 1101 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1110
		thus ?thesis
		proof (intro exI ballI)
			fix c'
			assume "c' \<in> set (fst (refc c vars) @ xs)"
	
			then consider (fst) "c' \<in> set (fst (refc c vars))"
				| (rest) "c' \<in> set xs"
				by fastforce
			thus "\<exists>t \<in> c'. \<exists>f \<in> c'. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
			proof cases
				case fst
				hence "(vmap_r\<up>) (fst ?q)"
					using 1110 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift pop_isin
					by (smt (verit, del_insts) ident.elims insert_iff)
				moreover have "\<not>(vmap_r\<up>) (Pos ?v)"
					using vmap_r ex_mid_lift vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have one: "\<exists>t \<in> {fst ?p, fst ?q, Pos ?v}. \<exists>f \<in> {fst ?p, fst ?q, Pos ?v}. (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					by blast

				have "\<not>(vmap_r\<up>) (fst ?s)"
					using 1110 v c_elem_alt ex_mid_lift fun_upd_apply vmap_r vmap_true_pos_lift vmap_false_neg_lift t t_lift
					by (smt (verit) ident.elims insert_iff)
				moreover have "(vmap_r\<up>) (Neg ?v)"
					using vmap_r vmap_false_neg_lift fun_upd_apply
					by metis
				ultimately have two: "\<exists>t \<in> insert (Neg ?v) (snd ?q). \<exists>f \<in> insert (Neg ?v) (snd ?q). (vmap_r\<up>) t \<and> \<not> (vmap_r\<up>) f"
					using q by blast

				thus ?thesis using one two expand fst by auto
			next
				case rest
				thus ?thesis using vmap_extend by simp
			qed
		qed
	next
		case 1111
		thus ?thesis using c_elem_alt f f_lift
			by (metis insertE singletonD)
	qed
qed


lemma naesat_truthy_checkpoint:
	assumes "naesat (c # xs)" "vars = idset (\<Union>(set (c # xs)))" "finite vars" "card c = 4"
					"\<forall>c' \<in> set (c # xs). finite c'"
	shows "naesat (fst (refc c vars) @ xs)"
	using assms naesat_truthy_checkpoint_aux naesat_truthy_card unfolding naesat_def nae_models_def
	by fast


lemma naesat_rotate_append: "naesat (xs @ ys) \<Longrightarrow> naesat (ys @ xs)"
	unfolding naesat_def nae_models_def by auto

lemma refc_rotate_naesat:
	assumes "naesat xs" "\<forall>c \<in> set xs. card c = 4" "n \<le> length xs"
	shows "naesat ((refc_rotate ^^ n) xs)"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have sat_n: "naesat ((refc_rotate ^^ n) xs)"
  	apply (rule Suc.IH)
  	using Suc.prems by auto

  then obtain ys where ys: "(refc_rotate ^^ n) xs = (drop n xs) @ ys"
  	by (metis drop_all nle_le self_append_conv2 ys_drop)

  hence "naesat ((refc_rotate ^^ n) xs) = naesat (drop n xs @ ys)"
  	by simp
	thus "naesat ((refc_rotate ^^ Suc n) xs)"
	proof -
		let ?vars = "idset (\<Union>(set (drop n xs @ ys)))"
		have sat_cp: "naesat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			apply (rule naesat_truthy_checkpoint)
			using Suc.prems sat_n ys apply (metis Cons_eq_appendI drop_eq_Nil2 list.exhaust_sel not_less_eq_eq)
			using Suc.prems apply (metis append_Cons drop_eq_Nil list.collapse not_less_eq_eq)
			using finite_expr_idset naesat_def sat_n ys apply (metis card_ge_0_finite)
			using Suc.prems apply (simp add: Suc_le_lessD hd_drop_conv_nth)
			using Suc.prems naesat_def sat_n ys apply (metis Cons_eq_appendI card_ge_0_finite drop_eq_Nil2 list.collapse not_less_eq_eq)
			done
	
		have sat_ys: "naesat ((refc_rotate ^^ n) xs) \<longleftrightarrow> naesat (drop n xs @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> naesat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> naesat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> naesat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using naesat_rotate_append by fastforce
		also have step4: "... \<longleftrightarrow> naesat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> naesat ((refc_rotate ^^ Suc n) xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "naesat ((refc_rotate ^^ Suc n) xs)"
			using sat_n sat_ys by blast
	qed
qed


lemma refc_rotate_nnaesat:
	assumes "\<not>naesat xs" "\<forall>c \<in> set xs. card c = 4" "n \<le> length xs"
	shows "\<not>naesat ((refc_rotate ^^ n) xs)"
	using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have sat_n: "\<not>naesat ((refc_rotate ^^ n) xs)"
  	apply (rule Suc.IH)
  	using Suc.prems by auto

  then obtain ys where ys: "(refc_rotate ^^ n) xs = (drop n xs) @ ys"
  	by (metis drop_all nle_le self_append_conv2 ys_drop)

  hence "naesat ((refc_rotate ^^ n) xs) = naesat (drop n xs @ ys)"
  	by simp
	thus "\<not>naesat ((refc_rotate ^^ Suc n) xs)"
	proof -
		let ?vars = "idset (\<Union>(set (drop n xs @ ys)))"
		have sat_cp: "\<not>naesat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			apply (rule naesat_falsy_checkpoint)
			using Suc.prems sat_n ys apply (metis Cons_eq_appendI drop_eq_Nil2 list.exhaust_sel not_less_eq_eq)
			using Suc.prems apply (metis append_Cons drop_eq_Nil list.collapse not_less_eq_eq)
			using Suc.prems finite_expr_idset ys refc_rotate_finite apply (metis Suc_leD card.infinite zero_neq_numeral)
			using Suc.prems apply (simp add: Suc_le_lessD hd_drop_conv_nth)
			using Suc.prems ys refc_rotate_finite
			by (metis Cons_eq_appendI Suc_leD Suc_le_lessD card_ge_0_finite drop_eq_Nil2 list.collapse not_less_eq_eq not_numeral_le_zero)
	
		have sat_ys: "\<not>naesat ((refc_rotate ^^ n) xs) \<longleftrightarrow> \<not>naesat (drop n xs @ ys)"
			using ys by simp
		also have step1: "... \<longleftrightarrow> \<not>naesat (hd (drop n xs) # (tl (drop n xs) @ ys))"
			using Suc.prems(3) by (metis Cons_eq_appendI drop_eq_Nil2 hd_Cons_tl not_less_eq_eq)
		also have step2: "... \<longleftrightarrow> \<not>naesat ((fst (refc (hd (drop n xs)) ?vars)) @ (tl (drop n xs) @ ys))"
			using sat_cp calculation sat_n by arith
		also have step3: "... \<longleftrightarrow> \<not>naesat (tl (drop n xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			using naesat_rotate_append by (metis append.assoc)
		also have step4: "... \<longleftrightarrow> \<not>naesat ((drop (Suc n) xs) @ ys @ fst (refc (hd (drop n xs)) ?vars))"
			by (simp add: drop_Suc tl_drop)
		also have "... \<longleftrightarrow> \<not>naesat ((refc_rotate ^^ Suc n) xs)"
			using ys_drop_suc sat_ys ys Suc.prems(3) by (metis Suc_le_lessD)
	
		finally show "\<not>naesat ((refc_rotate ^^ Suc n) xs)"
			using sat_n sat_ys by blast
	qed
qed



lemma refc_rotate_card_eq3:
	assumes "\<forall>c \<in> set xs. finite c" "n \<le> length xs" "\<forall>c \<in> set xs. card c = 4"
	shows "\<forall>c \<in> set (drop (length xs - n) ((refc_rotate ^^ n) xs)). card c = 3"
	using assms
proof (induction n arbitrary: xs)
  case 0
  thus ?case by simp
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
		thus "card c = 3"
		proof cases
			case set_ys
			thm Suc.IH
			have "\<forall>c \<in> set (drop (length xs - n) ((refc_rotate ^^ n) xs)). card c = 3"
				apply (rule Suc.IH)
				using Suc.prems by simp+

			moreover have "c \<in> set (drop (length xs - n) ((refc_rotate ^^ n) xs))"
				using set_ys ys_alt by blast

			ultimately show ?thesis by blast
		next
			case rear

			let ?vars = "idset (\<Union> (set (drop n xs @ ys)))"
			let ?s = "stock (card (hd (drop n xs)) - 3) ?vars"

			have aux1: "set (tl (rev ?s)) \<inter> hd (drop n xs) = {}"
				apply (rule refc_stock_clause_disj)
				unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
				using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
				using Suc.prems apply (simp add: Suc_le_lessD hd_drop_conv_nth)
				using idset_iff Suc.prems apply (smt (verit) UnionI append_is_Nil_conv drop_eq_Nil hd_append2 list.set_sel(1) not_less_eq_eq subset_iff)
				done
	
			have aux2: "last ?s \<notin> set (tl (rev ?s)) \<union> hd (drop n xs)"
				apply (rule refc_init_uniq)
				unfolding refc_def using assms apply (simp add: Let_def split: if_splits)
				using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
				using Suc.prems apply (simp add: Suc_le_lessD hd_drop_conv_nth)
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
				using Suc.prems apply (simp add: Suc_le_lessD hd_drop_conv_nth)
				using Suc.prems finite_expr_idset refc_rotate_finite ys apply (metis Suc_leD)
				using aux2 apply simp
				using aux1 apply simp
				done

			thus ?thesis
				using card.infinite by fastforce
		qed
	qed
qed

term "filter"

definition to_nae3sat :: "('a::fresh) lit set list \<Rightarrow> 'a lit set list"
	where "to_nae3sat expr = (case find (\<lambda>c. card c \<noteq> 4) expr of Some _ \<Rightarrow> [{}] | None \<Rightarrow> to_le3sat expr)"

lemma card_decrement:
	assumes "\<forall>c \<in> set xs. card c = 4"
	shows "\<forall>c \<in> set ((refc_rotate ^^ length xs) xs). card c = 3"
	using assms refc_rotate_card_eq3 drop_0 unfolding nae4sat_def
	by (metis cancel_comm_monoid_add_class.diff_cancel card.infinite dual_order.refl zero_neq_numeral)

lemma nae4sat_nae3sat:
	assumes "nae4sat expr"
	shows "nae3sat (to_nae3sat expr)"
	using assms unfolding nae4sat_def to_nae3sat_def to_le3sat_def
	apply (cases "find (\<lambda>c. card c \<noteq> 4) expr")
	apply (fastforce simp add: refc_rotate_naesat card_decrement nae4sat_def nae3sat_def)
	by (metis (mono_tags, lifting) find_Some_iff nth_mem)

lemma nae3sat_nae4sat_aux:
	assumes "\<not>nae4sat expr" "\<forall>clause \<in> set expr. card clause = 4"
	shows "\<not>naesat (to_nae3sat expr)"
	unfolding to_nae3sat_def to_le3sat_def
	apply (cases "find (\<lambda>c. card c \<noteq> 4) expr")
	using assms nae4sat_def refc_rotate_nnaesat
	by (fastforce simp add: naesat_def)+

lemma nae3sat_nae4sat_card:
	assumes "\<exists>c \<in> set expr. card c \<noteq> 4"
	shows "\<not>nae3sat (to_nae3sat expr)"
	using assms unfolding nae3sat_def to_nae3sat_def to_le3sat_def
	by (cases "find (\<lambda>c. card c \<noteq> 4) expr", auto simp add: find_None_iff)

lemma nae3sat_nae4sat:
	assumes "\<not>nae4sat expr"
	shows "\<not>nae3sat (to_nae3sat expr)"
	using assms nae3sat_nae4sat_aux nae3sat_nae4sat_card
	unfolding nae4sat_def nae3sat_def by blast


definition nae3sat_pset :: "('a :: fresh) lit set list set"
	where "nae3sat_pset = {expr. nae3sat expr}"

lemma nae4sat_reduce_nae3sat: "is_reduction to_nae3sat nae4sat_pset nae3sat_pset"
	unfolding is_reduction_def nae4sat_pset_def nae3sat_pset_def
	using nae4sat_nae3sat nae3sat_nae4sat
	by blast

lemma eq3sat_reduce_nae3sat: "is_reduction (to_nae3sat \<circ> augment) eq3sat_pset nae3sat_pset"
	using eq3sat_reduce_nae4sat nae4sat_reduce_nae3sat by (rule is_reduction_trans)


end