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

lemma "is_reduction augment eq3sat_pset nae4sat_pset"
	unfolding is_reduction_def eq3sat_pset_def nae4sat_pset_def
	using eq3sat_to_nae4sat nae4sat_to_eq3sat
	by blast


lemma
	assumes "nae4sat expr"
	shows "nae3sat (to_le3sat expr)"
	unfolding nae4sat_def nae3sat_def to_le3sat_def
	using assms 








end