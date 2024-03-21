theory PART_MAXCUT
	imports Complex_Main "../Reductions"
begin

definition partition_pset
	where "partition_pset \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs ! i \<in> {0, 1}) \<and> length as = length xs
  				\<and> (\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i * (1 - xs ! i))}"

definition cutset :: "('a * 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a * 'a) set"
	where "cutset E S = {(u, v) | u v. (u, v) \<in> E \<and> u \<in> S \<and> v \<notin> S}"

definition weight :: "('a * 'a) set \<Rightarrow> ('a * 'a \<Rightarrow> real) \<Rightarrow> real"
	where weight_def[simp]: "weight cs w = sum w cs"

definition maxcut_pset :: "(('a * 'a) set * 'a set * ('a * 'a \<Rightarrow> real) * real) set"
	where "maxcut_pset = {(E, V, w, W). \<exists>S. (\<forall>e \<in> E. fst e \<in> V \<and> snd e \<in> V) \<and> S \<subseteq> V \<and> weight (cutset E S) w \<ge> W}"

lemma cutset_expand: "S \<subseteq> V \<Longrightarrow> cutset (V \<times> V) S = S \<times> (V-S)"
	unfolding cutset_def by blast

lemma "\<forall>e \<in> V \<times> V. fst e \<in> V \<and> snd e \<in> V"
	by simp

definition ew :: "nat list \<Rightarrow> nat * nat \<Rightarrow> nat"
	where "ew as p = as ! fst p * as ! snd p"

lemma cutset_weight_split: "sum (ew as) (S \<times> (V-S)) = sum (\<lambda>u. as ! u) S * sum (\<lambda>v. as ! v) (V-S)"
proof -
	have "sum (\<lambda>u. as ! u) S * sum (\<lambda>v. as ! v) (V-S) = sum (\<lambda>u. sum (\<lambda>v. as ! u * as ! v) (V-S)) S"
		using sum_product by blast
	also have "... = sum (\<lambda>(u, v). as ! u * as ! v) (S \<times> (V-S))"
		using sum.cartesian_product by fast
	also have "... = sum (ew as) (S \<times> (V-S))"
		unfolding ew_def by (meson case_prod_beta')
	finally show ?thesis by (subst eq_commute)
qed

lemma cutset_weight_split_general: "sum (ew as) (S \<times> T) = sum ((!) as) S * sum ((!) as) T"
proof -
	have "sum ((!) as) S * sum ((!) as) T = sum (\<lambda>u. sum (\<lambda>v. as ! u * as ! v) T) S"
		using sum_product by blast
	also have "... = sum (\<lambda>(u, v). as ! u * as ! v) (S \<times> T)"
		using sum.cartesian_product by fast
	also have "... = sum (ew as) (S \<times> T)"
		unfolding ew_def by (meson case_prod_beta')
	finally show ?thesis by (subst eq_commute)
qed

lemma cutset_weight_permute: "sum (ew as) (S \<times> (V-S)) = sum (ew as) ((V-S) \<times> S)"
	by (subst cutset_weight_split, subst mult.commute, subst cutset_weight_split_general[symmetric], rule refl)


lemma set_filter_upt: "{i. i < length xs \<and> v = xs ! i} = set (filter (\<lambda>n. xs ! n = v) [0 ..< length xs])"
	by auto

find_theorems "distinct ?xs \<Longrightarrow> sum ?g (set ?xs) = sum_list (map ?g ?xs)"
find_theorems "sum_list ?xs = foldr (+) ?xs 0"
lemma cutset_sum_fold: "sum (\<lambda>u. (as :: nat list) ! u) {i. i < length xs \<and> v = xs ! i} = fold (+) (map (\<lambda>u. as ! u) (filter (\<lambda>n. xs ! n = v) [0 ..< length xs])) 0"
	apply (subgoal_tac "distinct (filter (\<lambda>n. xs ! n = v) [0 ..< length xs])")
	subgoal apply (subst set_filter_upt)
		apply (subst sum.distinct_set_conv_list)
		subgoal by assumption
		subgoal apply (subst sum_list.eq_foldr)
			apply (subst foldr_fold)
			subgoal by fastforce
			subgoal .. . .
	subgoal by (rule distinct_filter, rule distinct_upt).



(*
lemma "i < length (butlast xs) \<Longrightarrow> xs ! i = 1 \<Longrightarrow> butlast xs ! i = 1"
	apply (induction xs arbitrary: i)
	 apply auto
	by (metis Suc_diff_eq_diff_pred Suc_pred length_greater_0_conv not_gr_zero nth_Cons' zero_less_diff)
*)

lemma map_aux: "length xs \<le> length as \<Longrightarrow> \<forall>x \<in> set xs. x < length as \<Longrightarrow> map ((!) (as @ [a])) xs = map ((!) as) xs"
	apply (induction xs arbitrary: as a rule: rev_induct)
	by (auto simp add: nth_append)

lemma map_aux_snd: "length xs \<le> length as \<Longrightarrow> \<forall>x \<in> set xs. snd x < length as \<Longrightarrow> map (\<lambda>i. (as @ [a]) ! snd i) xs = map (\<lambda>i. as ! snd i) xs"
	apply (induction xs arbitrary: as a rule: rev_induct)
	by (auto simp add: nth_append)

lemma filter_eq: "\<forall>x \<in> set xs. P x = Q x \<Longrightarrow> filter P xs = filter Q xs"
	by (induction xs arbitrary: P Q) auto

thm arg_cong
thm map_cong
thm filter_cong

lemma nth_append_set: "xs = xs' @ [x'] \<Longrightarrow> \<forall>i \<in> set [0..<length xs']. xs ! i = xs' ! i"
	by (simp add: nth_append)

lemma cutset_partition_sum:
	assumes "\<forall>x \<in> set (xs :: nat list). x \<in> {0, 1}" "length xs = length as"
	shows "fold (+) (map ((!) as) (filter (\<lambda>i. xs ! i = 1) [0..<length xs])) c = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as)) c"
	using assms
proof (induction as arbitrary: xs c rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc a as)
  then obtain x' xs' where xs: "xs = xs' @ [x']"
  	by (metis length_Suc_conv_rev)
  then consider (one) "x' = 1"
  	| (zero) "x' = 0"
  	using snoc.prems by force
  thus ?case
  proof cases
  	case one
  	hence "fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 1) [0..<length xs])) c = fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 1) [0..<length xs']) @ [(as @ [a]) ! length xs']) c"
  		using xs snoc.prems apply simp by (metis nth_append_length)
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs ! i = 1) [0..<length xs']) @ [(as @ [a]) ! length xs']) c"
  		apply (subst map_aux)
				subgoal using snoc.prems(2) xs
					by (metis diff_zero length_append_singleton length_filter_le length_upt nat.inject)
				subgoal using snoc.prems(2) xs by simp
				subgoal ..
				done
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 1) [0..<length xs']) @ [(as @ [a]) ! length xs']) c"
  		by (subst filter_eq[where ?P = "(\<lambda>i. xs ! i = 1)" and ?Q = "(\<lambda>i. xs' ! i = 1)"])
  			(use nth_append_set xs in fastforce)+
  	also have "... = (fold (+) [(as @ [a]) ! length xs'] \<circ> fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 1) [0..<length xs']))) c"
  		by (subst fold_append, rule refl)
  	also have "... = fold (+) [(as @ [a]) ! length xs'] (fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 1) [0..<length xs'])) c)"
  		by (rule comp_apply)
  	also have "... = fold (+) [(as @ [a]) ! length xs'] (fold (+) (map (\<lambda>x. fst x * snd x) (zip xs' as)) c)"
  		by (subst snoc.IH) (use snoc.prems xs in auto)
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs' as) @ [a]) c"
  		using snoc.prems(2) xs by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs' as) @ map (\<lambda>x. fst x * snd x) [(x', a)]) c"
  		using one by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip (xs' @ [x']) (as @ [a]))) c"
  		by (subst map_append[symmetric], subst zip_append) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs (as @ [a]))) c"
  		by (subst xs, rule refl)
  	finally show ?thesis.
  next
  	case zero
  	hence "fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 1) [0..<length xs])) c = fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 1) [0..<length xs'])) c"
  		using xs snoc.prems apply simp
  		by (metis One_nat_def nth_append_length zero_neq_one)
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs ! i = 1) [0..<length xs'])) c"
  		apply (subst map_aux)
  		subgoal using snoc.prems(2) xs
  			by (metis diff_zero length_append_singleton length_filter_le length_upt nat.inject)
  		subgoal using snoc.prems(2) xs by simp
  		subgoal .. .
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 1) [0..<length xs'])) c"
  		by (subst filter_eq[where ?P = "(\<lambda>i. xs ! i = 1)" and ?Q = "(\<lambda>i. xs' ! i = 1)"])
  			(use nth_append_set xs in fastforce)+
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs' as)) c"
  		by (subst snoc.IH) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs' as) @ map (\<lambda>x. fst x * snd x) [(x', a)]) c"
  		using zero by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip (xs' @ [x']) (as @ [a]))) c"
  		by (subst map_append[symmetric], subst zip_append) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs (as @ [a]))) c"
  		by (subst xs, rule refl)
  	finally show ?thesis.
  qed
qed


lemma cutset_partition_sum_coset:
	assumes "\<forall>x \<in> set (xs :: nat list). x \<in> {0, 1}" "length xs = length as"
	shows "fold (+) (map ((!) as) (filter (\<lambda>i. xs ! i = 0) [0..<length xs])) c = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as)) c"
	using assms
proof (induction as arbitrary: xs c rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc a as)
  then obtain x' xs' where xs: "xs = xs' @ [x']"
  	by (metis length_Suc_conv_rev)
  then consider (one) "x' = 1"
  	| (zero) "x' = 0"
  	using snoc.prems by force
  thus ?case
  proof cases
  	case one
  	hence "fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 0) [0..<length xs])) c = fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 0) [0..<length xs'])) c"
  		using xs snoc.prems apply simp
  		by (metis One_nat_def nth_append_length zero_neq_one)
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs ! i = 0) [0..<length xs'])) c"
  		apply (subst map_aux)
  		subgoal using snoc.prems(2) xs
  			by (metis diff_zero length_append_singleton length_filter_le length_upt nat.inject)
  		subgoal using snoc.prems(2) xs by simp
  		subgoal .. .
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 0) [0..<length xs'])) c"
  		by (subst filter_eq[where ?P = "(\<lambda>i. xs ! i = 0)" and ?Q = "(\<lambda>i. xs' ! i = 0)"])
  			(use nth_append_set xs in fastforce)+
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs' as)) c"
  		by (subst snoc.IH) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs' as) @ map (\<lambda>x. (1 - fst x) * snd x) [(x', a)]) c"
  		using one by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip (xs' @ [x']) (as @ [a]))) c"
  		by (subst map_append[symmetric], subst zip_append) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs (as @ [a]))) c"
  		by (subst xs, rule refl)
  	finally show ?thesis.
  next
  	case zero
  	hence "fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 0) [0..<length xs])) c = fold (+) (map ((!) (as @ [a])) (filter (\<lambda>i. xs ! i = 0) [0..<length xs']) @ [(as @ [a]) ! length xs']) c"
  		using xs snoc.prems apply simp
  		by (metis less_numeral_extra(3) nth_append_length)
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs ! i = 0) [0..<length xs']) @ [(as @ [a]) ! length xs']) c"
  		apply (subst map_aux)
  		subgoal using snoc.prems(2) xs
  			by (metis diff_zero length_append_singleton length_filter_le length_upt nat.inject)
  		subgoal using snoc.prems(2) xs by simp
  		subgoal .. .
  	also have "... = fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 0) [0..<length xs']) @ [(as @ [a]) ! length xs']) c"
  		by (subst filter_eq[where ?P = "(\<lambda>i. xs ! i = 0)" and ?Q = "(\<lambda>i. xs' ! i = 0)"])
  			(use nth_append_set xs in fastforce)+
  	also have "... = (fold (+) [(as @ [a]) ! length xs'] \<circ> fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 0) [0..<length xs']))) c"
  		by (subst fold_append, rule refl)
  	also have "... = fold (+) [(as @ [a]) ! length xs'] (fold (+) (map ((!) as) (filter (\<lambda>i. xs' ! i = 0) [0..<length xs'])) c)"
  		by (rule comp_apply)
  	also have "... = fold (+) [(as @ [a]) ! length xs'] (fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs' as)) c)"
  		by (subst snoc.IH) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs' as) @ [a]) c"
  		using snoc.prems(2) xs by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs' as) @ map (\<lambda>x. (1 - fst x) * snd x) [(x', a)]) c"
  		using zero by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip (xs' @ [x']) (as @ [a]))) c"
  		by (subst map_append[symmetric], subst zip_append) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs (as @ [a]))) c"
  		by (subst xs, rule refl)
  	finally show ?thesis.
  qed
qed


lemma cond_max:
	assumes "x + y = (c :: real)" "0 \<le> x" "0 \<le> y"
	shows "(c/2)\<^sup>2 \<ge> x*y"
	using assms arith_geo_mean_sqrt sqrt_le_D by blast

lemma cond_max_iff:
	assumes "x + y = (c :: real)" "0 \<le> x" "0 \<le> y" "x \<noteq> y"
	shows "(c/2)\<^sup>2 > x*y"
	using assms
proof -
	have diff_sq_neq: "(x - y)\<^sup>2 > 0"
		using assms(4) by simp

	have "4*x*y = (x + y)\<^sup>2 - (x - y)\<^sup>2"
		by algebra
	hence "4*x*y = c\<^sup>2 - (x - y)\<^sup>2"
		using assms(1) by simp
	hence "4*x*y < c\<^sup>2"
		using diff_sq_neq by simp
	hence "x*y < c\<^sup>2/4"
		by simp
	hence "x*y < (c/2)\<^sup>2"
		by (simp add: numeral_eq_Suc)
	thus ?thesis by simp
qed

lemma cond_max_iff_real:
	assumes "x + y = (c :: real)" "0 \<le> x" "0 \<le> y" "x \<noteq> y"
	shows "(real c/2)\<^sup>2 > real (x*y)"
	using assms cond_max_iff by fastforce

(*
lemma "\<Union>{{u, v} | u v. u \<noteq> v \<and> u \<in> V \<and> v \<in> V} \<subseteq> V"
	by blast

lemma "\<forall>e \<in> {{u, v} | u v. u \<noteq> v \<and> u \<in> V \<and> v \<in> V}. card e = 2"
	by fastforce
*)

lemma a:
	assumes "\<forall>i < length xs. xs ! i \<in> {0, 1}"
	shows "{i. i < length xs \<and> xs ! i = 1} \<subseteq> {0 ..< length xs}"
	using assms by fastforce

lemma set_filter: "{(v, i) | i. i < length xs \<and> xs ! i = v} = set (filter (\<lambda>n. fst n = v) (zip xs [0 ..< length xs]))" 
proof (induction xs arbitrary: v rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc a xs)
  thm snoc.IH
  then consider (eq) "a = v"
  	| (neq) "a \<noteq> v"
  	by arith
  thus ?case
  proof cases
  	case eq
  	hence "set (filter (\<lambda>n. fst n = v) (zip (xs @ [a]) [0 ..< length (xs @ [a])])) = insert (a, length xs) (set (filter (\<lambda>n. fst n = v) (zip xs [0..<length xs])))"
  		by auto
  	also have "... = insert (a, length xs) {(v, i) | i. i < length xs \<and> xs ! i = v}"
  		by (subst snoc.IH, rule refl)
  	also have "... = insert (v, length xs) {(v, i) | i. i < length xs \<and> xs ! i = v}"
  		by (subst eq, rule refl)
  	also have "... = {(v, i) | i. i < length (xs @ [a]) \<and> (xs @ [a]) ! i = v}"
  		apply auto
  		subgoal by (rule eq)
  		subgoal by (simp add: nth_append)
  		subgoal by (metis less_SucE nth_append).
  	finally show ?thesis by simp
  next
  	case neq
  	hence "set (filter (\<lambda>n. fst n = v) (zip (xs @ [a]) [0 ..< length (xs @ [a])])) = set (filter (\<lambda>n. fst n = v) (zip xs [0..<length xs]))"
  		by auto
  	also have "... = {(v, i) | i. i < length xs \<and> xs ! i = v}"
  		by (subst snoc.IH, rule refl)
  	also have "... = {(v, i) | i. i < length (xs @ [a]) \<and> (xs @ [a]) ! i = v}"
  		apply auto
  		subgoal by (simp add: nth_append)
  		subgoal using neq by (metis less_SucE nth_append_length)
  		subgoal by (metis \<open>\<And>i. \<lbrakk>i < Suc (length xs); v = (xs @ [a]) ! i\<rbrakk> \<Longrightarrow> i < length xs\<close> nth_append).
  	finally show ?thesis by simp
  qed
qed

lemma "set (filter (\<lambda>n. fst n = 1) (zip xs [0 ..< length xs])) \<subseteq> set (zip xs [0 ..< length xs])"
	by (rule filter_is_subset)

lemma "snd ` {(v, i) | i. i < length xs \<and> xs ! i = v} = {i. i < length xs \<and> xs ! i = v}"
	by force

lemma "sum snd {(v, i) | i. i < length xs \<and> xs ! i = v} = fold (+) (map snd (filter (\<lambda>n. fst n = v) (zip xs [0 ..< length xs]))) 0"
	apply (subst eq_commute)
	apply (subst foldr_fold[symmetric])
	subgoal by fastforce
	subgoal
		apply (subst sum_list.eq_foldr[symmetric])
		apply (subgoal_tac "distinct (filter (\<lambda>n. fst n = v) (zip xs [0..<length xs]))")
		subgoal
			apply (subst sum.distinct_set_conv_list[symmetric])
			subgoal by assumption
			subgoal apply (subst set_filter[symmetric]) by metis.
		subgoal by (rule distinct_filter, rule distinct_zipI2, rule distinct_upt).
	.

lemma aux_upt_set: "set [0..<length l] = {..<length l}"
	by auto

lemma partition_sum_zip:
	assumes "length as = length xs"
	shows "(\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length (zip xs as). snd ((zip xs as) ! i) * fst ((zip xs as) ! i))"
	using assms by simp

lemma partition_sum_map: "(\<Sum>i < length l. fst (l ! i) * snd (l ! i)) = (\<Sum>i < length l. (map (\<lambda>x. fst x * snd x) l ! i))"
	by simp

lemma partition_sum_fold_rev: "(\<Sum>i < length l. (map (\<lambda>x. fst x * snd x) l ! i)) = fold (+) (rev (map (\<lambda>x. fst x * snd x) l)) 0"
	apply (subst fold_plus_sum_list_rev[where ?xs = "rev (map (\<lambda>x. fst x * snd x) l)"])
	apply (subst rev_rev_ident)
	apply (subgoal_tac "distinct [0..<length l]")
	subgoal
		apply (subst aux_upt_set[symmetric])
		apply (subst sum.distinct_set_conv_list[where ?g = "(!) (map (\<lambda>x. fst x * snd x) l)" and ?xs = "[0..<length l]"])
		subgoal by assumption
		subgoal 
			apply (subst length_map[symmetric, where ?f = "(\<lambda>x. fst x * snd x)"])
			apply (subst map_nth[where ?xs = "map (\<lambda>x. fst x * snd x) l"])
			apply (subst add_0_right)
			by (rule refl).
	subgoal by (rule distinct_upt).

lemma partition_sum_fold_aux: "foldr (+) (map (\<lambda>x. fst x * snd x) (zip (xs :: nat list) as)) = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as))"
	by (rule foldr_fold) auto

lemma partition_sum_fold:
	assumes "length (as :: nat list) = length (xs :: nat list)"
	shows "(\<Sum>i < length as. as ! i * xs ! i) = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as)) 0"
	using assms
proof -
	have "(\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length (zip xs as). snd ((zip xs as) ! i) * fst ((zip xs as) ! i))"
		by (insert assms, erule partition_sum_zip)
	also have "... = (\<Sum>i < length (zip xs as). (map (\<lambda>x. fst x * snd x) (zip xs as) ! i))"
		apply (insert partition_sum_map[where ?l = "zip xs as"])
		apply (subst mult.commute)
		by assumption
	also have "... = fold (+) (rev (map (\<lambda>x. fst x * snd x) (zip xs as))) 0"
		by (rule partition_sum_fold_rev)
	also have "... = foldr (+) (map (\<lambda>x. fst x * snd x) (zip xs as)) 0"
		by (subst foldr_conv_fold[symmetric], rule refl)
	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as)) 0"
		by (subst partition_sum_fold_aux, rule refl)
	finally show ?thesis.
qed


lemma partition_sum_cutset:
	assumes "\<forall>x \<in> set (xs :: nat list). x \<in> {0, 1}" "length as = length xs"
	shows "fold (+) (map (snd) (filter (\<lambda>p. fst p = 1) (zip xs as))) c = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as)) c"
	using assms
proof (induction xs arbitrary: as c)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  then obtain as' a' where as: "as = a' # as'"
  	by (metis Suc_length_conv)

  then consider (one) "x = 1"
  	| (zero) "x = 0"
  	using Cons.prems by force
  thus ?case
  proof cases
  	case one
  	hence "fold (+) (map snd (filter (\<lambda>p. fst p = 1) (zip (x # xs) as))) c = fold (+) (map snd (filter (\<lambda>p. fst p = 1) ((x, a') # zip xs as'))) c"
  		using as Cons.prems by simp
  	also have "... = fold (+) (a' # (map snd (filter (\<lambda>p. fst p = 1) (zip xs as')))) c"
  		using one by simp
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = 1) (zip xs as'))) (a' + c)"
  		by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as')) (a' + c)"
  		by (rule Cons.IH) (use as Cons.prems in simp_all)
  	also have "... = fold (+) (a' # map (\<lambda>x. fst x * snd x) (zip xs as')) c"
  		by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip (x # xs) (a' # as'))) c"
  		using one by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip (x # xs) as)) c"
  		by (subst as, rule refl)
  	finally show ?thesis.
  next
  	case zero
  	hence "fold (+) (map snd (filter (\<lambda>p. fst p = 1) (zip (x # xs) as))) c = fold (+) (map snd (filter (\<lambda>p. fst p = 1) ((x, a') # zip xs as'))) c"
  		using as Cons.prems by simp
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = 1) (zip xs as'))) c"
  		using zero by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as')) c"
  		by (rule Cons.IH) (use as Cons.prems in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip (x # xs) (a' # as'))) c"
  		using zero by simp
  	also have "... = fold (+) (map (\<lambda>x. fst x * snd x) (zip (x # xs) as)) c"
  		by (subst as, rule refl)
  	finally show ?thesis.
  qed
qed


lemma cutset_sum_upt:
	assumes "length (as :: nat list) = length (xs :: nat list)" "\<forall>x \<in> set xs. x \<in> {0, 1}"
	shows "fold (+) (map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs [0 ..< length xs]))) c = fold (+) (map snd (filter (\<lambda>p. fst p = v) (zip xs as))) c"
	using assms
proof (induction as arbitrary: xs c v rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc a as)
  then obtain xs' x' where xs: "xs = xs' @ [x']"
  	by (metis length_Suc_conv_rev)

  then consider (one) "x' = v"
  	| (zero) "x' \<noteq> v"
  	using snoc.prems by force
  thus ?case
  proof cases
  	case one
  	hence "fold (+) (map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs [0..<length xs]))) c = fold (+) (map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])) @ [(as @ [a]) ! (length xs')]) c"
  		using snoc.prems xs by simp
  	also have "... = fold (+) (map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])) @ [(as @ [a]) ! (length xs')]) c"
  		apply (subst map_cong[where ?ys = "filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])" and ?g = "\<lambda>i. as ! snd i"])
  		subgoal by (rule refl)
  		subgoal using xs snoc.prems filter_set
  			by (metis add_right_imp_eq in_set_zipE length_append list.size(4) member_filter nth_append_set prod.collapse)
  		subgoal .. .
  	also have "... = (fold (+) [(as @ [a]) ! (length xs')] \<circ> fold (+) (map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])))) c"
  		by (subst fold_append, rule refl)
  	also have "... = fold (+) [(as @ [a]) ! (length xs')] (fold (+) (map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs']))) c)"
  		by (subst comp_apply, rule refl)
  	also have "... = fold (+) [(as @ [a]) ! (length xs')] (fold (+) (map snd (filter (\<lambda>p. fst p = v) (zip xs' as))) c)"
  		by (subst snoc.IH) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) ((map snd (filter (\<lambda>p. fst p = v) (zip xs' as))) @ (map snd [(x', a)])) c"
  		using snoc.prems xs by (simp add: nth_append)
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = v) (zip (xs' @ [x']) (as @ [a])))) c"
  		by (subst map_append[symmetric], subst zip_append) (use snoc.prems xs one in simp_all)
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = v) (zip xs (as @ [a])))) c"
  		by (subst xs, rule refl)
  	finally show ?thesis.
  next
  	case zero
  	hence "fold (+) (map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs [0..<length xs]))) c = fold (+) (map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs']))) c"
  		using snoc.prems xs by simp
  	also have "... = fold (+) (map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs']))) c"
  		apply (subst map_cong[where ?ys = "filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])" and ?g = "\<lambda>i. as ! snd i"])
  		subgoal by (rule refl)
  		subgoal using xs snoc.prems filter_set
  			by (metis add_right_imp_eq in_set_zipE length_append list.size(4) member_filter nth_append_set prod.collapse)
  		subgoal .. .
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = v) (zip xs' as))) c"
  		by (subst snoc.IH) (use snoc.prems xs in simp_all)
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = v) (zip (xs' @ [x']) (as @ [a])))) c"
  		using snoc.prems xs zero by simp
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = v) (zip xs (as @ [a])))) c"
  		by (subst xs, rule refl)
  	finally show ?thesis.
  qed
qed


lemma cutset_sum_map:
	assumes "length (as :: nat list) = length (xs :: nat list)" "\<forall>x \<in> set xs. x \<in> {0, 1}"
	shows "map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs [0 ..< length xs])) = map ((!) as) (filter (\<lambda>n. xs ! n = v) [0..<length xs])"
	using assms
proof (induction as arbitrary: xs v rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc a as)
  then obtain xs' x' where xs: "xs = xs' @ [x']"
  	by (metis length_Suc_conv_rev)

  then consider (one) "x' = v"
  	| (zero) "x' \<noteq> v"
  	using snoc.prems by force
  thus ?case
  proof cases
  	case one
  	hence "map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs [0..<length xs])) = map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])) @ [(as @ [a]) ! length xs']"
  		using snoc.prems xs by simp
  	also have "... = map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])) @ [(as @ [a]) ! length xs']"
  		apply (subst map_cong[where ?ys = "filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])" and ?g = "\<lambda>i. as ! snd i"])
  		subgoal ..
  		subgoal using xs snoc.prems filter_set
  			by (metis add_right_imp_eq in_set_zipE length_append list.size(4) member_filter nth_append_set prod.collapse)
  		subgoal .. .
  	also have "... = map ((!) as) (filter (\<lambda>n. xs' ! n = v) [0..<length xs']) @ [(as @ [a]) ! length xs']"
  		by (subst snoc.IH) (use xs snoc.prems in simp_all)
  	also have "... = map ((!) as) (filter (\<lambda>n. xs ! n = v) [0..<length xs']) @ [(as @ [a]) ! length xs']"
  		by (subst filter_eq[where ?Q = "\<lambda>n. xs ! n = v"]) (use xs snoc.prems nth_append_set in fastforce)+
  	also have "... = map ((!) (as @ [a])) (filter (\<lambda>n. xs ! n = v) [0..<length xs']) @ [(as @ [a]) ! length xs']"
  		apply (subst map_cong[where ?ys = "filter (\<lambda>n. xs ! n = v) [0..<length xs']" and ?g = "(!) (as @ [a])"])
  		subgoal ..
  		subgoal using xs snoc.prems filter_set
  			by (metis add_right_imp_eq length_append list.size(4) member_filter nth_append_set)
  		subgoal .. .
  	also have "... = map ((!) (as @ [a])) (filter (\<lambda>n. xs ! n = v) [0..<length xs'] @ [length xs'])"
  		by simp
  	also have "... = map ((!) (as @ [a])) (filter (\<lambda>n. xs ! n = v) [0..<length xs])"
  		using one xs by (simp add: nth_append_set)
  	finally show ?thesis.
  next
  	case zero
  	hence "map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs [0..<length xs])) = map (\<lambda>i. (as @ [a]) ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs']))"
  		using snoc.prems xs by simp
  	also have "... = map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs']))"
  		apply (subst map_cong[where ?ys = "filter (\<lambda>n. fst n = v) (zip xs' [0..<length xs'])" and ?g = "\<lambda>i. as ! snd i"])
  		subgoal ..
  		subgoal using xs snoc.prems filter_set
  			by (metis add_right_imp_eq in_set_zipE length_append list.size(4) member_filter nth_append_set prod.collapse)
  		subgoal .. .
  	also have "... = map ((!) as) (filter (\<lambda>n. xs' ! n = v) [0..<length xs'])"
  		by (subst snoc.IH) (use xs snoc.prems in simp_all)
  	also have "... = map ((!) as) (filter (\<lambda>n. xs ! n = v) [0..<length xs'])"
  		by (subst filter_eq[where ?Q = "\<lambda>n. xs ! n = v"]) (use xs snoc.prems nth_append_set in fastforce)+
  	also have "... = map ((!) (as @ [a])) (filter (\<lambda>n. xs ! n = v) [0..<length xs'])"
  		apply (subst map_cong[where ?ys = "filter (\<lambda>n. xs ! n = v) [0..<length xs']" and ?g = "(!) (as @ [a])"])
  		subgoal ..
  		subgoal using xs snoc.prems filter_set
  			by (metis add_right_imp_eq length_append list.size(4) member_filter nth_append_set)
  		subgoal .. .
  	also have "... = map ((!) (as @ [a])) (filter (\<lambda>n. xs ! n = v) [0..<length xs])"
  		using zero xs by (simp add: nth_append_set)
  	finally show ?thesis.
  qed
qed

lemma partition_cutset_sum_full:
	assumes "length (as :: nat list) = length (xs :: nat list)" "\<forall>x \<in> set xs. x \<in> {0, 1}"
	shows "(\<Sum>i < length as. as ! i * xs ! i) = sum (\<lambda>u. as ! u) {i. i < length xs \<and> 1 = xs ! i}"
	using assms
proof -
	have "(\<Sum>i < length as. as ! i * xs ! i) = fold (+) (map (\<lambda>x. fst x * snd x) (zip xs as)) 0"
		by (insert assms, erule partition_sum_fold)
	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = 1) (zip xs as))) 0"
		by (insert assms, erule(1) partition_sum_cutset[symmetric])
	also have "... = fold (+) (map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = 1) (zip xs [0 ..< length xs]))) 0"
		by (insert assms, erule cutset_sum_upt[symmetric])
	also have "... = fold (+) (map ((!) as) (filter (\<lambda>n. xs ! n = 1) [0..<length xs])) 0"
		by (insert assms, subst cutset_sum_map) simp_all
	also have "... = sum (\<lambda>u. as ! u) {i. i < length xs \<and> 1 = xs ! i}"
		by (subst cutset_sum_fold, rule refl)
	finally show ?thesis.
qed
		






lemma partition_sum_zip_coset:
	assumes "length as = length xs"
	shows "(\<Sum>i < length as. as ! i * (1 - xs ! i)) = (\<Sum>i < length (zip xs as). snd ((zip xs as) ! i) * (1 - fst ((zip xs as) ! i)))"
	using assms by simp

lemma partition_sum_map_coset: "(\<Sum>i < length l. (1 - fst (l ! i)) * snd (l ! i)) = (\<Sum>i < length l. (map (\<lambda>x. (1 - fst x) * snd x) l ! i))"
	by simp

lemma partition_sum_fold_rev_coset: "(\<Sum>i < length l. (map (\<lambda>x. (1 - fst x) * snd x) l ! i)) = fold (+) (rev (map (\<lambda>x. (1 - fst x) * snd x) l)) 0"
	apply (subst fold_plus_sum_list_rev[where ?xs = "rev (map (\<lambda>x. (1 - fst x) * snd x) l)"])
	apply (subst rev_rev_ident)
	apply (subgoal_tac "distinct [0..<length l]")
	subgoal
		apply (subst aux_upt_set[symmetric])
		apply (subst sum.distinct_set_conv_list[where ?g = "(!) (map (\<lambda>x. (1 - fst x) * snd x) l)" and ?xs = "[0..<length l]"])
		subgoal by assumption
		subgoal 
			apply (subst length_map[symmetric, where ?f = "(\<lambda>x. (1 - fst x) * snd x)"])
			apply (subst map_nth[where ?xs = "map (\<lambda>x. (1 - fst x) * snd x) l"])
			apply (subst add_0_right)
			by (rule refl).
	subgoal by (rule distinct_upt).


lemma partition_sum_fold_aux_coset: "foldr (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip (xs :: nat list) as)) = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as))"
	by (rule foldr_fold) auto

lemma partition_sum_fold_coset:
	assumes "length (as :: nat list) = length (xs :: nat list)"
	shows "(\<Sum>i < length as. as ! i * (1 - (xs ! i))) = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as)) 0"
	using assms
proof -
	have "(\<Sum>i < length as. as ! i * (1 - (xs ! i))) = (\<Sum>i < length (zip xs as). snd ((zip xs as) ! i) * (1 - fst ((zip xs as) ! i)))"
		by (insert assms, erule partition_sum_zip_coset)
	also have "... = (\<Sum>i < length (zip xs as). (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as) ! i))"
		apply (insert partition_sum_map_coset[where ?l = "zip xs as"])
		apply (subst mult.commute)
		by assumption
	also have "... = fold (+) (rev (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as))) 0"
		by (rule partition_sum_fold_rev_coset)
	also have "... = foldr (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as)) 0"
		by (subst foldr_conv_fold[symmetric], rule refl)
	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as)) 0"
		by (subst partition_sum_fold_aux_coset, rule refl)
	finally show ?thesis.
qed


lemma partition_sum_cutset_coset:
	assumes "\<forall>x \<in> set (xs :: nat list). x \<in> {0, 1}" "length as = length xs"
	shows "fold (+) (map (snd) (filter (\<lambda>p. fst p = 0) (zip xs as))) c = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as)) c"
	using assms
proof (induction xs arbitrary: as c)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  then obtain as' a' where as: "as = a' # as'"
  	by (metis Suc_length_conv)

  then consider (one) "x = 1"
  	| (zero) "x = 0"
  	using Cons.prems by force
  thus ?case
  proof cases
  	case one
  	hence "fold (+) (map snd (filter (\<lambda>p. fst p = 0) (zip (x # xs) as))) c = fold (+) (map snd (filter (\<lambda>p. fst p = 0) ((x, a') # zip xs as'))) c"
  		using as Cons.prems by simp
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = 0) (zip xs as'))) c"
  		using one by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as')) c"
  		by (rule Cons.IH) (use as Cons.prems in simp_all)
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x)* snd x) (zip (x # xs) (a' # as'))) c"
  		using one by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip (x # xs) as)) c"
  		by (subst as, rule refl)
  	finally show ?thesis.
  next
  	case zero
  	hence "fold (+) (map snd (filter (\<lambda>p. fst p = 0) (zip (x # xs) as))) c = fold (+) (map snd (filter (\<lambda>p. fst p = 0) ((x, a') # zip xs as'))) c"
  		using as Cons.prems by simp
  	also have "... = fold (+) (a' # (map snd (filter (\<lambda>p. fst p = 0) (zip xs as')))) c"
  		using zero by simp
  	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = 0) (zip xs as'))) (a' + c)"
  		by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as')) (a' + c)"
  		by (rule Cons.IH) (use as Cons.prems in simp_all)
  	also have "... = fold (+) (a' # map (\<lambda>x. (1 - fst x) * snd x) (zip xs as')) c"
  		by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip (x # xs) (a' # as'))) c"
  		using zero by simp
  	also have "... = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip (x # xs) as)) c"
  		by (subst as, rule refl)
  	finally show ?thesis.
  qed
qed


lemma partition_cutset_sum_full_coset:
	assumes "length (as :: nat list) = length (xs :: nat list)" "\<forall>x \<in> set xs. x \<in> {0, 1}"
	shows "(\<Sum>i < length as. as ! i * (1 - xs ! i)) = sum (\<lambda>v. as ! v) {i. i < length xs \<and> 0 = xs ! i}"
	using assms
proof -
	have "(\<Sum>i < length as. as ! i * (1 - xs ! i)) = fold (+) (map (\<lambda>x. (1 - fst x) * snd x) (zip xs as)) 0"
		by (insert assms, erule partition_sum_fold_coset)
	also have "... = fold (+) (map snd (filter (\<lambda>p. fst p = 0) (zip xs as))) 0"
		by (insert assms, erule(1) partition_sum_cutset_coset[symmetric])
	also have "... = fold (+) (map (\<lambda>i. as ! snd i) (filter (\<lambda>n. fst n = 0) (zip xs [0 ..< length xs]))) 0"
		by (insert assms, erule cutset_sum_upt[symmetric])
	also have "... = fold (+) (map ((!) as) (filter (\<lambda>n. xs ! n = 0) [0..<length xs])) 0"
		by (insert assms, subst cutset_sum_map) simp_all
	also have "... = sum (\<lambda>v. as ! v) {i. i < length xs \<and> 0 = xs ! i}"
		by (subst cutset_sum_fold, rule refl)
	finally show ?thesis.
qed


lemma v_min_s:
	assumes "\<forall>x \<in> set (xs :: nat list). x \<in> {0, 1}"
	shows "{..< length xs} - {i. i < length xs \<and> 0 = xs ! i} = {i. i < length xs \<and> 1 = xs ! i}"
	using assms nth_mem by fastforce

lemma v_min_s_alt:
	assumes "\<forall>x \<in> set (xs :: nat list). x \<in> {0, 1}"
	shows "{..< length xs} - {i. i < length xs \<and> 1 = xs ! i} = {i. i < length xs \<and> 0 = xs ! i}"
	using assms nth_mem by fastforce

lemma cutset_weight_partition:
	assumes "\<forall>x \<in> set xs. x \<in> {0, 1}" "length (as :: nat list) = length (xs :: nat list)"
	shows "sum (ew as) ({i. i < length xs \<and> 0 = xs ! i} \<times> {i. i < length xs \<and> 1 = xs ! i}) = (\<Sum>i < length as. as ! i * xs ! i) * (\<Sum>i < length as. as ! i * (1 - xs ! i))"
	using assms v_min_s cutset_weight_split[where ?S = "{i. i < length xs \<and> 0 = xs ! i}" and ?V = "{..< length xs}"]
		partition_cutset_sum_full partition_cutset_sum_full_coset
	by simp

lemma cutset_weight_iff:
	assumes "\<forall>x \<in> set xs. x \<in> {0, 1}" "length (as :: nat list) = length (xs :: nat list)"
	shows "(\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i * (1 - xs ! i)) \<longleftrightarrow> sum ((!) as) {i. i < length xs \<and> 0 = xs ! i} = sum ((!) as) {i. i < length xs \<and> 1 = xs ! i}"
	using assms v_min_s cutset_weight_split[where ?S = "{i. i < length xs \<and> 0 = xs ! i}" and ?V = "{..< length xs}"]
		partition_cutset_sum_full partition_cutset_sum_full_coset
	by arith

lemma partition_sum:
	assumes "\<forall>x \<in> set xs. x \<in> {0, 1}" "length (as :: nat list) = length (xs :: nat list)"
	shows "(\<Sum>i < length as. as ! i * xs ! i) + (\<Sum>i < length as. as ! i * (1 - xs ! i)) = (\<Sum>i < length as. as ! i)"
	using assms
proof -
	have aux: "\<forall>i < length as. (xs ! i + (1 - xs ! i)) = 1"
		apply (intro allI impI)
		apply (case_tac "xs ! i = 0")
		using assms nth_mem by fastforce+

	have "(\<Sum>i < length as. as ! i * xs ! i) + (\<Sum>i < length as. as ! i * (1 - xs ! i)) = (\<Sum>i < length as. as ! i * xs ! i + as ! i * (1 - xs ! i))"
		by (subst sum.distrib, rule refl)
	also have "... = (\<Sum>i < length as. as ! i * (xs ! i + (1 - xs ! i)))"
		by (subst distrib_left[symmetric], rule refl)
	also have "... = (\<Sum>i < length as. as ! i * 1)"
		using aux by simp
	also have "... = (\<Sum>i < length as. as ! i)"
		by simp
	finally show ?thesis.
qed

definition partition_maxcut :: "nat list \<Rightarrow> (nat \<times> nat) set \<times> nat set \<times> (nat \<times> nat \<Rightarrow> real) \<times> real"
	where "partition_maxcut as = ({..< length as} \<times> {..< length as}, {..< length as}, real \<circ> ew as, (\<Sum>i < length as. as ! i)\<^sup>2 / 4)"

lemma "is_reduction partition_maxcut partition_pset maxcut_pset"
	unfolding is_reduction_def
proof (intro allI)
	fix as
	show "as \<in> partition_pset = (partition_maxcut as \<in> maxcut_pset)"
	proof (intro iffI)
		assume "as \<in> partition_pset"

		hence "\<exists>xs. (\<forall>i < length xs. xs ! i \<in> {0, 1}) \<and> length as = length xs
  				\<and> (\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i * (1 - xs ! i))"
  		unfolding partition_pset_def by simp

  	then obtain xs where bit: "\<forall>i < length xs. xs ! i \<in> {0, 1}" and len: "length as = length xs"
  									and partition: "(\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i * (1 - xs ! i))"
  		by blast

  	have twice: "2 * (\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i)"
  		apply (subst mult_2, subst (2) partition, insert bit len)
  		by (rule partition_sum) (use in_set_conv_nth in metis)+

  	hence div: "(\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i)/2"
  		by arith

		thus "partition_maxcut as \<in> maxcut_pset"
			unfolding partition_maxcut_def maxcut_pset_def
		proof (intro CollectI case_prodI)
			obtain S where S: "S = {i. i < length xs \<and> 0 = xs ! i}"
				by simp
			show "\<exists>S. (\<forall>e \<in> {..< length as} \<times> {..< length as}. fst e \<in> {..< length as} \<and> snd e \<in> {..< length as})
								\<and> S \<subseteq> {..< length as}
								\<and> (sum ((!) (map real as)) {..<length as})\<^sup>2 / 4 \<le> weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as)"
      proof (intro exI conjI) 
      	show "\<forall>e \<in> {..< length as} \<times> {..< length as}. fst e \<in> {..< length as} \<and> snd e \<in> {..< length as}"
      		by simp
      next
      	show "S \<subseteq> {..< length as}"
      		using S len by fastforce
      next
      	show "(sum ((!) (map real as)) {..<length as})\<^sup>2 / 4 \<le> weight (cutset ({..<length as} \<times> {..<length as}) S) (real \<circ> ew as)"
      	proof -
      		define V where V: "V = {..< length as}"
      		have "weight (cutset ({..<length as} \<times> {..<length as}) S) (real \<circ> ew as) = weight (S \<times> (V - S)) (real \<circ> ew as)"
      			by (subst cutset_expand) (use S V len in fastforce)+
      		also have "... = sum (ew as) (S \<times> (V - S))"
      			by (smt comp_apply of_nat_sum sum.cong weight_def)
      		also have "... = sum (ew as) ({i. i < length xs \<and> 0 = xs ! i} \<times> ({..<length xs} - {i. i < length xs \<and> 0 = xs ! i}))"
      			unfolding S V using len by fastforce
      		also have "... = (\<Sum>i < length as. as ! i * xs ! i) * (\<Sum>i < length as. as ! i * (1 - xs ! i))"
      			apply (insert bit, subst v_min_s)
      			subgoal by (metis in_set_conv_nth)
      			subgoal apply (subst cutset_weight_partition)
      				subgoal by (metis in_set_conv_nth)
      				subgoal by (rule len)
      				subgoal .. . .
      		also have "... = (\<Sum>i < length as. as ! i * xs ! i) * (\<Sum>i < length as. as ! i * xs ! i)"
      			by (subst partition[symmetric], rule refl)
      		also have "... = ((\<Sum>i < length as. as ! i)/2) * ((\<Sum>i < length as. as ! i)/2)"
      			using div by (smt of_nat_mult)
      		also have "... = (\<Sum>i < length as. as ! i)\<^sup>2 / 4"
      			by (simp add: power2_eq_square)
      		finally show ?thesis by simp
      	qed
      qed
    qed
	next
		assume a: "partition_maxcut as \<in> maxcut_pset"

		hence "({..< length as} \<times> {..< length as}, {..< length as}, real \<circ> ew as, (\<Sum>i < length as. as ! i)\<^sup>2 / 4)
						\<in> {(E, V, w, W). \<exists>S. (\<forall>e \<in> E. fst e \<in> V \<and> snd e \<in> V) \<and> S \<subseteq> V \<and> weight (cutset E S) w \<ge> W}"
			using a unfolding partition_maxcut_def maxcut_pset_def by simp

		hence "\<exists>S. (\<forall>e \<in> ({..< length as} \<times> {..< length as}). fst e \<in> {..< length as} \<and> snd e \<in> {..< length as})
						\<and> S \<subseteq> {..< length as}
						\<and> weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as) \<ge> (\<Sum>i < length as. as ! i)\<^sup>2 / 4"
			by simp

		then obtain S where s_edges: "\<forall>e \<in> ({..< length as} \<times> {..< length as}). fst e \<in> {..< length as} \<and> snd e \<in> {..< length as}"
										and s_subset: "S \<subseteq> {..< length as}"
										and s_maxcut: "weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as) \<ge> (\<Sum>i < length as. as ! i)\<^sup>2 / 4"
			by blast

		thus "as \<in> partition_pset"
			unfolding partition_pset_def
		proof (intro CollectI)
			have "\<exists>xs. xs = map (\<lambda>i. if i \<in> S then 0 else 1) [0 ..< length as]"
				by blast
			define xs where xs[simp]: "(xs :: nat list) = map (\<lambda>i. if i \<in> S then 0 else 1) [0 ..< length as]"

			have "sum ((!) as) S = sum ((!) as) ({..< length as} - S)"
			proof -
				have "weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as) = weight (S \<times> ({..< length as} - S)) (real \<circ> ew as)"
					by (subst cutset_expand) (use s_subset in fastforce)+
				also have "... = sum ((!) as) S * sum ((!) as) ({..< length as} - S)"
					unfolding weight_def by (subst cutset_weight_split[symmetric], fastforce)
				finally have ineq: "sum ((!) as) S * sum ((!) as) ({..< length as} - S) \<ge> (\<Sum>i < length as. as ! i)\<^sup>2 / 4"
					using s_maxcut by arith
				moreover have addsum: "sum ((!) as) S + sum ((!) as) ({..< length as} - S) = sum ((!) as) {..< length as}"
					using s_subset by (metis add.commute finite_lessThan sum.subset_diff)
	
				ultimately have "sum ((!) as) S * sum ((!) as) ({..< length as} - S) \<le> ((sum ((!) as) {..< length as}) / 2)\<^sup>2"
					using cond_max by (metis of_nat_0_le_iff of_nat_add of_nat_mult)
				moreover have "((sum ((!) as) {..< length as}) / 2)\<^sup>2 = (\<Sum>i < length as. as ! i)\<^sup>2 / 4"
					by (simp add: power_divide)
				ultimately show "sum ((!) as) S = sum ((!) as) ({..< length as} - S)"
					by (smt ineq addsum cond_max_iff_real le_add1 le_add_same_cancel1 of_nat_add)
			qed

			hence S: "S = {i. i < length xs \<and> 0 = xs ! i} \<or> S = {i. i < length xs \<and> 1 = xs ! i}"
				using s_subset xs by (auto, arith)

			thus "\<exists>xs. (\<forall>i < length xs. xs ! i \<in> {0, 1}) \<and> length as = length xs
							\<and> (\<Sum>i<length as. as ! i * xs ! i) = (\<Sum>i<length as. as ! i * (1 - xs ! i))"
      proof (intro exI conjI)
      	show "\<forall>i < length xs. xs ! i \<in> {0, 1}"
      		using xs by (smt (verit) insertCI length_map nth_map)
      next
      	show "length as = length xs"
      		by simp
      next
      	show "(\<Sum>i<length as. as ! i * xs ! i) = (\<Sum>i<length as. as ! i * (1 - xs ! i))"
      	proof (rule ccontr)
      		assume neq: "(\<Sum>i<length as. as ! i * xs ! i) \<noteq> (\<Sum>i<length as. as ! i * (1 - xs ! i))"
      		then consider (one) "S = {i. i < length xs \<and> 1 = xs ! i}"
      			| (zero) "S = {i. i < length xs \<and> 0 = xs ! i}"
      			using S by arith
      		thus "False"
      		proof cases
      			case one
      			have "(\<Sum>i<length as. as ! i * xs ! i) * (\<Sum>i<length as. as ! i * (1 - xs ! i)) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							apply (rule cond_max_iff_real)
							subgoal apply (subgoal_tac "(\<Sum>i<length as. as ! i * xs ! i) + (\<Sum>i<length as. as ! i * (1 - xs ! i)) = sum ((!) as) {..<length as}")
								subgoal by arith
								subgoal by (rule partition_sum) (fastforce)+ .
							using neq by auto
						hence "sum (ew as) ({i. i < length xs \<and> 0 = xs ! i} \<times> {i. i < length xs \<and> 1 = xs ! i}) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							by (subst cutset_weight_partition) (fastforce)+
						hence "sum (ew as) ({i. i < length xs \<and> 1 = xs ! i} \<times> {i. i < length xs \<and> 0 = xs ! i}) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							by (simp add: cutset_weight_permute cutset_weight_split_general mult.commute)
						hence "sum (ew as) ({i. i < length xs \<and> 1 = xs ! i} \<times> ({..< length xs} - {i. i < length xs \<and> 1 = xs ! i})) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							by (subst v_min_s_alt) (fastforce)+
						hence "sum (ew as) (cutset ({..< length xs} \<times> {..< length xs}) S) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							by (subst cutset_expand) (use xs one in fastforce)+
						hence "sum (ew as) (cutset ({..< length as} \<times> {..< length as}) S) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							using xs by simp
						hence "weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							unfolding weight_def cutset_def by simp
						hence "weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as) < (\<Sum>i < length as. as ! i)\<^sup>2 / 4"
							by (simp add: power_divide)
      			thus ?thesis using s_maxcut by simp
      		next
      			case zero
      			have "(\<Sum>i<length as. as ! i * xs ! i) * (\<Sum>i<length as. as ! i * (1 - xs ! i)) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							apply (rule cond_max_iff_real)
							subgoal apply (subgoal_tac "(\<Sum>i<length as. as ! i * xs ! i) + (\<Sum>i<length as. as ! i * (1 - xs ! i)) = sum ((!) as) {..<length as}")
								subgoal by arith
								subgoal by (rule partition_sum) (fastforce)+ .
							using neq by auto
						hence "sum (ew as) ({i. i < length xs \<and> 0 = xs ! i} \<times> {i. i < length xs \<and> 1 = xs ! i}) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							by (subst cutset_weight_partition) (fastforce)+
						hence "sum (ew as) ({i. i < length xs \<and> 0 = xs ! i} \<times> ({..< length xs} - {i. i < length xs \<and> 0 = xs ! i})) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							by (subst v_min_s) (fastforce)+
						hence "sum (ew as) (cutset ({..< length xs} \<times> {..< length xs}) S) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							by (subst cutset_expand) (use xs zero in fastforce)+
						hence "sum (ew as) (cutset ({..< length as} \<times> {..< length as}) S) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							using xs by simp
						hence "weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as) < ((\<Sum>i < length as. as ! i) / 2)\<^sup>2"
							unfolding weight_def cutset_def by simp
						hence "weight (cutset ({..< length as} \<times> {..< length as}) S) (real \<circ> ew as) < (\<Sum>i < length as. as ! i)\<^sup>2 / 4"
							by (simp add: power_divide)
      			thus ?thesis using s_maxcut by simp
      		qed
      	qed
      qed
    qed
  qed
qed

end