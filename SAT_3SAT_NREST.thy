theory SAT_3SAT_NREST
	imports Main "../Polynomial_Reductions" SAT_3SAT
begin

type_synonym cost = "enat"

definition elog :: "nat \<Rightarrow> enat"
	where "elog n = enat (nat (ceiling (ln n)))"

definition nat_comp_c :: "cost" where "nat_comp_c = 1"
definition if_c :: "cost \<Rightarrow> cost" where "if_c cond = eSuc cond"
definition ret_c :: "cost" where "ret_c = 1"

definition pred_c :: "nat \<Rightarrow> nat nrest" where "pred_c n = REST [n-1 \<mapsto> 1]"

(* lists *)
definition nil_c :: "'a list nrest" where "nil_c = REST [[] \<mapsto> 1]"

term length
definition length_c :: "'a list \<Rightarrow> nat nrest"
	where "length_c xs = REST [length xs \<mapsto> 1]"

term hd
definition hd_c :: "'a list \<Rightarrow> 'a nrest"
	where "hd_c xs = REST [hd xs \<mapsto> 1]"

term tl
definition tl_c :: "'a list \<Rightarrow> 'a list nrest"
	where "tl_c xs = REST [tl xs \<mapsto> 1]"

(*
term last
definition last_c :: "'a list \<Rightarrow> 'a nrest"
	where "last_c (x # xs) = RECT (\<lambda>fix xs.
		do	{
			len \<leftarrow> length_c xs;
			cond \<leftarrow> SPECT [len = 0 \<mapsto> nat_comp_c];
			if cond then
				
			else
		}
	) (x # xs)"
*)

term Cons
definition cons_c :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list nrest"
	where "cons_c x xs = REST [x # xs \<mapsto> 1]"

term append
definition append_c :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list nrest"
	where "append_c xs ys = RECT (\<lambda>fix (xs, ys).
		do	{
			len \<leftarrow> length_c xs;
			cond \<leftarrow> SPECT [len = 0 \<mapsto> nat_comp_c];
			if cond then
				RETURNT ys
			else do	{
				hd \<leftarrow> hd_c xs;
				tl \<leftarrow> tl_c xs;
				call \<leftarrow> fix (tl, ys);
				cons_c hd call
			}
		}
	) (xs, ys)"

term rev
definition rev_c :: "'a list \<Rightarrow> 'a list nrest"
	where "rev_c xs = RECT (\<lambda>fix xs.
		do	{
			len \<leftarrow> length_c xs;
			cond \<leftarrow> SPECT [len = 0 \<mapsto> nat_comp_c];
			if cond then
				RETURNT xs
			else do	{
				nil \<leftarrow> nil_c;
				hd \<leftarrow> hd_c xs;
				tl \<leftarrow> tl_c xs;

				single \<leftarrow> cons_c hd nil;
				call \<leftarrow> fix tl;
				append_c call single
			}
		}
	) xs"

definition "rev_t n = n * n * n * n"

(*
lemma "rev_c xs \<le> SPEC (\<lambda>ys. ys = rev xs) (\<lambda>_. rev_t (length xs))"
	unfolding SPEC_def
  apply (rule T_specifies_I)
  apply (vcg' \<open>-\<close>)
  apply (auto simp add: rev_c_def RECT_def nat_comp_c_def nil_c_def)
*)

(* sets *)
definition empty_c :: "'a set nrest" where "empty_c = REST [{} \<mapsto> 1]"

term card
definition card_c :: "'a set \<Rightarrow> nat nrest"
	where "card_c A = REST [card A \<mapsto> 1]"

term fresh
definition fresh_c :: "('a :: fresh) set \<Rightarrow> 'a \<Rightarrow> 'a nrest"
	where "fresh_c notin seed = REST [fresh notin seed \<mapsto> let n = card notin in 1 + (n*(elog n))]"

term insert
definition insert_c :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set nrest"
	where "insert_c x A = REST [insert x A \<mapsto> let n = card A in 1 + (n*(elog n))]"

term pop
definition pop_c :: "'a lit set \<Rightarrow> ('a lit * 'a lit set) nrest"
	where "pop_c c = REST [pop c \<mapsto> let n = card c in 1 + elog n]"

(* tuples *)
term fst
definition fst_c :: "'a * 'b \<Rightarrow> 'a nrest"
	where "fst_c p = REST [fst p \<mapsto> 1]"

term snd
definition snd_c :: "'a * 'b \<Rightarrow> 'b nrest"
	where "snd_c p = REST [snd p \<mapsto> 1]"



definition stock_c :: "nat \<Rightarrow> ('a :: fresh) set \<Rightarrow> 'a lit list nrest"
	where "stock_c n vars = RECT (\<lambda>fix (n, vars).
		do	{
			cond \<leftarrow> SPECT [n = 0 \<mapsto> nat_comp_c];
			if cond then 
				nil_c 
			else do	{
				f \<leftarrow> fresh_c vars undefined;

				pred_n \<leftarrow> pred_c n;
				insert_vars \<leftarrow> insert_c f vars; 
				call \<leftarrow> fix (pred_n, insert_vars);

				tmp \<leftarrow> (cons_c (Pos f) call);
				cons_c (Neg f) tmp
			}
		}
	) (n, vars)"


term splc
definition splc_c :: "('a :: fresh) lit set \<Rightarrow> 'a lit list \<Rightarrow> 'a lit \<Rightarrow> 'a lit set list nrest"
	where "splc_c c s init = RECT (\<lambda>fix (c, s, init).
		do	{
			len \<leftarrow> length_c s;
			l0 \<leftarrow> SPECT [len = 0 \<mapsto> nat_comp_c];
			l1 \<leftarrow> SPECT [len = 1 \<mapsto> nat_comp_c];
			if l0 then
				cons_c c []
			else if l1 then do	{
				nx \<leftarrow> hd_c s;

				p \<leftarrow> pop_c c;
				fst_p \<leftarrow> fst_c p;
				snd_p \<leftarrow> snd_c p;
				q \<leftarrow> pop_c snd_p;
				fst_q \<leftarrow> fst_c q;
				snd_q \<leftarrow> snd_c q;

				nil \<leftarrow> nil_c;
				empty \<leftarrow> empty_c;

				subs2 \<leftarrow> insert_c nx snd_q;
				
				subs1_1 \<leftarrow> insert_c init empty;
				subs1_2 \<leftarrow> insert_c fst_q subs1_1;
				subs1 \<leftarrow> insert_c fst_p subs1_2;

				cons_tmp \<leftarrow> cons_c subs2 nil;
				cons_c subs1 cons_tmp
			}
			else do	{
				n_prev \<leftarrow> hd_c s;
				tl \<leftarrow> tl_c s;
				p_cur \<leftarrow> hd_c tl;
				xs \<leftarrow> tl_c tl;

				p \<leftarrow> pop_c c;
				fst_p \<leftarrow> fst_c p;
				snd_p \<leftarrow> snd_c p;

				call \<leftarrow> fix (snd_p, xs, init);
				empty \<leftarrow> empty_c;
				set2 \<leftarrow> insert_c p_cur empty;
				set1 \<leftarrow> insert_c fst_p set2;
				set \<leftarrow> insert_c n_prev set1;

				cons_c set call
			}
		}
	) (c, s, init)"


definition refc :: "('a :: fresh) lit set \<Rightarrow> 'a set \<Rightarrow> 'a lit set list * 'a set"
	where "refc c vars = (
		if card c \<le> 3 then
			(c # [], vars)
		else
			let s = stock (card c - 3) vars in
				(splc c (tl (rev s)) (last s), idset (set s) \<union> vars)
	)"
term refc
definition refc_c :: "('a :: fresh) lit set \<Rightarrow> 'a set \<Rightarrow> ('a lit set list * 'a set) nrest"
	where "refc c vars = RECT (\<lambda>fix (c, vars).
		do	{
			len \<leftarrow> card_c c;
			cond \<leftarrow> SPECT [len \<le> 3 \<mapsto> nat_comp_c];
			if cond then do	{
				nil \<leftarrow> nil_c;
				RETURNT (cons_c c nil, vars)
			}
			else do	{
				c1 \<leftarrow> pred_c len;
				c2 \<leftarrow> pred_c c1;
				c3 \<leftarrow> pred_c c2;

				s \<leftarrow> stock_c c3 vars;
				rev_s \<leftarrow> rev_c s;
				tl_rev_s \<leftarrow> tl_c rev_s;
				
				

				RETURNT []
			}
		}
	) (c, vars)"



term has_empty
definition has_empty_nrest 
	where "has_empty_nrest expr =
	RECT (\<lambda>has_empty_rec expr.
		if expr = [] then
			RETURNT False
		else if card (hd expr) = 0 then
			RETURNT True
		else
			RETURNT (has_empty_rec (tl expr))
	 ) expr"

definition to_le3sat_nrest :: "'a lit set list \<Rightarrow> 'a lit set list nrest"
	where "to_le3sat_nrest expr = RETURNT []"

term preproc
definition preproc_nrest :: "('a :: fresh) lit set list \<Rightarrow> 'a lit set list nrest"
	where "preproc_nrest expr =	(
		if has_empty expr then
			RETURNT [{}]
		else
			RETURNT (to_le3sat expr)
	)"
                                                                                           
thm sat_reduce_le3sat
lemma sat_reduce_le3sat_nrest_refine: "sat_reduce_le3sat_nrest expr \<le> SPEC (\<lambda>le3expr. preproc expr = le3expr) to_le3sat_res"


lemma le3sat_reduce_3sat_nrest_refine:

end