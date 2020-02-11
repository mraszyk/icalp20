theory Necessary
  imports Computation
begin

locale necessary = fnft: fNFT ninit n\<delta> naccept nQ + fTDFA init \<delta> accept Q
  for ninit :: "'s"
  and n\<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> ('b :: finite) list \<Rightarrow> bool"
  and naccept :: "'s \<Rightarrow> bool"
  and nQ :: "'s set"
  and init :: "'t"
  and \<delta> :: "'t \<Rightarrow> ('a :: finite) Al \<times> ('b :: finite) Al \<Rightarrow> 't \<times> bool \<times> bool \<Rightarrow> bool"
  and accept :: "'t \<Rightarrow> bool"
  and Q :: "'t set" +
assumes equiv: "fnft.\<tau> = \<tau>"
begin

interpretation flip: TDFA init "\<lambda>q (a, b) (q', b1, b2). \<delta> q (b, a) (q', b2, b1)" accept Q
  using det finite_Q init_in_Q closed move_left move_right no_step
  apply unfold_locales
        apply auto
     apply fast+
  done

lemma flip_comp_intro: "q \<leadsto>(as, bs) q' \<Longrightarrow> flip.computation q (bs, as) q'"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct) auto

lemma flip_comp_dest: "flip.computation q (bs, as) q' \<Longrightarrow> q \<leadsto>(as, bs) q'"
  by (induction q "(bs, as)" q' arbitrary: as bs rule: flip.computation.induct) auto

lemma flip_comp_eq: "flip.computation q (bs, as) q' \<longleftrightarrow> q \<leadsto>(as, bs) q'"
  using flip_comp_intro flip_comp_dest
  by auto

lemmas flip_outs_Nil_dest = flip.outs_Nil_dest[unfolded flip_comp_eq]
lemmas flip_outs_Cons_dest = flip.outs_Cons_dest[unfolded flip_comp_eq]
lemmas flip_outs_Nil_intro = flip.outs_Nil_intro[unfolded flip_comp_eq]
lemmas flip_outs_Cons_intro = flip.outs_Cons_intro[unfolded flip_comp_eq]

lemma split_long:
  assumes "length w \<ge> n + 1"
  shows "\<exists>v' y z. w = v' @ y # z \<and> length z = n"
proof -
  obtain v' y z where split: "w = v' @ y # z" "length z \<ge> n"
    using assms
    by (metis Nat.le_diff_conv2 One_nat_def Suc_le_eq add_leD2 id_take_nth_drop length_drop)
  then show ?thesis
  proof (cases "length z > n")
    case True
    define z' where "z' = drop (length z - n) z"
    define y' where "y' = z ! (length z - n - 1)"
    have len_z': "length z' = n"
      using True
      by (auto simp add: z'_def)
    have split': "w = (v' @ y # (take (length z - n - 1) z)) @ y' # z'"
      using True
      by (auto simp add: split(1) y'_def z'_def) (metis Suc_diff_Suc diff_Suc_less drop_Nil
          id_take_nth_drop len_z' length_greater_0_conv nat_neq_iff z'_def)
    show ?thesis
      using split' len_z'
      by fast
  qed auto
qed

lemma concat_filter: "length qbs = length xs \<Longrightarrow> length ns = length xs \<Longrightarrow>
  concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) (filter (\<lambda>(n, (q, bs), (bs', q')). bs \<noteq> [])
  (zip ns (zip qbs xs)))) = concat (map snd qbs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma concat_length: "(\<And>n q bs bs' q'. (n, (q, bs), (bs', q')) \<in> set qss' \<Longrightarrow> length bs \<le> d) \<Longrightarrow>
  length (concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) qss')) \<le> length qss' * d"
  by (induction qss') fastforce+

lemma sorted_dest: "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow> i < j \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i < xs ! j"
  by (simp add: less_le nth_eq_iff_index_eq sorted_iff_nth_mono_less)

lemma map2_zip: "length qbs = length xs \<Longrightarrow> length qbs = length ns \<Longrightarrow>
  qbs = map2 (\<lambda>n ((q, bs), (bs', q')). (q, bs)) ns (zip qbs xs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma map2_zip': "length qbs = length xs \<Longrightarrow> length qbs = length ns \<Longrightarrow>
  xs = map2 (\<lambda>n ((q, bs), (bs', q')). (bs', q')) ns (zip qbs xs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma split_one: "n < length xs \<Longrightarrow> \<exists>ys ys'. xs = ys @ (xs ! n) # ys' \<and>
  length ys = n \<and> length ys' = length xs - (n + 1)"
  apply (induction n arbitrary: xs)
  subgoal for xs
    by (cases xs) auto
  subgoal for n xs
    apply (cases xs)
     apply auto
    apply (metis append_Cons length_Cons)
    done
  done

lemma split_two: "n < n' \<Longrightarrow> n' < length xs \<Longrightarrow>
  \<exists>ys ys' ys''. xs = ys @ (xs ! n) # ys' @ (xs ! n') # ys'' \<and> length ys = n \<and>
  length ys' = n' - (n + 1) \<and> length ys'' = length xs - (n' + 1)"
proof (induction n arbitrary: n' xs)
  case 0
  then show ?case
  proof (cases xs)
    case (Cons x xs')
    then show ?thesis
      using 0 split_one[of "n' - 1" xs']
      by auto
  qed auto
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case (Cons x xs')
    have n'_shift: "n < n' - 1" "n' - 1 < length xs'"
      using Suc(2,3)
      by (auto simp add: Cons)
    then obtain ys ys' ys'' where split: "xs' = ys @ xs' ! n # ys' @ xs' ! (n' - 1) # ys''"
      "length ys = n" "length ys' = n' - (Suc n + 1)" "length ys'' = length xs - (n' + 1)"
      using Suc(1)[OF n'_shift]
      by (auto simp add: Cons)
    show ?thesis
      apply (rule exI[of _ "x # ys"])
      using split Suc(2)
      by (auto simp add: Cons)
  qed auto
qed  

lemma joint_rem:
  assumes "fnft.computation s (as @ (if \<beta> then [case b of Symb b' \<Rightarrow> b'] else []), bs) s'"
    "s \<in> nQ" "length bs \<ge> (3 + card nQ * card Q) * fnft.max_fanout"
    "flip.outs a q (x # xs) q'' b \<beta>" "q \<in> Q"
    "length xs \<ge> 1 + card nQ * card Q"
    "as = map fst (x # xs)"
  shows "\<exists>as' bs' xs'. fnft.computation s (as', bs') s' \<and> flip.outs a q (x # xs') q'' b \<beta> \<and>
    length bs' < length bs \<and>
    as' = map fst (x # xs') @ (if \<beta> then [case b of Symb b' \<Rightarrow> b'] else [])"
proof -
  obtain c cs where as_def: "as = c # cs"
    using assms(7)
    by (cases as) auto
  have fst_x: "c = fst x"
    using assms(7)
    by (auto simp add: as_def)
  obtain s'' ds ds' where step: "n\<delta> s c (s'', ds)"
    "fnft.computation s'' (cs @ (if \<beta> then [case b of Symb b' \<Rightarrow> b'] else []), ds') s'"
    "bs = ds @ ds'"
    by (rule fnft.computation.cases[OF assms(1)[unfolded as_def]]) auto
  obtain t'' es es' where lstep: "fnft.computation s'' (cs, es) t''"
    "fnft.computation t'' (if \<beta> then [case b of Symb b' \<Rightarrow> b'] else [], es') s'" "ds' = es @ es'"
    using fnft.computation_split[OF step(2)]
    by auto
  have s''_nQ: "s'' \<in> nQ"
    using assms(2) step(1) fnft.\<delta>_closed
    by blast
  have len_es': "length es' \<le> fnft.max_fanout"
    using fnft.max_fanout_step[OF fnft.comp_closed[OF lstep(1) s''_nQ]] lstep(2)
    by (auto split: if_splits dest: fnft.no_step fnft.step_dest)
  have len_es: "length es \<ge> (1 + card nQ * card Q) * fnft.max_fanout"
  proof -
    have "(3 + card nQ * card Q) * fnft.max_fanout \<le> length ds + length es + length es'"
      using assms(3) step(3)[unfolded lstep(3)]
      by auto
    moreover have "\<dots> \<le> length es + fnft.max_fanout + fnft.max_fanout"
      using fnft.max_fanout_step[OF assms(2) step(1)] len_es'
      by auto
    finally show ?thesis
      by (simp add: numeral_Bit1)
  qed
  obtain qbs where qbs_def: "fnft.computation_ext s'' (cs, qbs) t''" "es = concat (map snd qbs)"
    using fnft.computation_ext_complete[OF lstep(1)]
    by auto
  note qbs_max_fanout = fnft.max_fanout_ext_computation[OF qbs_def(1) s''_nQ]
  have len_qbs: "length qbs = length xs"
    using fnft.computation_ext_length[OF qbs_def(1)] assms(7)
    by (auto simp add: as_def)
  have len_qbs': "length qbs = length cs"
    using assms(7) len_qbs
    by (auto simp add: as_def)
  define qss where "qss = zip [0..<length qbs] (zip qbs xs)"
  have len_qss: "length qss = length qbs"
    using len_qbs
    by (auto simp add: qss_def)
  have fst_qss_at: "\<And>i. i < length qss \<Longrightarrow> fst (qss ! i) = i"
    using len_qbs
    by (auto simp add: qss_def)
  have fst_set_qss: "\<And>x. x \<in> set qss \<Longrightarrow> fst x < length qss"
    using len_qbs
    by (auto simp add: qss_def dest: set_zip_leftD set_zip_rightD)
  define qss' where "qss' = filter (\<lambda>(n, (q, bs), (bs', q')). bs \<noteq> []) qss"
  have fst_set_qss': "\<And>x. x \<in> set qss' \<Longrightarrow> x \<in> set qss"
    by (auto simp add: qss'_def)
  define qs where "qs = map (\<lambda>(n, (q, bs), (bs', q')). (q, q')) qss'"
  have qss'_at: "\<And>i. i < length qss' \<Longrightarrow>
    fst (qss' ! i) < length qss \<and> qss' ! i = qss ! (fst (qss' ! i))"
    using fst_qss_at fst_set_qss' fst_set_qss
    apply (auto)
    by (metis fst_set_qss' in_set_conv_nth)
  have qss'_nonempty: "\<And>n q bs bs' q'. (n, (q, bs), (bs', q')) \<in> set qss' \<Longrightarrow> bs \<noteq> []"
    by (auto simp add: qss'_def)
  have sorted_fst_qss: "sorted (map fst qss)" "distinct (map fst qss)"
    using len_qbs
    by (auto simp add: qss_def)
  have sorted_fst_qss': "sorted (map fst qss')" "distinct (map fst qss')"
    unfolding qss'_def
     apply (rule sorted_filter)
    using sorted_fst_qss distinct_map_filter
    by blast+
  have len_qs: "length qs = length qss'"
    by (auto simp add: qs_def)
  have qs_sub: "set qs \<subseteq> nQ \<times> Q"
    using fnft.computation_ext_closed[OF qbs_def(1) s''_nQ] flip.outs_closed[OF assms(4,5)]
          len_qbs
    by (fastforce simp add: qs_def qss'_def qss_def dest: set_zip_leftD set_zip_rightD)
  have concat_qss': "concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) qss') = concat (map snd qbs)"
    using concat_filter[of _ _ "[0..<length qbs]"] len_qbs
    by (auto simp add: qss'_def qss_def)
  have len_qs_ge: "length qs \<ge> 1 + card nQ * card Q"
  proof (rule ccontr)
    assume lassm: "\<not> length qs \<ge> 1 + card nQ * card Q"
    have "length (concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) qss')) \<le>
      length qss' * fnft.max_fanout"
      apply (rule concat_length[of qss' fnft.max_fanout])
      using qbs_max_fanout
      by (auto simp add: qss'_def qss_def dest: set_zip_leftD set_zip_rightD)
    then show "False"
      using fnft.max_fanout_pos
      apply (auto simp add: arg_cong[OF concat_qss', of length] qbs_def(2)[symmetric])
      by (metis (mono_tags, lifting) lassm dual_order.trans le_less_linear len_es len_qs
          mult_le_cancel2 not_less_eq_eq)
  qed
  have not_distinct: "\<not> distinct qs"
  proof (rule ccontr)
    assume "\<not>\<not> distinct qs"
    then have contr: "distinct qs"
      by auto
    have card_qs: "card (set qs) \<ge> 1 + card nQ * card Q"
      using distinct_card[OF contr] len_qs_ge
      by (auto simp add: qs_def)
    have finite_prod: "finite (nQ \<times> Q)"
      using fnft.finite_Q finite_Q
      by blast
    have card_prod: "card (nQ \<times> Q) = card nQ * card Q"
      using card_cartesian_product
      by blast
    show "False"
      using card_qs card_mono[OF finite_prod qs_sub]
      by (auto simp add: card_prod)
  qed
  obtain qc qs' qs'' qs''' where qs_split: "qs = qs' @ [qc] @ qs'' @ [qc] @ qs'''"
    using not_distinct_decomp[OF not_distinct]
    by auto
  define n where "n = fst (qss' ! length qs')"
  define n' where "n' = fst (qss' ! (length qs' + 1 + length qs''))"
  have valid_idx: "length qs' < length qss'" "length qs' + 1 + length qs'' < length qss'"
    using qs_split len_qs len_qss
    by auto
  have qs_split_at: "qs ! (length qs') = qc" "qs ! (length qs' + 1 + length qs'') = qc"
    using qs_split
     apply auto
    by (metis add_Suc_right nth_Cons_Suc nth_append_length nth_append_length_plus)
  have n_n': "n < n'" "n' < length qbs" "qss ! n = qss' ! length qs'"
    "qss ! n' = qss' ! (length qs' + 1 + length qs'')"
    using qss'_at[OF valid_idx(1), folded n_def] qss'_at[OF valid_idx(2), folded n'_def]
          len_qss valid_idx sorted_dest[OF sorted_fst_qss']
    by (auto simp add: n_def n'_def)
  have qbs_map: "qbs = map (\<lambda>(n, (q, bs), (bs', q')). (q, bs)) qss"
    using map2_zip[OF len_qbs, of "[0..<length qbs]"]
    by (auto simp add: qss_def)
  obtain qbs' qbs'' qbs''' where decomp: "qbs = qbs' @ qbs ! n # qbs'' @ qbs ! n' # qbs'''"
    "length qbs' = n" "length qbs'' = n' - (n + 1)" "length qbs''' = length qbs - (n' + 1)"
    using split_two[OF n_n'(1,2)]
    by auto
  obtain bs' where bs'_def: "qbs ! n = (fst qc, bs')"
    using qbs_map n_n' qs_def len_qs qs_split_at(1) valid_idx(1)
    by (auto split: prod.splits)
  obtain bs'' where bs''_def: "qbs ! n' = (fst qc, bs'')" "bs'' \<noteq> []"
    using qbs_map n_n' qs_def len_qs qs_split_at(2) valid_idx(2) qss'_nonempty
    apply (auto split: prod.splits)
    by (metis in_set_conv_nth)
  obtain cs' cs'' cs''' c' c'' bs'a bs''' where new_comp:
    "fnft.computation s'' (cs' @ c' # cs''', bs'a @ bs' @ bs''') t''"
    "bs'a = concat (map snd qbs')" "bs''' = concat (map snd qbs''')"
    "cs = cs' @ c' # cs'' @ c'' # cs'''" "length cs' = length qbs'" "length cs'' = length qbs''"
    "length cs''' = length qbs'''"
    using fnft.computation_ext_rem[OF qbs_def(1)[unfolded decomp(1)[unfolded bs'_def bs''_def]]]
    by auto
  have new_length: "length (ds @ bs'a @ bs' @ bs''' @ es') < length bs"
    unfolding step(3) lstep(3)
    apply (auto simp add: new_comp(2,3) qbs_def(2))
    apply (subst decomp(1))
    apply (auto simp add: bs'_def bs''_def)
    done
  have xs_map: "xs = map (\<lambda>(n, (q, bs), (bs', q')). (bs', q')) qss"
    using map2_zip'[OF len_qbs, of "[0..<length qbs]"]
    by (auto simp add: qss_def)
  obtain xs' xs'' xs''' where decomp': "xs = xs' @ xs ! n # xs'' @ xs ! n' # xs'''"
    "length xs' = n" "length xs'' = n' - (n + 1)" "length xs''' = length xs - (n' + 1)"
    using split_two[OF n_n'(1) n_n'(2)[unfolded len_qbs]]
    by auto
  obtain ys' where ys'_def: "xs ! n = (ys', snd qc)"
    using xs_map n_n'[unfolded len_qbs] qs_def len_qs qs_split_at(1) valid_idx(1)
    by (auto split: prod.splits)
  obtain ys'' where ys''_def: "xs ! n' = (ys'', snd qc)"
    using xs_map n_n'[unfolded len_qbs] qs_def len_qs qs_split_at(2) valid_idx(2)
    by (auto split: prod.splits)
  have assoc: "flip.outs a q ((x # xs') @ (ys', snd qc) # xs'' @ (ys'', snd qc) # xs''') q'' b \<beta>"
    using assms(4)[unfolded decomp'(1)[unfolded ys'_def ys''_def]]
    by auto
  have "cs' @ c' # cs''' = map fst (xs' @ (ys', snd qc) # xs''')"
    using new_comp(4,5,6,7)[unfolded decomp(2,3,4) len_qbs] decomp' assms(7)[unfolded as_def]
    by (auto simp add: ys'_def ys''_def)
  then show ?thesis
    using fnft.comp_trans[OF fnft.step[OF step(1) new_comp(1)] lstep(2)]
    using new_length flip.outs_rem[OF assoc, simplified] step(3)
    by (fastforce simp add: fst_x)
qed

lemma conflict:
  assumes "fnft.computation s (as, bs @ bs') s'" "r \<leadsto>(as, bs') r'" "s \<in> nQ" "r \<in> Q"
    "length bs \<ge> (3 + card nQ * card Q) * fnft.max_fanout * (1 + length bs')"
  shows "\<exists>as' bs''. fnft.computation s (as', bs'') s' \<and> r \<leadsto>(as', bs') r' \<and>
    safe_hd as = safe_hd as' \<and> length bs'' < length (bs @ bs')"
  using assms
proof (induction bs' arbitrary: s as bs r)
  case Nil
  obtain xs q'' where outs: "flip.outs EOF r xs q'' EOF False"
    "\<delta> q'' (EOF, EOF) (r', False, False)" "as = map fst xs"
    using flip_outs_Nil_intro[OF Nil(2)]
    by auto
  have len_as: "length as \<ge> 3 + card nQ * card Q"
    using le_trans[OF Nil(5) fnft.max_fanout_computation[OF Nil(1,3), simplified]]
          fnft.max_fanout_pos
    by simp
  obtain c cs where xs_def: "xs = c # cs"
    using len_as outs(3)
    by (cases xs) auto
  have len_cs: "1 + card nQ * card Q \<le> length cs"
    using outs(3) len_as
    by (auto simp add: xs_def)
  obtain as' bs'' xs' where rem: "fnft.computation s (as', bs'') s'"
    "flip.outs EOF r (c # xs') q'' EOF False" "length bs'' < length bs"
    "as' = map fst (c # xs')"
    using joint_rem[OF _ Nil(3) _ outs(1)[unfolded xs_def] Nil(4) len_cs]
          Nil(1,5) outs(3)[unfolded xs_def]
    by force
  have rem': "r \<leadsto>(map fst (c # xs'), []) r'"
    using flip_outs_Nil_dest[OF rem(2), of r'] outs(2)
    by auto
  show ?case
    using rem(1,3) rem' outs(3)
    by (auto simp add: xs_def safe_hd_def rem(4) intro!: exI[of _ as'] exI[of _ bs''])
next
  case (Cons b bs')
  obtain xs q'' ba \<beta> as' where outs: "flip.outs (Symb b) r xs q'' ba \<beta>" "q''\<leadsto>(as', bs')r'"
    "(ba = EOF \<longrightarrow> \<not> \<beta>)" "(\<not> \<beta> \<longrightarrow> ba = flip.safe_hd as')"
    "as = map fst xs @ (if \<beta> then (case ba of Symb b' \<Rightarrow> b') # as' else as')"
    using flip_outs_Cons_intro[OF Cons(3)]
    by blast
  note q''_Q = flip.outs_closed'[OF outs(1) Cons(5)]
  have len_as: "length as \<ge> (3 + card nQ * card Q) * (2 + length bs')"
  proof -
    have "(3 + card nQ * card Q) * (2 + length bs') * fnft.max_fanout \<le> length (bs @ b # bs')"
      using Cons(6)
      by (subst semiring_normalization_rules(16)) auto
    then show ?thesis
      using fnft.max_fanout_computation[OF Cons(2,4)] fnft.max_fanout_pos
            le_trans mult_le_cancel2
      by (metis (no_types, lifting) add_gr_0 le_Suc_ex less_one)
  qed
  have as_assoc: "as = (map fst xs @ (if \<beta> then [case ba of Symb b' \<Rightarrow> b'] else [])) @ as'"
    using outs(5)
    by auto
  obtain q' ds ds' where split:
    "fnft.computation s (map fst xs @ (if \<beta> then [case ba of Symb b' \<Rightarrow> b'] else []), ds) q'"
    "fnft.computation q' (as', ds') s'"
    "bs @ b # bs' = ds @ ds'"
    using fnft.computation_split[OF Cons(2)[unfolded as_assoc]]
    by auto
  note q'_nQ = fnft.comp_closed[OF split(1) Cons(4)]
  show ?case
  proof (cases "(3 + card nQ * card Q) * fnft.max_fanout \<le> length ds")
    case True
    have len_as: "3 + card nQ * card Q \<le>
      length (map fst xs @ (if \<beta> then [case ba of Symb b' \<Rightarrow> b'] else []))"
    proof -
      have "(3 + card nQ * card Q) * fnft.max_fanout \<le>
        length (map fst xs @ (if \<beta> then [case ba of Symb b' \<Rightarrow> b'] else [])) * fnft.max_fanout"
        using Cons(6) le_trans[OF True fnft.max_fanout_computation[OF split(1) Cons(4)]]
        by auto
      then show ?thesis
        using fnft.max_fanout_pos mult_le_cancel2
        by (metis (no_types, lifting) add_gr_0 le_Suc_ex less_one)
    qed
    obtain c cs where xs_def: "xs = c # cs"
      using len_as outs(3)
      by (cases xs) (auto split: if_splits)
    have len_cs: "1 + card nQ * card Q \<le> length cs"
      using len_as
      by (auto simp add: xs_def split: if_splits)
    obtain as'' bs'' xs' where rem:
      "fnft.computation s (as'' @ (if \<beta> then [case ba of Symb b' \<Rightarrow> b'] else []), bs'') q'"
      "flip.outs (Symb b) r (c # xs') q'' ba \<beta>" "length bs'' < length ds"
      "as'' = map fst (c # xs')"
      using joint_rem[OF split(1) Cons(4) True outs(1)[unfolded xs_def] Cons(5) len_cs]
      by (auto simp add: xs_def)
    note rem' = flip_outs_Cons_dest[OF rem(2) outs(2,3,4) refl]
    show ?thesis
      using fnft.comp_trans[OF rem(1) split(2)] rem' rem(3) outs(5)
      by (auto simp add: safe_hd_def split(3) rem(4) xs_def
          intro!: exI[of _ "fst c # map fst xs' @ _"] split: if_splits)
  next
    case False
    have len_bs_ds: "length ds \<le> length (bs @ [b])"
      using False Cons(6)
      by auto
    obtain es where es_def: "ds' = es @ bs'"
      using split(3) split_app'[OF _ len_bs_ds]
      by fastforce
    have bs_ds_es: "bs @ [b] = ds @ es"
      using split(3)[unfolded es_def]
      by auto
    have len_es: "(3 + card nQ * card Q) * fnft.max_fanout * (1 + length bs') \<le> length es"
    proof -
      have "(3 + card nQ * card Q) * fnft.max_fanout * (2 + length bs') \<le> length (bs @ [b])"
        using Cons(6)
        by auto
      then have "(3 + card nQ * card Q) * fnft.max_fanout * (2 + length bs') \<le>
        length ds + length es"
        unfolding bs_ds_es
        by auto
      then show ?thesis
        using False
        by auto
    qed
    obtain as'' bs'' where rest: "fnft.computation q' (as'', bs'') s'" "q''\<leadsto>(as'', bs')r'"
      "flip.safe_hd as' = flip.safe_hd as''" "length bs'' < length (es @ bs')"
      using Cons(1)[OF split(2)[unfolded es_def] outs(2) q'_nQ q''_Q len_es]
      by auto
    have new_length: "length (ds @ bs'') < length (bs @ b # bs')"
      using rest(4)
      by (auto simp add: split(3) es_def)
    have "safe_hd as = safe_hd (map fst xs @
      (if \<beta> then (case ba of Symb b' \<Rightarrow> b') # as'' else as''))"
      using rest(3)
      by (cases xs) (auto simp add: outs(5) safe_hd_def split: list.splits)
    then show ?thesis
      using fnft.comp_trans[OF split(1) rest(1)] new_length
            flip_outs_Cons_dest[OF outs(1) rest(2) outs(3) outs(4)[unfolded rest(3)] refl]
      by fastforce
  qed
qed

lemma card_nQ_pos: "card nQ \<ge> 1"
  using fnft.finite_Q fnft.init_in_Q
  by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff)

lemma card_Q_pos: "card Q \<ge> 1"
  using finite_Q init_in_Q
  by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff)

lemma card_nQ_Q_pos: "card nQ * card Q \<ge> 1"
  using card_nQ_pos card_Q_pos
  by auto

lemma add_le_mult:
  fixes x y :: nat
  shows "x \<ge> 1 \<Longrightarrow> y \<ge> 1 \<Longrightarrow> x + y \<le> 2 * x * y"
  by (simp add: add_le_mono distrib_left mult.commute mult_2_right)

(* Theorem 8 *)
lemma bounded: "\<exists>K. fnft.bounded K"
proof (rule ccontr)
  assume "\<not>(\<exists>K. fnft.bounded K)"
  then obtain q q' t v w where unbounded: "fnft.computation ninit (t, v @ w) q"
    "fnft.active q []" "fnft.computation ninit (t, v) q'" "fnft.active q' w"
    "length w \<ge> (3 + card nQ * card Q) * fnft.max_fanout *
    (3 + (2 + card nQ) * (2 + card Q + fnft.max_fanout)) +
    (card nQ + 2) * (card Q + 2) + 1 + 1"
    by (auto simp add: fnft.bounded_def) (metis less_or_eq_imp_le neqE)
  note q_nQ = fnft.comp_closed[OF unbounded(1) fnft.init_in_Q]
  note q'_nQ = fnft.comp_closed[OF unbounded(3) fnft.init_in_Q]
  obtain u1 v1 nqf where ext: "fnft.computation q (u1, v1) nqf" "naccept nqf"
    "length u1 \<le> card nQ" "length v1 \<le> card nQ * fnft.max_fanout"
    using fnft.active_Nil_dest[OF unbounded(2) q_nQ]
    by auto
  obtain u2 v2 nqf' where ext': "fnft.computation q' (u2, w @ v2) nqf'" "naccept nqf'"
    "length v2 \<le> (1 + card nQ) * fnft.max_fanout"
    using fnft.active_dest[OF unbounded(4) q'_nQ]
    by auto
  obtain u x where t_def: "t = u @ [x]"
    using unbounded(1,5)
    by (cases t rule: rev_cases) (auto dest: fnft.no_step)
  have len_w: "length w \<ge> (card nQ + 2) * (card Q + 2) + 1 + 1"
    using unbounded(5)
    by auto
  obtain v' y z where w_def: "w = v' @ y # z" "length z = (card nQ + 2) * (card Q + 2) + 1"
    using split_long[OF len_w]
    by auto
  have "fnft.computation ninit (u @ x # u1, (v @ v') @ y # z @ v1) nqf"
    using fnft.comp_trans[OF unbounded(1) ext(1), unfolded w_def t_def]
    by auto
  then obtain qf where qf_def: "init \<leadsto>(u @ x # u1, (v @ v') @ y # z @ v1) qf" "accept qf"
    using ext(2) equiv
    by (fastforce simp add: fnft.\<tau>_def \<tau>_def)
  have "fnft.computation ninit (u @ x # u2, (v @ v') @ y # z @ v2) nqf'"
    using fnft.comp_trans[OF unbounded(3) ext'(1), unfolded w_def t_def]
    by auto
  then obtain qf' where qf'_def: "init \<leadsto>(u @ x # u2, (v @ v') @ y # z @ v2) qf'" "accept qf'"
    using ext'(2) equiv
    by (fastforce simp add: fnft.\<tau>_def \<tau>_def)
  show "False"
    using first_reaches[OF reachable_init refl refl qf_def(1) qf'_def(1)]
  proof (rule disjE)
    assume "\<exists>r cs y' cs'. reachable r ([] @ u) ([] @ cs) (Symb x) (Symb y') \<and>
      r \<leadsto>(x # u1, y' # cs' @ z @ v1) qf \<and> r \<leadsto>(x # u2, y' # cs' @ z @ v2) qf' \<and>
      cs @ y' # cs' = (v @ v') @ [y]"
    then obtain r cs y' cs' where tail: "reachable r u cs (Symb x) (Symb y')"
      "r \<leadsto>(x # u1, y' # cs' @ z @ v1) qf"
      by auto
    have "length z \<ge> (length u1 + 2) * (card Q + 2) + 1"
      unfolding w_def(2)
      using add_le_mono[OF ext(3), OF order.refl, of 2] add_le_mono1 mult_le_mono1
      by blast
    then show "False"
      using lin_bounded[OF tail(1,2) qf_def(2)]
      by (auto simp add: safe_hd_def)
  next
    assume "\<exists>r cs x' cs'. reachable r ([] @ cs) ([] @ v @ v') (Symb x') (Symb y) \<and>
      r \<leadsto>(x' # cs' @ u1, y # z @ v1) qf \<and> r \<leadsto>(x' # cs' @ u2, y # z @ v2) qf' \<and>
      cs @ x' # cs' = u @ [x]"
    then obtain r' cs x' cs' where tail': "reachable r' cs (v @ v') (Symb x') (Symb y)"
      "r' \<leadsto>(x' # cs' @ u2, y # z @ v2) qf'" "cs @ x' # cs' = u @ [x]"
      by auto
    obtain g gs where u2_def: "u2 = g # gs"
      using ext'(1)[unfolded w_def, simplified]
      by (cases u2) (auto dest: fnft.no_step)
    have comp: "r' \<leadsto>((x' # cs') @ g # gs, y # z @ v2) qf'"
      using tail'(2)[unfolded u2_def]
      by auto
    obtain r ds y' ds' where tail: "reachable r (u @ [x]) (v @ v' @ ds) (Symb g) y'"
      "r \<leadsto>(g # gs, ds') qf'" "y # z @ v2 = ds @ ds'" "y' = safe_hd ds'"
      using comp_suf[OF tail'(1) _ _ comp]
      by (auto simp add: safe_hd_def tail'(3))
    have r_Q: "r \<in> Q"
      using tail(1)
      by (auto simp add: reachable_def)
    have comp': "fnft.computation q' (g # gs, (v' @ ds) @ ds') nqf'"
      using ext'(1)[unfolded w_def u2_def, simplified] tail(3)
      by auto
    have len_ds': "length ds' \<le> 2 + (2 + card nQ) * (2 + card Q + fnft.max_fanout)"
    proof -
      have "length ds' \<le> 1 + length z + length v2"
        using arg_cong[OF tail(3), of length]
        by auto
      also have "\<dots> \<le> 2 + (2 + card nQ) * (2 + card Q + fnft.max_fanout)"
        using w_def(2) ext'(3)
        by (auto simp add: distrib_left)
      finally show ?thesis .
    qed
    have len_v': "(3 + card nQ * card Q) * fnft.max_fanout * (1 + length ds') \<le> length (v' @ ds)"
    proof -
      have "(3 + card nQ * card Q) * fnft.max_fanout * (1 + length ds') \<le>
        (3 + card nQ * card Q) * fnft.max_fanout *
        (1 + (2 + (2 + card nQ) * (2 + card Q + fnft.max_fanout)))"
        using mult_le_mono2[OF add_le_mono[OF _ len_ds'], OF order.refl]
        by fastforce
      also have "\<dots> \<le> (3 + card nQ * card Q) * fnft.max_fanout *
        (3 + (2 + card nQ) * (2 + card Q + fnft.max_fanout))"
        unfolding add.assoc[symmetric]
        by (metis less_or_eq_imp_le one_plus_numeral semiring_norm(3))
      also have "\<dots> \<le> length v'"
        using unbounded(5)[unfolded w_def(1)] w_def(2)
        by auto
      finally show ?thesis
        by auto
    qed
    obtain as' bs'' where rem: "fnft.computation q' (as', bs'') nqf'" "r \<leadsto>(as', ds') qf'"
      "flip.safe_hd (g # gs) = flip.safe_hd as'" "length bs'' < length ((v' @ ds) @ ds')"
      using conflict[OF comp' tail(2) q'_nQ r_Q len_v']
      by auto
    have wit1: "(u @ [x] @ as', v @ bs'') \<in> \<tau>"
      using fnft.comp_trans[OF unbounded(3) rem(1), unfolded t_def] ext'(2) fnft.\<tau>_def equiv
      by auto
    have wit2: "(u @ [x] @ as', v @ v' @ ds @ ds') \<in> \<tau>"
      using tail(1) rem(2) rem(3)[symmetric] tail(4)[symmetric] qf'_def(2)
      by (fastforce simp add: reachable_def \<tau>_def safe_hd_def split: list.splits)
    show "False"
      using functional[OF wit1 wit2] rem(4)
      by auto
  qed
qed

end

end