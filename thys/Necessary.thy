theory Necessary
  imports Computation
begin

locale necessary' = fnft: fNFT ninit n\<delta> naccept nQ + foTDFA init \<delta> accept Q
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

interpretation flip: oTDFA init "\<lambda>q (a, b) (q', b1, b2). \<delta> q (b, a) (q', b2, b1)" accept Q
  using det finite_Q init_in_Q closed move_left move_right no_step move_one
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

lemmas flip_outs_Nil_intro = flip.outs_Nil_intro[unfolded flip_comp_eq]
lemmas flip_outs_Cons_intro = flip.outs_Cons_intro[unfolded flip_comp_eq]
lemmas flip_outs_Nil_dest = flip.outs_Nil_dest[unfolded flip_comp_eq]
lemmas flip_outs_Cons_dest = flip.outs_Cons_dest[unfolded flip_comp_eq]

lemma split_long:
  assumes "length w \<ge> n"
  shows "\<exists>v' v''. w = v' @ v'' \<and> length v'' = n"
  using assms
  by (metis append_take_drop_id diff_diff_cancel length_drop)

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
  assumes "fnft.computation s (as, bs) s'"
    "s \<in> nQ" "length bs > card nQ * card Q * fnft.output_speed"
    "flip.outs a q xs q'' b" "q \<in> Q"
    "length xs > card nQ * card Q"
    "as = map fst xs"
  shows "\<exists>as' bs' xs'. fnft.computation s (as', bs') s' \<and> flip.outs a q xs' q'' b \<and>
    length bs' < length bs \<and> as' = map fst xs' \<and> safe_hd (map fst xs') = safe_hd (map fst xs)"
proof -
  obtain qbs where qbs_def: "fnft.computation_ext s (as, qbs) s'" "bs = concat (map snd qbs)"
    using fnft.computation_ext_complete[OF assms(1)]
    by auto
  note qbs_output_speed = fnft.output_speed_ext_computation[OF qbs_def(1) assms(2)]
  have len_qbs: "length qbs = length xs"
    using fnft.computation_ext_length[OF qbs_def(1)] assms(7)
    by auto
  have len_qbs': "length qbs = length as"
    using assms(7) len_qbs
    by auto
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
    using fnft.computation_ext_closed[OF qbs_def(1) assms(2)] flip.outs_closed[OF assms(4,5)]
          len_qbs
    by (fastforce simp add: qs_def qss'_def qss_def dest: set_zip_leftD set_zip_rightD)
  have concat_qss': "concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) qss') = concat (map snd qbs)"
    using concat_filter[of _ _ "[0..<length qbs]"] len_qbs
    by (auto simp add: qss'_def qss_def)
  have len_qs_ge: "length qs \<ge> 1 + card nQ * card Q"
  proof (rule ccontr)
    assume lassm: "\<not> length qs \<ge> 1 + card nQ * card Q"
    have "length (concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) qss')) \<le>
      length qss' * fnft.output_speed"
      apply (rule concat_length[of qss' fnft.output_speed])
      using qbs_output_speed
      by (auto simp add: qss'_def qss_def dest: set_zip_leftD set_zip_rightD)
    then show "False"
      using fnft.output_speed_pos assms(3) lassm less_le_trans
      by (fastforce simp add: arg_cong[OF concat_qss', of length] qbs_def(2)[symmetric]
          len_qs[symmetric])
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
    "fnft.computation s (cs' @ c' # cs''', bs'a @ bs' @ bs''') s'"
    "bs'a = concat (map snd qbs')" "bs''' = concat (map snd qbs''')"
    "as = cs' @ c' # cs'' @ c'' # cs'''" "length cs' = length qbs'" "length cs'' = length qbs''"
    "length cs''' = length qbs'''"
    using fnft.computation_ext_rem[OF qbs_def(1)[unfolded decomp(1)[unfolded bs'_def bs''_def]]]
    by auto
  have new_length: "length (bs'a @ bs' @ bs''') < length bs"
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
  have assoc: "flip.outs a q (xs' @ (ys', snd qc) # xs'' @ (ys'', snd qc) # xs''') q'' b"
    using assms(4)[unfolded decomp'(1)[unfolded ys'_def ys''_def]]
    by auto
  have "cs' @ c' # cs''' = map fst (xs' @ (ys', snd qc) # xs''')"
    using new_comp(4,5,6,7)[unfolded decomp(2,3,4) len_qbs] decomp' assms(7)
    by (auto simp add: ys'_def ys''_def)
  moreover have "safe_hd (map fst (xs' @ (ys', snd qc) # xs''')) = safe_hd (map fst xs)"
    using safe_hd_eq[OF decomp'(1)[unfolded ys'_def]]
    by auto
  ultimately show ?thesis
    using new_comp(1) new_length flip.outs_rem[OF assoc, simplified]
    by fastforce
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

lemma mult_all: "x \<le> card nQ * card Q * fnft.output_speed * x"
  using card_nQ_Q_pos fnft.output_speed_pos
  by auto

lemma conflict:
  assumes "fnft.computation s (as, bs @ bs') s'" "r \<leadsto>(as, bs') r'" "s \<in> nQ" "r \<in> Q"
    "length bs + length bs' > card nQ * card Q * fnft.output_speed * (1 + length bs')"
  shows "\<exists>as' bs''. fnft.computation s (as', bs'') s' \<and> r \<leadsto>(as', bs') r' \<and>
    safe_hd as = safe_hd as' \<and> length bs'' < length (bs @ bs')"
  using assms
proof (induction bs' arbitrary: s as bs r)
  case Nil
  obtain xs q'' where outs: "flip.outs Blank r xs q'' Blank"
    "\<delta> q'' (Blank, Blank) (r', False, False)" "as = map fst xs"
    using flip_outs_Nil_intro[OF Nil(2)]
    by auto
  have len_as: "length as > card nQ * card Q"
    using less_le_trans[OF Nil(5)[simplified]
          fnft.output_speed_computation[OF Nil(1,3), simplified]]
          fnft.output_speed_pos
    by auto
  obtain as' bs'' xs' where rem: "fnft.computation s (as', bs'') s'"
    "flip.outs Blank r xs' q'' Blank" "length bs'' < length bs"
    "as' = map fst xs'" "safe_hd (map fst xs') = safe_hd (map fst xs)"
    using joint_rem[OF Nil(1,3) _ outs(1) Nil(4) _ outs(3)] Nil(5) len_as[unfolded outs(3)]
    by auto
  have rem': "r \<leadsto>(map fst xs', []) r'"
    using flip_outs_Nil_dest[OF rem(2), of r'] outs(2)
    by auto
  show ?case
    using rem(1,3,5) rem' outs(3)
    by (auto simp add: safe_hd_def rem(4) intro!: exI[of _ as'] exI[of _ bs''])
next
  case (Cons b bs')
  obtain xs q'' ba as' where outs: "flip.outs (Symb b) r xs q'' ba" "q''\<leadsto>(as', bs')r'"
    "ba = safe_hd as'"
    "as = map fst xs @ as'"
    using flip_outs_Cons_intro[OF Cons(3)]
    by auto
  note q''_Q = flip.outs_closed'[OF outs(1) Cons(5)]
  have len_as: "length as \<ge> card nQ * card Q * (2 + length bs')"
  proof -
    have "card nQ * card Q * (2 + length bs') * fnft.output_speed \<le> length (bs @ b # bs')"
      using Cons(6)
      by (subst semiring_normalization_rules(16)) auto
    then show ?thesis
      using fnft.output_speed_computation[OF Cons(2,4)] fnft.output_speed_pos
      by (metis (no_types, lifting) One_nat_def Suc_le_eq le_trans mult_le_cancel2)
  qed
  obtain q' ds ds' where split:
    "fnft.computation s (map fst xs, ds) q'"
    "fnft.computation q' (as', ds') s'"
    "bs @ b # bs' = ds @ ds'"
    using fnft.computation_split[OF Cons(2)[unfolded outs(4)]]
    by auto
  note q'_nQ = fnft.comp_closed[OF split(1) Cons(4)]
  show ?case
  proof (cases "card nQ * card Q * fnft.output_speed < length ds")
    case True
    have len_as: "card nQ * card Q < length (map fst xs)"
    proof -
      have "card nQ * card Q * fnft.output_speed < length (map fst xs) * fnft.output_speed"
        using Cons(6) less_le_trans[OF True fnft.output_speed_computation[OF split(1) Cons(4)]]
        by auto
      then show ?thesis
        using fnft.output_speed_pos
        by auto
    qed
    obtain as'' bs'' xs' where rem:
      "fnft.computation s (as'', bs'') q'"
      "flip.outs (Symb b) r xs' q'' ba" "length bs'' < length ds"
      "as'' = map fst xs'" "safe_hd (map fst xs') = safe_hd (map fst xs)"
      using joint_rem[OF split(1) Cons(4) True outs(1) Cons(5) _ refl] len_as
      by auto
    note rem' = flip_outs_Cons_dest[OF rem(2) outs(2,3) refl]
    show ?thesis
      using fnft.comp_trans[OF rem(1) split(2)] rem' rem(3) outs(4) safe_hd_app[OF rem(5)]
      by (auto simp add: split(3) rem(4) intro!: exI[of _ "map fst xs' @ as'"] split: if_splits)
  next
    case False
    have len_bs_ds: "length ds \<le> length (bs @ [b])"
      using False mult_all[of "length (b # bs')"] Cons(6)
      by auto
    obtain es where es_def: "ds' = es @ bs'"
      using split(3) split_app'[OF _ len_bs_ds]
      by fastforce
    have bs_ds_es: "bs @ [b] = ds @ es"
      using split(3)[unfolded es_def]
      by auto
    have len_es: "card nQ * card Q * fnft.output_speed * (1 + length bs') < length es + length bs'"
    proof -
      have "card nQ * card Q * fnft.output_speed * (1 + length bs') + length ds \<le>
        card nQ * card Q * fnft.output_speed * (1 + length bs') +
        card nQ * card Q * fnft.output_speed"
        using False
        by auto
      also have "\<dots> < length ds + length es + length bs'"
        using arg_cong[OF bs_ds_es, of length] Cons(6)
        by auto
      finally show ?thesis
        by auto
    qed
    obtain as'' bs'' where rest: "fnft.computation q' (as'', bs'') s'" "q''\<leadsto>(as'', bs')r'"
      "safe_hd as' = safe_hd as''" "length bs'' < length (es @ bs')"
      using Cons(1)[OF split(2)[unfolded es_def] outs(2) q'_nQ q''_Q] len_es
      by auto
    have new_length: "length (ds @ bs'') < length (bs @ b # bs')"
      using rest(4)
      by (auto simp add: split(3) es_def)
    have "safe_hd as = safe_hd (map fst xs @ as'')"
      using safe_hd_app'[OF rest(3)[unfolded outs(4)]]
      by (auto simp add: outs(4))
    then show ?thesis
      using fnft.comp_trans[OF split(1) rest(1)] new_length
        flip_outs_Cons_dest[OF outs(1) rest(2) outs(3)[unfolded rest(3)] refl]
      by fastforce
  qed
qed

lemma bounded: "\<exists>K. fnft.bounded K"
proof (rule ccontr)
  (* home stretch *)
  define h where "h = (fnft.sg + 1) * (card Q + 1)"
  (* trail length *)
  define t where "t = card nQ * card Q * fnft.output_speed *
    (h + (fnft.sg + 1) * fnft.output_speed + 1)"
  assume "\<not>(\<exists>K. fnft.bounded K)"
  then obtain q q' u v w where unbounded: "fnft.computation ninit (u, v @ w) q"
    "fnft.active q []" "fnft.computation ninit (u, v) q'" "fnft.active q' w"
    "length w > t"
    by (auto simp add: fnft.bounded_def) (metis less_or_eq_imp_le neqE)
  note q_nQ = fnft.comp_closed[OF unbounded(1) fnft.init_in_Q]
  note q'_nQ = fnft.comp_closed[OF unbounded(3) fnft.init_in_Q]
  obtain u1 v1 nqf where ext: "fnft.computation q (u1, v1) nqf" "naccept nqf"
    "length u1 \<le> fnft.sg" "length v1 \<le> fnft.sg * fnft.output_speed"
    using fnft.active_Nil_dest_sg[OF unbounded(2) q_nQ]
    by auto
  obtain u2 v2 nqf' where ext': "fnft.computation q' (u2, w @ v2) nqf'" "naccept nqf'"
    "length v2 \<le> (1 + fnft.sg) * fnft.output_speed"
    using fnft.active_dest[OF unbounded(4) q'_nQ]
    by auto
  note len_w_gt = le_less_trans[OF mult_all[of "h + (fnft.sg + 1) * fnft.output_speed + 1"]
      unbounded(5)[unfolded t_def]]
  have len_w: "length w \<ge> h"
    using len_w_gt
    by auto
  obtain v' v'' where w_def: "w = v' @ v''" "length v'' = h"
    using split_long[OF len_w]
    by auto
  have "fnft.computation ninit (u @ u1, (v @ v') @ v'' @ v1) nqf"
    using fnft.comp_trans[OF unbounded(1) ext(1), unfolded w_def]
    by auto
  then obtain qf where qf_def: "init \<leadsto>(u @ u1, (v @ v') @ v'' @ v1) qf" "accept qf"
    using ext(2) equiv
    by (fastforce simp add: fnft.\<tau>_def \<tau>_def)
  have "fnft.computation ninit (u @ u2, (v @ v') @ v'' @ v2) nqf'"
    using fnft.comp_trans[OF unbounded(3) ext'(1), unfolded w_def]
    by auto
  then obtain qf' where qf'_def: "init \<leadsto>(u @ u2, (v @ v') @ v'' @ v2) qf'" "accept qf'"
    using ext'(2) equiv
    by (fastforce simp add: fnft.\<tau>_def \<tau>_def)
  have u_not_Nil: "u \<noteq> []"
    using fnft.output_speed_computation[OF unbounded(1) fnft.init_in_Q] unbounded(5)[unfolded t_def]
    by auto
  have v''_not_Nil: "v'' \<noteq> []"
    using w_def(2)[unfolded h_def]
    by auto
  then have safe_hd_v'': "safe_hd (v'' @ v1) = safe_hd (v'' @ v2)"
    using safe_hd_app''[OF v''_not_Nil]
    by auto
  have reach_init: "reachable init [] [] (safe_hd (u @ u1)) (safe_hd ((v @ v') @ v'' @ v1))"
    using reachable_init
    by auto
  have safe_hd_u1_u2: "safe_hd (u @ u1) = safe_hd (u @ u2)"
    using safe_hd_app''[OF u_not_Nil]
    by auto
  show "False"
    using first_reaches[OF reach_init safe_hd_u1_u2 safe_hd_v'' qf_def(1) qf'_def(1)]
  proof (rule disjE)
    assume "\<exists>r cs c cs'. reachable r ([] @ u) ([] @ cs) (safe_hd u1) c \<and>
      r\<leadsto>(u1, cs' @ v'' @ v1)qf \<and> r\<leadsto>(u2, cs' @ v'' @ v2)qf' \<and> cs @ cs' = v @ v' \<and>
      c = safe_hd (cs' @ v'' @ v1) \<and> c = safe_hd (cs' @ v'' @ v2)"
    then obtain r cs c cs' where tail: "reachable r u cs (safe_hd u1) c"
      "r \<leadsto>(u1, cs' @ v'' @ v1) qf" "c = safe_hd (cs' @ v'' @ v1)"
      by (force simp add: safe_hd_def)
    have le: "(length u1 + 1) * card Q \<le> (fnft.sg + 1) * card Q"
      using ext(3)
      by auto
    show "False"
      using le_trans[OF lin_bounded[OF tail(1,2) qf_def(2) refl tail(3)] le] w_def(2)
      unfolding h_def
      by auto
  next
    assume "\<exists>r cs c cs'. reachable r ([] @ cs) ([] @ v @ v') c (safe_hd (v'' @ v1)) \<and>
      r\<leadsto>(cs' @ u1, v'' @ v1)qf \<and> r\<leadsto>(cs' @ u2, v'' @ v2)qf' \<and> cs @ cs' = u \<and>
      c = safe_hd (cs' @ u1) \<and> c = safe_hd (cs' @ u2)"
    then obtain r' cs c cs' where tail': "reachable r' cs (v @ v') c (safe_hd (v'' @ v1))"
      "r' \<leadsto>(cs' @ u2, v'' @ v2) qf'" "cs @ cs' = u" "c = safe_hd (cs' @ u2)"
      by auto
    obtain f fs where u2_def: "u2 = f # fs"
      using fnft.output_speed_computation[OF ext'(1) q'_nQ] len_w_gt
      by (cases u2) auto
    have comp: "r' \<leadsto>(cs' @ f # fs, v'' @ v2) qf'"
      using tail'(2)[unfolded u2_def] .
    have "c = safe_hd (cs' @ [f])"
      using tail'(4)
      by (auto simp add: u2_def safe_hd_def split: list.splits)
         (metis Cons_eq_append_conv list.inject)
    obtain r ds y' ds' where tail: "reachable r u (v @ v' @ ds) (Symb f) y'"
      "r \<leadsto>(f # fs, ds') qf'" "v'' @ v2 = ds @ ds'" "y' = safe_hd ds'"
      using comp_suf[OF tail'(1) _ safe_hd_v'' comp, OF tail'(4)[unfolded u2_def]]
      by (auto simp add: safe_hd_def tail'(3))
    have r_Q: "r \<in> Q"
      using tail(1)
      by (auto simp add: reachable_def)
    have comp': "fnft.computation q' (f # fs, (v' @ ds) @ ds') nqf'"
      using ext'(1)[unfolded w_def u2_def, simplified] tail(3)
      by auto
    have len_ds': "length ds' \<le> h + (fnft.sg + 1) * fnft.output_speed"
      using arg_cong[OF tail(3), of length] w_def(2) ext'(3)
      by auto
    have len_v': "card nQ * card Q * fnft.output_speed * (1 + length ds') < length (v' @ ds @ ds')"
    proof -
      have "card nQ * card Q * fnft.output_speed * (1 + length ds') \<le> t"
        using len_ds'
        by (auto simp add: t_def)
      also have "\<dots> < length (v' @ v'')"
        using unbounded(5)[unfolded w_def(1)] .
      finally show ?thesis
        by (auto simp add: tail(3)[symmetric])
    qed
    obtain as' bs'' where rem: "fnft.computation q' (as', bs'') nqf'" "r \<leadsto>(as', ds') qf'"
      "safe_hd (f # fs) = safe_hd as'" "length bs'' < length ((v' @ ds) @ ds')"
      using conflict[OF comp' tail(2) q'_nQ r_Q] len_v'
      by auto
    have wit1: "(u @ as', v @ bs'') \<in> \<tau>"
      using fnft.comp_trans[OF unbounded(3) rem(1)] ext'(2) fnft.\<tau>_def equiv
      by auto
    have wit2: "(u @ as', v @ v' @ ds @ ds') \<in> \<tau>"
      using tail(1) rem(2) rem(3)[symmetric] tail(4)[symmetric] qf'_def(2)
      by (fastforce simp add: reachable_def \<tau>_def safe_hd_def split: list.splits)
    show "False"
      using functional[OF wit1 wit2] rem(4)
      by auto
  qed
qed

end

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

interpretation otdfa: oTDFA otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using otdfa_det otdfa_finite_Q otdfa_init_in_Q otdfa_closed[rotated]
        otdfa_move_left otdfa_move_right otdfa_no_step otdfa_move_one
  by unfold_locales auto

interpretation nec: necessary' ninit n\<delta> naccept nQ otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using functional
  by unfold_locales (auto simp add: equiv tdfa_equiv_otdfa)

(* Theorem 10 *)

lemma bounded: "\<exists>K. fnft.bounded K"
  using nec.bounded .

end

end