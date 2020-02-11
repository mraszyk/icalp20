theory Computation
  imports Main
begin

lemma split_app: "\<And>xs ys xs' ys'. xs @ ys = xs' @ ys' \<Longrightarrow> length xs \<le> length xs' \<Longrightarrow>
  \<exists>ds. xs' = xs @ ds"
  by (metis (full_types) append_eq_append_conv_if append_eq_conv_conj)

lemma split_app': "\<And>xs ys xs' ys'. xs @ ys = xs' @ ys' \<Longrightarrow> length xs \<le> length xs' \<Longrightarrow>
  \<exists>es. ys = es @ ys'"
  by (simp add: append_eq_append_conv_if)

lemma map_ext:
  assumes "map f xs = ys @ ys'"
  shows "\<exists>zs zs'. xs = zs @ zs' \<and> map f zs = ys \<and> map f zs' = ys'"
proof -
  define zs where "zs = take (length ys) xs"
  define zs' where "zs' = drop (length ys) xs"
  have "xs = zs @ zs'" "map f zs = ys" "map f zs' = ys'"
    using iffD1[OF append_eq_conv_conj, OF assms[symmetric]]
    by (auto simp add: zs_def zs'_def take_map drop_map)
  then show ?thesis
    by auto
qed

lemma app_decomp: "length xs = length (ys @ ys') \<Longrightarrow>
  \<exists>zs zs'. xs = zs @ zs' \<and> length zs = length ys \<and> length zs' = length ys'"
  by (metis append_eq_conv_conj length_drop length_rev rev_take)

lemma singleton_dest: "length xs = Suc 0 \<Longrightarrow> \<exists>x. xs = [x]"
  by (cases xs) auto

lemma set_zip: "set (zip xs ys) \<subseteq> set xs \<times> set ys"
  by (induction xs arbitrary: ys) (auto dest: set_zip_leftD set_zip_rightD)

fun iter_concat :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "iter_concat 0 xs = []"
| "iter_concat (Suc n) xs = xs @ iter_concat n xs"

lemma iter_concat_length: "length (iter_concat n xs) = n * length xs"
  by (induction n xs rule: iter_concat.induct) auto

lemma card_finite_product_subset:
  "finite Q \<Longrightarrow> QS' \<subseteq> Q \<times> Q \<Longrightarrow> card QS' \<le> card Q * card Q"
  by (metis card_cartesian_product card_mono finite_cartesian_product)

lemma finite_bounded_lists: "finite {bs :: ('b :: finite) list. length bs \<le> n}"
proof (induction n)
  case (Suc n)
  have split: "{bs :: 'b list. length bs \<le> Suc n} = {bs. length bs \<le> n} \<union> {bs. length bs = Suc n}"
    by auto
  have "{bs :: 'b list. length bs = Suc n} \<subseteq> (\<Union>(b, bs) \<in> UNIV \<times> {bs. length bs \<le> n}. {b # bs})"
  proof (rule subsetI)
    fix x
    assume "x \<in> {bs :: 'b list. length bs = Suc n}"
    then show "x \<in> (\<Union>(b, bs)\<in>UNIV \<times> {bs. length bs \<le> n}. {b # bs})"
      by (cases x) auto
  qed
  moreover have "finite (\<Union>(b, bs) \<in> UNIV \<times> {bs :: 'b list. length bs \<le> n}. {b # bs})"
    using Suc by auto
  ultimately have "finite {bs :: 'b list. length bs = Suc n}"
    using infinite_super by blast
  with Suc split show ?case
    by auto
qed auto

locale NFT =
  fixes init :: "'s"
    and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> ('b :: finite) list \<Rightarrow> bool"
    and accept :: "'s \<Rightarrow> bool"
    and Q :: "'s set"
  assumes finite_Q: "finite Q"
  and finite_\<delta>: "q \<in> Q \<Longrightarrow> finite {x. \<delta> q a x}"
  and init_in_Q: "init \<in> Q"
  and \<delta>_closed: "q \<in> Q \<Longrightarrow> \<delta> q a (q', bs) \<Longrightarrow> q' \<in> Q"
begin

(* notion of computation and computed relation *)

inductive computation :: "'s \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 's \<Rightarrow> bool" ("_/\<leadsto>_/_" [64,64,64]63) where
  base[intro]: "q \<leadsto>([], []) q"
| step[intro]: "\<delta> q a (q', bs) \<Longrightarrow> q' \<leadsto>(as, bs') q'' \<Longrightarrow> q \<leadsto>(a # as, bs @ bs') q''"

definition \<tau> :: "('a list \<times> 'b list) set" where
  "\<tau> = {(as, bs). \<exists>q. init \<leadsto>(as, bs) q \<and> accept q}"

definition active :: "'s \<Rightarrow> 'b list \<Rightarrow> bool" where
  "active q bs \<longleftrightarrow> (\<exists>q' as bs'. q \<leadsto>(as, bs @ bs') q' \<and> accept q')"

definition "bounded K \<equiv> \<forall>q q' u v v'. init \<leadsto>(u, v @ v') q \<and> active q [] \<and>
  init \<leadsto>(u, v) q' \<and> active q' v' \<longrightarrow> length v' \<le> K"

(* lemmas *)

lemma one_step: "\<delta> q a (q', bs) \<Longrightarrow> q \<leadsto>([a], bs) q'"
  using computation.step by fastforce

lemma step_dest: "q \<leadsto>([a], bs) q' \<Longrightarrow> \<delta> q a (q', bs)"
  apply (induction q "([a], bs)" q' rule: computation.induct)
  using computation.cases by fastforce

lemma comp_trans: "q \<leadsto>(as, bs) q' \<Longrightarrow> q' \<leadsto>(as', bs') q'' \<Longrightarrow> q \<leadsto>(as @ as', bs @ bs') q''"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct) auto

lemma computation_snoc: "q \<leadsto>(as, bs) q' \<Longrightarrow> \<delta> q' a (q'', bs') \<Longrightarrow> q \<leadsto>(as @ [a], bs @ bs') q''"
proof -
  assume assms: "q \<leadsto>(as, bs) q'" "\<delta> q' a (q'', bs')"
  from assms(2) have "q' \<leadsto>([a], bs') q''"
    using step by fastforce
  with assms(1) show "q \<leadsto>(as @ [a], bs @ bs') q''"
    using comp_trans by auto
qed

lemma no_step: "q \<leadsto>(as, bs) q' \<Longrightarrow> as = [] \<Longrightarrow> bs = [] \<and> q = q'"
  by (induction q "(as, bs)" q' rule: computation.induct) auto

lemma computation_split: "q \<leadsto>(as @ as', bs'') q' \<Longrightarrow>
  \<exists>q'' bs bs'. q \<leadsto>(as, bs) q'' \<and> q'' \<leadsto>(as', bs') q' \<and> bs'' = bs @ bs'"
proof (induction q "(as @ as', bs'')" q' arbitrary: as as' bs'' rule: computation.induct)
  case (step q' bs q a asa bs' q'')
  then show ?case
  proof (cases as)
    case (Cons x xs)
    then show ?thesis
      using step(1,2,4) step(3)[of xs as']
      by force
  qed auto
qed auto

lemma comp_rev_induct: "q\<leadsto>(as, bs) q' \<Longrightarrow>
  (\<And>q. P q [] [] q) \<Longrightarrow>
  (\<And>q a q' bs as bs' q''. P q as bs q'' \<Longrightarrow> q\<leadsto>(as, bs)q'' \<Longrightarrow> \<delta> q'' a (q', bs') \<Longrightarrow>
    P q (as @ [a]) (bs @ bs') q') \<Longrightarrow>
  P q as bs q'"
proof (induction as arbitrary: q bs q' rule: rev_induct)
  case Nil
  then show ?case
    using no_step
    by fastforce
next
  case (snoc x xs)
  obtain q'' cs cs' where split: "q \<leadsto>(xs, cs) q''" "q'' \<leadsto>([x], cs') q'" "bs = cs @ cs'"
    using computation_split[OF snoc(2)] by auto
  have P_xs: "P q xs cs q''"
    using snoc(1)[OF split(1) snoc(3,4)] by auto
  show ?case
    using snoc(4)[OF P_xs split(1) step_dest[OF split(2)]]
    by (auto simp add: split(3))
qed

lemma comp_closed: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> q' \<in> Q"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto simp add: \<delta>_closed)

inductive computation_ext :: "'s \<Rightarrow> 'a list \<times> ('s \<times> 'b list) list \<Rightarrow> 's \<Rightarrow> bool"
    ("_/\<leadsto>e_/_" [64,64,64]63) where
  base_ext[intro]: "q \<leadsto>e([], []) q"
| step_ext[intro]: "\<delta> q a (q', bs) \<Longrightarrow> q' \<leadsto>e(as, qs) q'' \<Longrightarrow> q \<leadsto>e(a # as, (q', bs) # qs) q''"

lemma computation_ext_no_step: "q \<leadsto>e([], []) q' \<Longrightarrow> q = q'"
  by (auto elim: computation_ext.cases)

lemma computation_ext_Cons_dest: "q\<leadsto>e(a # as', qb # qbs')q' \<Longrightarrow> \<delta> q a qb"
  by (auto elim: computation_ext.cases)

lemma computation_ext_trans: "q \<leadsto>e(as, qs) q' \<Longrightarrow> q' \<leadsto>e(as', qs') q'' \<Longrightarrow>
  q \<leadsto>e(as @ as', qs @ qs') q''"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct) auto

lemma computation_ext_length: "q \<leadsto>e(as, qs) q' \<Longrightarrow> length qs = length as"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct) auto

lemma computation_ext_sound: "q \<leadsto>e(as, qs) q' \<Longrightarrow> q \<leadsto>(as, concat (map snd qs)) q'"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct) auto

lemma computation_ext_complete: "q \<leadsto>(as, bs) q' \<Longrightarrow>
  \<exists>qs. q \<leadsto>e(as, qs) q' \<and> bs = concat (map snd qs)"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct) auto

lemma computation_ext_split: "length as = length qbs \<Longrightarrow>
  q \<leadsto>e(as @ a # as', qbs @ (q'', bs) # qbs') q' \<Longrightarrow>
  q \<leadsto>e(as @ [a], qbs @ [(q'', bs)]) q'' \<and> q'' \<leadsto>e(as', qbs') q'"
  by (induction as qbs arbitrary: q rule: list_induct2) (auto elim: computation_ext.cases)

lemma computation_ext_split_left: "q \<leadsto>e(as, qs) q' \<Longrightarrow> n < length qs \<Longrightarrow>
  q \<leadsto>e(take (Suc n) as, take (Suc n) qs) (fst (qs ! n))"
proof (induction q "(as, qs)" q' arbitrary: as qs n rule: computation_ext.induct)
  case (step_ext q' bs q a as qs q'')
  then show ?case
  proof (cases n)
    case (Suc nat)
    then show ?thesis
      using step_ext(1,2,4) step_ext(3)[of nat]
      by auto
  qed auto
qed auto

lemma computation_ext_split_right: "q \<leadsto>e(as, qs) q' \<Longrightarrow> n < length qs \<Longrightarrow>
  (fst (qs ! n)) \<leadsto>e(drop (Suc n) as, drop (Suc n) qs) q'"
proof (induction q "(as, qs)" q' arbitrary: as qs n rule: computation_ext.induct)
  case (step_ext q' bs q a as qs q'')
  then show ?case
  proof (cases n)
    case (Suc nat)
    then show ?thesis
      using step_ext(1,2,4) step_ext(3)[of nat]
      by auto
  qed auto
qed auto

lemma computation_ext_closed: "q \<leadsto>e(as, qs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> (r, bs) \<in> set qs \<Longrightarrow> r \<in> Q"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct)
     (auto simp add: \<delta>_closed)

definition all_trans :: "('s \<times> 'b list) set" where
  "all_trans = {x. \<exists>(q, a) \<in> (Q \<times> (UNIV :: 'a set)). \<delta> q a x}"

lemma all_trans_finite: "finite all_trans"
proof -
  have fin_Q_UNIV: "finite (Q \<times> (UNIV :: 'a set))"
    using finite_Q by auto
  have "all_trans \<subseteq> \<Union>((\<lambda>(q, a). {x. \<delta> q a x}) ` (Q \<times> (UNIV :: 'a set)))"
    unfolding all_trans_def by auto
  moreover have "finite (\<Union>((\<lambda>(q, a). {x. \<delta> q a x}) ` (Q \<times> (UNIV :: 'a set))))"
    using fin_Q_UNIV finite_\<delta> by auto
  ultimately show ?thesis
    using infinite_super by blast
qed

lemma all_trans_step: "q \<in> Q \<Longrightarrow> \<delta> q a x \<Longrightarrow> x \<in> all_trans"
  unfolding all_trans_def by auto

definition max_fanout :: nat where
  "max_fanout = Max (length ` snd ` all_trans \<union> {1})"

lemma max_fanout_step: "q \<in> Q \<Longrightarrow> \<delta> q a (q', bs) \<Longrightarrow> length bs \<le> max_fanout"
  unfolding max_fanout_def using all_trans_finite all_trans_step
  by (metis Max_ge UnCI finite.emptyI finite.insertI finite_UnI finite_imageI image_eqI snd_conv)

lemma max_fanout_computation: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> length bs \<le> length as * max_fanout"
  apply (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
  using max_fanout_step \<delta>_closed by (auto simp add: add_le_mono)

lemma max_fanout_ext_computation: "q \<leadsto>e(as, qbs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> (q'', bs) \<in> set qbs \<Longrightarrow>
  length bs \<le> max_fanout"
  apply (induction q "(as, qbs)" q' arbitrary: as qbs rule: computation_ext.induct)
  using max_fanout_step \<delta>_closed by auto

lemma max_fanout_pos: "max_fanout \<ge> 1"
proof -
  have fin: "finite (length ` snd ` all_trans \<union> {1})"
    using all_trans_finite
    by auto
  show ?thesis
    using Max_ge[OF fin, of 1]
    by (auto simp add: max_fanout_def)
qed

lemma computation_split_out: "q \<leadsto>(as'', bs @ bs') q' \<Longrightarrow> q \<in> Q \<Longrightarrow>
  \<exists>q'' as as' cs cs'. q \<leadsto>(as, cs) q'' \<and> q'' \<leadsto>(as', cs') q' \<and> as'' = as @ as' \<and>
    bs @ bs' = cs @ cs' \<and> length cs \<le> length bs \<and> length bs - length cs \<le> max_fanout"
proof (induction q "(as'', bs @ bs')" q' arbitrary: as'' bs bs' rule: computation.induct)
  case (step q a q' bsa as bsa' q'')
  from step(1,5) have length_bsa: "length bsa \<le> max_fanout"
    using max_fanout_step by auto
  show ?case
  proof (cases "length bsa \<le> length bs")
    case True
    with step(4) obtain bsa'' where "bs = bsa @ bsa''"
      by (metis append_eq_append_conv_if append_eq_conv_conj)
    then show ?thesis
      using step(1,2,4,5) step(3)[of bsa'' bs'] \<delta>_closed by fastforce
  next
    case False
    with step length_bsa have "q\<leadsto>([], [])q \<and> q\<leadsto>(a # as, bsa @ bsa')q'' \<and> a # as = [] @ (a # as) \<and>
      bs @ bs' = [] @ (bsa @ bsa') \<and> length [] \<le> length bs \<and> length bs - length [] \<le> max_fanout"
      using computation.step by fastforce
    then show ?thesis
      by blast
  qed
qed auto

lemma computation_ext_rem:
  assumes "q \<leadsto>e(as, qbs' @ (q', bs) # qbs'' @ (q', bs') # qbs''') q''"
  shows "\<exists>cs' cs'' cs''' c' c'' bs' bs'''.
    q \<leadsto>(cs' @ c' # cs''', bs' @ bs @ bs''') q'' \<and>
    bs' = concat (map snd qbs') \<and> bs''' = concat (map snd qbs''') \<and>
    as = cs' @ c' # cs'' @ c'' # cs''' \<and> length cs' = length qbs' \<and>
    length cs'' = length qbs'' \<and> length cs''' = length qbs'''"
proof -
  note len_as = computation_ext_length[OF assms(1), symmetric]
  obtain as' as'' as''' a a' where
    decomp': "as = as' @ [a] @ as'' @ [a'] @ as'''" "length as' = length qbs'"
    "length as'' = length qbs''" "length as''' = length qbs'''"
    using app_decomp[OF len_as]
    by (auto dest!: app_decomp[of _ "[(q', bs)]" "qbs'' @ [(q', bs')] @ qbs'''", simplified]
        app_decomp[of _ qbs'' "[(q', bs')] @ qbs'''", simplified]
        app_decomp[of _ "[(q', bs')]" "qbs'''", simplified]
        singleton_dest)
  have assoc: "q \<leadsto>e(as' @ a # as'' @ [a'] @ as''',
    qbs' @ (q', bs) # qbs'' @ [(q', bs')] @ qbs''') q''"
    using assms(1)[unfolded decomp']
    by auto
  have split: "q \<leadsto>e(as' @ [a], qbs' @ [(q', bs)]) q'" "q'\<leadsto>e(as'' @ a' # as''',
    qbs'' @ (q', bs') # qbs''') q''"
    using computation_ext_split[OF decomp'(2) assoc]
    by auto
  have split': "q' \<leadsto>e(as''', qbs''') q''"
    using computation_ext_split[OF decomp'(3) split(2)]
    by auto
  define bs' where "bs' = concat (map snd qbs')"
  define bs''' where "bs''' = concat (map snd qbs''')"
  have trans: "q \<leadsto>(as' @ [a], bs' @ bs) q'"
    using computation_ext_sound[OF split(1)]
    by (auto simp add: bs'_def)
  have trans': "q' \<leadsto>(as''', bs''') q''"
    using computation_ext_sound[OF split']
    by (auto simp add: bs'''_def)
  show ?thesis
    using comp_trans[OF trans trans'] decomp'(2,3,4)
    by (fastforce simp add: bs'_def bs'''_def decomp'(1))
qed

lemma computation_long_split: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> length as \<ge> 1 + card Q \<Longrightarrow>
  \<exists>as' bs'. q \<leadsto>(as', bs') q' \<and> length as' < length as"
proof -
  assume assms_comp: "q \<leadsto>(as, bs) q'" "q \<in> Q"
  obtain qbs where qbs_def: "q \<leadsto>e(as, qbs) q'" "bs = concat (map snd qbs)"
    using computation_ext_complete[OF assms_comp(1)]
    by auto
  then have qbs_len: "length qbs = length as"
    using computation_ext_length by auto
  assume assms_len: "length as \<ge> 1 + card Q"
  define qs where "qs = map fst qbs"
  have qs_sub: "set qs \<subseteq> Q"
    using computation_ext_closed[OF qbs_def(1) assms_comp(2)]
    by (auto simp add: qs_def)
  have not_distinct: "\<not>distinct qs"
  proof (rule ccontr)
    assume "\<not>\<not>distinct qs"
    then have contr: "distinct qs"
      by auto
    have card_qs: "card (set qs) \<ge> 1 + card Q"
      using distinct_card[OF contr] assms_len
      by (auto simp add: qs_def qbs_len)
    show "False"
      using card_qs card_mono[OF finite_Q qs_sub]
      by auto
  qed
  obtain q'' qs' qs'' qs''' where "qs = qs' @ [q''] @ qs'' @ [q''] @ qs'''"
    using not_distinct_decomp[OF not_distinct]
    by auto
  then obtain qbs' qbs'' qbs''' bs bs' where
    decomp: "qbs = qbs' @ (q'', bs) # qbs'' @ (q'', bs') # qbs'''"
    using map_ext[of fst qbs qs' "[q''] @ qs'' @ [q''] @ qs'''"]
          map_ext[of fst _ "qs''" "[q''] @ qs'''"]
    by (fastforce simp add: qs_def)
  show "\<exists>as' bs'. q \<leadsto>(as', bs') q' \<and> length as' < length as"
    using computation_ext_rem[OF qbs_def(1)[unfolded decomp(1)]]
    by auto
qed

lemma comp_norm: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>as' bs'. q \<leadsto>(as', bs') q' \<and> length as' \<le> card Q"
proof (induction "length as" arbitrary: as bs rule: nat_less_induct)
  case 1
  then show ?case
  proof (cases "length as \<le> card Q")
    case False
    obtain as' bs' where nex: "q \<leadsto>(as', bs') q'" "length as' < length as"
      using computation_long_split[OF 1(2,3)] False
      by auto
    then show ?thesis
      using 1(1,3)
      by auto
  qed auto
qed

lemma pumping: "q \<leadsto>(as, bs) q \<Longrightarrow> q \<leadsto>(iter_concat n as, iter_concat n bs) q"
  by (induction n) (auto intro: comp_trans)

lemma active_comp: "active q' bs \<Longrightarrow> q \<leadsto>(as, bs') q' \<Longrightarrow> active q (bs' @ bs)"
  using comp_trans
  by (fastforce simp add: active_def)

lemma active_mono: "active q (bs @ bs') \<Longrightarrow> active q bs"
  unfolding active_def by auto

lemma active_extend: "q \<leadsto>(as, bs @ bs') q' \<Longrightarrow> active q' bs \<Longrightarrow> active q bs"
  unfolding active_def using comp_trans by force

lemma active_Nil_dest: "active q [] \<Longrightarrow> q \<in> Q \<Longrightarrow>
  \<exists>as bs' q'. q \<leadsto>(as, bs') q' \<and> accept q' \<and> length as \<le> card Q \<and> length bs' \<le> card Q * max_fanout"
  using comp_norm max_fanout_computation
  apply (auto simp add: active_def)
  apply (meson dual_order.trans mult_le_mono1)
  done

lemma active_dest:
  assumes "active q bs" "q \<in> Q"
  shows "\<exists>as bs' q'. q \<leadsto>(as, bs @ bs') q' \<and> accept q' \<and>
    length bs' \<le> (1 + card Q) * max_fanout"
proof -
  obtain as bs' q' where act: "q \<leadsto>(as, bs @ bs') q'" "accept q'"
    using assms(1)
    by (auto simp add: active_def)
  then show ?thesis
  proof (cases "length bs' \<ge> max_fanout")
    case True
    have app: "bs @ bs' = (bs @ take max_fanout bs') @ (drop max_fanout bs')"
      using True
      by auto
    obtain q'' as' as'' cs cs' where split: "q\<leadsto>(as', cs)q''" "q''\<leadsto>(as'', cs')q'"
      "as = as' @ as''"
      "(bs @ take max_fanout bs') @ drop max_fanout bs' = cs @ cs'"
      "length cs \<le> length (bs @ take max_fanout bs')"
      "length (bs @ take max_fanout bs') - length cs \<le> max_fanout"
      using computation_split_out[OF act(1)[unfolded app] assms(2)]
      by auto
    obtain ds where ds_def: "cs = bs @ ds" "length ds \<le> max_fanout"
      using split(5,6) True split_app[OF split(4)[unfolded app[symmetric]]]
      by fastforce
    note q''_Q = comp_closed[OF split(1) assms(2)]
    obtain es fs where es_fs_def: "q''\<leadsto>(es, fs)q'" "length es \<le> card Q"
      using comp_norm[OF split(2) q''_Q]
      by auto
    have fs_len: "length fs \<le> card Q * max_fanout"
      using max_fanout_computation[OF es_fs_def(1) q''_Q] es_fs_def(2)
      by (meson dual_order.trans mult_le_mono1)
    show ?thesis
      using comp_trans[OF split(1)[unfolded ds_def(1)] es_fs_def(1)] ds_def(2) fs_len act(2)
      by fastforce
  qed fastforce
qed

lemma bounded_mono: "K \<le> K' \<Longrightarrow> bounded K \<Longrightarrow> bounded K'"
  by (fastforce simp add: bounded_def)

lemma bounded_dest: "\<And>q q' u v v'. bounded K \<Longrightarrow> init \<leadsto>(u, v @ v') q \<Longrightarrow> active q [] \<Longrightarrow>
  init \<leadsto>(u, v) q' \<Longrightarrow> active q' v' \<Longrightarrow> length v' \<le> K"
  by (auto simp add: bounded_def)

end

locale bNFT = NFT init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> ('b :: finite) list \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
fixes K :: nat
assumes bounded: "bounded K"
begin

lemmas bounded' = bounded_dest[OF bounded]

end

locale fNFT = NFT init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> ('b :: finite) list \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes functional: "(x, y) \<in> \<tau> \<Longrightarrow> (x, y') \<in> \<tau> \<Longrightarrow> y = y'"

datatype 'a Al = Symb (the_Symb: 'a) | EOF

locale TDFA =
  fixes init :: "'s"
  and \<delta> :: "'s \<Rightarrow> ('a :: finite) Al \<times> ('b :: finite) Al \<Rightarrow> 's \<times> bool \<times> bool \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set"
  assumes det: "\<delta> q z x \<Longrightarrow> \<delta> q z x' \<Longrightarrow> x = x'" and
  finite_Q: "finite Q" and
  init_in_Q: "init \<in> Q" and
  closed: "q \<in> Q \<Longrightarrow> \<delta> q z (q', b1, b2) \<Longrightarrow> q' \<in> Q" and
  move_left: "\<delta> q (a, b) (q', True, b2) \<Longrightarrow> a \<noteq> EOF" and
  move_right: "\<delta> q (a, b) (q', b1, True) \<Longrightarrow> b \<noteq> EOF" and
  no_step: "\<delta> q (a, b) (q', False, False) \<Longrightarrow> a = EOF \<and> b = EOF"
begin

(* notion of computation and computed relation *)

inductive computation :: "'s \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 's \<Rightarrow> bool" ("_/\<leadsto>_/_" [64,64,64]63) where
  step_L[intro]: "\<delta> q (Symb a, EOF) (q', True, False) \<Longrightarrow> q' \<leadsto>(as, []) q'' \<Longrightarrow>
    q \<leadsto>(a # as, []) q''"
| step_R[intro]: "\<delta> q (EOF, Symb b) (q', False, True) \<Longrightarrow> q' \<leadsto>([], bs) q'' \<Longrightarrow>
    q \<leadsto>([], b # bs) q''"
| step_TT[intro]: "\<delta> q (Symb a, Symb b) (q', True, True) \<Longrightarrow>  q' \<leadsto>(as, bs) q'' \<Longrightarrow>
    q \<leadsto>(a # as, b # bs) q''"
| step_TF[intro]: "\<delta> q (Symb a, Symb b) (q', True, False) \<Longrightarrow>  q' \<leadsto>(as, b # bs) q'' \<Longrightarrow>
    q \<leadsto>(a # as, b # bs) q''"
| step_FT[intro]: "\<delta> q (Symb a, Symb b) (q', False, True) \<Longrightarrow>  q' \<leadsto>(a # as, bs) q'' \<Longrightarrow>
    q \<leadsto>(a # as, b # bs) q''"
| last_step[intro]: "\<delta> q (EOF, EOF) (q', False, False) \<Longrightarrow> q \<leadsto>([], []) q'"

definition \<tau> :: "('a list \<times> 'b list) set" where
  "\<tau> = {(as, bs). \<exists>q. init \<leadsto>(as, bs) q \<and> accept q}"

(* lemmas *)

inductive outs :: "'a Al \<Rightarrow> 's \<Rightarrow> ('b \<times> 's) list \<Rightarrow> 's \<Rightarrow> 'b Al \<Rightarrow> bool \<Rightarrow> bool" where
  outs_base: "\<delta> q (Symb a, b) (q', True, \<beta>) \<Longrightarrow> outs (Symb a) q [] q' b \<beta>"
| outs_step: "\<delta> q (a, Symb b') (q'', False, True) \<Longrightarrow> outs a q'' xs q' b \<beta> \<Longrightarrow>
    outs a q ((b', q'') # xs) q' b \<beta>"
| outs_last: "\<delta> q (EOF, EOF) (q', False, False) \<Longrightarrow> outs EOF q [] q EOF False"

lemma outs_drop: "outs a q (xs' @ (b'', q'') # xs'') q' b \<beta> \<Longrightarrow> outs a q'' xs'' q' b \<beta>"
proof (induction a q "xs' @ (b'', q'') # xs''" q' b \<beta> arbitrary: xs' rule: outs.induct)
  case (outs_step q a b' q'' xs q' b \<beta>)
  then show ?case
    by (cases xs') auto
qed auto

lemma outs_rem: "outs a q (xs @ (b', q'') # xs' @ (b'', q'') # xs'') q' b \<beta> \<Longrightarrow>
  outs a q (xs @ (b', q'') # xs'') q' b \<beta>"
proof (induction a q "xs @ (b', q'') # xs' @ (b'', q'') # xs''" q' b \<beta> arbitrary: xs
  rule: outs.induct)
  case (outs_step q a b' q'' ixs q' b \<beta>)
  show ?case
    using outs_step(1,2,4) outs.intros(2)[OF outs_step(1) outs_step(3)] outs_drop outs.outs_step
    by (cases xs) auto
qed auto

lemma outs_closed: "outs a q xs q' b \<beta> \<Longrightarrow> q \<in> Q \<Longrightarrow> (b', q'') \<in> set xs \<Longrightarrow> q'' \<in> Q"
  apply (induction a q xs q' b \<beta> rule: outs.induct)
  using closed by auto

lemma outs_closed': "outs a q xs q' b \<beta> \<Longrightarrow> q \<in> Q \<Longrightarrow> q' \<in> Q"
  apply (induction a q xs q' b \<beta> rule: outs.induct)
  using closed by auto

lemma outs_norm:
  assumes "outs a q (x # xs) q' b \<beta>" "q \<in> Q" "length xs \<ge> 1 + card Q"
  shows "\<exists>xs'. outs a q (x # xs') q' b \<beta> \<and> length xs' < length xs"
proof -
  define qs where "qs = map snd xs"
  have qs_sub: "set qs \<subseteq> Q"
    using outs_closed[OF assms(1,2)]
    by (fastforce simp add: qs_def)
  have not_distinct: "\<not>distinct qs"
  proof (rule ccontr)
    assume "\<not>\<not>distinct qs"
    then have contr: "distinct qs"
      by auto
    have card_qs: "card (set qs) \<ge> 1 + card Q"
      using distinct_card[OF contr] assms(3)
      by (auto simp add: qs_def)
    show "False"
      using card_qs card_mono[OF finite_Q qs_sub]
      by auto
  qed
  obtain q'' qs' qs'' qs''' where "qs = qs' @ [q''] @ qs'' @ [q''] @ qs'''"
    using not_distinct_decomp[OF not_distinct]
    by auto
  then obtain xs' xs'' xs''' bs bs' where
    decomp: "xs = xs' @ (bs, q'') # xs'' @ (bs', q'') # xs'''"
    using map_ext[of snd xs qs' "[q''] @ qs'' @ [q''] @ qs'''"]
          map_ext[of snd _ "qs''" "[q''] @ qs'''"]
    by (fastforce simp add: qs_def)
  have outs': "outs a q ((x # xs') @ (bs, q'') # xs'' @ (bs', q'') # xs''') q' b \<beta>"
    using assms(1)[unfolded decomp]
    by auto
  show ?thesis
    using outs_rem[OF outs']
    by (auto simp add: decomp)
qed

lemma outs_Nil_dest: "outs EOF q xs q'' EOF False \<Longrightarrow> \<delta> q'' (EOF, EOF) (q', False, False) \<Longrightarrow>
  q \<leadsto>([], map fst xs) q'"
  by (induction "EOF :: 'a Al" q xs q'' "EOF :: 'b Al" False rule: outs.induct) auto

lemma outs_Nil_intro: "q \<leadsto>([], bs) q' \<Longrightarrow> \<exists>xs q''. outs EOF q xs q'' EOF False \<and>
  \<delta> q'' (EOF, EOF) (q', False, False) \<and> bs = map fst xs"
proof (induction q "([] :: 'a list, bs)" q' arbitrary: bs rule: computation.induct)
  case (step_R q b q' bs q'')
  obtain xs q''' where props: "outs EOF q' xs q''' EOF False"
    "\<delta> q''' (EOF, EOF) (q'', False, False)" "bs = map fst xs"
    using step_R(3)
    by auto
  show ?case
    using outs_step[OF step_R(1), OF props(1)] props(2,3)
    by (auto intro!: exI[of _ q'''] exI[of _ "(b, q') # xs"])
next
  case (last_step q q')
  show ?case
    using outs_last[OF last_step] last_step
    by auto
qed

definition "safe_hd bs' = (case bs' of [] \<Rightarrow> EOF | b # bs \<Rightarrow> Symb b)"

lemma safe_hd_Nil: "safe_hd [] = EOF"
  by (auto simp add: safe_hd_def)

lemma outs_Cons_dest: "outs (Symb a) q xs q'' b \<beta> \<Longrightarrow> q'' \<leadsto>(as, bs') q' \<Longrightarrow>
  (b = EOF \<longrightarrow> \<not>\<beta>) \<Longrightarrow> (\<not>\<beta> \<longrightarrow> b = safe_hd bs') \<Longrightarrow>
  bs = map fst xs @ (if \<beta> then (case b of Symb b' \<Rightarrow> b') # bs' else bs') \<Longrightarrow>
  q \<leadsto>(a # as, bs) q'"
  by (induction "Symb a" q xs q'' b \<beta> arbitrary: bs rule: outs.induct)
     (auto simp add: safe_hd_def split: list.splits Al.splits)

lemma outs_move_right: "outs a q xs q'' b'' True \<Longrightarrow> b'' \<noteq> EOF"
  apply (induction a q xs q'' b'' True rule: outs.induct)
  using move_right by auto

lemma outs_Cons_intro: "q \<leadsto>(a # as, bs) q' \<Longrightarrow> \<exists>xs q'' b \<beta> bs'. outs (Symb a) q xs q'' b \<beta> \<and>
  q'' \<leadsto>(as, bs') q' \<and> (b = EOF \<longrightarrow> \<not>\<beta>) \<and> (\<not>\<beta> \<longrightarrow> b = safe_hd bs') \<and>
  bs = map fst xs @ (if \<beta> then (case b of Symb b' \<Rightarrow> b') # bs' else bs')"
proof (induction q "(a # as, bs)" q' arbitrary: a as bs rule: computation.induct)
  case (step_L q a q' as q'')
  show ?case
    using outs_base[OF step_L(1)] step_L(2)
    by (auto simp add: safe_hd_def)
next
  case (step_TT q a b q' as bs q'')
  show ?case
    using outs_base[OF step_TT(1)] step_TT(2)
    by (fastforce simp add: safe_hd_def intro: outs.intros)
next
  case (step_TF q a b q' as bs q'')
  show ?case
    using outs_base[OF step_TF(1)] step_TF(2)
    by (fastforce simp add: safe_hd_def)
next
  case (step_FT q a b q' as bs q'')
  obtain q''' xs b' \<beta> bs' where props: "outs (Symb a) q' xs q''' b' \<beta>"
    "q'''\<leadsto>(as, bs')q''" "b' = EOF \<longrightarrow> \<not> \<beta>" "\<not> \<beta> \<longrightarrow> b' = safe_hd bs'"
    "bs = map fst xs @ (if \<beta> then (case b' of Symb b' \<Rightarrow> b') # bs' else bs')"
    using step_FT(3)
    by blast
  show ?case
    using outs_step[OF step_FT(1), OF props(1)] props(2,3,4,5)
    by (auto intro!: exI[of _ q'''] exI[of _ "(b, q') # xs"] exI[of _ b'])
qed

definition reachable :: "'s \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'a Al \<Rightarrow> 'b Al \<Rightarrow> bool" where
  "reachable q as bs a b \<longleftrightarrow> q \<in> Q \<and> (\<forall>u v q'. a = safe_hd u \<and> b = safe_hd v \<and>
    q \<leadsto>(u, v) q' \<and> accept q' \<longrightarrow> (as @ u, bs @ v) \<in> \<tau>)"

lemma ext_step: "\<delta> q (a, b) (q', b1, b2) \<Longrightarrow> q' \<leadsto>(u, v) q'' \<Longrightarrow> (\<not>b1 \<Longrightarrow> a = safe_hd u) \<Longrightarrow>
  (\<not>b2 \<Longrightarrow> b = safe_hd v) \<Longrightarrow> b1 \<or> b2 \<Longrightarrow>
  q \<leadsto>(if b1 then the_Symb a # u else u, if b2 then the_Symb b # v else v) q''"
  by (auto simp add: safe_hd_def the_Symb_def split: Al.splits list.splits
      dest: move_left move_right)

lemma reachable_step:
  assumes "\<delta> q (a, b) (q', b1, b2)" "reachable q as bs a b" "b1 \<or> b2"
  shows "reachable q' (if b1 then as @ [the_Symb a] else as) (if b2 then bs @ [the_Symb b] else bs)
    (if b1 then a' else a) (if b2 then b' else b)"
proof -
  have q'_Q: "q' \<in> Q"
    using closed[OF _ assms(1)] assms(2)
    by (auto simp add: reachable_def)
  have reach: "\<And>u v q'. a = safe_hd u \<Longrightarrow> b = safe_hd v \<Longrightarrow>
    q \<leadsto>(u, v) q' \<Longrightarrow> accept q' \<Longrightarrow> (as @ u, bs @ v) \<in> \<tau>"
    using assms(2)
    by (fastforce simp add: reachable_def)
  show ?thesis
  proof (cases b1)
    case True
    note True' = True
    show ?thesis
    proof (cases b2)
      case True
      show ?thesis
        using True' True q'_Q reach assms(1)
        by (cases a; cases b)
           (auto simp add: reachable_def safe_hd_def the_Symb_def
                 intro!: exI[of _ "as @ [the_Symb a]"] exI[of _ "bs @ [the_Symb b]"]
                 dest: ext_step move_left move_right)
    next
      case False
      show ?thesis
        using True False q'_Q reach assms(1)
        by (cases a)
           (auto simp add: reachable_def safe_hd_def the_Symb_def
                 intro!: exI[of _ "as @ [the_Symb a]"] exI[of _ bs]
                 dest: ext_step move_left)
    qed
  next
    case False
    then show ?thesis
      using assms(3)
    proof (cases b2)
      case True
      show ?thesis
        using False True q'_Q reach assms(1)
        by (cases b)
           (auto simp add: reachable_def safe_hd_def the_Symb_def
                 intro!: exI[of _ as] exI[of _ "bs @ [the_Symb b]"]
                 dest: ext_step move_right)
    qed auto
  qed
qed

lemma outs_reachable: "outs (Symb a) q xs q'' b'' \<beta> \<Longrightarrow> (b = EOF \<Longrightarrow> b'' = EOF) \<Longrightarrow>
  reachable q as bs (Symb a) b \<Longrightarrow> b = safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | _ \<Rightarrow> [])) \<Longrightarrow>
  reachable q'' (as @ [a]) (bs @ map fst xs @ (if \<beta> then [the_Symb b''] else []))
    a' (if \<beta> then b' else b'')"
proof (induction "Symb a" q xs q'' b'' \<beta> arbitrary: b bs rule: outs.induct)
  case (outs_base q b' q' \<beta>)
  show ?case
    using closed outs_base(1,3,4)
    by (auto simp add: safe_hd_def split: Al.splits dest: reachable_step)
next
  case (outs_step q b' q'' xs q' b'' \<beta>)
  have b_def: "b = Symb b'"
    using outs_step(6)
    by (auto simp add: safe_hd_def)
  have "safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | EOF \<Rightarrow> [])) = EOF \<Longrightarrow> b'' = EOF"
    by (auto simp add: safe_hd_def split: list.splits Al.splits)
  then show ?case
    using outs_step(3)[OF _ reachable_step[OF outs_step(1) outs_step(5)[unfolded b_def],
          simplified] refl]
    by auto
qed

lemma reachable_init: "reachable init [] [] a b"
  using init_in_Q
  by (auto simp add: reachable_def \<tau>_def)

lemma comp_suf:
  assumes "reachable q as bs a b" "a = safe_hd (u @ [x])" "b = safe_hd v"
    "q \<leadsto>(u @ x # u1, v) q'"
  shows "\<exists>r cs y' cs'. reachable r (as @ u) (bs @ cs) (Symb x) y' \<and>
    r \<leadsto>(x # u1, cs') q' \<and> v = cs @ cs' \<and> y' = safe_hd cs'"
  using assms
proof (induction "length u + length v" arbitrary: q as bs a b u v rule: nat_less_induct)
  case 1
  obtain a' where symb: "a = Symb a'"
    using 1(3,4)
    by (cases a) (auto simp add: safe_hd_def split: list.splits)
  show ?case
  proof (cases u)
    case Nil
    show ?thesis
      using 1(2,3,4,5)
      unfolding symb Nil
      by (cases v) (force simp add: safe_hd_def intro!: exI[of _ q] split: list.splits)+
  next
    case (Cons e u')
    have u_def: "u = a' # u'"
      using 1(3)[unfolded symb Cons] Cons
      by (auto simp add: safe_hd_def)
    have IH: "\<And>xa xb xc xd xe. length xa + length xb < length u + length v \<Longrightarrow>
      reachable xc xd xe (safe_hd (xa @ [x])) (safe_hd xb) \<Longrightarrow> xc \<leadsto>(xa @ x # u1, xb) q' \<Longrightarrow>
      (\<exists>r cs y' cs'. reachable r (xd @ xa) (xe @ cs) (Symb x) y' \<and> r \<leadsto>(x # u1, cs') q' \<and>
      xb = cs @ cs' \<and> y' = safe_hd cs')"
      using 1(1) by auto
    note comp = 1(5)[unfolded u_def, simplified]
    show ?thesis
    proof (cases v)
      case Nil
      have b_def: "b = EOF"
        using 1(4)
        by (auto simp add: safe_hd_def Nil)
      obtain qm where step: "\<delta> q (Symb a', EOF) (qm, True, False)" "qm \<leadsto>(u' @ x # u1, []) q'"
        by (rule computation.cases[OF comp[unfolded Nil]]) auto
      note reachable_qm = reachable_step[OF step(1) 1(2)[unfolded symb b_def], simplified]
      show ?thesis
        using IH[of u' "[]", unfolded Nil safe_hd_Nil, OF _ reachable_qm step(2)]
        by (auto simp add: u_def Nil)
    next
      case (Cons f v')
      have b_def: "b = Symb f"
        using 1(4)
        by (auto simp add: Cons safe_hd_def)
      have safe_hd_v: "safe_hd v = Symb f"
        using Cons
        by (auto simp add: safe_hd_def)
      obtain qm b1 b2 where step: "\<delta> q (Symb a', Symb f) (qm, b1, b2)"
        "qm \<leadsto>(if b1 then u' @ x # u1 else a' # u' @ x # u1,
        if b2 then v' else f # v') q'"
        by (rule computation.cases[OF comp[unfolded Cons]]) auto
      have b_or: "b1 \<or> b2"
        using step(1) no_step
        by fastforce
      note reachable_qm = reachable_step[OF step(1) 1(2)[unfolded symb b_def] b_or]
      show ?thesis
      proof (cases b1)
        case True
        note True' = True
        show ?thesis
        proof (cases b2)
          case True
          have reach: "reachable qm (as @ [a']) (bs @ [f]) (safe_hd (u' @ [x])) (safe_hd v')"
            using reachable_qm True' True
            by auto
          show ?thesis
            using IH[of u' v', OF _ reach] step(2) True' True
            unfolding u_def Cons
            by fastforce
        next
          case False
          have reach: "reachable qm (as @ [a']) bs (safe_hd (u' @ [x])) (safe_hd v)"
            using reachable_qm True' False
            by (auto simp add: safe_hd_v)
          show ?thesis
            using IH[of u' v, OF _ reach] step(2) True' False
            unfolding u_def Cons
            by fastforce
        qed
      next
        case False
        then show ?thesis
          using b_or
        proof (cases b2)
          case True
          have reach: "reachable qm as (bs @ [f]) (safe_hd (u @ [x])) (safe_hd v')"
            using reachable_qm False True
            by (auto simp add: safe_hd_v 1(3)[unfolded symb])
          show ?thesis
            using IH[of u v', OF _ reach] step(2) False True
            unfolding u_def Cons
            by fastforce
        qed auto
      qed
    qed
  qed
qed

lemma first_reaches:
  assumes "reachable q as bs a b" "a = safe_hd (u @ [x])" "b = safe_hd (v @ [y])"
    "q \<leadsto>(u @ x # u1, v @ y # v1) q'"
    "q \<leadsto>(u @ x # u2, v @ y # v2) q''"
  shows "(\<exists>r cs y' cs'. reachable r (as @ u) (bs @ cs) (Symb x) (Symb y') \<and>
    r \<leadsto>(x # u1, y' # cs' @ v1) q' \<and> r \<leadsto>(x # u2, y' # cs' @ v2) q'' \<and> cs @ y' # cs' = v @ [y]) \<or>
    (\<exists>r cs x' cs'. reachable r (as @ cs) (bs @ v) (Symb x') (Symb y) \<and>
    r \<leadsto>(x' # cs' @ u1, y # v1) q' \<and> r \<leadsto>(x' # cs' @ u2, y # v2) q'' \<and> cs @ x' # cs' = u @ [x])"
  using assms
proof (induction "length u + length v" arbitrary: q as bs a b u v rule: nat_less_induct)
  case 1
  obtain a' b' where symb: "a = Symb a'" "b = Symb b'"
    using 1(3,4)
    by (cases a; cases b) (auto simp add: safe_hd_def split: list.splits)
  show ?case
  proof (cases u)
    case Nil
    show ?thesis
      apply (rule disjI1)
      using 1(2,3,4,5,6)
      unfolding symb Nil
      apply (cases v)
       apply (auto simp add: safe_hd_def intro!: exI[of _ "[]"] split: list.splits)
      done
  next
    case (Cons e u')
    have u_def: "u = a' # u'"
      using 1(3)[unfolded symb Cons] Cons
      by (auto simp add: safe_hd_def)
    show ?thesis
    proof (cases v)
      case Nil
      show ?thesis
        apply (rule disjI2)
        using 1(2,3,4,5,6)
        unfolding symb Nil
        apply (cases u)
         apply (auto simp add: safe_hd_def intro!: exI[of _ "[]"] split: list.splits)
        done
    next
      case (Cons f v')
      have v_def: "v = b' # v'"
        using 1(4)[unfolded symb Cons] Cons
        by (auto simp add: safe_hd_def)
      note comp = 1(5)[unfolded u_def v_def, simplified]
      obtain qm b1 b2 where step: "\<delta> q (Symb a', Symb b') (qm, b1, b2)"
        "qm \<leadsto>(if b1 then u' @ x # u1 else a' # u' @ x # u1,
        if b2 then v' @ y # v1 else b' # v' @ y # v1) q'"
        by (rule computation.cases[OF comp]) auto
      note comp' = 1(6)[unfolded u_def v_def, simplified]
      have step': "qm \<leadsto>(if b1 then u' @ x # u2 else a' # u' @ x # u2,
        if b2 then v' @ y # v2 else b' # v' @ y # v2) q''"
        apply (rule computation.cases[OF comp'])
        using step(1) by (auto dest: det[OF step(1)])
      have b_or: "b1 \<or> b2"
        using step(1) no_step
        by fastforce
      note reachable_qm = reachable_step[OF step(1) 1(2)[unfolded symb] b_or]
      have IH: "\<And>xa xb xc xd xe. length xa + length xb < length u + length v \<Longrightarrow>
        reachable xc xd xe (safe_hd (xa @ [x])) (safe_hd (xb @ [y])) \<Longrightarrow>
        xc \<leadsto>(xa @ x # u1, xb @ y # v1) q' \<Longrightarrow> xc \<leadsto>(xa @ x # u2, xb @ y # v2) q'' \<Longrightarrow>
        (\<exists>r cs y' cs'. reachable r (xd @ xa) (xe @ cs) (Symb x) (Symb y') \<and>
          r\<leadsto>(x # u1, y' # cs' @ v1)q' \<and> r\<leadsto>(x # u2, y' # cs' @ v2)q'' \<and>
          cs @ y' # cs' = xb @ [y]) \<or>
        (\<exists>r cs x' cs'. reachable r (xd @ cs) (xe @ xb) (Symb x') (Symb y) \<and>
          r\<leadsto>(x' # cs' @ u1, y # v1)q' \<and> r\<leadsto>(x' # cs' @ u2, y # v2)q'' \<and>
          cs @ x' # cs' = xa @ [x])"
        using 1(1) by auto
      show ?thesis
      proof (cases b1)
        case True
        note True' = True
        show ?thesis
        proof (cases b2)
          case True
          have len: "length u' + length v' < length u + length v"
            by (auto simp add: u_def v_def)
          have reach: "reachable qm (as @ [a']) (bs @ [b'])
            (safe_hd (u' @ [x])) (safe_hd (v' @ [y]))"
            using reachable_qm True' True
            by auto
          show ?thesis
            using IH[OF len reach] step(2) step' True' True
            unfolding u_def v_def
            by fastforce
        next
          case False
          have len: "length u' + length (b' # v') < length u + length v"
            by (auto simp add: u_def v_def)
          have reach: "reachable qm (as @ [a']) bs
            (safe_hd (u' @ [x])) (safe_hd ((b' # v') @ [y]))"
            using reachable_qm True' False
            by (auto simp add: safe_hd_def)
          show ?thesis
            using IH[OF len reach] step(2) step' True' False
            unfolding u_def v_def
            by fastforce
        qed
      next
        case False
        then show ?thesis
          using b_or
        proof (cases b2)
          case True
          have len: "length (a' # u') + length v' < length u + length v"
            by (auto simp add: u_def v_def)
          have reach: "reachable qm as (bs @ [b'])
            (safe_hd ((a' # u') @ [x])) (safe_hd (v' @ [y]))"
            using reachable_qm False True
            by (auto simp add: safe_hd_def)
          show ?thesis
            using IH[OF len reach] step(2) step' False True
            unfolding u_def v_def
            by fastforce
        qed auto
      qed
    qed
  qed
qed

end

locale fTDFA = TDFA init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> ('a :: finite) Al \<times> ('b :: finite) Al \<Rightarrow> 's \<times> bool \<times> bool \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes functional: "(as, bs) \<in> \<tau> \<Longrightarrow> (as, bs') \<in> \<tau> \<Longrightarrow> bs = bs'"
begin

lemma lin_bounded: "reachable q as bs a b \<Longrightarrow> q \<leadsto>(u, v) q' \<Longrightarrow> accept q' \<Longrightarrow>
  a = safe_hd u \<Longrightarrow> b = safe_hd v \<Longrightarrow> length v \<le> (length u + 1) * (card Q + 2)"
proof (induction u arbitrary: as bs a b q v q')
  case Nil
  have q_Q: "q \<in> Q"
    using Nil(1)
    by (auto simp add: reachable_def)
  have reach: "\<And>u v q'. a = safe_hd u \<Longrightarrow> b = safe_hd v \<Longrightarrow>
    q \<leadsto>(u, v) q' \<Longrightarrow> accept q' \<Longrightarrow> (as @ u, bs @ v) \<in> \<tau>"
    using Nil(1)
    by (fastforce simp add: reachable_def)
  obtain xs q'' where outs: "outs EOF q xs q'' EOF False"
    "\<delta> q'' (EOF, EOF) (q', False, False)" "v = map fst xs"
    using outs_Nil_intro[OF Nil(2)]
    by auto
  then show ?case
  proof (cases "length xs \<ge> 2 + card Q")
    case True
    obtain y ys where ys_def: "xs = y # ys" "length ys \<ge> 1 + card Q"
      using True
      by (cases xs) auto
    obtain ys' where ys'_def: "outs EOF q (y # ys') q'' EOF False" "length ys' < length ys"
      using outs_norm[OF outs(1)[unfolded ys_def(1)] q_Q ys_def(2)]
      by auto
    have "(as, bs @ v) \<in> \<tau>"
      using reach Nil
      by fastforce
    moreover have "(as, bs @ map fst (y # ys')) \<in> \<tau>"
      using reach[OF Nil(4) _ outs_Nil_dest[OF ys'_def(1) outs(2)] Nil(3)]
            Nil(5)[unfolded outs(3) ys_def(1)]
      by (auto simp add: safe_hd_def)
    ultimately show ?thesis
      using functional ys'_def(2) map_eq_imp_length_eq
      by (fastforce simp add: ys_def(1) outs(3))
  qed auto
next
  case (Cons a' u)
  have q_Q: "q \<in> Q"
    using Cons(2)
    by (auto simp add: reachable_def)
  obtain as bs where reach: "\<And>u v q'. a = safe_hd u \<Longrightarrow> b = safe_hd v \<Longrightarrow>
    q \<leadsto>(u, v) q' \<Longrightarrow> accept q' \<Longrightarrow> (as @ u, bs @ v) \<in> \<tau>"
    using Cons(2)
    by (fastforce simp add: reachable_def)
  obtain xs q'' b'' \<beta> bs' where outs: "outs (Symb a') q xs q'' b'' \<beta>"
   "q''\<leadsto>(u, bs')q'" "(b'' = EOF \<longrightarrow> \<not> \<beta>)" "(\<not> \<beta> \<longrightarrow> b'' = safe_hd bs')"
   "v = map fst xs @ (if \<beta> then (case b'' of Symb b' \<Rightarrow> b') # bs' else bs')"
    using outs_Cons_intro[OF Cons(3)]
    by blast
  have aux: "(safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | EOF \<Rightarrow> [])) = EOF \<Longrightarrow> b'' = EOF)"
    by (auto simp add: safe_hd_def split: list.splits Al.splits)
  have a_def: "a = Symb a'"
    using Cons(5)
    by (auto simp add: safe_hd_def)
  have safe_hd_v: "safe_hd v = safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | EOF \<Rightarrow> []))"
    unfolding outs(5) using outs(3,4)
    by (cases xs) (auto simp add: safe_hd_def split: list.splits Al.splits)
  have "length xs \<ge> 2 + card Q \<Longrightarrow> False"
  proof -
    assume lassm: "length xs \<ge> 2 + card Q"
    obtain y ys where ys_def: "xs = y # ys" "length ys \<ge> 1 + card Q"
      using lassm
      by (cases xs) auto
    obtain ys' where ys'_def: "outs (Symb a') q (y # ys') q'' b'' \<beta>" "length ys' < length ys"
      using outs_norm[OF outs(1)[unfolded ys_def(1)] q_Q ys_def(2)]
      by auto
    have "(as @ a' # u, bs @ v) \<in> \<tau>"
      using reach Cons
      by fastforce
    moreover have "(as @ a' # u, bs @ map fst (y # ys') @
      (if \<beta> then (case b'' of Symb b' \<Rightarrow> b') # bs' else bs')) \<in> \<tau>"
      using reach[OF Cons(5) _ outs_Cons_dest[OF ys'_def(1) outs(2,3,4) refl] Cons(4)]
            Cons(6)[unfolded outs(5) ys_def]
      by (auto simp add: safe_hd_def)
    ultimately show "False"
      using functional ys'_def(2) map_eq_imp_length_eq
      by (fastforce simp add: ys_def(1) outs(5))
  qed
  then show ?case
    using outs(4) Cons(1)[OF _ outs(2) Cons(4) refl, OF outs_reachable[OF outs(1) _ _ refl,
          OF aux, simplified], OF Cons(2)[unfolded a_def Cons(6) safe_hd_v]]
    by (fastforce simp add: outs(5))
qed

end

end