theory Computation
  imports Main
begin

(* general helper lemmas *)

lemma split_app: "\<And>xs ys xs' ys'. xs @ ys = xs' @ ys' \<Longrightarrow> length xs \<le> length xs' \<Longrightarrow>
  \<exists>ds. xs' = xs @ ds"
  by (metis (full_types) append_eq_append_conv_if append_eq_conv_conj)

lemma split_app': "\<And>xs ys xs' ys'. xs @ ys = xs' @ ys' \<Longrightarrow> length xs \<le> length xs' \<Longrightarrow>
  \<exists>es. ys = es @ ys'"
  by (simp add: append_eq_append_conv_if)

lemma app_decomp: "length xs = length (ys @ ys') \<Longrightarrow>
  \<exists>zs zs'. xs = zs @ zs' \<and> length zs = length ys \<and> length zs' = length ys'"
  by (metis append_eq_conv_conj length_drop length_rev rev_take)

lemma singleton_dest: "length xs = Suc 0 \<Longrightarrow> \<exists>x. xs = [x]"
  by (cases xs) auto

lemma set_zip: "set (zip xs ys) \<subseteq> set xs \<times> set ys"
  by (induction xs arbitrary: ys) (auto dest: set_zip_leftD set_zip_rightD)

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

(* alphabet extended with a special blank symbol *)

datatype 'a Al = Symb (the_Symb: 'a) | Blank

definition "safe_hd bs' = (case bs' of [] \<Rightarrow> Blank | b # bs \<Rightarrow> Symb b)"

lemma safe_hd_Nil: "safe_hd [] = Blank"
  by (auto simp add: safe_hd_def)

lemma safe_hd_eq: "xs = xs' @ (bs, q'') # xs'' \<Longrightarrow>
  safe_hd (map fst xs) = safe_hd (map fst (xs' @ (bs, q'') # xs'''))"
  by (auto simp add: safe_hd_def split: list.splits) (metis Cons_eq_append_conv nth_Cons_0)

lemma safe_hd_app: "safe_hd xs = safe_hd xs' \<Longrightarrow> safe_hd (xs @ ys) = safe_hd (xs' @ ys)"
  by (auto simp add: safe_hd_def split: list.splits)

lemma safe_hd_app': "safe_hd ys = safe_hd ys' \<Longrightarrow> safe_hd (xs @ ys) = safe_hd (xs @ ys')"
  by (auto simp add: safe_hd_def split: list.splits) (metis append_Nil hd_append2 list.sel(1))

lemma safe_hd_app'': "xs \<noteq> [] \<Longrightarrow> safe_hd (xs @ ys) = safe_hd (xs @ ys')"
  by (cases xs) (auto simp add: safe_hd_def split: list.splits)

lemma safe_hd_Cons_app: "safe_hd (xs @ x # ys) = safe_hd (xs @ x # ys')"
  by (cases xs) (auto simp add: safe_hd_def split: list.splits)

(* Definition 1 *)

locale TDFA =
  fixes init :: "'s"
  and \<delta> :: "'s \<Rightarrow> ('a :: finite) Al \<times> ('b :: finite) Al \<Rightarrow> 's \<times> bool \<times> bool \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set"
  assumes det: "\<delta> q z x \<Longrightarrow> \<delta> q z x' \<Longrightarrow> x = x'" and
  finite_Q: "finite Q" and
  init_in_Q: "init \<in> Q" and
  closed: "q \<in> Q \<Longrightarrow> \<delta> q z (q', b1, b2) \<Longrightarrow> q' \<in> Q" and
  move_left: "\<delta> q (a, b) (q', True, b2) \<Longrightarrow> a \<noteq> Blank" and
  move_right: "\<delta> q (a, b) (q', b1, True) \<Longrightarrow> b \<noteq> Blank" and
  no_step: "\<delta> q (a, b) (q', False, False) \<Longrightarrow> a = Blank \<and> b = Blank"
begin

(* notion of computation and computed relation *)

inductive computation :: "'s \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 's \<Rightarrow> bool" ("_/\<leadsto>_/_" [64,64,64]63) where
  step_L[intro]: "\<delta> q (Symb a, Blank) (q', True, False) \<Longrightarrow> q' \<leadsto>(as, []) q'' \<Longrightarrow>
    q \<leadsto>(a # as, []) q''"
| step_R[intro]: "\<delta> q (Blank, Symb b) (q', False, True) \<Longrightarrow> q' \<leadsto>([], bs) q'' \<Longrightarrow>
    q \<leadsto>([], b # bs) q''"
| step_TT[intro]: "\<delta> q (Symb a, Symb b) (q', True, True) \<Longrightarrow>  q' \<leadsto>(as, bs) q'' \<Longrightarrow>
    q \<leadsto>(a # as, b # bs) q''"
| step_TF[intro]: "\<delta> q (Symb a, Symb b) (q', True, False) \<Longrightarrow>  q' \<leadsto>(as, b # bs) q'' \<Longrightarrow>
    q \<leadsto>(a # as, b # bs) q''"
| step_FT[intro]: "\<delta> q (Symb a, Symb b) (q', False, True) \<Longrightarrow>  q' \<leadsto>(a # as, bs) q'' \<Longrightarrow>
    q \<leadsto>(a # as, b # bs) q''"
| last_step[intro]: "\<delta> q (Blank, Blank) (q', False, False) \<Longrightarrow> q \<leadsto>([], []) q'"

definition \<tau> :: "('a list \<times> 'b list) set" where
  "\<tau> = {(as, bs). \<exists>q. init \<leadsto>(as, bs) q \<and> accept q}"

end

(* TDFA moving exactly one head in every step used in the proof of Theorem 10 *)

locale oTDFA = TDFA init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> ('a :: finite) Al \<times> ('b :: finite) Al \<Rightarrow> 's \<times> bool \<times> bool \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes move_one: "\<not>\<delta> q (a, b) (q', True, True)"
begin

(* lemmas *)

inductive outs :: "'a Al \<Rightarrow> 's \<Rightarrow> ('b \<times> 's) list \<Rightarrow> 's \<Rightarrow> 'b Al \<Rightarrow> bool" where
  outs_base: "\<delta> q (Symb a, b) (q', True, False) \<Longrightarrow> outs (Symb a) q [] q' b"
| outs_step: "\<delta> q (a, Symb b') (q'', False, True) \<Longrightarrow> outs a q'' xs q' b \<Longrightarrow>
    outs a q ((b', q'') # xs) q' b"
| outs_last: "\<delta> q (Blank, Blank) (q', False, False) \<Longrightarrow> outs Blank q [] q Blank"

lemma outs_drop: "outs a q (xs' @ (b'', q'') # xs'') q' b \<Longrightarrow> outs a q'' xs'' q' b"
proof (induction a q "xs' @ (b'', q'') # xs''" q' b arbitrary: xs' rule: outs.induct)
  case (outs_step q a b' q'' xs q' b)
  then show ?case
    by (cases xs') auto
qed auto

lemma outs_rem: "outs a q (xs @ (b', q'') # xs' @ (b'', q'') # xs'') q' b \<Longrightarrow>
  outs a q (xs @ (b', q'') # xs'') q' b"
proof (induction a q "xs @ (b', q'') # xs' @ (b'', q'') # xs''" q' b arbitrary: xs
  rule: outs.induct)
  case (outs_step q a b' q'' ixs q' b)
  show ?case
    using outs_step(1,2,4) outs.intros(2)[OF outs_step(1) outs_step(3)] outs_drop outs.outs_step
    by (cases xs) auto
qed auto

lemma outs_closed: "outs a q xs q' b \<Longrightarrow> q \<in> Q \<Longrightarrow> (b', q'') \<in> set xs \<Longrightarrow> q'' \<in> Q"
  apply (induction a q xs q' b rule: outs.induct)
  using closed by auto

lemma outs_closed': "outs a q xs q' b \<Longrightarrow> q \<in> Q \<Longrightarrow> q' \<in> Q"
  apply (induction a q xs q' b rule: outs.induct)
  using closed by auto

lemma outs_norm:
  assumes "outs a q xs q' b" "q \<in> Q" "length xs > card Q"
  shows "\<exists>xs'. outs a q xs' q' b \<and> length xs' < length xs \<and>
    safe_hd (map fst xs') = safe_hd (map fst xs)"
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
  have outs': "outs a q (xs' @ (bs, q'') # xs'' @ (bs', q'') # xs''') q' b"
    using assms(1)[unfolded decomp]
    by auto
  show ?thesis
    using outs_rem[OF outs'] safe_hd_eq[OF decomp]
    by (auto simp add: decomp)
qed

lemma outs_Nil_dest: "outs Blank q xs q'' Blank \<Longrightarrow> \<delta> q'' (Blank, Blank) (q', False, False) \<Longrightarrow>
  q \<leadsto>([], map fst xs) q'"
  by (induction "Blank :: 'a Al" q xs q'' "Blank :: 'b Al" rule: outs.induct) auto

lemma outs_Nil_intro: "q \<leadsto>([], bs) q' \<Longrightarrow> \<exists>xs q''. outs Blank q xs q'' Blank \<and>
  \<delta> q'' (Blank, Blank) (q', False, False) \<and> bs = map fst xs"
proof (induction q "([] :: 'a list, bs)" q' arbitrary: bs rule: computation.induct)
  case (step_R q b q' bs q'')
  obtain xs q''' where props: "outs Blank q' xs q''' Blank"
    "\<delta> q''' (Blank, Blank) (q'', False, False)" "bs = map fst xs"
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

lemma outs_Cons_dest: "outs (Symb a) q xs q'' b \<Longrightarrow> q'' \<leadsto>(as, bs') q' \<Longrightarrow>
  b = safe_hd bs' \<Longrightarrow> bs = map fst xs @ bs' \<Longrightarrow> q \<leadsto>(a # as, bs) q'"
  by (induction "Symb a" q xs q'' b arbitrary: bs rule: outs.induct)
     (auto simp add: safe_hd_def split: list.splits Al.splits)

lemma outs_Cons_intro: "q \<leadsto>(a # as, bs) q' \<Longrightarrow> \<exists>xs q'' b \<beta> bs'. outs (Symb a) q xs q'' b \<and>
  q'' \<leadsto>(as, bs') q' \<and> b = safe_hd bs' \<and> bs = map fst xs @ bs'"
proof (induction q "(a # as, bs)" q' arbitrary: a as bs rule: computation.induct)
  case (step_L q a q' as q'')
  show ?case
    using outs_base[OF step_L(1)] step_L(2)
    by (auto simp add: safe_hd_def)
next
  case (step_TT q a b q' as bs q'')
  show ?case
    using move_one step_TT(1)
    by auto
next
  case (step_TF q a b q' as bs q'')
  show ?case
    using outs_base[OF step_TF(1)] step_TF(2)
    by (fastforce simp add: safe_hd_def)
next
  case (step_FT q a b q' as bs q'')
  obtain q''' xs b' bs' where props: "outs (Symb a) q' xs q''' b'"
    "b' = safe_hd bs'" "bs = map fst xs @ bs'" "q'''\<leadsto>(as, bs')q''"
    using step_FT(3)
    by blast
  show ?case
    using outs_step[OF step_FT(1), OF props(1)] props(2,3,4)
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

lemma outs_reachable: "outs (Symb a) q xs q'' b'' \<Longrightarrow> (b = Blank \<Longrightarrow> b'' = Blank) \<Longrightarrow>
  reachable q as bs (Symb a) b \<Longrightarrow>
  b = safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | _ \<Rightarrow> [])) \<Longrightarrow>
  reachable q'' (as @ [a]) (bs @ map fst xs) a' b''"
proof (induction "Symb a" q xs q'' b'' arbitrary: b bs rule: outs.induct)
  case (outs_base q b' q' \<beta>)
  show ?case
    using closed outs_base(1,3,4)
    by (auto simp add: safe_hd_def split: Al.splits dest: reachable_step)
next
  case (outs_step q b' q'' xs q' b'')
  have b_def: "b = Symb b'"
    using outs_step(6)
    by (auto simp add: safe_hd_def)
  have "safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | Blank \<Rightarrow> [])) = Blank \<Longrightarrow> b'' = Blank"
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
  assumes "reachable q as bs a b" "a = safe_hd (u @ u1)" "b = safe_hd v"
    "q \<leadsto>(u @ u1, v) q'"
  shows "\<exists>r cs y' cs'. reachable r (as @ u) (bs @ cs) (safe_hd u1) y' \<and>
    r \<leadsto>(u1, cs') q' \<and> v = cs @ cs' \<and> y' = safe_hd cs'"
  using assms
proof (induction "length u + length v" arbitrary: q as bs a b u v rule: nat_less_induct)
  case 1
  show ?case
  proof (cases u)
    case Nil
    show ?thesis
      using 1(2,3,4,5)
      unfolding Nil
      by (cases v) (force simp add: safe_hd_def intro!: exI[of _ q] split: list.splits)+
  next
    case (Cons e u')
    obtain a' where u_def: "u = a' # u'" "a = Symb a'"
      using 1(3)[unfolded Cons] Cons
      by (auto simp add: safe_hd_def)
    have IH: "\<And>xa xb xc xd xe. length xa + length xb < length u + length v \<Longrightarrow>
      reachable xc xd xe (safe_hd (xa @ u1)) (safe_hd xb) \<Longrightarrow> xc \<leadsto>(xa @ u1, xb) q' \<Longrightarrow>
      (\<exists>r cs y' cs'. reachable r (xd @ xa) (xe @ cs) (safe_hd u1) y' \<and> r \<leadsto>(u1, cs') q' \<and>
      xb = cs @ cs' \<and> y' = safe_hd cs')"
      using 1(1) by auto
    note comp = 1(5)[unfolded u_def, simplified]
    show ?thesis
    proof (cases v)
      case Nil
      have b_def: "b = Blank"
        using 1(4)
        by (auto simp add: safe_hd_def Nil)
      obtain qm where step: "\<delta> q (Symb a', Blank) (qm, True, False)" "qm \<leadsto>(u' @ u1, []) q'"
        by (rule computation.cases[OF comp[unfolded Nil]]) auto
      note reachable_qm = reachable_step[OF step(1) 1(2)[unfolded b_def u_def(2)], simplified]
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
        "qm \<leadsto>(if b1 then u' @ u1 else a' # u' @ u1,
        if b2 then v' else f # v') q'"
        by (rule computation.cases[OF comp[unfolded Cons]]) auto
      have b_or: "b1 \<or> b2"
        using step(1) no_step
        by fastforce
      note reachable_qm = reachable_step[OF step(1) 1(2)[unfolded b_def u_def(2)] b_or]
      show ?thesis
      proof (cases b1)
        case True
        note True' = True
        show ?thesis
        proof (cases b2)
          case True
          have reach: "reachable qm (as @ [a']) (bs @ [f]) (safe_hd (u' @ u1)) (safe_hd v')"
            using reachable_qm True' True
            by auto
          show ?thesis
            using IH[of u' v', OF _ reach] step(2) True' True
            unfolding u_def Cons
            by fastforce
        next
          case False
          have reach: "reachable qm (as @ [a']) bs (safe_hd (u' @ u1)) (safe_hd v)"
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
          have reach: "reachable qm as (bs @ [f]) (safe_hd (u @ u1)) (safe_hd v')"
            using reachable_qm False True u_def(2)
            by (auto simp add: safe_hd_v 1(3))
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
  assumes "reachable q as bs (safe_hd (u @ u')) (safe_hd (v @ v'))"
    "safe_hd (u @ u') = safe_hd (u @ u'')"
    "safe_hd v' = safe_hd v''"
    "q \<leadsto>(u @ u', v @ v') q'"
    "q \<leadsto>(u @ u'', v @ v'') q''"
  shows "(\<exists>r cs c cs'. reachable r (as @ u) (bs @ cs) (safe_hd u') c \<and>
    r \<leadsto>(u', cs' @ v') q' \<and> r \<leadsto>(u'', cs' @ v'') q'' \<and> cs @ cs' = v \<and>
    c = safe_hd (cs' @ v') \<and> c = safe_hd (cs' @ v'')) \<or>
    (\<exists>r cs c cs'. reachable r (as @ cs) (bs @ v) c (safe_hd v') \<and>
    r \<leadsto>(cs' @ u', v') q' \<and> r \<leadsto>(cs' @ u'', v'') q'' \<and> cs @ cs' = u \<and>
    c = safe_hd (cs' @ u') \<and> c = safe_hd (cs' @ u''))"
  using assms
proof (induction "length u + length v" arbitrary: u v q as bs rule: nat_less_induct)
  case 1
  have IH: "\<And>x xa xb xc xd xe xf.
    length x + length xa < length u + length v \<Longrightarrow>
    reachable xb xc xd (safe_hd (x @ u')) (safe_hd (xa @ v')) \<Longrightarrow>
    safe_hd (x @ u') = safe_hd (x @ u'') \<Longrightarrow>
    xb\<leadsto>(x @ u', xa @ v')q' \<Longrightarrow> xb\<leadsto>(x @ u'', xa @ v'')q'' \<Longrightarrow>
    (\<exists>r cs c cs'. reachable r (xc @ x) (xd @ cs) (safe_hd u') c \<and>
      r\<leadsto>(u', cs' @ v')q' \<and> r\<leadsto>(u'', cs' @ v'')q'' \<and> cs @ cs' = xa \<and>
      c = safe_hd (cs' @ v') \<and> c = safe_hd (cs' @ v'')) \<or>
    (\<exists>r cs c cs'.
      reachable r (xc @ cs) (xd @ xa) c (safe_hd v') \<and>
      r\<leadsto>(cs' @ u', v')q' \<and> r\<leadsto>(cs' @ u'', v'')q'' \<and> cs @ cs' = x \<and>
      c = safe_hd (cs' @ u') \<and> c = safe_hd (cs' @ u''))"
    using 1(1) 1(4)
    by fast
  show ?case
  proof (cases v)
    case Nil
    show ?thesis
      apply (rule disjI2)
      using 1(2,3,5,6) safe_hd_app'[OF 1(3)]
      by (auto simp add: Nil intro!: exI[of _ q] exI[of _ "[]"])
  next
    case (Cons b b')
    note Cons' = Cons
    show ?thesis
    proof (cases u)
      case Nil
      show ?thesis
        apply (rule disjI1)
        using 1(2,4,5,6) safe_hd_app'[OF 1(4)]
        by (auto simp add: Nil intro!: exI[of _ q] exI[of _ "[]"])
    next
      case (Cons a a')
      note Cons'' = Cons
      have symbs: "safe_hd (a # a' @ u') = Symb a" "safe_hd (b # b' @ v') = Symb b"
        by (auto simp add: safe_hd_def)
      obtain qm b1 b2 where step: "\<delta> q (Symb a, Symb b) (qm, b1, b2)"
        "qm \<leadsto>((if b1 then a' else a # a') @ u', (if b2 then b' else b # b') @ v') q'"
        by (rule computation.cases[OF 1(5)[unfolded Cons' Cons]]) (auto simp add: safe_hd_def)
      have step': "qm \<leadsto>((if b1 then a' else a # a') @ u'', (if b2 then b' else b # b') @ v'') q''"
        apply (rule computation.cases[OF 1(6)])
        using det[OF step(1)]
        by (auto simp add: Cons' Cons)
      have b_props: "b1 \<or> b2" "\<not>(b1 \<and> b2)"
        using step(1) move_one no_step
        by fastforce+
      have reach: "reachable q as bs (Symb a) (Symb b)"
        using 1(2)
        by (auto simp add: Cons' Cons symbs)
      note reach' = reachable_step[OF step(1) reach b_props(1)]
      show ?thesis
      proof (cases b1)
        case True
        then show ?thesis
          using b_props(2)
        proof (cases b2)
          case False
          show ?thesis
          proof (cases a')
            case Nil
            show ?thesis
              apply (rule disjI1)
              using 1(4) step step' reach'[of "safe_hd u'"] True False
              unfolding Cons' Cons'' Nil
              by (auto simp add: safe_hd_def intro!: exI[of _ qm] exI[of _ "[]"])
          next
            case (Cons c c')
            have "(\<exists>r cs c cs'. reachable r ((as @ [a]) @ a') (bs @ cs) (safe_hd u') c \<and>
                r\<leadsto>(u', cs' @ v')q' \<and> r\<leadsto>(u'', cs' @ v'')q'' \<and> cs @ cs' = b # b' \<and>
                c = safe_hd (cs' @ v') \<and> c = safe_hd (cs' @ v'')) \<or>
              (\<exists>r cs c cs'.
                reachable r ((as @ [a]) @ cs) (bs @ b # b') c (safe_hd v') \<and>
                r\<leadsto>(cs' @ u', v')q' \<and> r\<leadsto>(cs' @ u'', v'')q'' \<and> cs @ cs' = a' \<and>
                c = safe_hd (cs' @ u') \<and> c = safe_hd (cs' @ u''))"
              using IH[of a' "b # b'" qm "as @ [a]" bs, unfolded Cons' Cons]
                    reach'[of "safe_hd (a' @ u')"] step(2) step' True False
              unfolding Cons Cons' Cons'' symbs
              by (auto simp add: safe_hd_def)
            then show ?thesis
              apply (rule disjE)
               apply (rule disjI1)
               apply (auto simp add: Cons' Cons'')[1]
              apply (rule disjI2)
              apply (fastforce simp add: Cons' Cons'')
              done
          qed
        qed auto
      next
        case False
        then show ?thesis
          using b_props(1)
        proof (cases b2)
          case True
          have safe_hd: "safe_hd ((a # a') @ u') = safe_hd ((a # a') @ u'')"
            by (auto simp add: safe_hd_def)
          have "(\<exists>r cs c cs'. reachable r (as @ a # a') ((bs @ [b]) @ cs) (safe_hd u') c \<and>
              r\<leadsto>(u', cs' @ v')q' \<and> r\<leadsto>(u'', cs' @ v'')q'' \<and> cs @ cs' = b' \<and>
              c = safe_hd (cs' @ v') \<and> c = safe_hd (cs' @ v'')) \<or>
            (\<exists>r cs c cs'.
              reachable r (as @ cs) ((bs @ [b]) @ b') c (safe_hd v') \<and>
              r\<leadsto>(cs' @ u', v')q' \<and> r\<leadsto>(cs' @ u'', v'')q'' \<and> cs @ cs' = a # a' \<and>
              c = safe_hd (cs' @ u') \<and> c = safe_hd (cs' @ u''))"
            using IH[of "a # a'" b' qm as "bs @ [b]", unfolded Cons' Cons]
                  reach'[of _ "safe_hd (b' @ v')"] safe_hd step(2) step' False True
            by (auto simp add: Cons' Cons symbs)
          then show ?thesis
            apply (rule disjE)
             apply (rule disjI1)
             apply (fastforce simp add: Cons' Cons)[1]
            apply (rule disjI2)
            apply (auto simp add: Cons' Cons)
            done
        qed auto
      qed
    qed
  qed
qed

end

(* simulating any TDFA by an oTDFA *)

type_synonym 's otdfa_s = "'s + 's"

context TDFA
begin

definition otdfa_init :: "'s otdfa_s" where
  "otdfa_init = Inl init"

inductive otdfa_delta :: "'s otdfa_s \<Rightarrow> 'a Al \<times> 'b Al \<Rightarrow> 's otdfa_s \<times> bool \<times> bool \<Rightarrow> bool" where
  "\<delta> q (a, b) (q', b1, b2) \<Longrightarrow> \<not>(b1 \<and> b2) \<Longrightarrow> otdfa_delta (Inl q) (a, b) (Inl q', b1, b2)"
| "\<delta> q (a, b) (q', True, True) \<Longrightarrow> otdfa_delta (Inl q) (a, b) (Inr q', True, False)"
| "otdfa_delta (Inr q) (a, Symb b) (Inl q, False, True)"

definition otdfa_accept :: "'s otdfa_s \<Rightarrow> bool" where
  "otdfa_accept q = (case q of Inl q' \<Rightarrow> accept q' | _ \<Rightarrow> False)"

definition otdfa_Q :: "'s otdfa_s set" where
  "otdfa_Q = Inl ` Q \<union> Inr ` Q"

lemma otdfa_det:
  assumes "otdfa_delta q z x" "otdfa_delta q z x'"
  shows "x = x'"
  by (rule otdfa_delta.cases[OF assms(1)]; rule otdfa_delta.cases[OF assms(2)]) (auto dest: det)

lemma otdfa_finite_Q: "finite otdfa_Q"
  using finite_Q
  by (auto simp add: otdfa_Q_def)

lemma otdfa_init_in_Q: "otdfa_init \<in> otdfa_Q"
  using init_in_Q
  by (auto simp add: otdfa_init_def otdfa_Q_def)

lemma otdfa_closed:
  assumes "otdfa_delta q z (q', b1, b2)" "q \<in> otdfa_Q"
  shows "q' \<in> otdfa_Q"
  apply (rule otdfa_delta.cases[OF assms(1)])
  using assms(2)
  by (auto simp add: otdfa_Q_def dest: closed)

lemma otdfa_move_left:
  assumes "otdfa_delta q (a, b) (q', True, b2)"
  shows "a \<noteq> Blank"
  apply (rule otdfa_delta.cases[OF assms(1)])
  using move_left by auto

lemma otdfa_move_right:
  assumes "otdfa_delta q (a, b) (q', b1, True)"
  shows "b \<noteq> Blank"
  apply (rule otdfa_delta.cases[OF assms(1)])
  using move_right by auto

lemma otdfa_no_step:
  assumes "otdfa_delta q (a, b) (q', False, False)"
  shows "a = Blank \<and> b = Blank"
  apply (rule otdfa_delta.cases[OF assms(1)])
  using no_step by auto

lemma otdfa_move_one:
  assumes "otdfa_delta q (a, b) (q', True, True)"
  shows "False"
  by (rule otdfa_delta.cases[OF assms(1)]) auto

interpretation otdfa: oTDFA otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using otdfa_det otdfa_finite_Q otdfa_init_in_Q otdfa_closed[rotated]
        otdfa_move_left otdfa_move_right otdfa_no_step otdfa_move_one
  by unfold_locales auto

lemma tdfa_comp_otdfa:
  assumes "q \<leadsto>(as, bs) q'"
  shows "otdfa.computation (Inl q) (as, bs) (Inl q')"
  using assms
proof (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
  case (step_TT q a b q' as bs q'')
  show ?case
    using step_TT(3)
          otdfa.computation.step_TF[OF otdfa_delta.intros(2)[OF step_TT(1)]
            otdfa.computation.step_FT[OF otdfa_delta.intros(3)]]
          otdfa.computation.step_TF[OF otdfa_delta.intros(2)[OF step_TT(1)]
            otdfa.computation.step_R[OF otdfa_delta.intros(3)]]
    by (cases as) auto
qed (auto intro: otdfa_delta.intros)

lemma otdfa_comp_tdfa:
  assumes "otdfa.computation r (as, bs) (Inl q')"
    "r = Inl q \<or> (r = Inr q'' \<and> \<delta> q (Symb a, safe_hd bs) (q'', True, True))"
  shows "q \<leadsto>(if r = Inr q'' then a # as else as, bs) q'"
  using assms
proof (induction r "(as, bs)" "Inl q' :: 's otdfa_s" arbitrary: q as bs q' a q''
  rule: otdfa.computation.induct)
  case (step_L r a r' as)
  show ?case
    using step_L
  proof (cases r')
    case (Inr r')
    show ?thesis
      using step_L move_right
      by (fastforce simp add: Inr elim: otdfa_delta.cases)
  qed (auto elim: otdfa_delta.cases)
next
  case (step_R r b' r' bs)
  show ?case
    using step_R
    by (cases r') (auto simp add: safe_hd_def elim: otdfa_delta.cases)
next
  case (step_TF r a' b' r' as bs)
  show ?case
    using step_TF
    by (cases r') (auto simp add: safe_hd_def elim: otdfa_delta.cases)
next
  case (step_FT r a' b' r' as bs)
  show ?case
    using step_FT
    by (cases r') (auto simp add: safe_hd_def elim: otdfa_delta.cases)
qed (auto elim: otdfa_delta.cases)

lemma tdfa_otdfa_comp: "q \<leadsto>(as, bs) q' \<longleftrightarrow> otdfa.computation (Inl q) (as, bs) (Inl q')"
  using tdfa_comp_otdfa otdfa_comp_tdfa
  by fastforce

lemma tdfa_equiv_otdfa: "\<tau> = otdfa.\<tau>"
  unfolding \<tau>_def otdfa.\<tau>_def
  unfolding otdfa_init_def otdfa_accept_def tdfa_otdfa_comp
  by (auto split: sum.splits) (meson obj_sumE)

end

(* functional automata *)

locale fTDFA = TDFA init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> ('a :: finite) Al \<times> ('b :: finite) Al \<Rightarrow> 's \<times> bool \<times> bool \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes functional: "(as, bs) \<in> \<tau> \<Longrightarrow> (as, bs') \<in> \<tau> \<Longrightarrow> bs = bs'"

locale foTDFA = oTDFA init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> ('a :: finite) Al \<times> ('b :: finite) Al \<Rightarrow> 's \<times> bool \<times> bool \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes functional: "(as, bs) \<in> \<tau> \<Longrightarrow> (as, bs') \<in> \<tau> \<Longrightarrow> bs = bs'"
begin

lemma lin_bounded: "reachable q as bs a b \<Longrightarrow> q \<leadsto>(u, v) q' \<Longrightarrow> accept q' \<Longrightarrow>
  a = safe_hd u \<Longrightarrow> b = safe_hd v \<Longrightarrow> length v \<le> (length u + 1) * card Q"
proof (induction u arbitrary: as bs a b q v q')
  case Nil
  have q_Q: "q \<in> Q"
    using Nil(1)
    by (auto simp add: reachable_def)
  have reach: "\<And>u v q'. a = safe_hd u \<Longrightarrow> b = safe_hd v \<Longrightarrow>
    q \<leadsto>(u, v) q' \<Longrightarrow> accept q' \<Longrightarrow> (as @ u, bs @ v) \<in> \<tau>"
    using Nil(1)
    by (fastforce simp add: reachable_def)
  obtain xs q'' where outs: "outs Blank q xs q'' Blank"
    "\<delta> q'' (Blank, Blank) (q', False, False)" "v = map fst xs"
    using outs_Nil_intro[OF Nil(2)]
    by auto
  then show ?case
  proof (cases "length xs > card Q")
    case True
    obtain xs' where xs'_def: "outs Blank q xs' q'' Blank" "length xs' < length xs"
      "safe_hd (map fst xs') = safe_hd (map fst xs)"
      using outs_norm[OF outs(1) q_Q True]
      by auto
    have "(as, bs @ v) \<in> \<tau>"
      using reach Nil
      by fastforce
    moreover have "(as, bs @ map fst xs') \<in> \<tau>"
      using reach[OF Nil(4) _ outs_Nil_dest[OF xs'_def(1) outs(2)] Nil(3)]
            Nil(5)[unfolded outs(3)] xs'_def(3)
      by (auto simp add: safe_hd_def)
    ultimately show ?thesis
      using functional map_eq_imp_length_eq xs'_def(2) True
      by (fastforce simp add: outs(3))
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
  obtain xs q'' b'' bs' where outs: "outs (Symb a') q xs q'' b''"
   "q''\<leadsto>(u, bs')q'" "b'' = safe_hd bs'" "v = map fst xs @ bs'"
    using outs_Cons_intro[OF Cons(3)]
    by auto
  have aux: "safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | Blank \<Rightarrow> [])) = Blank \<Longrightarrow>
    b'' = Blank"
    by (auto simp add: safe_hd_def split: list.splits Al.splits)
  have a_def: "a = Symb a'"
    using Cons(5)
    by (auto simp add: safe_hd_def)
  have safe_hd_v: "safe_hd v = safe_hd (map fst xs @ (case b'' of Symb x \<Rightarrow> [x] | Blank \<Rightarrow> []))"
    using outs(3,4)
    by (cases xs) (auto simp add: safe_hd_def split: list.splits Al.splits)
  have "length xs > card Q \<Longrightarrow> False"
  proof -
    assume lassm: "length xs > card Q"
    obtain xs' where xs'_def: "outs (Symb a') q xs' q'' b''" "length xs' < length xs"
      "safe_hd (map fst xs') = safe_hd (map fst xs)"
      using outs_norm[OF outs(1) q_Q lassm]
      by auto
    have "(as @ a' # u, bs @ v) \<in> \<tau>"
      using reach Cons
      by fastforce
    moreover have "(as @ a' # u, bs @ map fst xs' @ bs') \<in> \<tau>"
      using reach[OF Cons(5) _ outs_Cons_dest[OF xs'_def(1) outs(2,3) refl] Cons(4),
            unfolded safe_hd_app[OF xs'_def(3), of bs'] Cons(6), OF arg_cong[OF outs(4)]] .
    ultimately show "False"
      using functional xs'_def(2) map_eq_imp_length_eq
      by (fastforce simp add: outs(4))
  qed
  then show ?case
    using outs(4) Cons(1)[OF _ outs(2) Cons(4) refl, OF outs_reachable[OF outs(1) _ _ refl,
          OF aux, simplified], OF Cons(2)[unfolded a_def Cons(6) safe_hd_v] outs(3)]
    by (fastforce simp add: outs(4))
qed

end

(* Definition 2 *)

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

(* Bounded trailing *)

definition active :: "'s \<Rightarrow> 'b list \<Rightarrow> bool" where
  "active q bs \<longleftrightarrow> (\<exists>q' as bs'. q \<leadsto>(as, bs @ bs') q' \<and> accept q')"

definition "bounded K \<equiv> \<forall>q q' u v v'. init \<leadsto>(u, v @ v') q \<and> active q [] \<and>
  init \<leadsto>(u, v) q' \<and> active q' v' \<longrightarrow> length v' \<le> K"

(* helper lemmas *)

lemma no_step: "q \<leadsto>(as, bs) q' \<Longrightarrow> as = [] \<Longrightarrow> bs = [] \<and> q = q'"
  by (induction q "(as, bs)" q' rule: computation.induct) auto

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

(* Definition 5 *)

definition output_speed :: nat where
  "output_speed = Max (length ` snd ` all_trans \<union> {1})"

lemma output_speed_step: "q \<in> Q \<Longrightarrow> \<delta> q a (q', bs) \<Longrightarrow> length bs \<le> output_speed"
  unfolding output_speed_def using all_trans_finite all_trans_step
  by (metis Max_ge UnCI finite.emptyI finite.insertI finite_UnI finite_imageI image_eqI snd_conv)

lemma output_speed_computation: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow>
  length bs \<le> length as * output_speed"
  apply (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
  using output_speed_step \<delta>_closed by (auto simp add: add_le_mono)

lemma output_speed_ext_computation: "q \<leadsto>e(as, qbs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> (q'', bs) \<in> set qbs \<Longrightarrow>
  length bs \<le> output_speed"
  apply (induction q "(as, qbs)" q' arbitrary: as qbs rule: computation_ext.induct)
  using output_speed_step \<delta>_closed by auto

lemma output_speed_pos: "output_speed \<ge> 1"
proof -
  have fin: "finite (length ` snd ` all_trans \<union> {1})"
    using all_trans_finite
    by auto
  show ?thesis
    using Max_ge[OF fin, of 1]
    by (auto simp add: output_speed_def)
qed

lemma computation_split_out: "q \<leadsto>(as'', bs @ bs') q' \<Longrightarrow> q \<in> Q \<Longrightarrow>
  \<exists>q'' as as' cs cs'. q \<leadsto>(as, cs) q'' \<and> q'' \<leadsto>(as', cs') q' \<and> as'' = as @ as' \<and>
    bs @ bs' = cs @ cs' \<and> length cs \<le> length bs \<and> length bs - length cs \<le> output_speed"
proof (induction q "(as'', bs @ bs')" q' arbitrary: as'' bs bs' rule: computation.induct)
  case (step q a q' bsa as bsa' q'')
  from step(1,5) have length_bsa: "length bsa \<le> output_speed"
    using output_speed_step by auto
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
      bs @ bs' = [] @ (bsa @ bsa') \<and> length [] \<le> length bs \<and> length bs - length [] \<le> output_speed"
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
  \<exists>as bs' q'. q \<leadsto>(as, bs') q' \<and> accept q' \<and> length as \<le> card Q \<and>
    length bs' \<le> card Q * output_speed"
  using comp_norm output_speed_computation
  apply (auto simp add: active_def)
  apply (meson dual_order.trans mult_le_mono1)
  done

(* Definition 4 *)

definition sg :: nat where
  "sg = Max ((\<lambda>q. Inf (length ` {as. \<exists>bs q'. q \<leadsto>(as, bs) q' \<and> accept q'})) `
    {q \<in> Q. active q []})"

lemma sg_le_card:
  assumes "active init []"
  shows "sg \<le> card Q"
proof -
  define Q' where "Q' = {q \<in> Q. active q []}"
  have Q'_props: "finite Q'" "Q' \<noteq> {}"
    using finite_Q assms(1) init_in_Q
    by (auto simp add: active_def Q'_def)
  have "\<And>q. q \<in> Q' \<Longrightarrow> Inf (length ` {as. \<exists>bs q'. q\<leadsto>(as, bs)q' \<and> accept q'}) \<le> card Q"
  proof -
    fix q
    assume in_Q': "q \<in> Q'"
    then obtain as bs q' where wit: "q\<leadsto>(as, bs)q'" "accept q'" "length as \<le> card Q"
      using active_Nil_dest
      unfolding Q'_def
      by blast
    then have len_as_in: "length as \<in> length ` {as. \<exists>bs q'. q\<leadsto>(as, bs)q' \<and> accept q'}"
      by auto
    show "Inf (length ` {as. \<exists>bs q'. q\<leadsto>(as, bs)q' \<and> accept q'}) \<le> card Q"
      by (rule le_trans[OF cInf_lower[OF len_as_in] wit(3)]) auto
  qed
  then show ?thesis
    using Q'_props
    by (auto simp add: sg_def Q'_def[symmetric])
qed

lemma active_Nil_dest_sg:
  assumes "active q []" "q \<in> Q"
  shows "\<exists>as bs' q'. q \<leadsto>(as, bs') q' \<and> accept q' \<and> length as \<le> sg \<and>
    length bs' \<le> sg * output_speed"
proof -
  define ass where "ass = length ` {as. \<exists>bs q'. q \<leadsto>(as, bs) q' \<and> accept q'}"
  have "ass \<noteq> {}"
    using assms(1)
    by (auto simp add: ass_def active_def)
  then have "Inf ass \<in> ass"
    using Inf_nat_def1
    by auto
  then obtain as bs q' where wit: "q \<leadsto>(as, bs) q'" "accept q'" "length as = Inf ass"
    by (auto simp add: ass_def)
  moreover have "Inf ass \<le> sg"
    using assms finite_Q
    by (auto simp add: ass_def sg_def)
  ultimately show ?thesis
    using output_speed_computation[OF wit(1) assms(2)]
    by (auto simp add: mult.commute order_subst1 intro!: exI[of _ as] exI[of _ bs] exI[of _ q'])
qed

lemma active_dest:
  assumes "active q bs" "q \<in> Q"
  shows "\<exists>as bs' q'. q \<leadsto>(as, bs @ bs') q' \<and> accept q' \<and>
    length bs' \<le> (1 + sg) * output_speed"
proof -
  obtain as bs' q' where act: "q \<leadsto>(as, bs @ bs') q'" "accept q'"
    using assms(1)
    by (auto simp add: active_def)
  then show ?thesis
  proof (cases "length bs' \<ge> output_speed")
    case True
    have app: "bs @ bs' = (bs @ take output_speed bs') @ (drop output_speed bs')"
      using True
      by auto
    obtain q'' as' as'' cs cs' where split: "q\<leadsto>(as', cs)q''" "q''\<leadsto>(as'', cs')q'"
      "as = as' @ as''"
      "(bs @ take output_speed bs') @ drop output_speed bs' = cs @ cs'"
      "length cs \<le> length (bs @ take output_speed bs')"
      "length (bs @ take output_speed bs') - length cs \<le> output_speed"
      using computation_split_out[OF act(1)[unfolded app] assms(2)]
      by auto
    obtain ds where ds_def: "cs = bs @ ds" "length ds \<le> output_speed"
      using split(5,6) True split_app[OF split(4)[unfolded app[symmetric]]]
      by fastforce
    note q''_Q = comp_closed[OF split(1) assms(2)]
    have act_q'': "active q'' []"
      using split(2) act(2)
      by (auto simp add: active_def)
    obtain es fs q''' where es_fs_def: "q''\<leadsto>(es, fs)q'''" "accept q'''" "length es \<le> sg"
      using active_Nil_dest_sg[OF act_q'' q''_Q]
      by auto
    have fs_len: "length fs \<le> sg * output_speed"
      using output_speed_computation[OF es_fs_def(1) q''_Q] es_fs_def(3)
      by (meson dual_order.trans mult_le_mono1)
    show ?thesis
      using comp_trans[OF split(1)[unfolded ds_def(1)] es_fs_def(1)] ds_def(2) fs_len es_fs_def(2)
      by fastforce
  qed fastforce
qed

lemma bounded_mono: "K \<le> K' \<Longrightarrow> bounded K \<Longrightarrow> bounded K'"
  by (fastforce simp add: bounded_def)

lemma bounded_dest: "\<And>q q' u v v'. bounded K \<Longrightarrow> init \<leadsto>(u, v @ v') q \<Longrightarrow> active q [] \<Longrightarrow>
  init \<leadsto>(u, v) q' \<Longrightarrow> active q' v' \<Longrightarrow> length v' \<le> K"
  by (auto simp add: bounded_def)

end

(* NFT with trailing bound K *)

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

(* Definition 3 *)

locale fNFT = NFT init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> ('b :: finite) list \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes functional: "(x, y) \<in> \<tau> \<Longrightarrow> (x, y') \<in> \<tau> \<Longrightarrow> y = y'"

end