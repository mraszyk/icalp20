theory Example_Necessary
  imports Computation
begin

datatype states = Init | Copy bool | Skip bool

instantiation states :: finite
begin

instance
proof (standard)
  have "(UNIV :: states set) \<subseteq> {Init, Copy True, Copy False, Skip True, Skip False}"
    using states.exhaust by blast
  then show "finite (UNIV :: states set)"
    using finite_subset by auto
qed

end

type_synonym Sigma = "bool option"

inductive delta :: "states \<Rightarrow> Sigma \<Rightarrow> states \<times> Sigma list \<Rightarrow> bool" where
  "delta Init None (Copy True, [None])"
| "delta Init None (Skip False, [])"
| "delta Init (Some True) (Skip True, [])"
| "delta Init (Some False) (Copy False, [])"
| "delta (Copy True) (Some True) (Skip True, [])"
| "delta (Skip False) (Some False) (Copy False, [])"
| "delta (Copy b) None (Copy b, [None])"
| "delta (Skip b) None (Skip b, [])"

lemma finite_delta: "finite {x. delta q z x}"
proof -
  have "{x. delta q z x} \<subseteq> UNIV \<times> {xs. length xs \<le> 1}"
    by (auto elim: delta.cases)
  then show ?thesis
    using finite_subset finite_bounded_lists by fastforce
qed

interpretation NFT Init delta "\<lambda>q. q = Copy False \<or> q = Skip True" UNIV
  using finite_UNIV finite_delta
  by unfold_locales auto

(* lemmas *)

lemma nft_comp_Copy_False_Skip: "computation q (as, bs) q' \<Longrightarrow>
  q = Copy False \<Longrightarrow> q' = Skip b \<Longrightarrow> False"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto elim!: delta.cases)

lemma nft_comp_Skip_True_Copy: "computation q (as, bs) q' \<Longrightarrow>
  q = Skip True \<Longrightarrow> q' = Copy b \<Longrightarrow> False"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto elim!: delta.cases)

lemma nft_comp_Skip_dest: "computation q (as, bs) q' \<Longrightarrow> q = Skip b \<Longrightarrow> q' = Skip b' \<Longrightarrow>
  as = replicate (length as) None \<and> bs = [] \<and> b = b'"
  apply (induction q "(as, bs)" q' arbitrary: as bs b b' rule: computation.induct)
  using nft_comp_Copy_False_Skip by (force elim!: delta.cases)+

lemma nft_comp_Copy_dest: "computation q (as, bs) q' \<Longrightarrow> q = Copy b \<Longrightarrow> q' = Copy b' \<Longrightarrow>
  as = replicate (length as) None \<and> bs = as \<and> b = b'"
  apply (induction q "(as, bs)" q' arbitrary: as bs b b' rule: computation.induct)
  using nft_comp_Skip_True_Copy by (force elim!: delta.cases)+

lemma nft_comp_Skip_intro: "computation (Skip b) (replicate n None, []) (Skip b)"
  using computation.step delta.intros(8)
  by (induction n) fastforce+

lemma nft_comp_Copy_intro: "computation (Copy b) (replicate n None, replicate n None) (Copy b)"
  using computation.step delta.intros(7)
  by (induction n) fastforce+

lemma sound_True: "(replicate n None @ [Some True] @ replicate n' None, replicate n None) \<in> \<tau>"
  unfolding \<tau>_def
  using comp_trans[OF one_step[OF delta.intros(3)] nft_comp_Skip_intro]
        comp_trans[OF comp_trans[OF comp_trans[OF
        one_step[OF delta.intros(1)] nft_comp_Copy_intro]
        one_step[OF delta.intros(5)]] nft_comp_Skip_intro]
  by (cases n) auto

lemma sound_False: "(replicate n None @ [Some False] @ replicate n' None, replicate n' None) \<in> \<tau>"
  unfolding \<tau>_def
  using comp_trans[OF one_step[OF delta.intros(4)] nft_comp_Copy_intro]
        comp_trans[OF comp_trans[OF comp_trans[OF
        one_step[OF delta.intros(2)] nft_comp_Skip_intro]
        one_step[OF delta.intros(6)]] nft_comp_Copy_intro]
  by (cases n) auto

lemma snd_part:
  assumes "computation q (as, bs) q'" "q = Copy False \<or> q = Skip True"
    "q' = Copy False \<or> q' = Skip True"
  shows "q = q'" "as = replicate (length as) None \<and> bs = (if q = Copy False then as else [])"
proof -
  show q_q': "q = q'"
    using nft_comp_Copy_False_Skip[OF assms(1)] nft_comp_Skip_True_Copy[OF assms(1)] assms(2,3)
    by auto
  show "as = replicate (length as) None \<and> bs = (if q = Copy False then as else [])"
    using assms(2)
  proof (rule disjE)
    assume q_def: "q = Copy False"
    then show "as = replicate (length as) None \<and> bs = (if q = Copy False then as else [])"
      using nft_comp_Copy_dest[OF assms(1) q_def q_q'[symmetric, unfolded q_def]]
      by auto
  next
    assume q_def: "q = Skip True"
    then show "as = replicate (length as) None \<and> bs = (if q = Copy False then as else [])"
      using nft_comp_Skip_dest[OF assms(1) q_def q_q'[symmetric, unfolded q_def]]
      by auto
  qed
qed

lemma fst_part:
  assumes "computation q (as, bs) q'" "q = Copy True \<or> q = Skip False"
    "q' = Copy False \<or> q' = Skip True"
  shows "\<exists>n n'. as = replicate n None @ [Some (q = Copy True)] @ replicate n' None \<and>
    bs = replicate (if q = Copy True then n else n') None"
  using assms
proof (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
  case (step q a q' bs as bs' q'')
  show ?case
  proof (cases a)
    case None
    then show ?thesis
      using step nft_comp_Copy_dest nft_comp_Skip_dest
      apply (auto elim!: delta.cases)
         apply fastforce
        apply (metis (full_types) append_Cons replicate_Suc)
      apply (metis replicate_Suc)
      apply fastforce
      done
  next
    case (Some b)
    show ?thesis
      using step
      using snd_part[OF step(2)]
      apply (auto simp add: Some elim!: delta.cases)
      apply force
      done
  qed
qed auto

lemma completeness:
  assumes "(as, bs) \<in> \<tau>"
  shows "\<exists>n n' b. as = replicate n None @ [Some b] @ replicate n' None \<and>
    bs = replicate (if b then n else n') None"
  using assms
proof (cases as)
  case (Cons a as')
  obtain qf where comp: "computation Init (a # as', bs) qf" "qf = Copy False \<or> qf = Skip True"
    using assms
    unfolding \<tau>_def Cons
    by auto
  obtain q cs cs' where split: "delta Init a (q, cs)" "computation q (as', cs') qf"
    "bs = cs @ cs'"
    by (rule computation.cases[OF comp(1)]) auto
  show ?thesis
  proof (cases a)
    case None
    then have q_or: "q = Copy True \<or> q = Skip False"
      using split(1)
      by (auto elim: delta.cases)
    have cs_def: "cs = (if q = Copy True then [None] else [])"
      using split(1)
      by (auto simp add: None elim: delta.cases)
    obtain n n' where wit: "as' = replicate n None @ [Some (q = Copy True)] @ replicate n' None"
      "cs' = replicate (if q = Copy True then n else n') None"
      using fst_part[OF split(2) q_or comp(2)]
      by auto
    show ?thesis
      apply (auto simp add: Cons None split(3) cs_def wit)
      apply (rule exI[of _ "n + 1"])
         apply (auto)[1]
      apply (rule exI[of _ "n + 1"])
      apply auto
      done
  next
    case (Some b)
    then have q_or: "q = Copy False \<or> q = Skip True"
      using split(1)
      by (auto elim: delta.cases)
    have step_def: "b = (q = Skip True)" "cs = []"
      using split(1)
      by (auto simp add: Some elim: delta.cases)
    show ?thesis
      using snd_part(2)[OF split(2) q_or comp(2)] q_or
      apply (auto simp add: Cons Some step_def split(3))
       apply force
      apply fastforce
      done
  qed
qed (auto simp add: \<tau>_def dest: no_step)

lemma active_Copy: "active (Copy True) []"
  using one_step[OF delta.intros(5)]
  by (auto simp add: active_def)

lemma active_Skip: "active (Skip False) (replicate n None)"
  using comp_trans[OF one_step[OF delta.intros(6)] nft_comp_Copy_intro[of False "n"]]
  apply (auto simp add: active_def)
  apply (metis append_Nil2)
  done

(* main results *)

lemma correctness: "\<tau> = {(as, bs). \<exists>n n' b. as = replicate n None @ [Some b] @ replicate n' None \<and>
  bs = replicate (if b then n else n') None}"
  using sound_True sound_False completeness
  by fastforce

lemma unbounded: "\<not>bounded K"
  unfolding bounded_def
  using comp_trans[OF one_step[OF delta.intros(1)] nft_comp_Copy_intro[of True "K"]]
        active_Copy
        comp_trans[OF one_step[OF delta.intros(2)] nft_comp_Skip_intro[of False "K"]]
        active_Skip[of "K + 1"]
  using impossible_Cons
  by auto fastforce

end
