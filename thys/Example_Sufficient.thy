theory Example_Sufficient
  imports Sufficient
begin

(* Example 8 *)

datatype states = q0 | q1 | q2 | q3 | qf

instantiation states :: finite
begin

instance
proof (standard)
  have "(UNIV :: states set) \<subseteq> {q0, q1, q2, q3, qf}"
    using states.exhaust by blast
  then show "finite (UNIV :: states set)"
    using finite_subset by auto
qed

end

datatype Sigma = a | b

instantiation Sigma :: finite
begin

instance
proof (standard)
  have "(UNIV :: Sigma set) \<subseteq> {a, b}"
    using Sigma.exhaust by blast
  then show "finite (UNIV :: Sigma set)"
    using finite_subset by auto
qed

end

(* Figure 2 *)

inductive delta :: "states \<Rightarrow> Sigma \<Rightarrow> states \<times> Sigma list \<Rightarrow> bool" where
  "delta q0 a (q1, [a, b, a])"
| "delta q0 a (q2, [a, b, a, b])"
| "delta q0 a (q3, [a, b, a, b])"
| "delta q1 a (qf, [b, a])"
| "delta q1 a (qf, [b, a, b])"
| "delta q2 a (qf, [a, b])"
| "delta q3 b (qf, [a, a])"

lemma finite_delta: "finite {x. delta q z x}"
proof -
  have "{x. delta q z x} \<subseteq> UNIV \<times> {xs. length xs \<le> 4}"
    by (auto elim: delta.cases)
  then show ?thesis
    using finite_subset finite_bounded_lists by fastforce
qed

interpretation NFT q0 delta "\<lambda>q. q = qf" UNIV
  using finite_UNIV finite_delta
  by unfold_locales auto

(* lemmas *)

lemma comp_q0_qf: "computation q0 ([a, b], [a, b, a, b, a, a]) qf"
  using comp_trans[OF one_step[OF delta.intros(3)] one_step[OF delta.intros(7)]]
  by auto

lemma comp_q1_dest: "computation q1 (z # zs, bs) q' \<Longrightarrow>
  (z = a \<and> zs = [] \<and> bs = [b, a] \<and> q' = qf) \<or> (z = a \<and> zs = [] \<and> bs = [b, a, b] \<and> q' = qf)"
  by (auto elim: computation.cases delta.cases)

lemma comp_q2_dest: "computation q2 (z # zs, bs) q' \<Longrightarrow> z = a \<and> zs = [] \<and> bs = [a, b] \<and> q' = qf"
  by (auto elim: computation.cases delta.cases)

lemma comp_q3_dest: "computation q3 (z # zs, bs) q' \<Longrightarrow> z = b \<and> zs = [] \<and> bs = [a, a] \<and> q' = qf"
  by (auto elim: computation.cases delta.cases)

lemma comp_q3_qf: "computation q3 (as, bs) qf \<Longrightarrow> as = [b] \<and> bs = [a, a]"
  using comp_q3_dest
  by (cases as) (auto dest: no_step)

lemma comp_qf_dest: "computation qf (zs, bs) q' \<Longrightarrow> zs = [] \<and> bs = [] \<and> q' = qf"
  by (auto elim: computation.cases delta.cases)

(* accepted relation *)

lemma lang: "\<tau> = {([a, a], [a, b, a, b, a]), ([a, a], [a, b, a, b, a, b]),
  ([a, b], [a, b, a, b, a, a])}"
proof (rule set_eqI, rule iffI)
  fix x
  assume lassm: "x \<in> \<tau>"
  obtain as bs where x_def: "x = (as, bs)"
    by (cases x) auto
  have comp: "computation q0 (as, bs) qf"
    using lassm
    unfolding \<tau>_def x_def
    by auto
  show "x \<in> {([a, a], [a, b, a, b, a]), ([a, a], [a, b, a, b, a, b]),
    ([a, b], [a, b, a, b, a, a])}"
  proof (cases as)
    case Nil
    then show ?thesis
      using comp
      by (auto dest: no_step)
  next
    case (Cons a as')
    obtain q cs cs' where split: "delta q0 a (q, cs)" "computation q (as', cs') qf"
      "bs = cs @ cs'"
      by (rule computation.cases[OF comp[unfolded Cons]]) auto
    show ?thesis
      using split
      unfolding x_def Cons
      by (cases as')
         (auto elim!: delta.cases dest: no_step comp_q1_dest comp_q2_dest comp_q3_dest)
  qed
next
  fix x
  assume "x \<in> {([a, a], [a, b, a, b, a]), ([a, a], [a, b, a, b, a, b]),
    ([a, b], [a, b, a, b, a, a])}"
  then show "x \<in> \<tau>"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
          comp_trans[OF one_step[OF delta.intros(2)] one_step[OF delta.intros(6)]] comp_q0_qf
    by (auto simp add: \<tau>_def)
qed

lemma active_q1_dest: "active q1 bs \<Longrightarrow> \<exists>n. bs = take n [b, a, b]"
  apply (auto simp add: active_def)
  subgoal for as bs'
    apply (cases as)
    using comp_q1_dest
     apply (auto dest: no_step)
    by (metis append.assoc append.simps(1) append.simps(2) append_eq_conv_conj)
  done

lemma active_q2_dest: "active q2 bs \<Longrightarrow> \<exists>n. bs = take n [a, b]"
  apply (auto simp add: active_def)
  subgoal for as bs'
    apply (cases as)
    using comp_q2_dest
     apply (auto dest: no_step)
    by (metis append_eq_conv_conj take_append)
  done

lemma active_q3_dest: "active q3 bs \<Longrightarrow> \<exists>n. bs = take n [a, a]"
  apply (auto simp add: active_def)
  subgoal for as bs'
    apply (cases as)
    using comp_q3_dest
     apply (auto dest: no_step)
    by (metis append_eq_conv_conj take_append)
  done

lemma active_qf_dest: "active qf bs \<Longrightarrow> bs = []"
  by (auto simp add: active_def dest: comp_qf_dest)

(* bounded NFT with trailing bound 1 *)

interpretation bNFT q0 delta "\<lambda>q. q = qf" UNIV 1
  apply unfold_locales
  apply (auto simp add: bounded_def)
  subgoal premises prems for q q' u v v'
    using prems
  proof (cases u)
    case (Cons z zs)
    show ?thesis
      apply (rule computation.cases[OF prems(1)[unfolded Cons]];
             rule computation.cases[OF prems(3)[unfolded Cons]]; cases zs)
             apply (auto elim!: delta.cases dest!: comp_q1_dest comp_q2_dest comp_q3_dest)
              apply (auto dest!: no_step)
      done
  qed (auto dest: no_step)[1]
  done

lemma tdfa_init: "tdfa_init = Some ([], {(q0, 0)})"
  using comp_q0_qf
  by (auto simp add: tdfa_init_def active_def)

lemma delta_length: "delta x y z \<Longrightarrow> length (snd z) \<in> {2, 3, 4}"
  by (auto elim: delta.cases)

lemma delta_length': "n \<in> {2, 3, 4} \<Longrightarrow> \<exists>x y z. delta x y z \<and> length (snd z) = n"
  using delta.intros
  by fastforce

(* output speed *)

lemma output_speed: "output_speed = 4"
proof -
  have "length ` snd ` {x. \<exists>a b. delta a b x} = {2, 3, 4}"
    using delta_length delta_length'
    apply (auto)
      apply (metis imageI mem_Collect_eq snd_conv)+
    done
  then show ?thesis
    by (auto simp add: output_speed_def all_trans_def)
qed

(* buffer length *)

lemma K': "K' = 5"
  unfolding K'_def output_speed by auto

(* Figure 3 *)

lemma step_1: "tdfa_step tdfa_init (Symb a, Symb a) (Some ([a], {(q0, 0)}), False, True)"
  "Some ([a], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs a [] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step tdfa_init (Symb a, Symb a) (Some ([a], {(q0, 0)}), False, True)"
    using tdfa_step.intros(2)[OF init_in_tdfa_Q[unfolded tdfa_init] _ ext_qs[symmetric], of 0]
    unfolding tdfa_init drop_qs K'
    by auto
  then show "Some ([a], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF init_in_tdfa_Q[unfolded tdfa_init]]
    by (auto simp add: tdfa_init)
qed

lemma step_2: "tdfa_step (Some ([a], {(q0, 0)})) (Symb a, Symb b)
  (Some ([a, b], {(q0, 0)}), False, True)" "Some ([a, b], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs b [a] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (Some ([a], {(q0, 0)})) (Symb a, Symb b)
    (Some ([a, b], {(q0, 0)}), False, True)"
    using tdfa_step.intros(2)[OF step_1(2) _ ext_qs[symmetric], of 0]
    unfolding drop_qs K'
    by auto
  then show "Some ([a, b], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_1(2)]
    by auto
qed

lemma step_3: "tdfa_step (Some ([a, b], {(q0, 0)})) (Symb a, Symb a)
  (Some ([a, b, a], {(q0, 0)}), False, True)" "Some ([a, b, a], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs a [a, b] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (Some ([a, b], {(q0, 0)})) (Symb a, Symb a)
    (Some ([a, b, a], {(q0, 0)}), False, True)"
    using tdfa_step.intros(2)[OF step_2(2) _ ext_qs[symmetric], of 0]
    unfolding drop_qs K'
    by auto
  then show "Some ([a, b, a], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_2(2)]
    by auto
qed

lemma step_4: "tdfa_step (Some ([a, b, a], {(q0, 0)})) (Symb a, Symb b)
  (Some ([a, b, a, b], {(q0, 0)}), False, True)" "Some ([a, b, a, b], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs b [a, b, a] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (Some ([a, b, a], {(q0, 0)})) (Symb a, Symb b)
    (Some ([a, b, a, b], {(q0, 0)}), False, True)"
    using tdfa_step.intros(2)[OF step_3(2) _ ext_qs[symmetric], of 0]
    unfolding drop_qs K'
    by auto
  then show "Some ([a, b, a, b], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_3(2)]
    by auto
qed

lemma step_5: "tdfa_step (Some ([a, b, a, b], {(q0, 0)})) (Symb a, Symb a)
  (Some ([a, b, a, b, a], {(q0, 0)}), False, True)" "Some ([a, b, a, b, a], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs a [a, b, a, b] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (Some ([a, b, a, b], {(q0, 0)})) (Symb a, Symb a)
    (Some ([a, b, a, b, a], {(q0, 0)}), False, True)"
    using tdfa_step.intros(2)[OF step_4(2) _ ext_qs[symmetric], of 0]
    unfolding drop_qs K'
    by auto
  then show "Some ([a, b, a, b, a], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_4(2)]
    by auto
qed

lemma take_length: "n \<le> Suc (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> take n [a, b, a, b, a] = ys \<Longrightarrow>
  n = length ys"
  by auto

lemma step_6: "tdfa_step (Some ([a, b, a, b, a], {(q0, 0)})) (Symb a, Symb b)
  (Some ([b, a], {(q1, 0), (q2, 1), (q3, 1)}), True, False)"
  "Some ([b, a], {(q1, 0), (q2, 1), (q3, 1)}) \<in> tdfa_Q"
proof -
  have act_q1: "active q1 [b, a]"
    using one_step[OF delta.intros(4)]
    by (auto simp add: active_def)
  have act_q2: "active q2 [a]"
    using one_step[OF delta.intros(6)]
    by (auto simp add: active_def)
  have act_q3: "active q3 [a]"
    using one_step[OF delta.intros(7)]
    by (auto simp add: active_def)
  have upd_qs: "upd_qs a [a, b, a, b, a] {(q0, 0)} = {(q1, 3), (q2, 4), (q3, 4)}"
    by (auto simp add: upd_qs_def elim!: delta.cases
        dest: active_q1_dest active_q2_dest active_q3_dest take_length
        intro: delta.intros act_q1 act_q2 act_q3)
  have drop_qs: "drop_qs 3 {(q1, 3), (q2, 4), (q3, 4)} =
    {(q1, 0), (q2, 1), (q3, 1)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (Some ([a, b, a, b, a], {(q0, 0)})) (Symb a, Symb b)
    (Some ([b, a], {(q1, 0), (q2, 1), (q3, 1)}), True, False)"
    using tdfa_step.intros(3)[OF step_5(2) upd_qs[symmetric], of 3 "Symb b"]
    unfolding drop_qs K'
    by auto
  then show "Some ([b, a], {(q1, 0), (q2, 1), (q3, 1)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_5(2)]
    by auto
qed

lemma step_7: "tdfa_step (Some ([b, a], {(q1, 0), (q2, 1), (q3, 1)})) (Symb a, Symb b)
  (Some ([b, a, b], {(q1, 0), (q2, 1)}), False, True)"
  "Some ([b, a, b], {(q1, 0), (q2, 1)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs b [b, a] {(q1, 0), (q2, 1), (q3, 1)} = {(q1, 0), (q2, 1)}"
    using one_step[OF delta.intros(5)] one_step[OF delta.intros(6)]
    by (fastforce simp add: ext_qs_def active_def dest: comp_q3_qf)
  have drop_qs: "drop_qs 0 {(q1, 0), (q2, 1)} = {(q1, 0), (q2, 1)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (Some ([b, a], {(q1, 0), (q2, 1), (q3, 1)})) (Symb a, Symb b)
    (Some ([b, a, b], {(q1, 0), (q2, 1)}), False, True)"
    using tdfa_step.intros(2)[OF step_6(2) _ ext_qs[symmetric], of 0 a]
    unfolding drop_qs K'
    by auto
  then show "Some ([b, a, b], {(q1, 0), (q2, 1)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_6(2)]
    by auto
qed

lemma step_8: "tdfa_step (Some ([b, a, b], {(q1, 0), (q2, 1)})) (Symb a, Blank)
  (Some ([], {(qf, 0)}), True, False)"
  "Some ([], {(qf, 0)}) \<in> tdfa_Q"
proof -
  have act_qf: "active qf []"
    by (auto simp add: active_def)
  have upd_qs: "upd_qs a [b, a, b] {(q1, 0), (q2, 1)} = {(qf, 3)}"
    by (auto simp add: upd_qs_def elim!: delta.cases
        dest: active_qf_dest
        intro: delta.intros act_qf)
  have drop_qs: "drop_qs 3 {(qf, 3)} = {(qf, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (Some ([b, a, b], {(q1, 0), (q2, 1)})) (Symb a, Blank)
    (Some ([], {(qf, 0)}), True, False)"
    using tdfa_step.intros(3)[OF step_7(2) upd_qs[symmetric], of 3]
    unfolding drop_qs K'
    by auto
  then show "Some ([], {(qf, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_7(2)]
    by auto
qed

lemma step_9: "tdfa_step (Some ([], {(qf, 0)})) (Blank, Blank) (None, False, False)"
  using tdfa_step.intros(1)[OF step_8(2)]
  by auto

interpretation tdfa: TDFA tdfa_init tdfa_step tdfa_accept tdfa_Q
  using tdfa_axioms .

lemma comp_correct: "([a, a], [a, b, a, b, a, b]) \<in> tdfa.\<tau>"
  using tdfa.computation.intros(5)[OF step_1(1), OF tdfa.computation.intros(5)[OF step_2(1)],
        OF tdfa.computation.intros(5)[OF step_3(1)], OF tdfa.computation.intros(5)[OF step_4(1)],
        OF tdfa.computation.intros(5)[OF step_5(1)], OF tdfa.computation.intros(4)[OF step_6(1)],
        OF tdfa.computation.intros(5)[OF step_7(1)], OF tdfa.computation.intros(1)[OF step_8(1)],
        OF tdfa.computation.intros(6)[OF step_9(1)]]
  unfolding tdfa.\<tau>_def tdfa_accept_def
  by auto

end