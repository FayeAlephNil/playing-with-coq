From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem contrapositive : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H NQ PP.
  apply (NQ (H PP)).
Qed.

Inductive seq : nat -> Set :=
  | niln : seq 0
  | consn : forall n : nat, nat -> seq n -> seq (S n).

Fixpoint length (n : nat) (s : seq n) {struct s} : nat :=
  match s with
  | niln => 0
  | consn _ s' => S (length s')
  end.

Theorem length_corr : forall (n : nat) (s : seq n), length s = n.
Proof.
  intros n s.
  induction s.
  simpl.
  trivial.
  simpl.
  rewrite IHs.
  trivial.
Qed.

Lemma add_succ : forall (n m : nat), n + S m = S (n + m).
Proof.
  intros n m.
  induction n.

  simpl.
  trivial.

  simpl.
  rewrite IHn.
  trivial.
Qed.

Theorem add_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros n m.

  induction m.
  induction n.
  trivial.

  simpl.
  rewrite IHn.
  simpl.
  trivial.

  simpl.
  symmetry in IHm.
  rewrite IHm.
  apply add_succ.
Qed.

Lemma add_zero : forall (n : nat), n + 0 = n.
Proof.
  intros.
  rewrite add_comm.
  simpl.
  trivial.
Qed.

Theorem add_assoc : forall (n m k : nat), n + (m + k) = (n + m) + k.
Proof.
  intros n m k.

  induction n.
  simpl.
  trivial.

  rewrite add_comm.
  rewrite add_succ.
  rewrite add_comm.
  rewrite IHn.
  simpl.
  trivial.
Qed.

Theorem add_switch : forall (n m k : nat), n + (m + k) = m + (n + k).
Proof.
  intros.
  rewrite add_assoc.
  rewrite [n + m]add_comm.
  rewrite -add_assoc.
  trivial.
Qed.

Theorem add_elim : forall (n m k : nat), (n + m = n + k) -> (m = k).
Proof.
  intros.
  induction n.
  apply H.

  assert (P : n + m = n + k).
  simpl in H.
  injection H.
  trivial.
  apply IHn in P.
  trivial.
Qed.

Theorem add_elim_simple : forall (n m : nat), n + m = n -> m = 0.
Proof.
  intros.
  rewrite -[n]add_zero in H.
  rewrite -add_assoc in H.
  simpl in H.
  apply add_elim in H.
  apply H.
Qed.

Theorem mult_succ : forall (n m : nat), m + m * n = m * S n.
Proof.
  intros.
  induction m.
  trivial.
  simpl.
  rewrite add_assoc.
  rewrite [m + n]add_comm.
  rewrite -add_assoc.
  rewrite IHm.
  trivial.
Qed.

Theorem mult_comm : forall (n m : nat), n * m = m * n.
Proof.
  intros.
  induction n.
  induction m.
  trivial.
  trivial.

  simpl.
  rewrite IHn.
  apply mult_succ.
Qed.

Theorem mult_dist : forall (n m k : nat), n * (m + k) = n * m + n * k.
Proof.
  intros.
  induction n.
  trivial.

  simpl.
  rewrite IHn.
  rewrite -[m + k + (n * m + n * k)]add_assoc.
  rewrite [k + (n * m + n * k)]add_assoc.
  rewrite [k + n * m]add_comm.
  rewrite -[n * m + k + n * k]add_assoc.
  rewrite add_assoc.
  trivial.
Qed.

Theorem mult_assoc : forall (n m k : nat), n * (m * k) = (n * m) * k.
Proof.
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  rewrite mult_comm.
  rewrite [n * m * k]mult_comm.
  rewrite -mult_dist.
  rewrite mult_comm.
  trivial.
Qed.

Theorem add_zpp : forall (n m : nat), n + m = 0 -> n = 0 /\ m = 0.
Proof.
  split.
  induction n.
  trivial.
  simpl in H.
  inversion H.

  induction m.
  trivial.
  rewrite add_succ in H.
  inversion H.
Qed.

Theorem mult_zpp : forall (n m : nat), n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  induction n.
  left.
  trivial.

  right.
  simpl in H.
  apply add_zpp in H.
  destruct H as [Hl Hr].
  apply Hl.
Qed.


Definition le (n m : nat) : Prop := exists (k : nat), k + n = m.

Theorem le_trans : forall (n m k : nat), le n m -> le m k -> le n k.
Proof.
  intros n m k [i Hi] [j Hj].
  exists (j + i).
  rewrite -Hi in Hj.
  rewrite add_assoc in Hj.
  apply Hj.
Qed.

Theorem le_refl : forall (n : nat), le n n.
Proof.
  intros.
  exists 0.
  trivial.
Qed.

Theorem le_succ : forall (n : nat), le n (S n).
Proof.
  intro n.
  exists 1.
  simpl.
  trivial.
Qed.

Theorem le_anti_sym : forall (n m : nat), le n m -> le m n -> n = m.
Proof.
  intros n m [i Hi] [j Hj].
  rewrite -Hi in Hj.
  rewrite [i + n]add_comm in Hj.
  rewrite add_switch in Hj.
  apply add_elim_simple in Hj.
  apply add_zpp in Hj.
  destruct Hj as [_ Pi].
  rewrite Pi in Hi.
  simpl in Hi.
  apply Hi.
Qed.

Definition divides_with (n m r : nat) : Prop := exists (q : nat), r + q * n = m /\ 0 <= r < q.

Definition divides (n m : nat) : Prop := exists (k : nat), k * n = m.

Theorem divides_both : forall (n m k : nat), n * m = k -> divides n k /\ divides m k.
Proof.
  split.
  exists m; rewrite mult_comm; apply H.
  exists n; apply H.
Qed.

Theorem divides_trans : forall (n m k : nat), divides n m -> divides m k -> divides n k.
Proof.
  intros n m k [i Hn] [j Hm].
  rewrite -Hn in Hm.
  rewrite mult_assoc in Hm.
  exists (j * i).
  apply Hm.
Qed.

Theorem divides_refl : forall (n : nat), divides n n.
Proof.
  intros.
  exists 1.
  simpl; rewrite add_comm; simpl.
  trivial.
Qed.

Theorem divides_one : forall (n : nat), divides 1 n.
Proof.
  intros.
  exists n.
  rewrite mult_comm.
  simpl.
  rewrite add_zero. trivial.
Qed.

Theorem divides_le : forall (n m : nat), divides n m -> le n m \/ m = 0.
Proof.
  intros n m [k Hk].
  induction k.
  simpl in Hk.
  right; symmetry; apply Hk.

  left.
  simpl in Hk.
  exists (k * n).
  rewrite add_comm in Hk.
  apply Hk.
Qed.

Theorem divides_anti_sym : forall (n m : nat), divides n m -> divides m n -> n = m.
  intros n m p q.
  pose proof (divides_le p) as Hp.
  pose proof (divides_le q) as Hq.
  destruct p as [k Hk]; destruct q as [j Hj].
  destruct Hp as [ple | p0].
  destruct Hq as [qle | q0].
  - apply ((le_anti_sym ple) qle).
  - transitivity 0.
    apply q0.
    rewrite q0 in Hk.
    rewrite mult_comm in Hk; simpl in Hk; apply Hk.
  - symmetry; transitivity 0.
    apply p0.
    rewrite p0 in Hj; rewrite mult_comm in Hj; simpl in Hj; apply Hj.
Qed.

Theorem mult_one : forall (n m : nat), n * m = 1 -> n = 1 /\ m = 1.
  intros.
  pose proof (divides_both H) as [Pn Pm].
  split.
  apply ((divides_anti_sym Pn) (divides_one n)).
  apply ((divides_anti_sym Pm) (divides_one m)).
Qed.


Definition prime (p : nat) : Prop := forall (n : nat), divides n p -> n = 1 \/ n = p.

Definition composite (c : nat) : Prop := exists (n m : nat), n * m = c /\ n <> 1 /\ n <> c.

Theorem decidable_eq : forall (n m : nat), n = m \/ n <> m.
Proof.
  intros n.
  induction n.
  intro m.
  destruct m.
  left; trivial.
  right; trivial.

  intro m.
  destruct m.
  right.
  inversion 1.

  destruct (IHn m) as [IHn_eq | IHn_neq].
  - left. rewrite IHn_eq. trivial.
  - right. injection. apply IHn_neq.
Defined.

Theorem prime_not_comp : forall (p : nat), p <> 1 -> prime p <-> ~ composite p.
  intros p H. split. intro Pp.
  unfold not; intro Cp.
  destruct Cp as [n [m [Hnm [Hnn Hnc]]]].
  cut (divides n p).
  intro L.
  apply Pp in L.
  destruct L as [Lpn | Lnp].
  - apply (Hnn Lpn).
  - apply (Hnc Lnp).
  - exists (m).
    rewrite mult_comm; apply Hnm.
  - intro NCp. unfold not in NCp.
    intros m [k Hk].
    pose proof (decidable_eq m 1) as [Mone_eq | Mone_neq].
    -- left. apply Mone_eq.
    -- right.
       pose proof (decidable_eq m p) as [Mp_eq | Mp_neq].
       * apply Mp_eq.
       * cut (composite p).
         intro Cp. exfalso. apply (NCp Cp).
         exists m.
         exists k.
         rewrite mult_comm in Hk.
         split.
         apply Hk.
         split.
         apply Mone_neq.
         apply Mp_neq.
Qed.

Definition less (n m : nat) : Prop := le n m /\ n <> m.

Theorem less_succ : forall (n : nat), less n (S n).
Proof.
  intro n. split.
  apply le_succ.
  induction n.
  trivial.

  injection. apply IHn.
Qed.

Theorem less_zero : forall (n : nat), ~ less n 0.
Proof.
  intro n. unfold not. intro P.
  destruct P as [Ple Pneq].
  induction n.
  auto.

  destruct Ple as [k Pk].
  pose proof (add_zpp Pk) as [Hk HSn].
  inversion HSn.
Qed.

Theorem le_ind : forall (n m : nat), le n (S m) -> le n m \/ n = S m.
Proof.
  intros n m [k Hk].
  destruct k.
  right.
  simpl in Hk. apply Hk.

  left; exists k.
  simpl in Hk.
  injection Hk.
  trivial.
Qed.

Theorem le_less : forall (n m : nat), le n m <-> less n (S m).
Proof.
  intros n m.
  split.
  - intro H.
    split.
    -- apply ((le_trans H) (le_succ m)).
    -- destruct H as [k Hk].
       destruct k.
       --- simpl in Hk.
           rewrite Hk.
           trivial.
       --- rewrite add_comm in Hk; simpl in Hk.
           rewrite -Hk.
           rewrite -add_succ.
           rewrite -[n]add_zero.
           rewrite -add_assoc.
           simpl.
           cut (0 <> S (S k)). intro P.
           pose proof ((decidable_eq (n + 0)) (n + S (S k))) as [Qeq | Qneq].
           * pose proof (add_elim Qeq) as NQ.
             exfalso. apply (P NQ).
           * apply Qneq.
           * trivial.
  - intro H.
    destruct H as [Hle Hneq].
    pose proof (le_ind Hle) as [Hlem | Heq].
    -- apply Hlem.
    -- exfalso. apply (Hneq Heq).
Qed.

Theorem less_trans : forall (n m k : nat), less n m -> less m k -> less n k.
Proof.
  intros n m k P Q.
  destruct m.
  - exfalso. apply (less_zero P).
  - destruct k.
    exfalso; apply (less_zero Q).
    apply le_less in P.
    apply le_less in Q.
    pose proof (le_succ m) as H.
    pose proof ((le_trans P) H) as A.
    pose proof ((le_trans A) Q) as J.
    apply le_less in J.
    apply J.
Qed.

Theorem succ_neq : forall (n m k : nat), n <> 0 -> n + m = k -> m <> k.
Proof.
  intros n m k H P.
  pose proof (decidable_eq m k) as [Qeq | Qneq].
  - rewrite -[k]add_zero in P.
    rewrite add_comm in P.
    rewrite Qeq in P.
    apply add_elim in P.
    exfalso.
    apply (H P).
  - apply Qneq.
Qed.

Theorem less_ind : forall (n m : nat), less n (S m) -> less n m \/ n = m.
Proof.
  intros n m [Hle Hneq].
  apply le_ind in Hle.
  destruct Hle as [[k Hk] | Hle_eq].
  - destruct k.
    -- simpl in Hk. right. apply Hk.
    -- cut (S k <> 0). intro A.
       pose proof ((succ_neq A) Hk) as Q.
       left.
       split.
       * exists (S k). apply Hk.
       * apply Q.
       * auto.
  - exfalso. apply (Hneq Hle_eq).
Qed.

Theorem le_def : forall (n m : nat), le n m <-> less n m \/ n = m.
Proof.
  intros n m.
  split.
  intro P.
  apply le_less in P.
  apply less_ind.
  apply P.
  intro Q.
  destruct Q as [Qless | Qeq].
  - pose proof (less_succ m) as H.
    pose proof ((less_trans Qless) H) as K.
    apply le_less in K.
    apply K.
  - rewrite Qeq.
    apply (le_refl m).
Qed.


Theorem strong_ind : forall (P : nat -> Prop), (forall (n : nat), (forall (k : nat), less k n -> P k) -> P n) -> (forall (n : nat), P n).
Proof.
  intros P H n.
  cut (forall (m j : nat), le j m -> P j).
  * intro A.
    pose proof (le_refl n) as RefN.
    pose proof ((A n) n) as AN.
    apply (AN RefN).
  * intro m.
    induction m.

    ** intro j; intro Q.
       apply le_def in Q.
       destruct Q as [Qless | Qeq].
       - exfalso. apply (less_zero Qless).
       - cut (forall (k : nat), less k 0 -> P k).
         -- intro A.
            rewrite Qeq.
            apply ((H 0) A).
         -- intros k K. exfalso. apply (less_zero K).
    ** intros j LEJ.
       apply le_def in LEJ.
       destruct LEJ as [LEJ_less | LEJ_eq].
       - apply le_less in LEJ_less.
         apply ((IHm j) LEJ_less).
       - rewrite LEJ_eq.
         cut (forall (k : nat), less k (S m) -> P k).
         -- intro L.
            apply ((H (S m)) L).
         -- intros k K.
            apply le_less in K.
            apply le_def in K.
            destruct K as [K_less | K_eq].
            --- pose proof (less_succ m) as A.
                pose proof ((less_trans K_less) A) as K_le.
                apply le_less in K_le.
                apply ((IHm k) K_le).
            --- pose proof (le_refl m) as A.
                rewrite K_eq.
                apply ((IHm m) A).
Qed.

