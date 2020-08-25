From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma add_succ : forall (n : nat) (m : nat), n + S m = S (n + m).
Proof.
  intros n m.
  induction n.

  simpl.
  trivial.

  simpl.
  rewrite IHn.
  trivial.
Qed.

Theorem add_comm : forall (n : nat) (m : nat), n + m = m + n.
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


Theorem add_assoc : forall (n : nat) (m : nat) (k : nat), n + (m + k) = (n + m) + k.
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

Theorem add_elim : forall (n : nat) (m : nat) (k : nat), (n + m = n + k) -> (m = k).
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

Theorem mult_succ : forall (n : nat) (m : nat), m + m * n = m * S n.
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

Theorem mult_comm : forall (n : nat) (m : nat), n * m = m * n.
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

Theorem mult_dist : forall (n : nat) (m : nat) (k : nat), n * (m + k) = n * m + n * k.
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

Theorem mult_assoc : forall (n : nat) (m : nat) (k : nat), n * (m * k) = (n * m) * k.
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

Theorem add_zpp : forall (n : nat) (m : nat), n + m = 0 -> n = 0 /\ m = 0.
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

Theorem mult_zpp : forall (n : nat) (m : nat), n * m = 0 -> n = 0 \/ m = 0.
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

