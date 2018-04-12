Inductive True1 : Prop :=
  | tt1 : True1.

Inductive False1 : Prop := .

Inductive conj1 (A B : Prop) : Prop :=
  | and1 : A -> B -> conj1 A B.

Inductive disj1 (A B : Prop) : Prop :=
  | or1 : A -> B -> disj1 A B.

Inductive bool1 : Set :=
  | true1  : bool1
  | false1 : bool1.

Require Import Bool.

Definition  not_bool (b : bool) : bool :=
  match b with
    | false => true
    | true => false
  end.

Definition and_bool (b1 b2 : bool) : bool := 
  match b1 , b2 with
    | true , b2  => b2
    | false , b2 => false
  end.

Definition or_bool (b1 b2 : bool) : bool :=
  match b1 , b2 with
    | true  , b2 => true
    | false , b2 => false
  end.

Definition xor_bool (b1 b2 : bool) : bool :=
  match b1 , b2 with
    | true , false => true
    | false , true => true
    | b1 , b2 => false
  end.

Eval compute in not_bool false.

Eval compute in xor_bool false true.

Lemma not_bool_inv : forall b : bool, not_bool (not_bool b) = b.
  Proof.
    intro b.
    destruct b.
    +
      simpl.
      reflexivity.
    +
      simpl.
      reflexivity.
  Qed.

Lemma and_true_left : forall b, and_bool true b = b.
  Proof.
  intro b.
  destruct b.
  +
    simpl.
    reflexivity.
  +
    simpl.
    reflexivity.
  Qed.

Lemma and_false_left : forall b, and_bool false b = false.
  Proof.
  intro b.
  destruct b.
  +
    simpl.
    reflexivity.
  +
    simpl.
    reflexivity.
  Qed.

Lemma and_com : forall b b', and_bool b b' = and_bool b' b.
  Proof.
  intros b b'.
  destruct b.
  +
    destruct b'.
    - 
      simpl.
      reflexivity.
    -
      simpl.
      reflexivity.
  +
    destruct b'.
    - 
      simpl.
      reflexivity.
    -
      simpl.
      reflexivity.
  Qed.

Lemma and_assocc : forall b1 b2 b3, and_bool b1 (and_bool b2 b3) = and_bool (and_bool b1 b2) b3.
  Proof.
  intros b1 b2 b3.
  destruct b1.
  +
    destruct b2.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
  +
    destruct b2.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
  Qed.
(* 
Inductive nat1 : Set :=
| O : nat1
| S : nat1 -> nat1.

Fixpoint add (n m : nat) : nat :=
  match n with
    | O    => m
    | S n' => S (add n' m)
  end. *)
(* 
Eval compute in add 1 1. *)
(* 
Notation "n ':+:' m" := (add n m)(at level 40, left associativity). *)

Lemma zero_identity_add_left : forall n, 0 + n = n.
Proof.
    intro n.
    simpl.
    reflexivity.
Qed.

Lemma zero_identity_add_right : forall n, n + O = n.
  Proof.
    intro n.
    induction n as [ | n' IHn'].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite IHn'.
      reflexivity.
  Qed.

Lemma add_inc : forall m n, S (m + n) = m + S n.
  Proof.
    intros m n.
    induction m as [ | m' IHm'].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite IHm'.
      reflexivity.
  Qed.

Lemma add_commut : forall n m, n + m = m + n.
  Proof.
    intros n m.
    induction n as [| n' IHn'].
    +
      simpl.
      symmetry.
      apply zero_identity_add_right.
    +
      simpl.
      rewrite IHn'. (* nessa versão tem que fazer algumas correcoes*)
      apply add_inc.
  Qed.

Lemma add_associative : forall n m p, n + (m + p) = (n + m) + p.
    Proof.
      intros n m p.
      induction n as [| n' IHn'].
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite IHn'.
        reflexivity.
    Qed.

(*
Fixpoint times (n m : nat) : nat :=
      match n with
      | 0    => 0
      | S n' => m + (times n' m)
      end.
*)

Lemma one_identity_times_right : forall n, n * 1 = n.
  Proof.
    intro n.
    induction n as [| n' Ihn'].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite Ihn'.
      reflexivity.
  Qed.


Lemma one_identity_times_left : forall n, 1 * n = n.
  Proof.
    intro n.
    induction n as [| n' Ihn'].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite zero_identity_add_right.
      reflexivity.
  Qed.

Lemma zero_times_left : forall n, 0 * n = 0.
  Proof.
    intro n.
    simpl.
    reflexivity.
  Qed.

Lemma zero_times_right : forall n, n * 0 = 0.
  Proof.
    intro n.
    induction n as [|n' Ihn'].
    +
      reflexivity.
    +
      simpl.
      apply Ihn'.
  Qed.

Lemma add_mult_1 : forall n m p, (n + m) * p = n * p + m * p.
  Proof.
    intro n.
    induction n as [| n' Ihn].
    +
      intros m p.
      simpl.
      reflexivity.
    +
      simpl.
      intros m p.
      rewrite Ihn.
      apply add_associative.
  Qed.


Lemma times_associative : forall n m p, (n * m) * p = n * (m * p).
  Proof.
    intros n.
    induction n as  [| n' Ihn'].
    +
      simpl.
      intros m p.
      reflexivity.
    +
      simpl.
      intros m p.
      rewrite <- Ihn'.
      apply add_mult_1.
  Qed.

Lemma add_1 : forall n m p, n + (m + p) = m + (n + p).
  Proof.
    intro n.
    induction n as [|n' Ihn].
    +
      simpl.
      reflexivity.
    +
      intros m p.
      simpl.
      rewrite Ihn.
      rewrite add_inc.
      reflexivity.
  Qed.

Lemma times_1 : forall n m, n + n * m = n * S m.
  Proof.
    intro n.
    induction n as [| n' Ihn].
    +
      simpl.
      intro m.
      reflexivity.
    +
      simpl.
      intro m.
      rewrite <- Ihn.
      rewrite add_1.
(*       assert (n' + (m + n' * m) = m + (n' + n' * m)).
        admit. 
      rewrite H. *)
      reflexivity.
  Qed.

Lemma times_commut : forall n m, n * m = m * n.
  Proof.
    intros n.
    induction n as [| n' Ihn'].
    +
      simpl.
      intro m.
      rewrite zero_times_right.
      reflexivity.
    +
      simpl.
      intro m.
      rewrite Ihn'.
      apply times_1.
  Qed.


Fixpoint even_bool (n : nat) : bool :=
  match n with
    | 0 => true
    | S n => not_bool (even_bool n)
  end.

Lemma even_add_n : forall n, even_bool (n + n) = true.
  Proof.
    intro n.
    induction n as [|n' Ihn].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite add_commut.
      simpl.
      rewrite Ihn.
      simpl.
      reflexivity.
  Qed.

Fixpoint odd_bool (n: nat) : bool :=
  match n with
    | 0 => false
    | S n => not_bool (odd_bool n)
  end.

Lemma odd_add_n_n : forall n, odd_bool (n + n) = false.
  Proof.
    intro n.
    induction n as [|n' Ihn].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite add_commut.
      simpl.
      rewrite Ihn.
      simpl.
      reflexivity.
  Qed.

Lemma odd_add_n_Sn : forall n, odd_bool (n + S n) = true.
  Proof.
    intro n.
    induction n as [|n' Ihn].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite add_commut.
      simpl.
      rewrite odd_add_n_n.
      simpl.
      reflexivity.
  Qed.

Lemma even_SS : forall n, even_bool n = even_bool (S (S n)).
  Proof.
    intro n.
    induction n as [| n' Ihn].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite not_bool_inv.
      reflexivity.
  Qed.

Lemma odd_SS : forall n, odd_bool n = odd_bool (S (S n)).
  Proof.
    intro n.
    induction n as [| n' Ihn].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite not_bool_inv.
      reflexivity.
  Qed.

Lemma even_bool_S : forall n, even_bool n = not_bool (even_bool (S n)).
  Proof.
    intro n.
    induction n as [| n' Ihn].
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite not_bool_inv.
      reflexivity.
  Qed.

Lemma length_app
      : forall {A : Type}(xs ys : list A), length (xs ++ ys) = length xs + length ys.
    Proof.
      intros A xs ys.
      induction xs as [| z zs IHzs].
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite IHzs.
        reflexivity.
    Qed.

Lemma length_app_1
      : forall {A : Type}(xs ys : list A), length (xs ++ ys) = length xs + length ys.
    Proof.
      intros A xs ys.
      induction xs as [| z zs IHzs].
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite IHzs.
        reflexivity.
    Qed.

(*necessario para o restante dos exercicios.*)
Require Import List.

Lemma map_length {A B : Type}{f : A -> B} : forall xs, length (map f xs) = length xs.
    Proof.
      intros xs.
      induction xs as [ | y ys IHys].
      +
        reflexivity.
      +
        simpl.
        rewrite IHys.
        reflexivity.
    Qed.

(*reverse => rev*)
Lemma reverse_length {A : Type}: forall (xs : list A), length xs = length (rev xs).
    Proof.
      intros xs.
      induction xs.
      +
        reflexivity.
      +
        simpl.
        rewrite length_app, add_commut.
        rewrite IHxs.
        reflexivity.
    Qed.

(*reapeat esta com seus parametro trocados.*)
Lemma repeat_length {A : Type} : forall (n : nat)(x : A), length (repeat x n) = n. 
    Proof.
      intro n.
      induction n.
      +
        simpl.
        intro x.
        reflexivity.
      +
        intro x.
        simpl.
        rewrite IHn.
        reflexivity.
    Qed.

(*[] => nil - verificar depois*)
Lemma app_nil_right {A : Type} : forall (xs : list A), xs ++ nil = xs.
    Proof.
    intro xs.
    induction xs.
    +
      simpl.
      reflexivity.
    +
      simpl.
      rewrite IHxs.
      reflexivity.
   Qed.

Lemma app_assoc {A : Type} : 
  forall (xs ys zs : list A), xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
    Proof.
      intros xs.
      induction xs.
      +
        simpl.
        reflexivity.
      +
        simpl.
        intros ys zs.
        rewrite IHxs.
        reflexivity.
    Qed.

Lemma map_app {A B : Type}{f : A -> B}
      : forall xs ys, map f (xs ++ ys) = map f xs ++ map f ys.
    Proof.
      intro xs.
      induction xs.
      +
        simpl.
        reflexivity.
      +
        intro ys.
        simpl.
        rewrite IHxs.
        reflexivity.
    Qed.

(*reverse => rev*)

Lemma reverse_app {A : Type}
      : forall (xs ys : list A), rev (xs ++ ys) = rev ys ++ rev xs.
    Proof.
      intros xs.
      induction xs.
      +
        simpl.
        intro ys.
        rewrite app_nil_right.
        reflexivity.
      +
        intro ys.
        simpl.
        rewrite IHxs.
        rewrite app_assoc.
        reflexivity.
   Qed.

Lemma reverse_inv {A : Type}
      : forall (xs : list A), rev (rev xs) = xs.
    Proof.
      intro xs.
      induction xs.
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite reverse_app.
        simpl.
        rewrite IHxs.
        reflexivity.
    Qed.

Inductive even : nat -> Prop :=
| ev_zero : even 0
| ev_ss   : forall n, even n -> even (S (S n)).

Definition double (n : nat) := 2 * n.

Lemma double_n : 
  forall n, n + n = 2 * n.
    Proof.
      intro n.
      induction n.
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite zero_identity_add_right.
        reflexivity.
    Qed.

Lemma double_even : 
  forall n, even (double n).
    Proof.
      unfold double.
      intro n.
      induction n.
      +
        simpl.
        apply ev_zero.
      +
        simpl.
        rewrite zero_identity_add_right.
        rewrite add_commut.
        simpl.
        rewrite double_n.
        apply ev_ss.
        apply IHn.
    Qed.

Example teste_le : 3 <= 6.
    Proof.
      apply le_S.
      apply le_S.
      apply le_S.
      apply le_n.
    Qed.

Example teste_le_false : 2 <= 1 -> 1 + 1 = 10.
    Proof.
      intros H.
      inversion H.
      inversion H1.
    Qed.

Lemma le_0_n : forall n, 0 <= n.
    Proof.
      intros n.
      induction n as [| n' IHn'].
      +
        apply le_n.
      +
        apply le_S.
        assumption.
    Qed.

Lemma le_refl : forall n, n <= n.
  Proof.
    intro n.
    induction n.
    +
      apply le_n.
    +
      apply le_n.
  Qed.

Lemma le_cong_S : forall n m, n <= m -> S n <= S m.
  Proof.
    intros n m Hnm.
    induction Hnm.
    +
      apply le_refl.
    +
      apply le_S.
      assumption.
  Qed.

(*não entendi essa prova.*)
Lemma le_S_cong : forall n m, S n <= S m -> n <= m.
  Proof.
    intros n m.
    induction m as [| m' IHm'].
    +
      intros Hnm.
      inversion Hnm.
      -
        apply le_refl.
      -
        inversion H0.
    +
      intros Hnm.
      inversion Hnm.
      -
        subst.
        apply le_refl.
      -
        subst.
        apply le_S.
        apply IHm'.
        assumption.
  Qed.

Lemma le_n_sm :
  forall n m, n <= m -> n <= S m.
    Proof.
      intro n.
      induction n.
      -
        intro m.
        intro H0m.
        apply le_S.
        apply H0m.
     -
        intro m.
        intro Hsmn.
        apply le_S.
        apply Hsmn.
    Qed.

Lemma le_trans : 
  forall n m p, n <= m -> m <= p -> n <= p.
    Proof.
      intro n.
      induction n.
      +
        intros m p.
        intro H0m.
        intro Hmp.
        rewrite H0m.
        apply Hmp.
      +
        intros m p.
        intro Hsnm.
        intro Hmp.
        rewrite Hsnm.
        apply Hmp.
    Qed.

Lemma eq_zero_right :
  forall n, n = 0 -> 0 = n.
    Proof.
      intro n.
      induction n.
      +
        intro H00.
        assumption.
      +
        intro Hsn0.
        inversion Hsn0.
    Qed.

Lemma eq_zero_left :
  forall n, 0 = n -> n = 0.
    Proof.
      intro n.
      induction n.
      +
        intro H00.
        assumption.
      +
        intro Hsn0.
        inversion Hsn0.
    Qed.


Lemma le_zero_antisym_right :
  forall n, n <= 0 -> 0 <= n -> n = 0.
    Proof.
      intro n.
      induction n.
      +
        intro H001.
        intro H002.
        apply eq_refl.
      +
        intro Hsn0.
        intro H0sn.
        inversion Hsn0.
   Qed.

Lemma le_zero_antisym_left :
  forall n, 0 <= n -> n <= 0 -> 0 = n.
    Proof.
      intro n.
      induction n.
      +
        intro H001.
        intro H002.
        apply eq_refl.
      +
        intro H0sn.
        intro Hsn0.
        inversion Hsn0.
    Qed.

Lemma le_s_inject : forall n m, S n <= S m -> n <= m.
  Proof.
    intros n m.
    generalize dependent n.
    induction m.
    +
      intros n H.
      inversion H.
      -
        apply le_n.
      -
        inversion H1.
    +
      intro n.
      intro H.
      inversion H.
      -
        apply le_n.
      -
        apply IHm in H1.
        apply le_S.
        assumption.
    Qed.

Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
  Proof.
    intro n.
    induction n.
    intro m.
    +
      apply le_zero_antisym_left.
    +
      intro p.
      intro Hsnp.
      intro Hpsn.
      inversion Hsnp.
      -
        reflexivity.
      -
        f_equal.
        apply IHn.
        *
          rewrite <- H0 in Hsnp.
          apply le_s_inject.
          assumption.
        *
          rewrite <- H0 in Hsnp, Hpsn.
          apply le_s_inject.
          assumption.
  Qed.

Import ListNotations.

Inductive Sorted : list nat -> Prop :=
  | sorted_nil : Sorted []
  | sorted_cons1 a : Sorted [a]
  | sorted_consn a b l : Sorted (b :: l) -> a <= b -> Sorted (a :: b :: l) .


Example test_sorted1 : Sorted [].
  Proof.
    apply sorted_nil.
  Qed.

Example test_sorted2 : Sorted [10].
  Proof.
    apply sorted_cons1.
  Qed.

Example test_sorted3 : Sorted [1 ; 3 ; 5 ].
  Proof.
    apply sorted_consn.
    +
      apply sorted_consn.
      -
        apply sorted_cons1.
      -
        apply le_S.
        apply le_S.
        apply le_n.
    +
      apply le_S.
      apply le_S.
      apply le_n.
  Qed.

Reserved Notation "x '<<=' y" (at level 40, no associativity).

Inductive le_alt : nat -> nat -> Prop :=
| le_alt_zero : forall n, 0 <<= n
| le_alt_succ : forall n m, n <<= m -> S n <<= S m
where "x '<<=' y" := (le_alt x y).

 Lemma le_alt_refl : forall n, n <<= n.
    Proof.
      intro n.
      induction n.
      +
        apply le_alt_zero.
      +
        apply le_alt_succ.
        apply IHn.
    Qed.

Lemma le_alt_trans
      : forall n m p, n <<= m -> m <<= p -> n <<= p.
    Proof.
      induction n; intros m p H1 H2.
      +
        apply le_alt_zero.
      +
        inversion H2.
        -
          subst.
          inversion H1.
        -
          subst.
          apply le_alt_succ.
          apply (IHn n0 m0).
          *
            inversion H1.
            assumption.
          *
            assumption.
    Qed.

Lemma le_alt_antisymm : 
  forall n m, S n <<= S m -> n <<= m.
  Proof.
    induction n ; intros m H.
    +
      apply le_alt_zero.
    +
      inversion H.
      subst.
      assumption.
  Qed.

Lemma le_alt_antisym : 
  forall n m, n <<= m -> m <<= n -> n = m.
    Proof.
      induction n ; intros m H1 H2.
      +
        inversion H2.
        apply eq_refl.
      +
        inversion H1.
        subst.
        f_equal.
        apply (IHn m0).
        -
          inversion H1.
          assumption.
        -
          inversion H2.
          assumption.
    Qed.
Lemma le_zero :
  forall n, 0 <= n.
    Proof.
    induction n ; constructor ; try assumption.
  Qed.

Lemma le_alt_equiv_le : 
  forall n m, n <<= m <-> n <= m.
    Proof.
      induction n ; intros ; split ; intros.
      +
        apply le_zero.
      +
       constructor.
      +
        destruct m.
        -
          inversion H.
        -
          apply le_cong_S.
          inversion H.
          apply IHn in H2.
          assumption.
      +
        destruct m.
        -
          inversion H.
        -
          apply le_S_cong in H.
          constructor.
          apply IHn in H.
          assumption.
    Qed.