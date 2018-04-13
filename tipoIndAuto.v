Definition and_bool (b1 b2 : bool) : bool :=
  match b1 , b2 with
    | true ,  b2 => b2
    | false , b2 => false
  end.

Lemma and_true_left : 
  forall b, and_bool true b = b.
Proof.
  induction b; auto.
Qed.

Lemma and_false_left : 
  forall b, and_bool false b = false.
Proof.
  auto.
Qed.

Lemma and_com : 
  forall b b', and_bool b b' = and_bool b' b.
Proof.
  induction b; induction b'; auto.
Qed.

Lemma and_assocc : 
  forall b1 b2 b3, and_bool b1 (and_bool b2 b3) = and_bool (and_bool b1 b2) b3.
Proof.
  induction b1; induction b2; induction b3; auto.
Qed.

Lemma zero_identity_add_right : 
  forall n, n + 0 = n.
Proof.
  induction n; simpl; try (rewrite IHn);reflexivity.
Qed.

Lemma add_inc : 
  forall m n, S (m + n) = m + S n.
Proof.
  induction m; intro n; simpl; try (rewrite IHm); reflexivity.
Qed.

Lemma add_commut : 
  forall n m, n + m = m + n.
Proof.
  induction n; intro m; simpl; 
  repeat ((rewrite IHn) || (apply add_inc)); 
  try (rewrite zero_identity_add_right); reflexivity.
Qed.

Lemma add_associative : 
  forall n m p, n + (m + p) = (n + m) + p.
Proof.
  induction n; intros m p; simpl; try (rewrite IHn); reflexivity.
Qed.

Lemma one_identity_times_right : 
  forall n, n * 1 = n.
Proof.
  induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Lemma one_identity_times_left : 
  forall n, 1 * n = n.
Proof.
  induction n; simpl; 
  try rewrite IHn; 
  try rewrite zero_identity_add_right; 
  reflexivity.
Qed.

Lemma add_mult_1 : 
  forall n m p, (n + m) * p = n * p + m * p.
Proof.
  induction n; intros m p; simpl; 
  try rewrite IHn; 
  try apply add_associative; 
  auto.
Qed.

Lemma times_associative : 
  forall n m p, (n * m) * p = n * (m * p).
Proof.
  induction n; intros m p; simpl;
  try rewrite <- IHn; 
  try apply add_mult_1; 
  reflexivity.
Qed.

Lemma add_1 : 
  forall n m p, n + (m + p) = m + (n + p).
Proof.
  induction n; simpl; intros m p;
  try rewrite IHn;
  try apply add_inc;
  auto.
Qed.

Lemma times_1 : 
  forall n m, n + n * m = n * S m.
Proof.
  induction n; simpl; intro m; 
  try rewrite <- IHn;
  try rewrite <- add_1; auto.
Qed.

Lemma times_commut : 
  forall n m, n * m = m * n.
Proof.
  induction n; intros m; simpl; 
  try rewrite IHn; 
  try apply times_1;
  auto.
Qed.

Fixpoint not_bool (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Lemma not_not_b :
  forall b, not_bool (not_bool b) = b.
Proof.
  intro b ;destruct b;auto.
Qed.

Fixpoint even_bool (n : nat) : bool :=
  match n with
    | 0 => true
    | S n => not_bool (even_bool n)
  end.

Lemma even_add_n :
  forall n, even_bool (n + n) = true.
Proof.
  induction n;
  simpl;
  try rewrite add_commut; 
  simpl;
  try rewrite IHn;
  auto.
Qed.

Fixpoint odd_bool (n : nat) : bool :=
  match n with
    | 0 => false
    | S n => not_bool (odd_bool n)
  end.

Lemma odd_add_n_n :
  forall n, odd_bool (n + n) = false.
Proof.
  induction n; simpl; auto;
  try rewrite add_commut; simpl;
  try rewrite IHn; auto.
Qed.

Lemma odd_add_n :
  forall n, odd_bool (n + S n) = true.
Proof.
  induction n;
  simpl;
  try rewrite add_commut;
  simpl;
  try rewrite odd_add_n_n;
  auto.
Qed.

Lemma even_SS : 
  forall n, even_bool n = even_bool (S (S n)).
Proof.
  induction n; simpl; 
  try rewrite not_not_b; auto.
Qed.

Lemma odd_SS :
  forall n, odd_bool n = odd_bool (S (S n)).
Proof.
  induction n; simpl; 
  try rewrite not_not_b; auto.
Qed.

Lemma even_bool_S:
  forall n, even_bool n = not_bool (even_bool (S n)).
Proof.
  induction n; simpl;
  try rewrite not_not_b; auto.
Qed.

Require Import List.

Lemma repeat_length {A : Type} : 
  forall (n : nat)(x : A), length (repeat x n) = n.
Proof.
  induction n; intros x; simpl; 
  try rewrite IHn;
  reflexivity.
Qed.

Lemma app_nil_right {A : Type} : 
  forall (xs : list A), xs ++ nil = xs.
Proof.
  induction xs; simpl;
  try rewrite IHxs;
  reflexivity.
Qed.

Lemma app_assoc {A : Type} : 
  forall (xs ys zs : list A), xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  induction xs; intros ys zs; simpl;
  try rewrite IHxs;
  reflexivity.
Qed.

Lemma map_app {A B : Type}{f : A -> B}
  : forall xs ys, map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  induction xs; intros; simpl;
  try rewrite IHxs;
  reflexivity.
Qed.

Lemma reverse_app {A : Type}
  : forall (xs ys : list A), rev (xs ++ ys) = rev ys ++ rev xs.
Proof.
  induction xs; intros; simpl;
  try rewrite app_nil_right;
  try rewrite IHxs;
  try rewrite app_assoc;
  reflexivity.
Qed.

Lemma reverse_inv {A : Type}
  : forall (xs : list A), rev (rev xs) = xs.
Proof.
  induction xs; simpl;
  try rewrite reverse_app;
  simpl;
  try rewrite IHxs;
  auto.
Qed.

Inductive even : nat -> Prop :=
| ev_zero : even 0
| ev_ss   : forall n, even n -> even (S (S n)).

Definition double (n : nat) := 2 * n.

Lemma double_2 :
  forall n, double n = n + n.
Proof.
  unfold double;
  induction n;
  simpl;
  try rewrite zero_identity_add_right;
  auto.
Qed.

Lemma double_even : 
  forall n, even (double n).
Proof.
  unfold double; induction n; simpl; 
  try rewrite IHn; 
  try apply ev_zero;
  try rewrite zero_identity_add_right;
  try rewrite add_commut;
  simpl;
  try rewrite <- double_2;
  unfold double;
  try apply ev_ss;
  auto.
Qed.

Lemma le_refl : 
  forall n, n <= n.
Proof.
  apply le_n.
Qed.

Lemma le_cong_S : 
  forall n m, n <= m -> S n <= S m.
Proof.
  intros;
  induction H;
  try apply le_refl;
  try apply le_S;
  auto.
Qed.

Lemma le_S_cong : 
  forall n m, S n <= S m -> n <= m.
Proof.
  intros;
  induction m;
  inversion H;
  try apply le_refl;
  try inversion H1;
  auto.
Qed.

Lemma le_trans : 
  forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  induction n; intros; try rewrite H; auto.
Qed.

Lemma le_zero_antisym_left :
  forall n, 0 <= n -> n <= 0 -> 0 = n.
Proof.
  induction n; intros; auto.
  inversion H0.
Qed.

Lemma le_antisym : 
  forall n m, n <= m -> m <= n -> n = m.
Proof.
  induction n; intros; 
  try apply le_zero_antisym_left;
  inversion H;
  subst; auto; subst;
  apply f_equal;
  apply IHn;
  apply le_S_cong;
  auto.
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
  repeat ((apply sorted_consn)||(apply sorted_cons1)||(apply le_n)||(apply le_S)).
Qed.

Reserved Notation "x '<<=' y" (at level 40, no associativity).

Inductive le_alt : nat -> nat -> Prop :=
| le_alt_zero : forall n, 0 <<= n
| le_alt_succ : forall n m, n <<= m -> S n <<= S m
where "x '<<=' y" := (le_alt x y).

Lemma le_alt_refl : 
  forall n, n <<= n.
Proof.
  induction n; 
  try apply le_alt_zero;
  try apply le_alt_succ;
  try apply IHn.
Qed.

Lemma le_alt_trans
  : forall n m p, n <<= m -> m <<= p -> n <<= p.
Proof.
  induction n; intros; try apply le_alt_zero;
  inversion H0;
  subst;
  inversion H;
  subst;
  apply le_alt_succ;
  apply (IHn n0 m0);
  inversion H;
  auto.
Qed.

Lemma le_alt_antisym : 
  forall n m, n <<= m -> m <<= n -> n = m.
Proof.
  induction n; intros.
  inversion H0; auto.
  inversion H;
  subst;
  apply f_equal;
  apply (IHn m0);
  inversion H0;
  auto.
Qed.

Lemma le_zero :
  forall n, 0 <= n.
Proof.
  induction n ; constructor ; try assumption.
Qed.

Lemma le_alt_equiv_le : 
  forall n m, n <<= m <-> n <= m.
Proof.
  induction n ; intros ; split ; intros; try apply le_zero; try constructor;
  destruct m;
  inversion H;
  subst;
  try apply le_alt_refl;
  try apply le_cong_S;
  try apply IHn in H2;
  try apply le_S_cong in H;
  try apply IHn in H;
  try constructor;
  auto.
Qed.


























