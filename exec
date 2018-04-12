Variables A B C : Prop.

Theorem first_theorem : (A-> B) -> A -> B.
Proof.
  intro Hab.
  intro Ha.
  apply Hab.
  assumption.
Qed.

Lemma ex1 : A -> B -> A.
Proof.
  intro Ha.
  intro hb.
  assumption.
Qed.

Lemma ex2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
  intro Hab.
  intro Hbc.
  intro Ha.
  apply Hbc.
  apply Hab.
  assumption.
Qed.


Lemma and_comm : A /\ B -> B /\ A.
Proof.
  intro Hab.
  destruct Hab as [Ha Hb].
  split.
  - assumption.
  - assumption.
Qed.

Lemma and_assoc : A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
 intro Habc.
 destruct Habc as [Ha [Hb Hc]].
 split.
 + split.
  * assumption.
  * assumption.
 + assumption.
Qed.

Lemma ex3 : (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  intro Habc.
  destruct Habc as [[Ha Hb] Hc].
  split.
  + assumption.
  + split.
    - assumption.
    - assumption.
Qed.

Lemma ex4 : ((A /\ B) -> C) -> (A -> B -> C).
Proof.
  intro Habic.
  intros Ha Hb.
  apply Habic.
  split.
  + assumption.
  + assumption.
Qed.

Lemma ex5 : (A -> B -> C) -> ((A /\ B) -> C).
Proof.
  intro Hiabc.
  intro Hab.
  destruct Hab as [Ha Hb].
  apply Hiabc.
  + assumption.
  + assumption.
Qed.

Lemma ex6 : ((A -> B) /\ (A -> C)) -> A -> (B /\ C).
Proof.
  intro Habac.
  intro Ha.
  destruct Habac as [Hab Hac].
  split.
  + apply Hab.
    assumption.
  + apply Hac.
    assumption.
Qed.

Lemma and_comm_iff : (A /\ B) <-> (B /\ A).
Proof.
  unfold iff.
  split.
  + apply and_comm.
  + intro Hba.
    destruct Hba as [Hb Ha].
    split.
    - assumption.
    - assumption.
Qed.

Lemma modus_tollens : ((A -> B) /\ ~ B) -> ~ A.
Proof.
    intro H.
    destruct H as [Hb Hnb].
    unfold not.
    unfold not in Hnb.
    intro Ha.
    apply Hnb.
    apply Hb.
    assumption.
Qed.

Lemma contra : A -> ~ A -> B.
Proof.
  intro Ha.
  intro Hna.
  contradiction.
Qed.

Lemma or_comm : (A \/ B) -> (B \/ A).
Proof.
  intro Hab.
  destruct Hab as [Ha | Hb].
  +
    right.
    assumption.
  +
    left.
    assumption.
Qed.

Lemma or_assoc : A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intro Habc.
  destruct Habc as [Ha | [Hb | Hc]].
  +
    left.
    left.
    assumption.
  +
    left.
    right.
    assumption.
  +
    right.
    assumption.
Qed.

Lemma ex7 : ((A \/ B) /\ ~ A) -> B.
Proof.
  intro Habna.
  destruct Habna as [Hab Hna].
  unfold not in Hna.
  destruct Hab as [Ha | Hb].
  + contradiction.
  + assumption.
Qed.

Lemma ex8 : (A \/ (B /\ C)) -> (A \/ B) /\ (A \/ C).
Proof.
  intro Habc.
  destruct Habc as [Ha | [Hb Hc]].
  split.
  +
    left.
    assumption.
  +
    left.
    assumption.
  +
    split.
    - right.
      assumption.
    - right.
      assumption.
Qed.

Hypothesis U : Set.
Hypothesis u : U.
Hypothesis P : U -> Prop.
Hypothesis Q : U -> Prop.
Hypothesis R : U -> Prop.

Lemma forall_and : (forall x : U, P x /\ Q x) -> ((forall x : U, P x) /\ (forall x : U, Q x)).
Proof.
  intro H.
  split.
  +
    intro y.
    destruct (H y).
    assumption.
  +
    intro y.
    destruct (H y).
    assumption.
Qed.

Lemma forall_modus_ponens : ((forall x : U, P x -> Q x) /\
                               (forall y : U, Q y -> R y)) ->
                              (forall z : U, P z -> R z).
Proof.
  intro Hpqr.
  destruct Hpqr as [Hpq Hqr].
  intro z.
  intro Hpz.
  apply Hqr.
  apply Hpq.
  assumption.
Qed.

Lemma ex_or : (exists x : U, P x \/ Q x) -> (exists x : U, P x) \/ (exists y : U, Q y).
Proof.
  intro Hpq.
  destruct Hpq as [x [Hpx | Hqx]].
  +
    left.
    exists x.
    assumption.
  +
    right.
    exists x.
    assumption.
Qed.

Lemma ex9 : forall x : U, P x -> exists y : U, P y.
Proof.
  intro z.
  intro Pz.
  exists z.
  assumption.
Qed.

Lemma ex10 : (forall x : U, P x -> ~ Q x) -> ~ exists y : U, P y /\ Q y.
Proof.
  intro H.
  unfold not.
  intro H1.
  destruct H1 as [y [Hp Hnq]].
  apply H in Hp.
  contradiction.
Qed.

Lemma ex11 : (forall x : U, P x -> Q x) -> (forall x : U, ~ Q x) -> (forall x : U, ~ P x).
Proof.
 intro H1.
 intro H2.
 intro y.
 unfold not.
 intro Py.
 apply H1 in Py.
 apply (H2 y).
 assumption.
Qed.