Inductive exp : Set :=
| Zero   : exp
| Succ   : exp -> exp
| T      : exp
| F      : exp
| Pred   : exp -> exp
| If     : exp -> exp -> exp -> exp
| IsZero : exp -> exp
| Plus   : exp -> exp -> exp
| And    : exp -> exp -> exp.

(*Exercicio 50*)
(*Adicionar operações de soma de números e conjunção de boleanos*)

Inductive bvalue : exp -> Prop :=
| btrue  : bvalue T
| bfalse : bvalue F.

Inductive nvalue : exp -> Prop :=
| nzero  : nvalue Zero
| nsucc  : forall n, nvalue n -> nvalue (Succ n).

Inductive value : exp -> Prop :=
| Bvalue : forall e, bvalue e -> value e
| Nvalue : forall e, nvalue e -> value e.

Hint Constructors bvalue nvalue value.

Reserved Notation "e '==>' e1" (at level 40).

Inductive step : exp -> exp -> Prop :=
| ST_If_T
  : forall e e', (If T e e') ==> e
| ST_If_F
  : forall e e', If F e e' ==> e'
| ST_If
  : forall e e' e1 e2,
    e ==> e'                ->
    If e e1 e2 ==> If e' e1 e2
| ST_Succ
  : forall e e',
    e ==> e'                ->
    (Succ e) ==> (Succ e')
| ST_Pred_Zero
  : Pred Zero ==> Zero
| ST_Pred_Succ
  : forall e,
    nvalue e         ->
    Pred (Succ e) ==> e
| ST_Pred
  : forall e e',
    e ==> e'           ->
    (Pred e) ==> (Pred e')
| ST_IsZeroZero
  : IsZero Zero ==> T
| ST_IsZeroSucc
  : forall e,
    nvalue e           ->
    IsZero (Succ e) ==> F
| ST_IsZero
  : forall e e',
    e ==> e'               -> 
    (IsZero e) ==> (IsZero e')
| St_PlusZero
  : forall e,
    nvalue e   ->
    Plus Zero e ==> e
| St_PlusSucc
  : forall e e1 n,
    (nvalue e) -> (nvalue e1) -> 
    e ==> e1 ->
    Plus e n ==> Succ (Plus e1 n)
| St_AndF
  : forall e,
    And F e ==> F
| ST_AndT
  : forall e,
    bvalue e   ->
    And T e ==> e
where "e '==>' e1" := (step e e1).
                        

Hint Constructors step.

Definition normal_form e := ~ exists e', step e e'.

Definition stuck e := normal_form e /\ ~ value e.

Ltac inverts H := inversion H ; clear H ; subst.

(*Exercicio 51*)
(*Terminar a provar*)

Lemma value_is_nf' : forall e, value e -> normal_form e.
Proof.
  intros e Hv.
  unfold normal_form.
  intro contra.
  induction e.
  +
    inverts contra.
    inverts H.
  +
    inverts contra.
    inverts Hv.
    inverts H0.
    inverts H0.
    apply IHe.
    auto.
    inverts H.
    exists e'.
    auto.
  +
    inverts contra.
    inverts H.
  +
    inverts contra.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
Qed.

Ltac s :=
      match goal with
      | [ H : ex _ |- _ ] => destruct H
      | [ H : Zero ==> _ |- _] => inverts H
      | [ H : T ==> _ |- _] => inverts H
      | [ H : F ==> _ |- _] => inverts H
      | [ H : value (Pred _) |- _] => inverts H
      | [ H : bvalue (Pred _) |- _] => inverts H
      | [ H : nvalue (Pred _) |- _] => inverts H
      | [ H : value (If _ _ _) |- _] => inverts H
      | [ H : bvalue (If _ _ _) |- _] => inverts H
      | [ H : nvalue (If _ _ _) |- _] => inverts H
      | [ H : value (IsZero _) |- _] => inverts H
      | [ H : bvalue (IsZero _) |- _] => inverts H
      | [ H : nvalue (IsZero _) |- _] => inverts H
      | [ H : value (Succ _) |- _] => inverts H
      | [ H : bvalue (Succ _) |- _] => inverts H
      | [ H : nvalue (Succ _) |- _] => inverts H
      | [ H : (Succ _) ==> _ |- _ ] => inverts H
      | [ H : value (Plus _ _) |- _] => inverts H
      | [ H : bvalue (Plus _ _) |- _] => inverts H
      | [ H : nvalue (Plus _ _) |- _] => inverts H
      | [ H : value (And _ _) |- _] => inverts H
      | [ H : bvalue (And _ _) |- _] => inverts H
      | [ H : nvalue (And _ _) |- _] => inverts H
      end.

Lemma value_is_nf : forall e, value e -> normal_form e.
Proof.
  unfold normal_form ; intros e H contra ; induction e ;
    try (repeat s) ; eauto.
Qed.

Hint Resolve value_is_nf.

(*Exercicio 52*)
(*Fazer LTac para o restante dos construtores*)

Ltac s1 :=
  match goal with
  | [ H : (nvalue ?e) , H1 : ?e ==> _ |- _] =>
    apply Nvalue in H ; apply value_is_nf in H ;
    unfold normal_form in H ; apply ex_intro in H1 ; contradiction
  end.

Lemma step_deterministic
  : forall e e', e ==> e' -> forall e1, e ==> e1-> e' = e1.
Proof.
  intros e e' H ; induction H ; intros e'' H' ;
    inverts H' ; f_equal ; try repeat s ; auto ; try repeat s1.
Qed.

Reserved Notation "e '==>>' e1" (at level 40).

Inductive big_step : exp -> exp -> Prop :=
| B_Value
  : forall v, value v -> v ==>> v
| B_If_True
  : forall e e1 e11 e2,
    e ==>> T ->
    e1 ==>> e11 ->
    (If e e1 e2) ==>> e11
| B_If_False
  : forall e e1 e2 e22,
    e ==>> F ->
    e2 ==>> e22 ->
    (If e e1 e2) ==>> e22
| B_Succ
  : forall e nv,
    nvalue nv ->
    e ==>> nv ->
    (Succ e) ==>> (Succ nv)
| B_PredZero
  : forall e,
    e ==>> Zero ->
    (Pred e) ==>> Zero
| B_PredSucc
  : forall e nv,
    nvalue nv ->
    e ==>> (Succ nv) ->
    Pred e ==>> nv
| B_IsZeroZero
  : forall e,
    e ==>> Zero ->
    (IsZero e) ==>> T
| B_IsZeroSucc
  : forall e nv,
    nvalue nv ->
    e ==>> (Succ nv) ->
    (IsZero e) ==>> F
| B_PlusZero
  : forall e1 e2 n,
    nvalue n -> e1 ==>> Zero ->
    e2 ==>> n ->
    Plus Zero e2 ==>> n
| B_PlusSucc
  : forall e1 e2 n1 n2,
    nvalue n1 -> e1 ==>> (Succ n1) ->
    nvalue n2 -> e2 ==>> n2 ->
    Plus e1 e2 ==>> Succ (Plus n1 n2)
| B_AndF
  : forall e1 e2,
    e1 ==>> F ->
    And e1 e2 ==>> F 
| B_AndT
  : forall e1 e2 b,
    bvalue b -> e1 ==>> T ->
    e2 ==>> b ->
    And e1 e2 ==>> b
where "e '==>>' e1" := (big_step e e1).

Hint Constructors big_step.

Ltac bs := match goal with
            | [H : T ==>> _ |- _] => inverts H
            | [H : F ==>> _ |- _] => inverts H 
            | [H : Zero ==>> _ |- _] => inverts H
            | [H : (Succ _) ==>> _ |- _] => inverts H
            | [H : value _ |- _] => inverts H
            | [H : bvalue (Succ _) |- _] => inverts H
            | [H : nvalue (Succ _) |- _] => inverts H
            | [H : (Pred _) ==>> _ |- _] => inverts H     
            | [H : bvalue (Pred _) |- _] => inverts H
            | [H : nvalue (Pred _) |- _] => inverts H
            | [H : (If _ _ _) ==>> _ |- _] => inverts H     
            | [H : bvalue (If _ _ _) |- _] => inverts H
            | [H : nvalue (If _ _ _) |- _] => inverts H
            | [H : (IsZero _) ==>> _ |- _] => inverts H     
            | [H : bvalue (IsZero _) |- _] => inverts H
            | [H : nvalue (IsZero _) |- _] => inverts H
            | [H : value (Pred _) |- _] => inverts H
            | [ IH : forall v, ?e ==>> v -> forall v', ?e ==>> v' -> _
                , H : ?e ==>> _, H1 : ?e ==>> _ |- _] =>
              apply (IH _ H) in H1
            end ; subst ; try congruence ; try f_equal ; auto.

Lemma big_step_value_succ : forall e, value (Succ e) -> nvalue e /\ e ==>> e.
Proof.
  induction e ; intros H ; inverts H ; split ; eauto ; repeat bs.
Qed.

Hint Resolve big_step_value_succ.

Ltac value_solver :=
  repeat (match goal with
          | [H : value (Pred _) |- _] => inverts H
          | [H : bvalue (Pred _) |- _] => inverts H
          | [H : nvalue (Pred _) |- _] => inverts H
          | [H : value (If _ _ _) |- _] => inverts H
          | [H : bvalue (If _ _ _) |- _] => inverts H
          | [H : nvalue (If _ _ _) |- _] => inverts H
          | [H : value (IsZero _) |- _] => inverts H
          | [H : bvalue (IsZero _) |- _] => inverts H
          | [H : nvalue (IsZero _) |- _] => inverts H
          | [H : value (Plus _ _) |- _] => inverts H
          | [H : nvalue (Plus _ _) |- _] => inverts H
          | [H : bvalue (Plus _ _) |- _] => inverts H
          | [H : value (And _ _) |- _] => inverts H
          | [H : nvalue (And _ _) |- _] => inverts H
          | [H : bvalue (And _ _) |- _] => inverts H
          | [H : Zero ==>> _ |- _] => inverts H
end).



Ltac big_step_solver :=
  match goal with
    | [H  : value (Succ _) |- _] => eapply big_step_value_succ in H; destruct H
    | [IH : forall v : exp, ?e ==>> v -> forall v': exp, ?e ==>> v' -> _,
       H1 : ?e ==>> _, 
       H2 : ?e ==>> _ |- _] => specialize (IH _ H1 _ H2) ; subst 
    | [ _ : _ |- Succ ?n = Succ ?n ] => auto
  
    | [H  : Zero = Succ _ |- _ ] => inverts H
    | [H  : Succ _ = Zero |- _ ] => inverts H
    | [H  : Succ ?v = Succ ?v' |- ?v = ?v'] => congruence
    | [H  : T = F |- _ ] => inverts H
    | [H  : F = T |- _ ] => inverts H
    | [H  : Succ _ = Succ _ |- _] => inverts H; auto
  end.

Lemma big_step_deterministic : forall e v, e ==>> v -> forall v', e ==>> v' -> v = v'.
Proof.
  induction e ; intros v H v' H' ; inverts H ; inverts H' ; value_solver ; eauto; repeat big_step_solver.
Qed.

Hint Resolve big_step_deterministic.

Reserved Notation "e '==>*' e1" (at level 40).

Inductive multi_step : exp -> exp -> Prop :=
| mstep_refl
  : forall e, e ==>* e
| mstep_step
  : forall e e1 e',
    e ==> e1   ->
    e1 ==>* e' ->
    e ==>* e'
where "e '==>*' e1" := (multi_step e e1).

Hint Constructors multi_step.
(*
Ltac multi_solver :=
  match goal with
    | [H : bvalue _ |- _] => inverts H; subst
    | [H : nvalue _ |- _] => inverts H; subst
    | [H : Zero ==>* _ |- _] => inverts H
    | [H : Zero ==> _ |- _] => inverts H
    | [_ : _ |- Zero ==>> Zero] => auto
  end.
*)
Lemma nvalue_step : forall e, nvalue e -> e ==>> e.
Proof.
  induction e; intros; auto.
Qed.
  
(*Exercicio 53*)
Lemma multi_step_big_step  : forall e v, value v -> e ==>* v -> e ==>> v.
Proof.
  induction e;  intros v Hv; inverts Hv; intros.
  inversion H; subst.
  inverts H0.
  inverts H1.
  inverts H0.
  inverts H1.
  inverts H0.
  auto.
  inverts H1.
Admitted.


(*Exercicio 54*)
Lemma big_step_mult_step  : forall e v, value v -> e ==>> v -> e ==>* v.
Proof.
Admitted.

Inductive type : Set :=
| TBool : type
| TNat  : type.

Reserved Notation "e '<<-' t" (at level 40).

Inductive has_type : exp -> type -> Prop :=
| T_True
  : T <<- TBool
| T_False
  : F <<- TBool
| T_Zero
  : Zero <<- TNat
| T_Succ
  : forall e,
    e <<- TNat ->
    (Succ e) <<- TNat
| T_Pred
  : forall e,
    e <<- TNat  ->
    (Pred e) <<- TNat
| T_If
  : forall e e' e'' t,
    e <<- TBool ->
    e' <<- t    ->
    e'' <<- t   ->
    (If e e' e'') <<- t
| T_IsZero
  : forall e,
    e <<- TNat ->
    (IsZero e) <<- TBool
where "e '<<-' t" := (has_type e t).

Ltac auxs :=
  match goal with
    | [H : T <<- TNat |- _] => inverts H
    | [H : F <<- TNat |- _] => inverts H
    | [H : Zero <<- TBool |- _] => inverts H
    | [H : Succ _ <<- TBool |- _] => inverts H
    | [H : Plus _ _ <<- TBool |- _] => inverts H
    | [H : And _ _ <<- TNat |- _] => inverts H 
  end.

(*Exercicio 55*)
Lemma bool_canonical : forall e, e <<- TBool -> value e -> bvalue e.
Proof.
  induction e; intros; repeat bs; repeat auxs; repeat value_solver.
Qed.

(*Exercicio 56*)
Lemma nat_canonical : forall e, e <<- TNat -> value e -> nvalue e. 
Proof.
  induction e; intros; repeat bs; repeat auxs; repeat value_solver.
Qed.

Theorem progress : forall e t, e <<- t -> value e \/ exists e', e ==> e'.
Proof.
  induction 1 ; try solve [left ; auto] ;
    try repeat (match goal with
                | [H : _ \/ _ |- _] => destruct H
                | [H : ex _ |- _] => destruct H
                | [H : value _ |- _] => inverts H
                | [H : bvalue _ |- _] => inverts H
                | [H : T <<- _ |- _] => inverts H
                | [H : F <<- _ |- _] => inverts H
                | [H : nvalue _ |- context[(Pred _)]] => inverts H
                | [H : nvalue _ |- context[(IsZero _)]] => inverts H
                | [H : ?e <<- TBool , H1 : nvalue ?e |- _] =>
                  inverts H1 ; inverts H
                end ; try solve [ right ; eexists ; eauto ] ; auto).
Qed.

Theorem preservation : forall e t, e <<- t -> forall e', e ==> e' -> e' <<- t.
Proof.
  induction e ; intros t He e' He' ; inverts He ; inverts He' ; repeat s ; eauto.
  +
    inverts H1 ; eauto.
    inverts H0 ; eauto.
Qed.

Theorem has_type_det : forall e t, e <<- t -> forall t', e <<- t' -> t = t'.
Proof.
  induction 1 ; intros t' Hc ; inverts Hc ; eauto.
Qed.

Lemma mult_big :
  forall e, e <<- t -> forall v, value v -> e ==>* v -> e ==>> v.
