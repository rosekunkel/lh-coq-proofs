Require Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Import List.ListNotations.

Open Scope list_scope.
Open Scope Z_scope.

Inductive expr : Type :=
| EVal : Z -> expr
| EAdd : expr -> expr -> expr.

Fixpoint eval (e : expr) : Z :=
  match e with
  | EVal n => n
  | EAdd x y => eval x + eval y
  end.

Inductive op : Type :=
| OPush : Z -> op
| OAdd : op.

Definition stack := list Z.
Definition code := list op.

Fixpoint exec (c : code) (s : stack) : option stack :=
  match (c, s) with
  | ([], s) => Some s
  | (OPush n :: c', s) => exec c' (n :: s)
  | (OAdd :: c', (m :: n :: s)) => exec c' (n + m :: s)
  | _ => None
  end.

Fixpoint comp (e : expr) : code :=
  match e with
  | EVal n => [OPush n]
  | EAdd x y => comp x ++ comp y ++ [OAdd]
  end.

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
  | None => None
  | Some a' => f a'
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Lemma exec_append_dist : forall x y s,
    exec (x ++ y) s = exec x s >>= fun s' => exec y s'.
Proof.
  intros x.
  induction x as [|x xs  IHx]; simpl; intros y s.
  - destruct (exec y s); reflexivity.
  - destruct x as [n|].
    + apply IHx.
    + destruct s as [|m [|n s'']]; solve [reflexivity | apply IHx].
Qed.

Lemma comp_any_stack : forall s e,
    exec (comp e) s = Some (eval e :: s).
Proof.
  intros s e.
  generalize dependent s.
  induction e; intros s; simpl.
  - reflexivity.
  - rewrite exec_append_dist. rewrite IHe1. simpl.
    rewrite exec_append_dist. rewrite IHe2.
    reflexivity.
Qed.

Theorem comp_correct : forall e,
    exec (comp e) [] = Some [eval e].
Proof.
  apply (comp_any_stack []).
Qed.

Fixpoint comp' (e : expr) (c : code) : code :=
  match e with
  | EVal n => OPush n :: c
  | EAdd x y => comp' x (comp' y (OAdd :: c))
  end.

Lemma comp'_comp_append : forall e c,
    comp' e c = comp e ++ c.
Proof.
  induction e; intros c.
  - reflexivity.
  - simpl. rewrite IHe1, IHe2.
    fold ([OAdd] ++ c). rewrite !List.app_assoc.
    reflexivity.
Qed.

Theorem comp'_correct_general : forall c s e,
    exec (comp' e c) s = exec c (eval e :: s).
Proof.
  intros c s e.
  rewrite comp'_comp_append.
  rewrite exec_append_dist.
  rewrite comp_any_stack.
  reflexivity.
Qed.

Corollary comp'_correct : forall e,
    exec (comp' e []) [] = Some [eval e].
Proof.
  intros e.
  rewrite comp'_correct_general.
  reflexivity.
Qed.
