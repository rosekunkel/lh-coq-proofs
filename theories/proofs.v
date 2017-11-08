Require Coq.Lists.List.
Require Import Coq.omega.Omega.
Import List.ListNotations.

(* We need this to use list notation. *)
Open Scope list_scope.

Theorem add_0_r : forall n,
    n + 0 = n.
Proof.
  intros. omega.
Qed.

Theorem add_assoc : forall x y z,
    x + (y + z) = (x + y) + z.
Proof.
  intros. omega.
Qed.

Section lists.
  Variable A:Type.

  Theorem rev_singleton_id : forall x:A,
      List.rev [x] = [x].
  Proof.
    reflexivity.
  Qed.

  Theorem repeat_length : forall (x:A) n,
      length (List.repeat x n) = n.
  Proof.
    induction n.
    - reflexivity.
    - simpl. f_equal. assumption.
  Qed.

  Theorem app_nil_r : forall l:list A,
      l ++ [] = l.
  Proof.
    induction l.
    - reflexivity.
    - simpl. f_equal. assumption.
  Qed.

  Theorem app_assoc : forall x y z:list A,
      x ++ (y ++ z) = (x ++ y) ++ z.
  Proof.
    induction x; intros; simpl.
    - reflexivity.
    - f_equal. trivial.
  Qed.

  Theorem rev_app_distr : forall x y:list A,
      List.rev (x ++ y) = (List.rev y) ++ (List.rev x).
  Proof.
    induction x; intros; simpl.
    - symmetry. apply app_nil_r.
    - rewrite IHx. symmetry. apply app_assoc.
  Qed.

  Theorem rev_involutive : forall l:list A,
      List.rev (List.rev l) = l.
  Proof.
    induction l.
    - reflexivity.
    - simpl. rewrite rev_app_distr. simpl. f_equal. assumption.
  Qed.
End lists.
