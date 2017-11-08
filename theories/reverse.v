Require Coq.Lists.List.
Require Import Coq.Program.Basics.
Import List.ListNotations.

Open Scope list_scope.

Section reverse.
  Variables A:Type.

  Lemma rev_append_rev : forall l l':list A,
      List.rev_append l l' = List.rev l ++ l'.
  Proof.
    induction l; intros; simpl.
    - reflexivity.
    - rewrite <- List.app_assoc. apply IHl.
  Qed.

  Theorem rev_alt : forall l:list A,
      List.rev l = List.rev_append l [].
  Proof.
    induction l.
    - reflexivity.
    - simpl. rewrite rev_append_rev. reflexivity.
  Qed.

  Lemma rev_fold_append : forall l l':list A,
      List.rev l ++ l' = List.fold_left (flip cons) l l'.
  Proof.
    induction l; intros; simpl.
    - reflexivity.
    - rewrite <- IHl. rewrite <- List.app_assoc. reflexivity.
  Qed.

  Theorem rev_fold_alt : forall l:list A,
      List.rev l = List.fold_left (flip cons) l [].
  Proof.
    intros.
    rewrite <- rev_fold_append. rewrite List.app_nil_r. reflexivity.
  Qed.
End reverse.