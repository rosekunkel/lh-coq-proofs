Require Coq.Lists.List.
Import List.ListNotations.

Open Scope list_scope.

Section replicate.
  Variable A : Type.

  Theorem repeat_length : forall (x : A) n,
      length (List.repeat x n) = n.
  Proof.
    induction n.
    - reflexivity.
    - simpl. f_equal. assumption.
  Qed.
End replicate.
