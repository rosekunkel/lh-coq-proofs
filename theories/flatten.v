Require Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Import List.ListNotations.

Open Scope list_scope.

Inductive Tree : Type :=
| Leaf : Z -> Tree
| Node : Tree -> Tree -> Tree.

Fixpoint flatten (t : Tree) : list Z :=
  match t with
  | Leaf n => [n]
  | Node l r => flatten l ++ flatten r
  end.

Fixpoint flatten' (t : Tree) (ns : list Z) : list Z :=
  match t with
  | Leaf n => n::ns
  | Node l r => flatten' l (flatten' r ns)
  end.

Lemma flatten'_append : forall t ns,
    flatten' t ns = flatten t ++ ns.
Proof.
  induction t; intros; simpl.
  - reflexivity.
  - rewrite IHt1, IHt2. rewrite List.app_assoc. reflexivity.
Qed.

Theorem flatten_alt : forall t,
    flatten t = flatten' t [].
Proof.
  intros.
  rewrite flatten'_append. symmetry. apply List.app_nil_r.
Qed.