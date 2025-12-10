From Coq Require Import Lists.List.
Import ListNotations.

Ltac test := simpl; reflexivity.

Theorem t : forall (l1 l2 :list nat), length (l1 ++ l2) = length l1 + length l2.
Proof.
 intros.
    induction l1 as [|x l1 IHl1].
    - test.
    - simpl. rewrite IHl1. reflexivity.
Qed.
