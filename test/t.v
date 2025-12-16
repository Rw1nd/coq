From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Arith.PeanoNat.

Ltac test := simpl; reflexivity.

Theorem t : forall (l1 l2 :list nat), length (l1 ++ l2) = length l1 + length l2.
Proof.
 intros.
    induction l1 as [|x l1 IHl1].
    - apply length_app with (l := []) (l' := l2).
    - simpl. rewrite <- IHl1.  reflexivity.
Qed.


Theorem t2 : forall (l1 l2 :list nat), length (rev (l1 ++ l2)) = length l1 + length l2.
Proof.
    intros.
    induction l1 as [|x l1 IHl1].
    - apply length_rev. 
    - simpl. rewrite length_app. rewrite <- IHl1. simpl. rewrite  Nat.add_succ_r. auto.
Qed.
