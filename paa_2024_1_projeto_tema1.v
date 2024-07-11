(** Projeto e Análise de Algoritmos - 2024-1 *)
(** Projeto em Coq - tema 1 *)
(** Provar a equivalência entre duas definições distintas da noção de permutação de listas de números naturais. *)

(* begin hide *)
Require Import Arith List Lia.
(* end hide *)

Inductive perm : list nat -> list nat -> Prop :=
| perm_refl: forall l, perm l l
| perm_ins: forall x l1 l2, perm l1 l2 -> perm (x::l1) (x::l2)
| perm_flip: forall x1 x2 l, perm (x1::x2::l) (x2::x1::l)
| perm_transit : forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Require Import Permutation.

Print Permutation.

Lemma perm_implies_Permutation: forall l1 l2, perm l1 l2 -> Permutation l1 l2.
Proof.
Admitted.

Lemma Permutation_implies_perm: forall l1 l2, Permutation l1 l2 -> perm l1 l2.
Proof.
Admitted.

Theorem perm_equiv_Permutation: forall l1 l2, perm l1 l2 <-> Permutation l1 l2.
Proof.  
Admitted.

Fixpoint num_oc x l := match l with
                       | nil => 0
                       | h :: tl => if (x =? h) then S(num_oc x tl) else (num_oc x tl)
                       end.

Definition perm' l1 l2 := forall x, num_oc x l1 = num_oc x l2.

Lemma perm_implies_perm': forall l1 l2, perm l1 l2 -> perm' l1 l2.
Proof.
Admitted.

Lemma perm'_implies_perm: forall l1 l2, perm' l1 l2 -> perm l1 l2.
Proof.
Admitted.
  
Theorem perm_equiv_perm': forall l1 l2, perm l1 l2 <-> perm' l1 l2.
Proof.
Admitted.

