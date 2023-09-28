Inductive Nat : Type :=
| O : Nat
| S : Nat -> Nat.

Fixpoint add (n m : Nat) : Nat :=
  match n with 
  | O => m
  | S n' => S(add n' m)
end.

Eval compute in add O(S O).

Fixpoint add_r (n m : Nat) : Nat :=
  match m with 
  | O => n
  | S m' => S(add_r n m')
end.

(* 0 + n = n *)

Lemma add_O_l : forall m: Nat, add O m = m.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.



(* n + 0 = n *)


Lemma add_O_r : forall n: Nat, add n O = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. 
    reflexivity.
Qed.

Lemma add_m_Sn : forall n m , add n(S m) = S (add n m).
Proof.
  induction n.
  - intros m. simpl.
    reflexivity.
  - intros m. simpl.  
    rewrite IHn.
    reflexivity.
Qed.

Lemma add_com : forall n m : Nat, add n m = add m n.
Proof. 
  induction n.
  - intros m. simpl.
  symmetry.
  rewrite add_O_r.
  reflexivity.
  - intros m. simpl.
    rewrite add_m_Sn, IHn.
    reflexivity.
Qed.
    
  
   




