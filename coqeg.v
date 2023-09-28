Inductive bool :=
  | true
  | false.

Definition notgate (x : bool) : bool :=
  match x with
  | true => false
  | false => true
  end.

Eval compute in notgate(true).

Theorem not1 : forall (x : bool), notgate(notgate x) = x.
Proof.
  intros x.
  destruct x.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.

Theorem not2 : forall (x : bool), notgate(notgate(notgate x)) = notgate x.
Proof.
  intros x.
  destruct x.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.

Definition andgate (x1 x2 : bool) : bool :=
  match x1, x2 with
  | true, true => true
  | _, _ => false
end.

Theorem andgateotherway : forall (x1 x2 : bool),
  andgate x1 x2 = true -> x1 = true /\ x2 = true.
Proof.
  intros x1 x2 Hb.
  destruct x1.
  destruct x2.
  split. reflexivity. reflexivity.
  split. reflexivity.
  simpl in Hb.
  inversion Hb.
  destruct x2.
  split.
  simpl in Hb.
  inversion Hb.
  reflexivity.
  simpl in Hb.
  inversion Hb.
Qed.


Theorem and_assoc : forall(a b c : bool),
  andgate a (andgate b c) = andgate (andgate a b) c.
Proof.
  intros a b c.
  destruct a.
  destruct b.
  destruct c.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + destruct c.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
  + destruct b.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
Qed.

(* shortened proof of the above theorem *)

Theorem and_assoc_short : forall(a b c : bool),
  andgate a (andgate b c) = andgate (andgate a b) c.
Proof.
  intros [|] [|] [|] ; simpl ; reflexivity.
Qed.

Theorem and_commu : forall a b, andgate a b = andgate b a.
Proof.
  intros a b.
  destruct a.
  + destruct b. simpl. reflexivity.
  simpl. reflexivity.
  + destruct b.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
Qed.
  

Definition orgate (x1 x2 : bool) : bool :=
  match x1, x2 with 
  | false, false => false
  | _, _ => true
end.

Theorem andnotor : forall (a b : bool),
 notgate(andgate a b) = orgate (notgate a) (notgate b).
Proof.
  intros a b.
  destruct a.
  + destruct b. simpl. reflexivity. 
  simpl. reflexivity.
  + destruct b. simpl. reflexivity.
  simpl. reflexivity.
Qed.









