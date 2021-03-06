(* Days of the week *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

(* Booleans *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

(* Exercise: 1 star (nandb) *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
    | false, false => true
    | false, _ => true
    | _, false => true
    | _, _ => false
  end.

Example test_nand1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nand2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nand3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nand4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
    | true, true, true => true
    | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* Function Types *)

Check true.
Check (negb true).
Check negb.

(* Numbers *)

Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n:nat) : nat :=
  match n with
      | O => O
      | S n' => n'
  end.

End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
      | O => true
      | S O => false
      | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power: nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(* Exercise: 1 star (factorial) *)

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S p => mult n (factorial p)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | O, S m' => false
    | S n', O => false
    | S n', S m' => beq_nat n' m'
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n, m with
    | O, _ => true
    | S n', O => false
    | S n', S m' => ble_nat n' m'
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

(* Exercise: 2 stars (blt_nat) *)

Definition blt_nat (n m : nat) : bool := (andb (ble_nat n m) (negb (beq_nat n m))).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.


(* Proof by Simplification *)

Theorem plus_O_n: forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l: forall (n:nat), 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l: forall (n:nat), 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(* Proof by Rewriting *)

Theorem plus_id_example : forall (n m : nat),
                            n = m ->
                            n + n = m + m.
  Proof.
    intros n m. (* move both quantifiers n, m into the context *)
    intros H. (* move the hypothesis, here called H, into the context *)
    rewrite -> H. (* rewrite the goal using the hypothesis *)
    reflexivity. Qed.

(* Exercise: 1 star (plus_id_exercise) *)

Theorem plus_id_exercise: forall (n m o : nat),
                            n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1. (* move the hypothesis, n = m, into a variable H1 into the context *)
  intros H2. (* move the hypothesis, m = o, into a variable H2 into the context *)
  rewrite -> H1. (* rewrite the goal using the first hypothesis *)
  rewrite -> H2. (* rewrite the goal using the second hypothesis *)
  reflexivity. Qed.
  
Theorem mult_O_plus: forall (n m : nat),
                       (O + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

(* Exercise: 2 stars (mult_S_1) *)

Theorem mult_S_1: forall (n m : nat),
                    m = S n ->
                    m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H. (* move the hypothesis, m = S n, into a variable H into the context *)
  rewrite -> plus_1_l. (* rewrite the goal based on the theorem plus_1_l *)
  rewrite -> H. (* rewrite the goal using the hypothesis m = S n *)
  reflexivity. Qed.
