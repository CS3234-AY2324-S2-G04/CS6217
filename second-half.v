(*
  Time-stamp: <2026-02-25 08:59:13 kim>
*)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Nat Arith List Bool.

(* Paraphernalia *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
    nil =>
    match v2s with
      nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
      nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Lemma fold_unfold_eqb_list_nil :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v2s : list V),
    eqb_list V eqb_V nil v2s =
    match v2s with
      nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Lemma fold_unfold_eqb_list_cons :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    eqb_list V eqb_V (v1 :: v1s') v2s =
    match v2s with
      nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Fixpoint list_fold_right (V W : Type) (n : W) (c : V -> W -> W) (vs : list V) : W :=
  match vs with
    nil =>
      n
  | v :: vs' =>
      c v (list_fold_right V W n c vs')
  end.

Lemma fold_unfold_list_fold_right_nil:
  forall (V W : Type)
         (n : W)
         (c : V -> W -> W),
    list_fold_right V W n c nil = n.
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_right_cons:
  forall (V W : Type)
         (n : W)
         (c : V -> W -> W)
         (v : V)
         (vs : list V),
    list_fold_right V W n c (v :: vs) = c v (list_fold_right V W n c vs).
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Fixpoint list_fold_left_acc (V W : Type) (c : V -> W -> W) (vs : list V) (a : W) : W :=
  match vs with
    nil =>
      a
  | v :: vs' =>
      list_fold_left_acc V W c vs' (c v a)
  end.

Lemma fold_unfold_list_fold_left_acc_nil:
  forall (V W : Type)
         (c : V -> W -> W)
         (a : W),
    list_fold_left_acc V W c nil a = a.
Proof.
  fold_unfold_tactic list_fold_left_acc.
Qed.

Lemma fold_unfold_list_fold_left_acc_cons:
  forall (V W : Type)
         (c : V -> W -> W)
         (v : V)
         (vs' : list V)
         (a : W),
    list_fold_left_acc V W c (v :: vs') a = list_fold_left_acc V W c vs' (c v a) .
Proof.
  fold_unfold_tactic list_fold_left_acc.
Qed.

Definition list_fold_left (V W : Type) (n : W) (c : V -> W -> W) (vs : list V) : W :=
  list_fold_left_acc V W c vs n.

(* *** *)

Check Nat.eqb.

Definition test_second_half (candidate : forall (V : Type), list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: 2 :: nil)) (2 :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: 2 :: 3 :: nil)) (3 :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: 2 :: 3 :: 4 :: nil)) (3 :: 4 :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: 2 :: 3 :: 4 :: 5:: nil)) (4 :: 5 :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: 2 :: 3 :: 4 :: 5:: nil)) (4 :: 5 :: nil)).

(*
  Using a slow pointer and a fast pointer.
  Here the slow pointer is going at 1x speed,
  and the fast pointer is going at 2x speed.
 *)

Definition second_half (V : Type) (vs : list V) : list V :=
  let fix visit fp sp :=
    match fp with
    | nil =>
        sp
    | f :: fp' =>
        match fp' with
        | nil =>
            match sp with
            | nil =>
                nil
            | s :: sp' =>
                sp'
            end
        | f' :: fp'' =>
            match sp with
            | nil =>
                nil
            | s :: sp' =>
                visit fp'' sp'
            end
        end
    end in visit vs vs.

Compute second_half nat (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil).


Theorem second_half_passes_its_unit_tests:
  test_second_half second_half = true.
Proof.
  compute.
  reflexivity.
Qed.

(* Use a boolean to program second_half so that there is only a nil case and a cons case *)

Check negb.

(*
  Using a slow pointer and a fast pointer.
  Here the slow pointer is going at 0.5x speed,
  and the fast pointer is going at 1x speed.
*)

Definition second_half_v2 (V : Type) (vs : list V) : list V :=
  let fix visit fp sp b :=
    match fp with
    | nil =>
        sp
    | f :: fp' =>
        match b with
        | true =>
            visit fp' sp (negb b)
        | false =>
            match sp with
            | nil =>
                nil
            | s :: sp' =>
                visit fp' sp' (negb b)
            end
        end
    end in visit vs vs false.

Compute second_half_v2 nat (1 :: nil).

Theorem second_half_v2_passes_its_unit_test:
  test_second_half second_half_v2 = true.
Proof.
  compute.
  reflexivity.
Qed.

Check list_fold_right.
Definition second_half_v3 (V : Type) (vs : list V) :=
  (snd (list_fold_right V (bool * (list V)) (false, vs) (fun v w => match w with
                                                              | (false, nil)
                                                                => (false, nil)
                                                              | (false, s :: sp')
                                                                => (true, sp')
                                                              | (true, sp)
                                                                => (false, sp)
                                                              end) vs)).

Theorem second_half_v3_passes_its_unit_test:
  test_second_half second_half_v3 = true.
Proof.
  compute.
  reflexivity.
Qed.

Definition second_half_v4 (V : Type) (vs : list V) :=
  (snd (list_fold_left V (bool * (list V)) (false, vs) (fun v w => match w with
                                                              | (false, nil)
                                                                => (false, nil)
                                                              | (false, s :: sp')
                                                                => (true, sp')
                                                              | (true, sp)
                                                                => (false, sp)
                                                              end) vs)).

Theorem second_half_v4_passes_its_unit_test:
  test_second_half second_half_v4 = true.
Proof.
  compute.
  reflexivity.
Qed.
