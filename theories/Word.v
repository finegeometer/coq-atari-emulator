From Coq Require Import ssreflect ssrbool Arith.PeanoNat PropExtensionality.
Import EqNotations.

Inductive word : nat -> Type :=
| trivial : word 0
| push_low {n} : bool * word n -> word (S n)
.

Definition destruct_word {n} (w : word n) :
  match n return _ -> Type with
  | 0 => fun w => w = trivial
  | S n => fun w => { w' : bool * word n | push_low w' = w }
  end w :=
  match w with
  | trivial => eq_refl
  | push_low bw => exist _ bw eq_refl
  end.

Definition word0 : forall w, w = trivial := destruct_word.

Definition pop_low {n} (w : word (S n)) : bool * word n
  := proj1_sig (destruct_word w).

Definition push_pop_low {n} (w : word (S n))
  : push_low (pop_low w) = w
  := proj2_sig (destruct_word w).

Definition pop_push_low {n} (bw : bool * word n)
  : pop_low (push_low bw) = bw
  := eq_refl.



Definition word1_of_bit (b : bool) : word 1 := push_low (b, trivial).
Definition bit_of_word1 (w : word 1) : bool := fst (pop_low w).

Theorem bit_of_word1_of_bit b : bit_of_word1 (word1_of_bit b) = b.
Proof.
  done.
Qed.

Theorem word1_of_bit_of_word1 w : word1_of_bit (bit_of_word1 w) = w.
Proof.
  rewrite -(push_pop_low w).
  move: (pop_low w) => [lo w'].
  rewrite (word0 w').
  done.
Qed.



Fixpoint push_high {n} : word n * bool -> word (S n) :=
  match n with
  | 0 => fun '(_, b) => push_low (b, trivial)
  | S n => fun '(w, hi) => 
      let '(lo, w) := pop_low w in
      push_low (lo, push_high (w, hi))
  end.

Fixpoint pop_high {n} : word (S n) -> word n * bool :=
  match n with
  | 0 => fun w =>
      let '(b, _) := pop_low w in
      (trivial, b)
  | S n => fun w =>
      let '(lo, w) := pop_low w in 
      let '(w, hi) := pop_high w in
      (push_low (lo, w), hi)
  end.

(* This proof is purposefully written very explicitly. Decide later whether to shorten it. *)
Theorem pop_push_high {n} (x : word n * bool) : pop_high (push_high x) = x.
Proof.
  elim: n x => [|n IH] [w hi].
  - rewrite (word0 w).
    rewrite /pop_high /push_high.
    rewrite pop_push_low.
    reflexivity.
  - rewrite -(push_pop_low w); move: (pop_low w) => [lo w'].
    rewrite /pop_high -/pop_high.
    rewrite /push_high -/push_high.
    rewrite pop_push_low.
    rewrite pop_push_low.
    rewrite IH.
    reflexivity.
Qed.

Theorem push_pop_high {n} (w : word (S n)) : push_high (pop_high w) = w.
Proof.
  elim: n w => [|n IH] w.
  - rewrite -(word1_of_bit_of_word1 w).
    move: (bit_of_word1 w) => b.
    cbv.
    reflexivity.
  - rewrite -(push_pop_low w); move: (pop_low w) => [lo w'].
    rewrite /pop_high -/pop_high /push_high -/push_high.
    rewrite pop_push_low.
    rewrite -{2}(IH w').
    move: (pop_high w') => [w'' hi].
    rewrite pop_push_low.
    reflexivity.
Qed.



Fixpoint concat {m n} (w??? : word m) (w??? : word n) : word (m+n) :=
  match w??? with
  | trivial => w???
  | push_low (b, w???) => push_low (b, concat w??? w???)
  end.

Fixpoint split {m n} : word (m+n) -> word m * word n :=
  match m with
  | 0 => fun w => (trivial , w)
  | S m => fun w =>
    let (b,w) := pop_low w in
    let (w???,w???) := split w in
    (push_low (b,w???) , w???)
  end.

Theorem split_concat {m n} (w??? : word m) (w??? : word n) : split (concat w??? w???) = (w???,w???).
Proof.
  elim: m w??? w??? => [|m IH] w??? w???.
  - rewrite (word0 w???).
    done.
  - rewrite -(push_pop_low w???); move: (pop_low w???) => [lo w???'].
    rewrite /concat -/concat /split -/split.
    rewrite pop_push_low.
    rewrite IH.
    reflexivity.
Qed.

Theorem concat_split {m n} (w : word (m + n)) : concat (fst (split w)) (snd (split w)) = w.
Proof.
  elim: m w => [|m IH] w.
  - done.
  - rewrite -(push_pop_low w); move: (pop_low w) => [lo w'].
    rewrite /split -/split.
    rewrite pop_push_low.
    rewrite (surjective_pairing (split w')).
    simpl.
    rewrite IH.
    reflexivity.
Qed.



Fixpoint op??? {n} : bool -> word n :=
  match n with
  | 0 => fun _ => trivial
  | S n => fun op => push_low (op, op??? op)
  end.
Fixpoint op??? {n} : (bool -> bool) -> (word n -> word n) :=
  match n with
  | 0 => fun _ _ => trivial
  | S n => fun op w => let '(b,w) := pop_low w in push_low (op b, op??? op w)
  end.
Fixpoint op??? {n} : (bool -> bool -> bool) -> (word n -> word n -> word n) :=
  match n with
  | 0 => fun _ _ _ => trivial
  | S n => fun op w1 w2 =>
    let '(b1,w1) := pop_low w1 in
    let '(b2,w2) := pop_low w2 in
    push_low (op b1 b2, op??? op w1 w2)
  end.

(* Accessing Individual Bits *)

Declare Scope bounded_scope.
Delimit Scope bounded_scope with b.

Record bounded (n : nat) : Type :=
  { nat_of_bounded : nat
  ; bound_of_bounded : nat_of_bounded < n
  }.

Arguments nat_of_bounded {n}.
Arguments bound_of_bounded {n}.

Definition bounded_zero {n} : bounded (S n) :=
  {| nat_of_bounded := 0
  ; bound_of_bounded := Nat.lt_0_succ n
  |}.

Definition bounded_suc {n} (b : bounded n) : bounded (S n) :=
  {| nat_of_bounded := S (nat_of_bounded b)
  ; bound_of_bounded := Lt.lt_n_S _ _ (bound_of_bounded b)
  |}.

Number Notation bounded Nat.of_num_uint Nat.to_num_uint (via nat mapping [[bounded_zero] => O, [bounded_suc] => S]) : bounded_scope.

Theorem bounded_eq {n} (i j : bounded n) : (nat_of_bounded i = nat_of_bounded j) -> i = j.
Proof.
  move: i => [i pf_i].
  move: j => [j pf_j].
  simpl.
  move=> eq.
  move: pf_i pf_j.
  rewrite eq.
  move=> pf_i pf_j.
  rewrite (proof_irrelevance _ pf_i pf_j).
  reflexivity.
Qed.



Fixpoint bit {n} (w : word n) : bounded n -> bool :=
  match w with
  | trivial => fun '(Build_bounded _ i pf) => match Nat.nlt_0_r i pf with end
  | push_low (b, w) => fun '(Build_bounded _ i pf) =>
    match i return i < _ -> bool with
    | 0 => fun _ => b
    | S i => fun pf => bit w (Build_bounded _ i (Lt.lt_S_n _ _ pf)) 
    end pf
  end.

(* Two words are equal if, and only if, their bits are equal. *)
Theorem eq_bits {n} {w??? w??? : word n} :
  (forall i, bit w??? i = bit w??? i) <-> (w??? = w???).
Proof.
  split.
  - elim: n w??? w??? => [|n IH] w??? w???.
    + rewrite (word0 w???) (word0 w???).
      reflexivity.
    + rewrite -(push_pop_low w???) -(push_pop_low w???).
      move: (pop_low w???) => [lo??? w???'].
      move: (pop_low w???) => [lo??? w???'].
      move=> eq.
      f_equal; f_equal.
      * exact (eq bounded_zero).
      * apply IH => i.
        move: (eq (bounded_suc i)).
        simpl.
        rewrite (bounded_eq (Build_bounded _ _ _) i eq_refl).
        done.
  - move=>->.
    done.
Qed.

Fixpoint eqb {n} : word n -> word n -> bool :=
  match n with
  | 0 => fun _ _ => true
  | S n => fun w1 w2 => 
    let (b1,w1) := pop_low w1 in
    let (b2,w2) := pop_low w2 in
    (Bool.eqb b1 b2) && eqb w1 w2
  end%bool.

Theorem eqb_spec {n} {w??? w??? : word n} : reflect (w??? = w???) (eqb w??? w???).
Proof.
    elim: n w??? w??? => [|n IH] w??? w???.
    - rewrite (word0 w???) (word0 w???). by constructor.
    - rewrite -(push_pop_low w???) -(push_pop_low w???).
        move: (pop_low w???) (pop_low w???) => [b??? w???'] [b??? w???'].
        specialize (IH w???' w???').
        simpl.
        apply: (iffP andP); rewrite -(rwP IH) -(rwP (Bool.eqb_spec b??? b???)).
        + by move=> [-> ->].
        + move /(f_equal pop_low).
          do 2 rewrite pop_push_low.
          apply pair_equal_spec.
Qed.

(* TODO: Bit interpretations of all of the operations. *)

(* Numerics *)

From Coq Require Import BinInt.

Definition int_of_bit (b : bool) : Z :=
  match b with
  | true => 1
  | false => 0
  end.

Fixpoint int_of_word {n} (w : word n) : Z :=
  match w with
  | trivial => 0
  | push_low (b, w) => int_of_bit b + Z.double (int_of_word w)
  end%Z.

Fixpoint word_of_int {n} : Z -> word n :=
  match n with
  | 0 => fun _ => trivial
  | S n => fun x => push_low (Z.odd x, word_of_int (Z.div2 x))
  end.

(* TODO: Numeric interpretations for the operations that have them. *)

Definition full_adder (a b c : bool) : (bool * bool) :=
  match a, b, c with
  | false, false, false => (false, false)

  | false, false, true
  | false, true, false
  | true, false, false => (true, false)

  | true, true, false
  | true, false, true
  | false, true, true => (false, true)

  | true, true, true => (true, true)
  end.

Lemma full_adder_spec (a b c : bool) :
  (int_of_bit a + int_of_bit b + int_of_bit c =
  int_of_bit (fst (full_adder a b c)) +
  Z.double (int_of_bit (snd (full_adder a b c))))%Z.
Proof.
  by case a; case b; case c.
Qed.

Fixpoint add_with_carry {n} : bool -> word n -> word n -> word n * bool := match n with
    | 0 => fun carry _ _ => (trivial, carry)
    | S n => fun carry a b =>
        let '(a, aa) := pop_low a in
        let '(b, bb) := pop_low b in
        let '(c, carry') := full_adder carry a b in
        let '(cc, carry'') := add_with_carry carry' aa bb in
        (push_low (c, cc), carry'')
end.

Definition add {n} (a b : word n) : word n := fst (add_with_carry false a b).

Definition sub_with_inv_borrow {n} : bool -> word n -> word n -> word n * bool
    := fun borrowin a b => add_with_carry borrowin a (op??? negb b).

Definition sub {n} (a b : word n) : word n := fst (sub_with_inv_borrow true a b).

Definition increment {n} (i : Z) (w : word n) : word n
    := add (word_of_int i) w.

(* Decimal Mode *)

Fixpoint int_of_decimal_word {n} : word (n * 4) -> option Z :=
  match n with
  | 0 => fun _ => Some 0%Z
  | S n => fun (w : word (S n * 4)) =>
      let (bbbb, w) := split w : (word 4 * word (n * 4))%type in
      let ones_place := int_of_word bbbb in
      match (ones_place <? 10)%Z, int_of_decimal_word w with
      | true, Some tens_place => Some (ones_place + 10 * tens_place)%Z
      | _, _ => None
      end
  end.