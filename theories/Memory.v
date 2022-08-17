From Coq Require Import ssreflect.
Require Import Word.

(* An efficient implementation of `word n -> V`. *)
Fixpoint memory n (V : Type) : Type := match n with
    | 0 => V
    | S n => memory n (V * V)
end.

Fixpoint read {n V} (w : word n) : memory n V -> V :=
match w with
| trivial => fun mem => mem
| push_low (false,w) => fun mem => fst (read w mem)
| push_low (true,w) => fun mem => snd (read w mem)
end.

Fixpoint modify {n V} (w : word n) (f : V -> V) : memory n V -> memory n V :=
match w in word n return memory n V -> memory n V with
| trivial => fun mem => f mem
| push_low (false,w) => modify w (fun mem => (f (fst mem), snd mem))
| push_low (true,w) => modify w (fun mem => (fst mem, f (snd mem)))
end.

Definition write {n V} (w : word n) (x : V) : memory n V -> memory n V :=
modify w (fun _ => x).

Fixpoint from_fn {n} : forall {V}, (word n -> V) -> memory n V :=
match n with
| 0 => fun _ f => f trivial
| S n => fun V f => @from_fn n _ (fun w => (f (push_low (false, w)), f (push_low (true, w))))
end.

(* Theorems *)

Theorem read_from_fn {n V addr} {f : word n -> V}: read addr (from_fn f) = f addr.
Proof.
    move: V addr f; elim: n => [|n IH] V addr f.
    - by rewrite [addr]word0.
    - rewrite -(push_pop_low addr); move: (pop_low addr) => [b w].
        by case b; simpl; rewrite IH.
Qed.

Theorem eq_read {n V} {mem1 mem2 : memory n V} :
    (forall w, read w mem1 = read w mem2) -> mem1 = mem2.
Proof.
    move: V mem1 mem2; elim: n => [|n IH] V mem1 mem2 H.
    - exact (H trivial).
    - apply: IH => w.
        apply: injective_projections.
        + exact (H (push_low (false, w))).
        + exact (H (push_low (true, w))).
Qed.

Theorem from_fn_read {n V} {mem : memory n V} : from_fn (fun w => read w mem) = mem.
Proof.
    apply: eq_read => w.
    apply: read_from_fn.
Qed.

Theorem read_modify {n V addr1 addr2 f} {mem : memory n V} :
    read addr1 (modify addr2 f mem) =
    if Word.eqb addr2 addr1 then f (read addr1 mem) else read addr1 mem.
Proof.
    move: V addr1 addr2 f mem; elim: n => [|n IH] V addr1 addr2 f mem.
    - by rewrite [addr1]word0 [addr2]word0.
    - rewrite -(push_pop_low addr1) -(push_pop_low addr2).
        move: (pop_low addr1) (pop_low addr2) => [b1 w1] [b2 w2].
        simpl; case b1; case b2; simpl; rewrite IH; case (Word.eqb w2 w1); done.
Qed.

Theorem read_write {n V addr1 addr2 v} {mem : memory n V} :
    read addr1 (write addr2 v mem) =
    if Word.eqb addr2 addr1 then v else read addr1 mem.
Proof.
    apply: read_modify.
Qed.

(* Writing down a ROM by hand *)

Definition concat {n V} : memory n V * memory n V -> memory (S n) V.
Proof.
    move: V; elim: n => [|n IH] V; simpl.
    - done.
    - apply IH.
Defined. 

Definition new n {A V} (f : A -> V) :
    nat_rect
        (fun _ => Type -> Type)
        (fun T => A -> T)
        (fun _ f T => f (f T))
        n
        (memory n V).
Proof.
    have: memory n V -> memory n V by []; move: {-1}(memory n V).
    elim: n => [|n IH] X g; simpl.
    - by move /f /g.
    - apply: (IH) => a.
        apply: IH => b.
        apply: g.
        apply: concat.
        exact (a,b).
Defined.

(* Testing new *)
Goal new 3 (fun x => x) 1 2 3 4 5 6 7 8 = (((1,2),(3,4)),((5,6),(7,8))).
reflexivity. Qed.

