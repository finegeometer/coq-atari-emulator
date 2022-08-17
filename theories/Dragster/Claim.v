From Coq Require Import BinInt ssrbool.
Require Word Memory Processor Atari Dragster.ROM.
Import Word ROM(rom).

(*
What does it mean to win Dragster?

The best I could figure out is that Dragster has been won if the branch at address 0xF39E is taken.
I was hoping there'd be a variable that clearly says "You have won!", but I couldn't find one.
*)
Definition has_won (s : Atari.state) : Prop :=
    Processor.RegPC (fst s) = word_of_int 0xf39e /\
    negb (Processor.FlagZ (Processor.RegP (fst s))).

(* The value of the active player's timer, in hundreds of microseconds. *)
Definition timer_100μs (s : Atari.state) : option Z :=
    let bcd :=
        (* The active player is stored in the low bit of RAM address 0x8f. *)
        if Word.bit (Memory.read (word_of_int 0x8f) (snd s)) 0%b
        (* The timer for Player 0 is stored in addresses 0xb3, 0xb5, and 0xb7. *)
        then
            Word.concat (Memory.read (word_of_int 0xb3) (snd s)) ( 
            Word.concat (Memory.read (word_of_int 0xb5) (snd s)) (
                        (Memory.read (word_of_int 0xb7) (snd s)) ))
        else
        (* The timer for Player 1 is stored in addresses 0xb4, 0xb6, and 0xb8. *)
            Word.concat (Memory.read (word_of_int 0xb4) (snd s)) (
            Word.concat (Memory.read (word_of_int 0xb6) (snd s)) (
                        (Memory.read (word_of_int 0xb8) (snd s)) ))
    in Word.int_of_decimal_word (n := 6) bcd.

(* The statement that Dragster cannot be beaten in less than 5.57 seconds. *)
Definition claim : Prop :=
    (* Choose any initial state of the Atari, *)
    forall s₀,
    (* with the program counter set to 0xf000. *)
    Processor.RegPC (fst s₀) = word_of_int 0xf000 ->

    (* Choose any later state, *)
    forall s₁,
    (* reachable from that initial state, *)
    Atari.reachable rom s₀ s₁ ->
    (* in which a player has just won. *)
    has_won s₁ ->

    (* Then the player's timer is a valid BCD number, *)
    match timer_100μs s₁ with
    | None => False
    (* and reads at least 5.57 seconds. *)
    | Some time => (time >= 55700)%Z
    end.

