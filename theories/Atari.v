(* This file defines what it means for a state of the Atari 2600 to be reachable from another state. *)

From Coq Require Import Relations.
Require Utils Word Memory Processor.
Import Word Memory(memory) Processor(cycle, cycles, read, write, zero, suc).

Inductive chip_selection :=
| ROM : word 12 -> chip_selection
| RAM : word 7 -> chip_selection
| TIA : word 6 -> chip_selection
| PIA : word 5 -> chip_selection
.

Definition chip_select (addr : word 16) : chip_selection :=
if       bit addr 12%b  then ROM (fst (split (m := 12) addr)) else
if negb (bit addr  7%b) then TIA (fst (split (m :=  6) addr)) else
if       bit addr  9%b  then PIA (fst (split (m :=  5) addr)) else
                             RAM (fst (split (m :=  7) addr))
.

Section with_rom.
    Variable rom : word 12 -> word 8.

    Definition cycle_rel {T}
        (input : cycle T * memory 7 (word 8))
        (output :      T * memory 7 (word 8)) : Prop :=
    match fst input with
    | read addr continuation => snd input = snd output /\
        match chip_select addr with
        | ROM addr => continuation (rom addr) = fst output
        | RAM addr => continuation (Memory.read addr (snd input)) = fst output
        | _ => exists w, continuation w = fst output
        end
    | write addr w continuation => continuation = fst output /\
        match chip_select addr with
        | RAM addr => Memory.write addr w (snd input) = snd output
        | _ => snd input = snd output
        end
    end.

    Definition cycles_rel {T}
        (input : cycles T * memory 7 (word 8))
        (output :       T * memory 7 (word 8)) : Prop :=
    clos_refl_trans_1n _
        (fun x => match fst x with
        | zero t => fun _ => False
        | suc t => cycle_rel (t, snd x)
        end)
        input (zero (fst output), snd output).

    Definition state := (Processor.registers * memory 7 (word 8))%type.
    
    Definition instruction_rel : relation state :=
    fun x z => exists y,
        cycle_rel (Processor.step (fst x), snd x) y /\
        match fst y with
        | Some c => cycles_rel (c, snd y) z
        (* If an illegal opcode is executed, I assume anything can happen. *)
        | None => True
        end.

    Definition reachable : relation state := clos_refl_trans_1n _ instruction_rel.
End with_rom.


