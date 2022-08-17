(* This file attempts to implement a cycle-accurate emulation of a 6502 processor,
    failing only on illegal opcodes.
*)

From Coq Require Import ssreflect BinInt.
From RecordUpdate Require Import RecordSet.
Require Memory. Import Memory(memory).
Require Import Word.

(* Flags *)

Record flags : Set := mk_flags
{ FlagC : bool
; FlagZ : bool
; FlagI : bool
; FlagD : bool
; FlagV : bool
; FlagN : bool
}.

#[global]
Instance set_flags : Settable _ := settable! mk_flags
<FlagC; FlagZ; FlagI; FlagD; FlagV; FlagN>.

Definition byte_of_flags (flags : flags) : word 8 :=
Word.push_low (FlagC flags,
Word.push_low (FlagZ flags,
Word.push_low (FlagI flags,
Word.push_low (FlagD flags,
Word.push_low (true,
Word.push_low (true,
Word.push_low (FlagV flags,
Word.push_low (FlagN flags,
Word.trivial)))))))).

Definition flags_of_byte (w : word 8) : flags :=
let (C, w) := Word.pop_low w in
let (Z, w) := Word.pop_low w in
let (I, w) := Word.pop_low w in
let (D, w) := Word.pop_low w in
let (_, w) := Word.pop_low w in
let (_, w) := Word.pop_low w in
let (V, w) := Word.pop_low w in
let (N, w) := Word.pop_low w in
mk_flags C Z I D V N.

Definition setZN (w : word 8) (f : flags) : flags :=
set FlagZ (fun _ => Word.eqb w (op₀ false)) (set FlagN (fun _ => Word.bit w 7%b) f).

(* Registers *)

Record registers : Set :=
{ RegPC : word 16
; RegA : word 8
; RegX : word 8
; RegY : word 8
; RegS : word 8
; RegP : flags
}.

#[global]
Instance set_registers : Settable _ := settable! Build_registers
<RegPC; RegA; RegX; RegY; RegS; RegP>.

(* Cycles *)

Inductive cycle (T : Type) :=
| read : word 16 -> (word 8 -> T) -> cycle T
| write : word 16 -> word 8 -> T -> cycle T
.
Arguments read {T}.
Arguments write {T}.

Inductive cycles (T : Type) :=
| zero : T -> cycles T
| suc : cycle (cycles T) -> cycles T
.
Arguments zero {T}.
Arguments suc {T}.

Definition cycles_builder (A : Type) : Type :=
forall B, (A -> cycles B) -> cycles B.

(* Addressing Modes *)
(* Citation: Appendix A of
    http://archive.6502.org/books/mcs6500_family_hardware_manual.pdf
*)

Inductive addressing_mode : Set :=
| Accumulator
| Immediate
| Implied
| Relative
| Absolute
| ZeroPage
| Indirect
| AbsoluteX
| AbsoluteY
| ZeroPageX
| ZeroPageY
| IndexedIndirect
| IndirectIndexed
.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

(* The first argument should be true if this operation only *reads* memory,
    and does not write it. This is necessary because the processor
    occasionally takes one fewer cycle in that case.
*)
Definition effective_address (read_only : bool)
    (mode : addressing_mode) (r : registers) : cycles_builder (word 16) :=
fun _ continuation => match mode with
| Immediate => continuation (Word.increment 1 (RegPC r))
| Absolute =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.increment 2 $ RegPC r) $ fun hi =>
    continuation $ Word.concat lo hi
| AbsoluteX =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.increment 2 $ RegPC r) $ fun hi =>
    let (lo, carry) := Word.add_with_carry false lo (RegX r) in
    if carry || negb read_only
    then
        suc $ read (Word.concat lo hi) $ fun _ =>
        continuation $ Word.concat lo (if carry then Word.increment 1 hi else hi)
    else
        continuation $ Word.concat lo hi
| AbsoluteY =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.increment 2 $ RegPC r) $ fun hi =>
    let (lo, carry) := Word.add_with_carry false lo (RegY r) in
    if carry || negb read_only
    then
        suc $ read (Word.concat lo hi) $ fun _ =>
        continuation $ Word.concat lo (if carry then Word.increment 1 hi else hi)
    else
        continuation $ Word.concat lo hi
| ZeroPage =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    continuation $ Word.concat lo (op₀ false)
| ZeroPageX =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.concat lo (op₀ false)) $ fun _ =>
    continuation $ Word.concat (Word.add lo (RegX r)) (op₀ false)
| ZeroPageY =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.concat lo (op₀ false)) $ fun _ =>
    continuation $ Word.concat (Word.add lo (RegY r)) (op₀ false)
| IndexedIndirect =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.concat lo (op₀ false)) $ fun _ =>
    let lo := Word.add lo (RegX r) in
    suc $ read (Word.concat lo (op₀ false)) $ fun lo' =>
    suc $ read (Word.concat (Word.increment 1 lo) (op₀ false)) $ fun hi' =>
    continuation $ Word.concat lo' hi'
| IndirectIndexed =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.concat lo (op₀ false)) $ fun lo' =>
    suc $ read (Word.concat (Word.increment 1 lo) (op₀ false)) $ fun hi' =>
    let (lo', carry) := Word.add_with_carry false lo' (RegY r) in
    if carry || negb read_only
    then
        suc $ read (Word.concat lo' hi') $ fun _ =>
        continuation $ Word.concat lo' (if carry then Word.increment 1 hi' else hi')
    else
        continuation $ Word.concat lo' hi'
| Indirect =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun lo =>
    suc $ read (Word.increment 2 $ RegPC r) $ fun hi =>
    (* Yes, this behaves weirdly when lo = 0xFF. Yes, that's intended. *)
    suc $ read (Word.concat lo hi) $ fun lo' =>
    suc $ read (Word.concat (Word.increment 1 lo) hi) $ fun hi' =>
    continuation $ Word.concat lo' hi'
| Relative =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun offset =>
    suc $ read (Word.increment 2 (RegPC r)) $ fun _ =>
    let (lo, hi) := Word.split (m := 8) (Word.increment 2 (RegPC r)) in
    let (lo, carry) := Word.add_with_carry false lo offset in
    let page_change := (
        Word.int_of_bit carry -
        Word.int_of_bit (Word.bit offset 7%b)
    )%Z in
    if Z.eqb page_change 0
    then
        continuation $ Word.concat lo hi
    else
        suc $ read (Word.concat lo hi) $ fun _ =>
        continuation $ Word.concat lo (Word.increment page_change hi)

(* These modes don't really produce addresses, so I'll produce dummy values. *)
| Accumulator =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun _ =>
    continuation $ op₀ false
| Implied =>
    suc $ read (Word.increment 1 $ RegPC r) $ fun _ =>
    continuation $ op₀ false
end.

Definition mode_length (mode : addressing_mode) : Z :=
match mode with
| Accumulator => 1
| Immediate => 2
| Implied => 1
| Relative => 2
| Absolute => 3
| AbsoluteX => 3
| AbsoluteY => 3
| ZeroPage => 2
| ZeroPageX => 2
| ZeroPageY => 2
| IndexedIndirect => 2
| IndirectIndexed => 2
| Indirect => 3
end.

Definition inc_pc (mode : addressing_mode) : registers -> registers :=
set RegPC (Word.increment (mode_length mode)).

Definition execute_non_memory_op (f : registers -> registers)
    (mode : addressing_mode) (r : registers) : cycles registers :=
suc $ read (Word.increment 1 $ RegPC r) $ fun _ =>
zero $ f (inc_pc mode r).

(* There are no "read accumulator" operations. *)
Definition execute_read_op (f : registers -> word 8 -> registers)
    (mode : addressing_mode) (r : registers) : cycles registers :=
effective_address true mode r _ $ fun addr =>
suc $ read addr $ fun w =>
zero $ f (inc_pc mode r) w.

Definition execute_write_op (f : registers -> registers * word 8)
    (mode : addressing_mode) (r : registers) : cycles registers :=
effective_address false mode r _ $ fun addr =>
let (r,w) := f (inc_pc mode r) in
suc $ write addr w $
zero $ r.

Definition execute_modify_op (f : registers -> word 8 -> registers * word 8)
    (mode : addressing_mode) (r : registers) : cycles registers :=
match mode with
| Accumulator =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    let (r,w) := f (inc_pc Accumulator r) (RegA r) in
    zero $ set RegA (fun _ => w) r
| _ =>
    effective_address false mode r _ $ fun addr =>
    suc $ read addr $ fun w =>
    suc $ write addr w $
    let (r,w) := f (inc_pc mode r) w in
    suc $ write addr w $
    zero $ r
end.

Definition execute_branch (cond : registers -> bool) (r : registers) : cycles registers :=
if cond r
then
    effective_address true Relative r _ $ fun addr =>
    zero $ set RegPC (fun _ => addr) r
else
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    zero $ inc_pc Relative r.

(* Instructions *)

Inductive instruction : Set :=
| ADC : instruction 
| AND : instruction 
| ASL : instruction 
| BCC : instruction 
| BCS : instruction 
| BEQ : instruction 
| BIT : instruction 
| BMI : instruction 
| BNE : instruction 
| BPL : instruction 
| BRK : instruction 
| BVC : instruction 
| BVS : instruction 
| CLC : instruction
| CLD : instruction 
| CLI : instruction 
| CLV : instruction 
| CMP : instruction 
| CPX : instruction 
| CPY : instruction 
| DEC : instruction 
| DEX : instruction 
| DEY : instruction 
| EOR : instruction 
| INC : instruction 
| INX : instruction 
| INY : instruction 
| JMP : instruction
| JSR : instruction 
| LDA : instruction 
| LDX : instruction 
| LDY : instruction 
| LSR : instruction 
| NOP : instruction 
| ORA : instruction 
| PHA : instruction 
| PHP : instruction 
| PLA : instruction 
| PLP : instruction 
| ROL : instruction 
| ROR : instruction 
| RTI : instruction
| RTS : instruction 
| SBC : instruction 
| SEC : instruction 
| SED : instruction 
| SEI : instruction 
| STA : instruction 
| STX : instruction 
| STY : instruction 
| TAX : instruction 
| TAY : instruction 
| TSX : instruction 
| TXA : instruction 
| TXS : instruction 
| TYA : instruction
.

Definition run (instruction : instruction) :
    addressing_mode -> registers -> cycles registers :=
match instruction with
| NOP => execute_non_memory_op $ fun r => r

| BIT => execute_read_op $ fun r w => set RegP
    (fun f =>
        set FlagN (fun _ => Word.bit w 7%b) $
        set FlagV (fun _ => Word.bit w 6%b) $
        set FlagZ (fun _ => Word.eqb (op₂ andb w (RegA r)) (op₀ false)) f)
    r

| CMP => execute_read_op $ fun r w =>
    let (w , inv_borrow) := Word.sub_with_inv_borrow true (RegA r) w in
    set RegP (fun f => set FlagC (fun _ => inv_borrow) $ setZN w f) r
| CPX => execute_read_op $ fun r w =>
    let (w , inv_borrow) := Word.sub_with_inv_borrow true (RegX r) w in
    set RegP (fun f => set FlagC (fun _ => inv_borrow) $ setZN w f) r
| CPY => execute_read_op $ fun r w =>
    let (w , inv_borrow) := Word.sub_with_inv_borrow true (RegY r) w in
    set RegP (fun f => set FlagC (fun _ => inv_borrow) $ setZN w f) r

| DEC => execute_modify_op $ fun r w => let w := Word.increment (-1) w in
    (set RegP (setZN w) r, w)
| DEX => execute_non_memory_op $ fun r => let w := Word.increment (-1) (RegX r) in
    set RegP (setZN w) $ set RegX (fun _ => w) r
| DEY => execute_non_memory_op $ fun r => let w := Word.increment (-1) (RegY r) in
    set RegP (setZN w) $ set RegY (fun _ => w) r

| INC => execute_modify_op $ fun r w => let w := Word.increment 1 w in
    (set RegP (setZN w) r, w)
| INX => execute_non_memory_op $ fun r => let w := Word.increment 1 (RegX r) in
    set RegP (setZN w) $ set RegX (fun _ => w) r
| INY => execute_non_memory_op $ fun r => let w := Word.increment 1 (RegY r) in
    set RegP (setZN w) $ set RegY (fun _ => w) r

(* Bitwise Operations *)
| AND => execute_read_op $ fun r w =>
    let w := op₂ andb w (RegA r) in
    set RegA (fun _ => w) $
    set RegP (setZN w) r
| EOR => execute_read_op $ fun r w =>
    let w := op₂ xorb w (RegA r) in
    set RegA (fun _ => w) $
    set RegP (setZN w) r
| ORA => execute_read_op $ fun r w =>
    let w := op₂ orb w (RegA r) in
    set RegA (fun _ => w) $
    set RegP (setZN w) r

| ASL => execute_modify_op $ fun r w =>
    let (w , carry) := Word.pop_high (Word.push_low (false, w)) in
    (set RegP (fun f => set FlagC (fun _ => carry) $ setZN w f) r, w)
| LSR => execute_modify_op $ fun r w =>
    let (carry , w) := Word.pop_low (Word.push_high (w , false)) in
    (set RegP (fun f => set FlagC (fun _ => carry) $ setZN w f) r, w)
| ROL => execute_modify_op $ fun r w =>
    let (w , carry) := Word.pop_high (Word.push_low (FlagC (RegP r), w)) in
    (set RegP (fun f => set FlagC (fun _ => carry) $ setZN w f) r, w)
| ROR => execute_modify_op $ fun r w =>
    let (carry , w) := Word.pop_low (Word.push_high (w , FlagC (RegP r))) in
    (set RegP (fun f => set FlagC (fun _ => carry) $ setZN w f) r, w)

(* Moving Data Around *)
| LDA => execute_read_op $ fun r w => set RegP (setZN w) $ set RegA (fun _ => w) r
| LDX => execute_read_op $ fun r w => set RegP (setZN w) $ set RegX (fun _ => w) r
| LDY => execute_read_op $ fun r w => set RegP (setZN w) $ set RegY (fun _ => w) r
| STA => execute_write_op $ fun r => (r , RegA r)
| STX => execute_write_op $ fun r => (r , RegX r)
| STY => execute_write_op $ fun r => (r , RegY r)
| TAX => execute_non_memory_op $ fun r =>
    set RegP (setZN (RegA r)) $ set RegX (fun _ => RegA r) r
| TAY => execute_non_memory_op $ fun r =>
    set RegP (setZN (RegA r)) $ set RegY (fun _ => RegA r) r
| TSX => execute_non_memory_op $ fun r =>
    set RegP (setZN (RegS r)) $ set RegX (fun _ => RegS r) r
| TXA => execute_non_memory_op $ fun r =>
    set RegP (setZN (RegX r)) $ set RegA (fun _ => RegX r) r
| TXS => execute_non_memory_op $ fun r =>
    set RegP (setZN (RegX r)) $ set RegS (fun _ => RegX r) r
| TYA => execute_non_memory_op $ fun r =>
    set RegP (setZN (RegY r)) $ set RegA (fun _ => RegY r) r

(* Flags *)
| CLC => execute_non_memory_op $ set RegP $ set FlagC $ fun _ => false
| CLD => execute_non_memory_op $ set RegP $ set FlagD $ fun _ => false
| CLI => execute_non_memory_op $ set RegP $ set FlagI $ fun _ => false
| CLV => execute_non_memory_op $ set RegP $ set FlagV $ fun _ => false
| SEC => execute_non_memory_op $ set RegP $ set FlagC $ fun _ => true
| SED => execute_non_memory_op $ set RegP $ set FlagD $ fun _ => true
| SEI => execute_non_memory_op $ set RegP $ set FlagI $ fun _ => true

(* Branch and Jump *)
| BCS => fun _ => execute_branch $ fun r =>      (FlagC (RegP r))
| BCC => fun _ => execute_branch $ fun r => negb (FlagC (RegP r))
| BEQ => fun _ => execute_branch $ fun r =>      (FlagZ (RegP r))
| BNE => fun _ => execute_branch $ fun r => negb (FlagZ (RegP r))
| BVS => fun _ => execute_branch $ fun r =>      (FlagV (RegP r))
| BVC => fun _ => execute_branch $ fun r => negb (FlagV (RegP r))
| BMI => fun _ => execute_branch $ fun r =>      (FlagN (RegP r))
| BPL => fun _ => execute_branch $ fun r => negb (FlagN (RegP r))
| JMP => fun mode r => effective_address true mode r _ $ fun addr =>
    zero $ set RegPC (fun _ => addr) r

(* Addition and Subtraction *)
| ADC => execute_read_op $ fun r num1 =>
    let num0 := RegA r in
    let (binary_sum, binary_carry) :=
        Word.add_with_carry (FlagC (RegP r)) num0 num1 in
    if FlagD (RegP r)
    then
        let (lo0, hi0) := Word.split (m := 4) num0 in
        let (lo1, hi1) := Word.split (m := 4) num1 in

        let (lo, carry_mid) := Word.add_with_carry (FlagC (RegP r)) lo0 lo1 in
        let (lo_minus_10, no_decimal_carry) :=
            Word.sub_with_inv_borrow true lo (word_of_int 10) in
        let (lo, carry_mid) :=
            if no_decimal_carry
            then (lo, carry_mid)
            else (lo_minus_10, true) in

        let (hi, carry_out) := Word.add_with_carry carry_mid hi0 hi1 in
        let (hi_minus_10, no_decimal_carry) :=
            Word.sub_with_inv_borrow true hi (word_of_int 10) in
        let (hi, carry_out) :=
            if no_decimal_carry
            then (hi, carry_out)
            else (hi_minus_10, true) in

        set RegA (fun _ => Word.concat lo hi) $
        set RegP
            (fun f =>
                set FlagC (fun _ => carry_out) $
                set FlagZ (fun _ => Word.eqb binary_sum (op₀ false)) $
                set FlagN (fun _ => Word.bit hi 3%b) $
                set FlagV
                    (fun _ =>
                       Word.bit hi0 3%b
                    && Word.bit hi1 3%b
                    && negb (Word.bit hi 3%b)
                    || negb (Word.bit hi0 3%b)
                    && negb (Word.bit hi1 3%b)
                    && Word.bit hi 3%b
                    )%bool $
                setZN binary_sum f)
            r
    else
        set RegA (fun _ => binary_sum) $
        set RegP
            (fun f =>
                set FlagC (fun _ => binary_carry) $
                set FlagV
                    (fun _ =>
                       Word.bit num0 7%b
                    && Word.bit num1 7%b
                    && negb (Word.bit binary_sum 7%b)
                    || negb (Word.bit num0 7%b)
                    && negb (Word.bit num1 7%b)
                    && Word.bit binary_sum 7%b
                    )%bool $
                setZN binary_sum f)
            r
| SBC => execute_read_op $ fun r num1 =>
    let num0 := RegA r in
    let (binary_difference, binary_inv_borrow) :=
        Word.sub_with_inv_borrow (FlagC (RegP r)) num0 num1 in
    let r := set RegP
        (fun f =>
            set FlagC (fun _ => binary_inv_borrow) $
            set FlagV (fun _ =>
                Word.bit num0 7%b
                && negb (Word.bit num1 7%b)
                && negb (Word.bit binary_difference 7%b)
                || negb (Word.bit num0 7%b)
                && Word.bit num1 7%b
                && Word.bit binary_difference 7%b
                )%bool $
            setZN binary_difference f)
        r in
    if FlagD (RegP r)
    then
        let (lo0, hi0) := Word.split (m := 4) num0 in
        let (lo1, hi1) := Word.split (m := 4) num1 in

        let (lo, inv_borrow_mid) := Word.sub_with_inv_borrow (FlagC (RegP r)) lo0 lo1 in
        let lo := if inv_borrow_mid then lo else Word.increment 10 lo in

        let (hi, inv_borrow_out) := Word.sub_with_inv_borrow inv_borrow_mid hi0 hi1 in
        let hi := if inv_borrow_out then hi else Word.increment 10 hi in

        set RegA (fun _ => Word.concat lo hi) r
    else
        set RegA (fun _ => binary_difference) r

(* Stack operations *)
| BRK => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    let (lo, hi) := Word.split (m := 8) (RegPC r) in
    suc $ write (Word.concat                      (RegS r)  (word_of_int 1)) hi $
    suc $ write (Word.concat (Word.increment (-1) (RegS r)) (word_of_int 1)) lo $
    suc $ write (Word.concat (Word.increment (-2) (RegS r)) (word_of_int 1))
        (byte_of_flags (RegP r)) $
    suc $ read (word_of_int 0xfffe) $ fun lo =>
    suc $ read (word_of_int 0xffff) $ fun hi =>
    zero $
        set RegS (Word.increment (-3)) $
        set RegP (set FlagI (fun _ => true)) $
        set RegPC (fun _ => Word.concat lo hi) r
| JSR => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun lo' =>
    let (lo, hi) := Word.split (m := 8) (Word.increment 2 (RegPC r)) in
    suc $ read  (Word.concat                      (RegS r)  (word_of_int 1)) $ fun _ =>
    suc $ write (Word.concat                      (RegS r)  (word_of_int 1)) hi $
    suc $ write (Word.concat (Word.increment (-1) (RegS r)) (word_of_int 1)) lo $
    suc $ read (Word.increment 2 (RegPC r)) $ fun hi' =>
    zero $
        set RegS (Word.increment (-2)) $
        set RegPC (fun _ => Word.concat lo' hi') r
| PHA => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    suc $ write (Word.concat (RegS r)  (word_of_int 1)) (RegA r) $
    zero $
        set RegS (Word.increment (-1)) $
        set RegPC (Word.increment 1) r
| PHP => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    suc $ write (Word.concat (RegS r)  (word_of_int 1)) (byte_of_flags (RegP r)) $
    zero $
        set RegS (Word.increment (-1)) $
        set RegPC (Word.increment 1) r
| PLA => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    suc $ read (Word.concat                   (RegS r)  (word_of_int 1)) $ fun _ =>
    suc $ read (Word.concat (Word.increment 1 (RegS r)) (word_of_int 1)) $ fun w =>
    zero $
        set RegS (Word.increment 1) $
        set RegA (fun _ => w) $
        set RegPC (Word.increment 1) r
| PLP => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    suc $ read (Word.concat                   (RegS r)  (word_of_int 1)) $ fun _ =>
    suc $ read (Word.concat (Word.increment 1 (RegS r)) (word_of_int 1)) $ fun w =>
    zero $
        set RegS (Word.increment 1) $
        set RegP (fun _ => flags_of_byte w) $
        set RegPC (Word.increment 1) r
| RTI => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    suc $ read (Word.concat                   (RegS r)  (word_of_int 1)) $ fun _ =>
    suc $ read (Word.concat (Word.increment 1 (RegS r)) (word_of_int 1)) $ fun flags =>
    suc $ read (Word.concat (Word.increment 2 (RegS r)) (word_of_int 1)) $ fun lo =>
    suc $ read (Word.concat (Word.increment 3 (RegS r)) (word_of_int 1)) $ fun hi =>
    suc $ read (Word.concat lo hi) $ fun _ =>
    zero $
        set RegS (Word.increment 3) $
        set RegP (fun _ => flags_of_byte flags) $
        set RegPC (fun _ => Word.concat lo hi) r
| RTS => fun _ r =>
    suc $ read (Word.increment 1 (RegPC r)) $ fun _ =>
    suc $ read (Word.concat                   (RegS r)  (word_of_int 1)) $ fun _ =>
    suc $ read (Word.concat (Word.increment 1 (RegS r)) (word_of_int 1)) $ fun lo =>
    suc $ read (Word.concat (Word.increment 2 (RegS r)) (word_of_int 1)) $ fun hi =>
    suc $ read (Word.concat lo hi) $ fun _ =>
    zero $
        set RegS (Word.increment 2) $
        set RegPC (fun _ => Word.increment 1 (Word.concat lo hi)) r
end.

(* Opcodes *)

Definition opcode_table : memory 8 (option (instruction * addressing_mode)) :=
    Eval compute in Memory.new 8 (fun x => x)

    (Some (BRK, Implied))   (Some (ORA, IndexedIndirect)) None                      None
    None                    (Some (ORA, ZeroPage))        (Some (ASL, ZeroPage))    None
    (Some (PHP, Implied))   (Some (ORA, Immediate))       (Some (ASL, Accumulator)) None
    None                    (Some (ORA, Absolute))        (Some (ASL, Absolute))    None
    (Some (BPL, Relative))  (Some (ORA, IndirectIndexed)) None                      None
    None                    (Some (ORA, ZeroPageX))       (Some (ASL, ZeroPageX))   None
    (Some (CLC, Implied))   (Some (ORA, AbsoluteY))       None                      None
    None                    (Some (ORA, AbsoluteX))       (Some (ASL, AbsoluteX))   None

    (Some (JSR, Absolute))  (Some (AND, IndexedIndirect)) None                      None
    (Some (BIT, ZeroPage))  (Some (AND, ZeroPage))        (Some (ROL, ZeroPage))    None
    (Some (PLP, Implied))   (Some (AND, Immediate))       (Some (ROL, Accumulator)) None
    (Some (BIT, Absolute))  (Some (AND, Absolute))        (Some (ROL, Absolute))    None
    (Some (BMI, Relative))  (Some (AND, IndirectIndexed)) None                      None
    None                    (Some (AND, ZeroPageX))       (Some (ROL, ZeroPageX))   None
    (Some (SEC, Implied))   (Some (AND, AbsoluteY))       None                      None
    None                    (Some (AND, AbsoluteX))       (Some (ROL, AbsoluteX))   None

    (Some (RTI, Implied))   (Some (EOR, IndexedIndirect)) None                      None
    None                    (Some (EOR, ZeroPage))        (Some (LSR, ZeroPage))    None
    (Some (PHA, Implied))   (Some (EOR, Immediate))       (Some (LSR, Accumulator)) None
    (Some (JMP, Absolute))  (Some (EOR, Absolute))        (Some (LSR, Absolute))    None
    (Some (BVC, Relative))  (Some (EOR, IndirectIndexed)) None                      None
    None                    (Some (EOR, ZeroPageX))       (Some (LSR, ZeroPageX))   None
    (Some (CLI, Implied))   (Some (EOR, AbsoluteY))       None                      None
    None                    (Some (EOR, AbsoluteX))       (Some (LSR, AbsoluteX))   None

    (Some (RTS, Implied))   (Some (ADC, IndexedIndirect)) None                      None
    None                    (Some (ADC, ZeroPage))        (Some (ROR, ZeroPage))    None
    (Some (PLA, Implied))   (Some (ADC, Immediate))       (Some (ROR, Accumulator)) None
    (Some (JMP, Indirect))  (Some (ADC, Absolute))        (Some (ROR, AbsoluteX))   None
    (Some (BVS, Relative))  (Some (ADC, IndirectIndexed)) None                      None
    None                    (Some (ADC, ZeroPageX))       (Some (ROR, ZeroPageX))   None
    (Some (SEI, Implied))   (Some (ADC, AbsoluteY))       None                      None
    None                    (Some (ADC, AbsoluteX))       (Some (ROR, Absolute))    None

    None                    (Some (STA, IndexedIndirect)) None                      None
    (Some (STY, ZeroPage))  (Some (STA, ZeroPage))        (Some (STX, ZeroPage))    None
    (Some (DEY, Implied))   None                          (Some (TXA, Implied))     None
    (Some (STY, Absolute))  (Some (STA, Absolute))        (Some (STX, Absolute))    None
    (Some (BCC, Relative))  (Some (STA, IndirectIndexed)) None                      None
    (Some (STY, ZeroPageX)) (Some (STA, ZeroPageX))       (Some (STX, ZeroPageY))   None
    (Some (TYA, Implied))   (Some (STA, AbsoluteY))       (Some (TXS, Implied))     None
    None                    (Some (STA, AbsoluteX))       None                      None

    (Some (LDY, Immediate)) (Some (LDA, IndexedIndirect)) (Some (LDX, Immediate))   None
    (Some (LDY, ZeroPage))  (Some (LDA, ZeroPage))        (Some (LDX, ZeroPage))    None
    (Some (TAY, Implied))   (Some (LDA, Immediate))       (Some (TAX, Implied))     None
    (Some (LDY, Absolute))  (Some (LDA, Absolute))        (Some (LDX, Absolute))    None
    (Some (BCS, Relative))  (Some (LDA, IndirectIndexed)) None                      None
    (Some (LDY, ZeroPageX)) (Some (LDA, ZeroPageX))       (Some (LDX, ZeroPageY))   None
    (Some (CLV, Implied))   (Some (LDA, AbsoluteY))       (Some (TSX, Implied))     None
    (Some (LDY, AbsoluteX)) (Some (LDA, AbsoluteX))       (Some (LDX, AbsoluteY))   None

    (Some (CPY, Immediate)) (Some (CMP, IndexedIndirect)) None                      None
    (Some (CPY, ZeroPage))  (Some (CMP, ZeroPage))        (Some (DEC, ZeroPage))    None
    (Some (INY, Implied))   (Some (CMP, Immediate))       (Some (DEX, Implied))     None
    (Some (CPY, Absolute))  (Some (CMP, Absolute))        (Some (DEC, Absolute))    None
    (Some (BNE, Relative))  (Some (CMP, IndirectIndexed)) None                      None
    None                    (Some (CMP, ZeroPageX))       (Some (DEC, ZeroPageX))   None
    (Some (CLD, Implied))   (Some (CMP, AbsoluteY))       None                      None
    None                    (Some (CMP, AbsoluteX))       (Some (DEC, AbsoluteX))   None

    (Some (CPX, Immediate)) (Some (SBC, IndexedIndirect)) None                      None
    (Some (CPX, ZeroPage))  (Some (SBC, ZeroPage))        (Some (INC, ZeroPage))    None
    (Some (INX, Implied))   (Some (SBC, Immediate))       (Some (NOP, Implied))     None
    (Some (CPX, Absolute))  (Some (SBC, Absolute))        (Some (INC, Absolute))    None
    (Some (BEQ, Relative))  (Some (SBC, IndirectIndexed)) None                      None
    None                    (Some (SBC, ZeroPageX))       (Some (INC, ZeroPageX))   None
    (Some (SED, Implied))   (Some (SBC, AbsoluteY))       None                      None
    None                    (Some (SBC, AbsoluteX))       (Some (INC, AbsoluteX))   None.

Definition parse_opcode (w : word 8) : option (instruction * addressing_mode) :=
    Memory.read w opcode_table.

(* Step through a single processor instruction. *)
Definition step (r : registers) : cycle (option (cycles registers)) :=
read (RegPC r) $ fun opcode => option_map
    (fun x => run (fst x) (snd x) r)
    (parse_opcode opcode).

