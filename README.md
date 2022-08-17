A formalization of the claim that the game Dragster cannot be beaten in fewer than 5.57 seconds. Proof not included.

# Dependencies

- coq.8.15.2
- coq-record-update.0.3.0

# Ideas

There are a lot of improvements I could make to this project.

- Word.v
    - I could turn this file into an introduction to Coq for the typical speedrunner.
    - Alternatively, I could rework the program to use https://github.com/coq-community/bits.
        - I've had issues with ssreflect calculations not computing, though.
- Memory.v
    - It would be better if `memory` were its own type.
        Sometimes Coq becomes slightly sluggish, because it's trying to print the full expansion of `memory 7 (word 8)` a whole bunch of times.
- Processor.v
    - Is there a nicer way to arrange the instructions, rather than as an enum with 56 constructors?
- Atari.v
    - This could be replaced with an actual implementation of the TIA and RIOT chips.
- Other
    - Checking that an emulator is implemented correctly is a difficult task.
        Is there some way the behavior could be proven correct, relative to the transistor layout of the chip?
        https://github.com/trebonian/visual6502 is a transistor-level simulation of the 6502, so the transistor layout is clearly known.

# Proving a Lower Bound

The goal for this project was to formally prove that Dragster cannot be beaten in fewer than 5.57 seconds. But I found myself unable to tame the complexity of assembly code.

Possible approaches:
- Specification Logic. This is more typically used for high-level languages. But a way to use it for assembly code is described in https://jbj.github.io/research/hlsl.pdf.
- Simplify the code, using repeated automatic code transformations:
    - Translate from assembly code into SSA form.
    - Run passes like dead-code elimination. This would simplify a lot; most flag writes, for instance, are not read before being overwritten.
    - Continue inventing passes to simplify the code, until it reaches a manageable complexity.
