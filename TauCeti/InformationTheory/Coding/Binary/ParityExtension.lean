/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Basic
public import TauCeti.InformationTheory.Coding.ParityExtension

/-!
# Parity extension of binary codes

Every binary parity extension is even, and parity-extending a puncture of an even binary code
recovers the original code up to the displayed coordinate equivalence. This gives the recovery
mechanism for punctured even codes, including extended binary Golay codes.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §1.5.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Every binary parity extension is even. -/
theorem BinaryCode.isEven_parityExtension (C : LinearCode (ZMod 2) ι) :
    BinaryCode.IsEven (parityExtension C) :=
  BinaryCode.isEven_iff_le_singleParityCheckCode.mpr
    (parityExtension_le_singleParityCheckCode C)

/-- Every even binary code is recovered by parity-extending a puncture at any coordinate. -/
theorem BinaryCode.IsEven.parityExtension_punctureAt [DecidableEq ι]
    {C : LinearCode (ZMod 2) ι} (hC : BinaryCode.IsEven C) (i : ι) :
    parityExtension (punctureAt C i) = reindex C (Equiv.optionSubtypeNe i) :=
  TauCeti.parityExtension_punctureAt C i
    (BinaryCode.isEven_iff_le_singleParityCheckCode.mp hC)

end TauCeti
