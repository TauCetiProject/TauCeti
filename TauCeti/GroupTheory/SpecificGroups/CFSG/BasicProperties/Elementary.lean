/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Finiteness and simplicity of the cyclic and alternating groups on the classification list

The classification list `TauCeti.CFSGIndex` has two elementary families. The cyclic index
`TauCeti.CFSGIndex.cyclic p hp` carries the group `Multiplicative (ZMod p)` for a prime `p`, and
the alternating index `TauCeti.CFSGIndex.alternating n hn` carries Mathlib's
`alternatingGroup (Fin n)` for `5 ≤ n`. This file proves that both carriers, read through the
dispatcher `TauCeti.CFSGIndex.Group`, are finite and simple.

The cyclic carrier has exactly `p` elements, so it is simple by Mathlib's prime-cardinality
criterion `isSimpleGroup_of_prime_card`; the alternating carrier is simple by Mathlib's
`alternatingGroup.isSimpleGroup`, which applies because `Fin n` has `n ≥ 5` elements. In both cases
the only input is the proof field recorded by the index itself.

## Main results

* `TauCeti.CFSGIndex.finite_cyclic`, `TauCeti.CFSGIndex.isSimpleGroup_cyclic`: the carrier of a
  cyclic index is finite and simple, and `TauCeti.CFSGIndex.natCard_cyclic` records its order `p`.
* `TauCeti.CFSGIndex.finite_alternating`, `TauCeti.CFSGIndex.isSimpleGroup_alternating`: the
  carrier of an alternating index is finite and simple.
-/

public section

namespace TauCeti.CFSGIndex

variable (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 5 ≤ n)

/-- The carrier of the cyclic index `C_p` has exactly `p` elements. -/
theorem natCard_cyclic : Nat.card (cyclic p hp).Group = p :=
  (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)

/-- **The carrier of a cyclic index is finite.** -/
instance finite_cyclic : Finite (cyclic p hp).Group :=
  Nat.finite_of_card_ne_zero <| by rw [natCard_cyclic]; exact hp.ne_zero

/-- **The carrier of a cyclic index is simple**, because its order is the prime `p`. -/
theorem isSimpleGroup_cyclic : IsSimpleGroup (cyclic p hp).Group :=
  isSimpleGroup_of_prime_card (hp := ⟨hp⟩) (natCard_cyclic p hp)

/-- **The carrier of an alternating index is finite.** Instance search already finds this through
Mathlib's finiteness of `alternatingGroup (Fin n)`; the named statement is the alternating case of
the finiteness of every listed carrier. -/
theorem finite_alternating : Finite (alternating n hn).Group :=
  inferInstance

/-- **The carrier of an alternating index is simple**, because its degree is at least five. -/
theorem isSimpleGroup_alternating : IsSimpleGroup (alternating n hn).Group :=
  alternatingGroup.isSimpleGroup (by simpa using hn)

end TauCeti.CFSGIndex

end
