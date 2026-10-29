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
# Finiteness and simplicity of the elementary CFSG entries

The cyclic and alternating entries on the CFSG list are finite simple groups. These results
refer to the exact `CFSGIndex.Group` carriers: `Multiplicative (ZMod p)` for a prime `p`, and
`alternatingGroup (Fin n)` for `5 ≤ n`.

Finiteness comes from the existing instances. Simplicity uses Mathlib's prime-order criterion
and its simplicity theorem for alternating groups of degree at least five. In particular, the
prime two and degree five are included.
-/

public section

namespace TauCeti.CFSGIndex

/-- The cyclic entry of the CFSG list is finite because its prime parameter is nonzero. -/
theorem finite_cyclic (p : ℕ) (hp : p.Prime) : Finite (cyclic p hp).Group := by
  have : NeZero p := ⟨hp.ne_zero⟩
  change Finite (Multiplicative (ZMod p))
  infer_instance

/-- The cyclic entry of the CFSG list is simple, including the group of order two. -/
theorem isSimpleGroup_cyclic (p : ℕ) (hp : p.Prime) :
    IsSimpleGroup (cyclic p hp).Group := by
  have : Fact p.Prime := ⟨hp⟩
  apply isSimpleGroup_of_prime_card (p := p)
  change Nat.card (Multiplicative (ZMod p)) = p
  simp [Nat.card_eq_fintype_card]

/-- Every alternating entry of the CFSG list is a finite permutation group. -/
theorem finite_alternating (n : ℕ) (hn : 5 ≤ n) : Finite (alternating n hn).Group := by
  change Finite (alternatingGroup (Fin n))
  infer_instance

/-- Every alternating entry of the CFSG list is simple, including degree five. -/
theorem isSimpleGroup_alternating (n : ℕ) (hn : 5 ≤ n) :
    IsSimpleGroup (alternating n hn).Group := by
  change IsSimpleGroup (alternatingGroup (Fin n))
  exact alternatingGroup.isSimpleGroup (by simpa using hn)

end TauCeti.CFSGIndex
