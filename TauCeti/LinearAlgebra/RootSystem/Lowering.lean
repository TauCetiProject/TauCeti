/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Height

/-!
# Lowering positive roots by simple reflections

When the root index type is finite, the coefficient ring is a domain and the pairing is reduced,
a positive root that is not simple can be lowered by a simple reflection while remaining positive
and strictly decreasing its height relative to a root-pairing base.

## Main results

* `RootPairing.Base.IsPos.exists_mem_support_height_reflectionPerm_lt` gives the positive-root
  lowering step for a nonsimple positive root.

## References

The argument follows Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.

Mathlib already carries out this lowering step inside the proof of
`RootPairing.Base.IsPos.induction_on_reflect`, where it is packaged as a strong induction
principle rather than exposed. The theorem below states it in its own right, using the height
computation `RootPairing.Base.height_reflectionPerm_lt_iff`.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} {b : P.Base} [CharZero R] [P.IsCrystallographic]

/-- A nonsimple positive root admits a simple reflection that remains positive and has strictly
smaller height. This is the positive-root lowering step used by induction on height. -/
theorem IsPos.exists_mem_support_height_reflectionPerm_lt [Finite ι] [IsDomain R]
    [P.IsReduced] {j : ι} (hj : b.IsPos j) (hj' : j ∉ b.support) :
    ∃ i ∈ b.support, b.IsPos (P.reflectionPerm i j) ∧
      b.height (P.reflectionPerm i j) < b.height j := by
  -- Mathlib provides the transposed pairing; finiteness makes the two pairings have the same sign.
  obtain ⟨i, hi, hpair⟩ := hj.exists_mem_support_pos_pairingIn
  refine ⟨i, hi, hj.reflectionPerm hi (ne_of_mem_of_not_mem hi hj').symm, ?_⟩
  rwa [height_reflectionPerm_lt_iff b hi, P.zero_lt_pairingIn_iff']

end RootPairing.Base
