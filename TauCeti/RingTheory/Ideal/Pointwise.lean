/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Maximal ideals under the pointwise action

A group acting on a ring by ring automorphisms permutes its maximal ideals: the translate
`g • I` is the preimage of `I` under the ring automorphism `g⁻¹`. This is the maximal-ideal
companion of Mathlib's `Ideal.IsPrime.smul`.

## Main results

* `Ideal.IsMaximal.smul`: the translate of a maximal ideal is maximal.
-/

public section

open scoped Pointwise

namespace Ideal

variable {M R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]

/-- **Translates of maximal ideals are maximal.** The translate `g • I` is the preimage of `I`
under a ring automorphism, so it is maximal whenever `I` is. -/
instance IsMaximal.smul {I : Ideal R} [I.IsMaximal] (g : M) : (g • I).IsMaximal := by
  rw [I.pointwise_smul_eq_comap]
  infer_instance

end Ideal
