/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Ideals under the pointwise action of a group

When a group `M` acts on a semiring `R` by ring automorphisms, the pointwise translate `g • I` of
an ideal `I` is its image under the ring isomorphism `MulSemiringAction.toRingEquiv M R g` and its
preimage under `g⁻¹`. In particular, the action permutes maximal ideals, giving the maximal-ideal
companion of Mathlib's `Ideal.IsPrime.smul`.

## Main results

* `Ideal.pointwise_smul_eq_map_toRingEquiv`: `g • I = I.map (MulSemiringAction.toRingEquiv M R g)`.
* `Ideal.IsMaximal.smul`: the translate of a maximal ideal is maximal.
-/

public section

open scoped Pointwise

namespace Ideal

variable {M R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]

/-- The pointwise translate `g • I` of an ideal under a group action is its image under the
corresponding ring isomorphism `MulSemiringAction.toRingEquiv M R g`. -/
theorem pointwise_smul_eq_map_toRingEquiv {g : M} (I : Ideal R) :
    g • I = I.map (MulSemiringAction.toRingEquiv M R g) := by
  ext x
  rw [mem_pointwise_smul_iff_inv_smul_mem, ← symm_apply_mem_of_equiv_iff,
    MulSemiringAction.toRingEquiv_apply_symm_apply]

/-- **Translates of maximal ideals are maximal.** The translate `g • I` is the preimage of `I`
under a ring automorphism, so it is maximal whenever `I` is. -/
instance IsMaximal.smul {I : Ideal R} [I.IsMaximal] (g : M) : (g • I).IsMaximal := by
  rw [I.pointwise_smul_eq_comap]
  infer_instance

end Ideal
