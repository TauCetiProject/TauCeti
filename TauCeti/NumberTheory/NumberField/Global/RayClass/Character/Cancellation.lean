/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Sum
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.PartialSums

/-!
# Cancellation for the ideal weight of a ray class character

The ideal partial sums of the unitary weight `χ.toUnitaryIdealWeight` of a ray class character
`χ` of `𝔪` are the character sums `rayClassCharacterPartialSum 𝔪 χ`: the weight vanishes on the
ideals that are not prime to `𝔪` and is `χ` of the ray class on the others. For a nontrivial
character those sums are `O(x ^ (1 - 1 / [K : ℚ]))`, which is the cancellation hypothesis
`TauCeti.HasCancellation` of the Arithmetic Dirichlet Series library. Through
`TauCeti.differentiableOn_continuedLFunctionOfWeight` it continues the L-series of a nontrivial
ray class character holomorphically to `Re s > 1 - 1 / [K : ℚ]`, a half-plane containing the
line `Re s = 1`.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.idealSummatory_toUnitaryIdealWeight`: the ideal
  partial sums of the weight are the character sums.
* `TauCeti.GlobalNumberFields.RayClassCharacter.hasCancellation_toUnitaryIdealWeight`: the weight
  of a nontrivial ray class character has cancellation.

## Implementation notes

The reindexing proof of `idealSummatory_toUnitaryIdealWeight` is adapted from the private lemma
`idealSummatory_restrictAway_galoisCharacterUnitaryWeight` formerly in
`TauCeti/NumberTheory/Chebotarev/GaloisCharacter/Cyclotomic/Cancellation.lean`, which now derives
its cancellation from `hasCancellation_toUnitaryIdealWeight` instead.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **The ideal partial sums of a ray class weight are the character sums.** Summing the unitary
weight of `χ` over the nonzero ideals of norm at most `x` gives the sum of `χ` over the integral
ideals prime to `𝔪` of norm at most `x`, since the weight vanishes on the other ideals. -/
theorem idealSummatory_toUnitaryIdealWeight (χ : RayClassCharacter 𝔪) (x : ℝ) :
    idealSummatory K χ.toUnitaryIdealWeight.toIdealArithmeticFunction x =
      rayClassCharacterPartialSum 𝔪 χ x := by
  classical
  have hmem (J : Ideal (𝓞 K)) : J ∈ integralIdealsPrimeTo 𝔪 ↔ J.IsPrimeTo 𝔪.support :=
    NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo
  let e : integralIdealsPrimeTo 𝔪 → (Ideal (𝓞 K))⁰ := fun I ↦
    ⟨I, mem_nonZeroDivisors_of_ne_zero ((hmem I).mp I.2).ne_bot⟩
  have hsum : rayClassCharacterPartialSum 𝔪 χ x =
      ∑ I ∈ normLE (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x,
        (χ.onIdeals I : ℂ) := by
    rw [rayClassCharacterPartialSum_def, ← finsum_mem_coe_finset, coe_normLE]
    exact finsum_set_coe_eq_finsum_mem (f := fun I ↦ (χ.onIdeals I : ℂ))
      {I : integralIdealsPrimeTo 𝔪 | Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x}
  -- The ideals prime to `𝔪` embed into the nonzero ideals; off the image the weight is `0`.
  rw [hsum, idealSummatory_apply]
  refine (Finset.sum_of_injOn e (fun I _ J _ h ↦ Subtype.ext (by simpa [e] using h))
    (fun I hI ↦ by simpa [e] using hI) (fun J hJ hJe ↦ ?_) (fun I _ ↦ ?_)).symm
  · have hJ𝔪 : ¬ (J : Ideal (𝓞 K)).IsPrimeTo 𝔪.support :=
      fun hJ𝔪 ↦ hJe ⟨⟨J, (hmem J).mpr hJ𝔪⟩, by simpa using hJ, rfl⟩
    simp [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hJ𝔪]
  · simp [e, toMultiplicativeIdealWeight_apply_of_isPrimeTo χ ((hmem I).mp I.2)]

/-- **Cancellation for a nontrivial ray class character.** The unitary weight of a nontrivial
ray class character has ideal partial sums `O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem hasCancellation_toUnitaryIdealWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) :
    HasCancellation χ.toUnitaryIdealWeight := by
  simpa [hasCancellation_iff_isBigO, idealSummatory_toUnitaryIdealWeight] using
    isBigO_rayClassCharacterPartialSum 𝔪 χ hχ

end TauCeti.GlobalNumberFields.RayClassCharacter
