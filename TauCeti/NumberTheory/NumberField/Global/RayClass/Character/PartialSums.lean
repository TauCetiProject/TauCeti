/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Sum
import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic

/-!
# Cancellation in the partial sums of a nontrivial ray class character

Let `𝔪` be a modulus of a number field `K` and `χ` a nontrivial ray class character of `𝔪`.
This file shows that the sum of `χ` over the nonzero integral ideals prime to `𝔪` of norm at
most `x` is `O(x ^ (1 - 1 / [K : ℚ]))`, in explicit form and in the form `O(x ^ (1 - δ))` for
some `δ > 0`.

## Main results

* `TauCeti.GlobalNumberFields.isBigO_rayClassCharacterPartialSum`: the partial sums of a
  nontrivial ray class character are `O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.GlobalNumberFields.rayClassCharacter_partialSums`: the partial sums of a nontrivial
  ray class character are `O(x ^ (1 - δ))` for some `δ > 0`.
-/

public section

open Asymptotics Filter

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **Cancellation of a nontrivial ray class character, with an explicit power saving.**  The
partial sums of a nontrivial ray class character over the integral ideals of norm at most `x` are
`O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem isBigO_rayClassCharacterPartialSum (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (hχ : χ ≠ 1) :
    (fun x : ℝ => rayClassCharacterPartialSum 𝔪 χ x) =O[atTop]
      (fun x : ℝ => x ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) := by
  have : Fintype (RayClassGroup 𝔪) := Fintype.ofFinite _
  -- the character values sum to zero, so the common main term drops out
  have hχ0 : ∑ c : RayClassGroup 𝔪, (χ c : ℂ) = 0 :=
    sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) fun h ↦ hχ <|
      MonoidHom.ext fun c ↦ Units.ext (DFunLike.congr_fun h c)
  -- regrouped by ray class, the partial sum is the `χ`-weighted combination of the class counts;
  -- every class has the same main term `rayClassIdealMainTerm 𝔪 * x`, so only the error terms of
  -- the class counts remain
  have hsum (x : ℝ) : rayClassCharacterPartialSum 𝔪 χ x = ∑ c : RayClassGroup 𝔪,
      (χ c : ℂ) * (((rayClassIdealCountingFunction 𝔪 c x : ℝ) -
        rayClassIdealMainTerm 𝔪 * x : ℝ) : ℂ) := by
    simp [rayClassCharacterPartialSum_eq_sum 𝔪 χ x, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hχ0]
  simp_rw [hsum]
  exact IsBigO.fun_sum fun c _ ↦ (Complex.isBigO_ofReal_left.mpr
    (isBigO_rayClassIdealCountingFunction_sub 𝔪 c)).const_mul_left _

/-- **Cancellation of a nontrivial ray class character.**  The partial sums of a nontrivial ray
class character over the integral ideals of norm at most `x` are `O(x ^ (1 - δ))` for some
`δ > 0`, with the comparison function coerced to `ℂ`.  For the explicit saving
`δ = 1 / [K : ℚ]` against a real comparison function, use
`isBigO_rayClassCharacterPartialSum`. -/
theorem rayClassCharacter_partialSums (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (fun x : ℝ => rayClassCharacterPartialSum 𝔪 χ x) =O[atTop]
        (fun x : ℝ => ((x ^ (1 - δ) : ℝ) : ℂ)) :=
  ⟨(Module.finrank ℚ K : ℝ)⁻¹, by simp [Module.finrank_pos],
    Complex.isBigO_ofReal_right.mpr (isBigO_rayClassCharacterPartialSum 𝔪 χ hχ)⟩

end TauCeti.GlobalNumberFields
