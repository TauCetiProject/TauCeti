/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Ring

/-!
# Moduli of scalar families up to a norm power

For a family of positive integers `N`, the relation `HasNormUpToPower N c f` allows the squared
norm of `c` to differ from `f²` by a constant times a fixed integral power of `N`. It is preserved
by multiplication and inversion, even for families that vanish. At a reference point where both
`N` and `f` are `1` and `c` is nonzero, division by the reference scalar removes the constant.

This relation lets one track the moduli of scalar factors in chain Gram identities while leaving
the exponents of the norms of the twisting moduli unspecified.

## References

* `New.Data.HasAbsUpToNormPower` and `New.Data.HasAbsUpToNormPower.exists_norm_div_eq` in
  `grh/src/New/Determinant/Chain/Moduli.lean` of <https://github.com/lsernau/grh-lean>,
  revision `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open scoped BigOperators

namespace TauCeti

/-- The squared norms of `c` agree with the squares of `f` up to one real factor and one
integral power of the positive integer family `N`. Both witnesses are uniform in the index. -/
def HasNormUpToPower {ι 𝕜 : Type*} [Norm 𝕜] (N : ι → ℕ+) (c : ι → 𝕜) (f : ι → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℤ), ∀ i, ‖c i‖ ^ 2 = C * ((N i : ℕ) : ℝ) ^ k * f i ^ 2

variable {ι 𝕜 : Type*} {N : ι → ℕ+}

/-- The defining squared norm identity of `HasNormUpToPower`. -/
theorem hasNormUpToPower_iff [Norm 𝕜] {c : ι → 𝕜} {f : ι → ℝ} :
    HasNormUpToPower N c f ↔
      ∃ (C : ℝ) (k : ℤ), ∀ i, ‖c i‖ ^ 2 = C * ((N i : ℕ) : ℝ) ^ k * f i ^ 2 :=
  Iff.rfl

namespace HasNormUpToPower

/-- If compensating the squared norm by one integral power of `N` makes it constant, its
modulus up to a power of `N` is `1`. -/
theorem of_norm_sq_mul_zpow_eq_const [Norm 𝕜] {c : ι → 𝕜} {C : ℝ} {k : ℤ}
    (h : ∀ i, ‖c i‖ ^ 2 * ((N i : ℕ) : ℝ) ^ k = C) : HasNormUpToPower N c 1 := by
  refine ⟨C, -k, fun i ↦ ?_⟩
  have hpow : ((N i : ℕ) : ℝ) ^ k ≠ 0 := by positivity
  simpa [zpow_neg, div_eq_mul_inv] using (eq_div_iff hpow).2 (h i)

/-- A constant family has modulus `1` up to a power of `N`. -/
theorem const [Norm 𝕜] (N : ι → ℕ+) (a : 𝕜) : HasNormUpToPower N (fun _ ↦ a) 1 :=
  ⟨‖a‖ ^ 2, 0, by simp⟩

/-- The constant family `1` has modulus `1` up to a power of `N`. -/
@[simp] theorem one [Norm 𝕜] [One 𝕜] (N : ι → ℕ+) : HasNormUpToPower N (1 : ι → 𝕜) 1 :=
  const N 1

variable {c c' : ι → 𝕜} {f f' : ι → ℝ}

/-- The moduli of pointwise products multiply, with the exponents adding. -/
theorem mul [Norm 𝕜] [Mul 𝕜] [NormMulClass 𝕜]
    (h : HasNormUpToPower N c f) (h' : HasNormUpToPower N c' f') :
    HasNormUpToPower N (c * c') (f * f') := by
  obtain ⟨C, k, hk⟩ := hasNormUpToPower_iff.mp h
  obtain ⟨C', k', hk'⟩ := hasNormUpToPower_iff.mp h'
  refine ⟨C * C', k + k', fun i ↦ ?_⟩
  have hNi : ((N i : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Pi.mul_apply, norm_mul, mul_pow, hk, hk', zpow_add₀ hNi]
  ring

section DivisionRing

variable [NormedDivisionRing 𝕜]

/-- Pointwise inversion inverts the modulus, with the exponent negated. Inversion at zeros
uses the ordinary field convention `0⁻¹ = 0`. -/
theorem inv (h : HasNormUpToPower N c f) : HasNormUpToPower N c⁻¹ f⁻¹ := by
  obtain ⟨C, k, hk⟩ := hasNormUpToPower_iff.mp h
  refine ⟨C⁻¹, -k, fun i ↦ ?_⟩
  simp [norm_inv, inv_pow, hk, zpow_neg, mul_comm, mul_left_comm]

/-- A nonzero reference value at which `N` and `f` both equal `1` removes the constant factor.
The conclusion uses `|f i|` because `f` may take negative values. The exponent is `k / 2`
for an integer `k`. -/
theorem exists_norm_div_eq (h : HasNormUpToPower N c f) {i₀ : ι} (hN : N i₀ = 1)
    (hf : f i₀ = 1) (hc : c i₀ ≠ 0) :
    ∃ k : ℤ, ∀ i, ‖c i / c i₀‖ = ((N i : ℕ) : ℝ) ^ ((k : ℝ) / 2) * |f i| := by
  obtain ⟨C, k, hk⟩ := hasNormUpToPower_iff.mp h
  have hC : ‖c i₀‖ ^ 2 = C := by simpa [hN, hf] using hk i₀
  refine ⟨k, fun i ↦ ?_⟩
  have hsq : (‖c i‖ / ‖c i₀‖) ^ 2 = ((N i : ℕ) : ℝ) ^ k * f i ^ 2 := by
    rw [div_pow, hk i, ← hC]
    rw [mul_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))]
  have hNi : 0 ≤ ((N i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpower : √(((N i : ℕ) : ℝ) ^ k) = ((N i : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
    simp only [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_intCast_mul hNi, one_mul]
  simpa only [Real.sqrt_sq (by positivity : 0 ≤ ‖c i‖ / ‖c i₀‖),
    Real.sqrt_mul (zpow_nonneg hNi k), hpower, Real.sqrt_sq_eq_abs, norm_div] using
    congrArg Real.sqrt hsq

end DivisionRing

/-- A finite product of scalar families has modulus equal to the product of their moduli. -/
theorem prod [Norm 𝕜] [CommMonoid 𝕜] [NormMulClass 𝕜] {κ : Type*} {s : Finset κ}
    {c : κ → ι → 𝕜} {f : κ → ι → ℝ} (h : ∀ j ∈ s, HasNormUpToPower N (c j) (f j)) :
    HasNormUpToPower N (∏ j ∈ s, c j) (∏ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).mul (ih fun k hk ↦ h k (Finset.mem_insert_of_mem hk))

end HasNormUpToPower

end TauCeti
