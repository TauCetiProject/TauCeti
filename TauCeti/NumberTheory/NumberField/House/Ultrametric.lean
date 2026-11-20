/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.NumberField.House

import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm

/-!
# Liouville's inequality at an ultrametric place

Let `K` be a number field of degree `D` and `σ : K →+* L` an embedding into an algebraically
closed field `L` with an ultrametric norm. A nonzero algebraic integer `x ∈ K` satisfies
`1 ≤ ⌈x⌉ ^ D ‖σ x‖`, where `⌈x⌉` is the house of `x`, provided nonzero integers `n` satisfy
`1 ≤ |n| ‖n‖` in `L`. This holds in every normed field over `ℚ_[p]`, for instance in `ℂ_[p]`
(`Padic.one_le_abs_mul_norm_intCast`, `TauCeti.norm_intCast_eq_norm_padic`).

The proof is that of the archimedean inequality `NumberField.one_le_norm_mul_house_pow`: the field
norm `N` of `x` is a nonzero integer with `|N| ≤ ⌈x⌉ ^ D`, and in `L` it is the product of the
conjugates of `x`. Every conjugate is an algebraic integer, so it has norm at most `1` in `L`
(`IsUltrametricDist.norm_le_one_of_isIntegral`), and `‖N‖ ≤ ‖σ x‖`. Unlike at an archimedean place
the exponent is `D`, not `D - 1`: for `K = ℚ` and `x = p`, `‖p‖ = p⁻¹` in `ℚ_[p]`.

The second form allows a denominator: if `δ ^ a x` is a nonzero algebraic integer of house at most
`H` for a natural number `δ`, then `1 ≤ H ^ D ‖σ x‖`, since `‖δ‖ ≤ 1` in `L`. This is the form in
which Liouville's inequality is applied to numbers of known size in transcendence proofs at a
`p`-adic place, such as Baker's method over `ℂ_p`.

## Main results

* `NumberField.one_le_house_pow_mul_norm_embedding_of_isUltrametricDist`: Liouville's inequality
  `1 ≤ ⌈x⌉ ^ D ‖σ x‖` for a nonzero algebraic integer `x`.
* `NumberField.one_le_pow_mul_norm_embedding_of_isUltrametricDist`: Liouville's inequality
  `1 ≤ H ^ D ‖σ x‖` when `δ ^ a x` is a nonzero algebraic integer of house at most `H`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 2.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000,
  Proposition 3.14.
* M. Karatarakis, formalisation of Baker's theorem over `ℂ_p`, `baker-padic` branch of
  `mkaratarakis/mathlib4`, file `Mathlib/NumberTheory/Transcendental/Baker/Padic/Liouville.lean`
  (Apache 2.0), which proves the integer bound and this inequality for `ℂ_[p]`.
-/

public section

open Module
open scoped NumberField

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [NormedField L] [IsUltrametricDist L]
  [IsAlgClosed L]

/-- **Liouville's inequality at an ultrametric place.** Let `L` be an algebraically closed field
with an ultrametric norm in which every nonzero integer `n` satisfies `1 ≤ |n| ‖n‖`. Then a nonzero
algebraic integer `x` of a number field `K` of degree `D` satisfies `1 ≤ ⌈x⌉ ^ D ‖σ x‖` for every
embedding `σ : K →+* L`. -/
theorem one_le_house_pow_mul_norm_embedding_of_isUltrametricDist
    (hL : ∀ n : ℤ, n ≠ 0 → 1 ≤ |(n : ℝ)| * ‖(n : L)‖) {x : K} (hx : IsIntegral ℤ x)
    (hx0 : x ≠ 0) (σ : K →+* L) : 1 ≤ house x ^ finrank ℚ K * ‖σ x‖ := by
  classical
  have : CharZero L := (RingHom.charZero_iff σ.injective).1 inferInstance
  -- The field norm of `x` is a nonzero integer `N` with `|N| ≤ ⌈x⌉ ^ D`.
  set y : 𝓞 K := ⟨x, hx⟩
  set N := Algebra.norm ℤ y
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.2 fun h ↦ hx0 congr(($h : K))
  have hNx : Algebra.norm ℚ x = N := (Algebra.coe_norm_int y).symm
  have hNle : |(N : ℝ)| ≤ house x ^ finrank ℚ K :=
    RingOfIntegers.abs_norm_le_pow _ fun τ ↦ norm_embedding_le_house x τ
  -- In `L`, `N` is the product of the conjugates of `x`, all of norm at most `1` except `σ x`.
  set σ' := σ.toRatAlgHom
  have hNσ : ‖(N : L)‖ ≤ ‖σ x‖ := calc
    ‖(N : L)‖ = ‖σ' x * ∏ τ ∈ Finset.univ.erase σ', τ x‖ := by
      rw [Finset.mul_prod_erase _ (· x) (Finset.mem_univ σ'), ← Algebra.norm_eq_prod_embeddings,
        hNx, map_intCast]
    _ ≤ ‖σ' x‖ * 1 := by
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun τ _ ↦
        IsUltrametricDist.norm_le_one_of_isIntegral (hx.map (τ : K →+* L).toIntAlgHom))
        (norm_nonneg _)
    _ = ‖σ x‖ := by rw [mul_one, RingHom.toRatAlgHom_apply]
  calc (1 : ℝ) ≤ |(N : ℝ)| * ‖(N : L)‖ := hL N hN
    _ ≤ house x ^ finrank ℚ K * ‖σ x‖ :=
      mul_le_mul hNle hNσ (norm_nonneg _) (pow_nonneg (house_nonneg x) _)

/-- **Liouville's inequality at an ultrametric place, for a number of known size.** Let `L` be an
algebraically closed field with an ultrametric norm in which every nonzero integer `n` satisfies
`1 ≤ |n| ‖n‖`, and let `K` be a number field of degree `D`. If `x ∈ K` is nonzero and `δ ^ a x` is
an algebraic integer of house at most `H` for a nonzero natural number `δ`, then `1 ≤ H ^ D ‖σ x‖`
for every embedding `σ : K →+* L`. -/
theorem one_le_pow_mul_norm_embedding_of_isUltrametricDist
    (hL : ∀ n : ℤ, n ≠ 0 → 1 ≤ |(n : ℝ)| * ‖(n : L)‖) {δ a : ℕ} (hδ : δ ≠ 0) {x : K}
    (hx0 : x ≠ 0) {H : ℝ} (hint : IsIntegral ℤ ((δ : K) ^ a * x))
    (hH : house ((δ : K) ^ a * x) ≤ H) (σ : K →+* L) : 1 ≤ H ^ finrank ℚ K * ‖σ x‖ := by
  have hy0 : (δ : K) ^ a * x ≠ 0 := mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hδ)) hx0
  -- The factor `δ ^ a` has norm at most `1` in `L`.
  have hσ : ‖σ ((δ : K) ^ a * x)‖ ≤ ‖σ x‖ := by
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one L δ))
  calc (1 : ℝ) ≤ house ((δ : K) ^ a * x) ^ finrank ℚ K * ‖σ ((δ : K) ^ a * x)‖ :=
        one_le_house_pow_mul_norm_embedding_of_isUltrametricDist hL hint hy0 σ
    _ ≤ H ^ finrank ℚ K * ‖σ x‖ :=
        mul_le_mul (pow_le_pow_left₀ (house_nonneg _) hH _) hσ (norm_nonneg _)
          (pow_nonneg ((house_nonneg _).trans hH) _)

end NumberField
