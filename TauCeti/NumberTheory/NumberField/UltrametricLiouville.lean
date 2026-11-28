/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.NumberTheory.NumberField.House

import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Liouville's inequality at an ultrametric place

Let `K` be a number field of degree `d`, let `c` be a nonzero integer and let `x ∈ K` be nonzero
with `c x` an algebraic integer of house at most `H`. For every ring homomorphism `σ : K → L` into
an ultrametric normed field `L` in which every integer `n` has norm at least `1 / |n|`,

  `1 ≤ H ^ d * ‖σ x‖`.

This rests on the norm `N` of `c x` from `K` to `ℚ`: a nonzero integer with `|N| ≤ H ^ d` that is
a multiple of `c x` in the ring of integers of `K`. The exponent is `d`, not the `d - 1` of the
archimedean inequality (`TauCeti.one_le_house_pow_mul_norm_of_mem_rootSet`), and the bound is
attained by `x = p` in `ℚ_p`.

Every normed field over `ℚ_p`, such as `ℂ_p`, satisfies the hypotheses on `L`: it is ultrametric
(Mathlib's `IsUltrametricDist.of_normedAlgebra`) and integers satisfy the norm bound
(`TauCeti.inv_abs_le_norm_intCast`). The inequality is the lower bound for nonzero algebraic
values that p-adic transcendence arguments set against analytic upper bounds.

## Main results

* `NumberField.one_le_house_pow_mul_norm_of_isUltrametricDist`: Liouville's inequality
  `1 ≤ H ^ d * ‖σ x‖` in an ultrametric normed field.
* `NumberField.one_le_house_pow_mul_norm_of_normedAlgebra`: the same inequality in every normed
  field over `ℚ_p`.
* `RingHom.inv_pow_le_norm_sub_prod_pow`: a uniform separation bound for distinct monomials
  of bounded total degree whose factors have a common denominator and house bound.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 1.
-/

public section

open Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Liouville's inequality at an ultrametric place.** Let `L` be an ultrametric normed field in
which every integer `n` has norm at least `1 / |n|`. If `c ≠ 0` is an integer and `x ∈ K` is
nonzero with `c x` an algebraic integer of house at most `H`, then `1 ≤ H ^ [K : ℚ] * ‖σ x‖` for
every ring homomorphism `σ : K → L`. -/
theorem one_le_house_pow_mul_norm_of_isUltrametricDist {L : Type*} [NormedField L]
    [IsUltrametricDist L] (hL : ∀ n : ℤ, (|n| : ℝ)⁻¹ ≤ ‖(n : L)‖) {c : ℤ} (hc : c ≠ 0)
    {x : K} (hx : x ≠ 0) (hint : IsIntegral ℤ ((c : K) * x)) {H : ℝ}
    (hH : house ((c : K) * x) ≤ H) (σ : K →+* L) :
    1 ≤ H ^ finrank ℚ K * ‖σ x‖ := by
  obtain ⟨y, hyK⟩ : ∃ y : 𝓞 K, (y : K) = c * x := ⟨⟨_, hint⟩, rfl⟩
  have hy : y ≠ 0 := by
    rw [ne_eq, RingOfIntegers.ext_iff, hyK]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hc) hx
  set N := Algebra.norm ℤ y
  have hN : N ≠ 0 := by simpa [N] using hy
  -- `y = c x` divides its norm `N` in `𝓞 K`, so in `L` the integer `N` is `c σ(x)` times the
  -- image of an algebraic integer, which has norm at most `1`.
  obtain ⟨z, hz⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 K) y
  rw [Algebra.intNorm_eq_norm] at hz
  have hNK : (N : K) = c * x * z := by
    simpa [hyK] using congrArg ((↑) : 𝓞 K → K) hz
  have hz1 : ‖σ (z : K)‖ ≤ 1 :=
    IsUltrametricDist.norm_le_one_of_isIntegral (fun _ _ _ ↦ norm_pow _ _)
      ((RingOfIntegers.isIntegral_coe z).map σ.toIntAlgHom)
  have hNσ : ‖(N : L)‖ ≤ ‖σ x‖ := by
    rw [← map_intCast σ, hNK, map_mul, map_mul, map_intCast, norm_mul, norm_mul]
    calc ‖(c : L)‖ * ‖σ x‖ * ‖σ (z : K)‖ ≤ 1 * ‖σ x‖ * 1 := by
          gcongr
          exact IsUltrametricDist.norm_intCast_le_one L c
      _ = ‖σ x‖ := by ring
  -- In `ℝ`, the integer `N` is the norm of `c x`, which is bounded by its house.
  have hNH : |(N : ℝ)| ≤ H ^ finrank ℚ K :=
    RingOfIntegers.abs_norm_le_pow y fun σ ↦ (norm_embedding_le_house _ σ).trans (hyK ▸ hH)
  have hN0 : (0 : ℝ) < |(N : ℝ)| := by exact_mod_cast abs_pos.mpr hN
  calc (1 : ℝ) = |(N : ℝ)| * |(N : ℝ)|⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
    _ ≤ H ^ finrank ℚ K * ‖σ x‖ :=
      mul_le_mul hNH ((hL N).trans hNσ) (by positivity) (hN0.le.trans hNH)

/-- **Liouville's inequality over `ℚ_p`.** If `c ≠ 0` is an integer and `x ∈ K` is nonzero with
`c x` an algebraic integer of house at most `H`, then `1 ≤ H ^ [K : ℚ] * ‖σ x‖` for every ring
homomorphism `σ` from `K` to a normed field over `ℚ_p`, such as `ℂ_p`. -/
theorem one_le_house_pow_mul_norm_of_normedAlgebra (p : ℕ) [Fact p.Prime] {L : Type*}
    [NormedField L] [NormedAlgebra ℚ_[p] L] {c : ℤ} (hc : c ≠ 0) {x : K} (hx : x ≠ 0)
    (hint : IsIntegral ℤ ((c : K) * x)) {H : ℝ} (hH : house ((c : K) * x) ≤ H) (σ : K →+* L) :
    1 ≤ H ^ finrank ℚ K * ‖σ x‖ :=
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  one_le_house_pow_mul_norm_of_isUltrametricDist (TauCeti.inv_abs_le_norm_intCast p) hc hx hint
    hH σ

open Finset in
/-- **Separation of algebraic monomials at an ultrametric place.** Suppose the numbers `δ * α i`
are integral of house at most `G`, with `0 < δ ≤ G`. Two distinct products of the `α i` of total
degree at most `N` have distance at least `((2 * G ^ N) ^ [K : ℚ])⁻¹` after embedding into an
ultrametric field in which every nonzero integer has norm at least its inverse absolute value. -/
theorem _root_.RingHom.inv_pow_le_norm_sub_prod_pow {L : Type*} [NormedField L]
    [IsUltrametricDist L] (σ : K →+* L) (hL : ∀ n : ℤ, (|n| : ℝ)⁻¹ ≤ ‖(n : L)‖)
    {ι : Type*} (s : Finset ι) {α : ι → K} {δ N : ℕ} {G : ℝ} (hδ : δ ≠ 0)
    (hG : (δ : ℝ) ≤ G) (hint : ∀ i ∈ s, IsIntegral ℤ ((δ : K) * α i))
    (hh : ∀ i ∈ s, house ((δ : K) * α i) ≤ G) {a b : ι → ℕ}
    (ha : ∑ i ∈ s, a i ≤ N) (hb : ∑ i ∈ s, b i ≤ N)
    (hne : ∏ i ∈ s, α i ^ a i ≠ ∏ i ∈ s, α i ^ b i) :
    ((2 * G ^ N) ^ finrank ℚ K)⁻¹ ≤
      ‖σ (∏ i ∈ s, α i ^ a i) - σ (∏ i ∈ s, α i ^ b i)‖ := by
  have size (t : ι → ℕ) (ht : ∑ i ∈ s, t i ≤ N) :
      IsIntegral ℤ ((δ : K) ^ N * ∏ i ∈ s, α i ^ t i) ∧
      house ((δ : K) ^ N * ∏ i ∈ s, α i ^ t i) ≤ G ^ N := by
    have hi := IsIntegral.pow_sum_mul_prod (s := s) fun i hi ↦
      (mul_pow (δ : K) (α i) (t i)) ▸ (hint i hi).pow (t i)
    have h := house_pow_sum_mul_prod_le (s := s) fun i hi ↦
      (mul_pow (δ : K) (α i) (t i)) ▸ house_pow_le_of_le (hh i hi) (t i)
    rw [prod_pow_eq_pow_sum] at h
    exact ⟨hi.pow_mul_of_le (isIntegral_natCast δ) ht,
      (house_natCast_pow_mul_le_of_le ht hG h).trans_eq (by rw [← pow_add, Nat.sub_add_cancel ht])⟩
  obtain ⟨hia, hha⟩ := size a ha
  obtain ⟨hib, hhb⟩ := size b hb
  have hGpos : 0 < G := (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hδ)).trans_le hG
  rw [inv_le_iff_one_le_mul₀ (by positivity), mul_comm, ← map_sub]
  apply one_le_house_pow_mul_norm_of_isUltrametricDist hL (c := (δ : ℤ) ^ N)
    (pow_ne_zero _ (by exact_mod_cast hδ)) (sub_ne_zero.mpr hne)
  · simpa only [Int.cast_pow, Int.cast_natCast, mul_sub] using hia.sub hib
  · simp only [Int.cast_pow, Int.cast_natCast, mul_sub, house, map_sub]
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add hha hhb)

/-! ### Examples -/

/-- The inequality is sharp: in `ℚ_p`, the integer `x = p` of house `p` has norm `p⁻¹`, so that
`1 ≤ p ^ 1 * ‖p‖` holds with equality. -/
example (p : ℕ) [Fact p.Prime] : (p : ℝ) ^ finrank ℚ ℚ * ‖(p : ℚ_[p])‖ = 1 := by
  rw [finrank_self, pow_one, Padic.norm_p,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]

end NumberField
