/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic

/-!
# Products of twisted values and height transport

This file contains the algebraic part of the twisted-ratio calculation. A pointwise formula for
values indexed by `1 ≤ j ≤ z` gives a product formula with the power `q ^ (z ^ 2)`, since
the exponents `2 * j - 1` sum to `z ^ 2`. Natural subtraction is intentional. Finite-set and nested
finite-pair versions give the corresponding multiplicative factorization over families of twists.

Here `lValueProd` is the bare interval product. The separate theorem
`conductor_mul_lValueProd_eq_mul_prod_ratio_sq` retains the conductor powers outside the product
of already-squared L-values, as in the source normalization.

Integer powers of a natural number prime to `p` have norm one in `ℂ_[p]`. Together with the
analogue for `PadicAlgCl` already available for `PrimePadicIso`, this transports height bounds
using `PrimePadicIso.HeightLe.mono`. The existing `HeightLe` bounds and their `mono`,
`heightLe_one`, `HeightLe.mul`, `HeightLe.pow`, and `HeightLe.prod` operations are reused without
a parallel height definition.

## Main results

* `sum_Icc_one_two_mul_sub_one`: the first `z` odd numbers sum to `z ^ 2`.
* `prod_eq_pow_sum_mul_prod_mul_prod_sq`: finite twisted products split into three factors.
* `prod_prod_eq_pow_sum_mul_prod_mul_prod_sq`: the nested finite-family factorization.
* `lValueProd_eq_mul_prod_ratio_sq`: the critical-interval product formula.
* `lValueProd_eq_mul_sq_prod_ratio`: the ratio product collected before squaring.
* `conductor_mul_lValueProd_eq_mul_prod_ratio_sq`: the conductored squared-value product.
* `lValueProd_eq_mul_prod_ratio_sq_of_le`: restriction to a lower critical endpoint.
* `lValueProd_eq_lValueProd_mul_prod_Ioc`: splitting off the upper interval.
* `padicComplex_norm_natCast_zpow_eq_one` and
  `padicComplex_norm_place_natCast_zpow_eq_one`: norm-one integer powers in `ℂ_[p]`.
* `heightLe_of_eq_zpow_mul`: transport of the existing height bound.

## References

The algebraic normalization and height argument follow [ShortProof], `lsernau/grh-lean` at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`,
`New/OneLift/HeckeValues/TwistedRatio.lean`. The proofs here are independent.
-/

public noncomputable section

namespace TauCeti.ThetaLift

/-- The first `z` odd numbers, written using natural subtraction, sum to `z ^ 2`. -/
theorem sum_Icc_one_two_mul_sub_one (z : ℕ) :
    ∑ j ∈ Finset.Icc 1 z, (2 * j - 1) = z ^ 2 := by
  induction z with
  | zero => simp
  | succ z ih =>
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le z)), ih]
      have h : 2 * (z + 1) - 1 = 2 * z + 1 := by omega
      rw [h]
      ring

/-- A finite product of `q ^ e i * Lbase i * ratio i ^ 2` splits into a power of `q`, the
product of the base values, and the product of the squared ratios. -/
theorem prod_eq_pow_sum_mul_prod_mul_prod_sq {α M : Type*} [CommMonoid M]
    (s : Finset α) (q : M) (e : α → ℕ) (Lbase ratio Ltw : α → M)
    (h : ∀ i ∈ s, Ltw i = q ^ e i * Lbase i * ratio i ^ 2) :
    (∏ i ∈ s, Ltw i) =
      q ^ (∑ i ∈ s, e i) * (∏ i ∈ s, Lbase i) * ∏ i ∈ s, ratio i ^ 2 := by
  calc
    (∏ i ∈ s, Ltw i) = ∏ i ∈ s, (q ^ e i * Lbase i * ratio i ^ 2) :=
      Finset.prod_congr rfl h
    _ = q ^ (∑ i ∈ s, e i) * (∏ i ∈ s, Lbase i) * ∏ i ∈ s, ratio i ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- In the finite twisted-product factorization, the product of squared ratios is equivalently the
square of the product of ratios. -/
theorem prod_eq_pow_sum_mul_prod_mul_sq {α M : Type*} [CommMonoid M]
    (s : Finset α) (q : M) (e : α → ℕ) (Lbase ratio Ltw : α → M)
    (h : ∀ i ∈ s, Ltw i = q ^ e i * Lbase i * ratio i ^ 2) :
    (∏ i ∈ s, Ltw i) =
      q ^ (∑ i ∈ s, e i) * (∏ i ∈ s, Lbase i) * (∏ i ∈ s, ratio i) ^ 2 := by
  rw [prod_eq_pow_sum_mul_prod_mul_prod_sq s q e Lbase ratio Ltw h, Finset.prod_pow]

/-- For a finite family of finite twisted products, all inner factors can be collected into one
power of `q`, one double product of base values, and one double product of squared ratios. -/
theorem prod_prod_eq_pow_sum_mul_prod_mul_prod_sq {α β M : Type*} [CommMonoid M]
    (s : Finset α) (t : α → Finset β) (q : M) (e : α → β → ℕ)
    (Lbase ratio Ltw : α → β → M)
    (h : ∀ i ∈ s, ∀ j ∈ t i, Ltw i j = q ^ e i j * Lbase i j * ratio i j ^ 2) :
    (∏ i ∈ s, ∏ j ∈ t i, Ltw i j) = q ^ (∑ i ∈ s, ∑ j ∈ t i, e i j) *
      (∏ i ∈ s, ∏ j ∈ t i, Lbase i j) * ∏ i ∈ s, ∏ j ∈ t i, ratio i j ^ 2 := by
  calc
    (∏ i ∈ s, ∏ j ∈ t i, Ltw i j) = ∏ i ∈ s, (q ^ (∑ j ∈ t i, e i j) *
        (∏ j ∈ t i, Lbase i j) * ∏ j ∈ t i, ratio i j ^ 2) :=
      Finset.prod_congr rfl fun i hi ↦
        prod_eq_pow_sum_mul_prod_mul_prod_sq (t i) q (e i) (Lbase i) (ratio i) (Ltw i) (h i hi)
    _ = q ^ (∑ i ∈ s, ∑ j ∈ t i, e i j) *
        (∏ i ∈ s, ∏ j ∈ t i, Lbase i j) * ∏ i ∈ s, ∏ j ∈ t i, ratio i j ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The product of the values `f j` at the critical points `1 ≤ j ≤ z`. -/
def lValueProd {M : Type*} [CommMonoid M] (f : ℕ → M) (z : ℕ) : M :=
  ∏ j ∈ Finset.Icc 1 z, f j

/-- If each twisted value is the corresponding base value multiplied by an odd power of `q`
and the square of a ratio, then its critical-interval product has the displayed three-factor
formula. -/
theorem lValueProd_eq_mul_prod_ratio_sq {M : Type*} [CommMonoid M]
    (q : M) (Lbase ratio Ltw : ℕ → M) (z : ℕ)
    (h : ∀ j ∈ Finset.Icc 1 z,
      Ltw j = q ^ (2 * j - 1) * Lbase j * ratio j ^ 2) :
    lValueProd Ltw z = q ^ (z ^ 2) * lValueProd Lbase z *
      ∏ j ∈ Finset.Icc 1 z, ratio j ^ 2 := by
  simpa only [lValueProd, sum_Icc_one_two_mul_sub_one] using
    prod_eq_pow_sum_mul_prod_mul_prod_sq (Finset.Icc 1 z) q (fun j ↦ 2 * j - 1)
      Lbase ratio Ltw h

/-- Equivalently, the last factor in the twisted product formula is the square of the product
of the ratios. -/
theorem lValueProd_eq_mul_sq_prod_ratio {M : Type*} [CommMonoid M]
    (q : M) (Lbase ratio Ltw : ℕ → M) (z : ℕ)
    (h : ∀ j ∈ Finset.Icc 1 z,
      Ltw j = q ^ (2 * j - 1) * Lbase j * ratio j ^ 2) :
    lValueProd Ltw z = q ^ (z ^ 2) * lValueProd Lbase z *
      (∏ j ∈ Finset.Icc 1 z, ratio j) ^ 2 := by
  rw [← Finset.prod_pow]
  exact lValueProd_eq_mul_prod_ratio_sq q Lbase ratio Ltw z h

/-- If the conductor splits into `q₀ * q₁`, and each already-squared twisted value is the base
value multiplied by a squared ratio, the full twisted product is `q₁ ^ (z ^ 2)` times the base
product and the squared-ratio product. Both external conductor powers are preserved. -/
theorem conductor_mul_lValueProd_eq_mul_prod_ratio_sq {M : Type*} [CommMonoid M]
    (q₀ q₁ : M) (Lbase ratio Ltw : ℕ → M) (z : ℕ)
    (h : ∀ j ∈ Finset.Icc 1 z, Ltw j = Lbase j * ratio j ^ 2) :
    (q₀ * q₁) ^ (z ^ 2) * lValueProd Ltw z = q₁ ^ (z ^ 2) *
      (q₀ ^ (z ^ 2) * lValueProd Lbase z * ∏ j ∈ Finset.Icc 1 z, ratio j ^ 2) := by
  have hprod : lValueProd Ltw z = lValueProd Lbase z *
      ∏ j ∈ Finset.Icc 1 z, ratio j ^ 2 := by
    simp only [lValueProd]
    rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib]
  rw [hprod, mul_pow]
  ac_rfl

/-- The twisted product formula restricts from an upper endpoint `z` to any lower endpoint
`z' ≤ z`; in particular, it applies to a critical lower point satisfying `1 ≤ z' ≤ z`. -/
theorem lValueProd_eq_mul_prod_ratio_sq_of_le {M : Type*} [CommMonoid M]
    (q : M) (Lbase ratio Ltw : ℕ → M) {z' z : ℕ} (hzz : z' ≤ z)
    (h : ∀ j ∈ Finset.Icc 1 z,
      Ltw j = q ^ (2 * j - 1) * Lbase j * ratio j ^ 2) :
    lValueProd Ltw z' = q ^ (z' ^ 2) * lValueProd Lbase z' *
      ∏ j ∈ Finset.Icc 1 z', ratio j ^ 2 := by
  apply lValueProd_eq_mul_prod_ratio_sq q Lbase ratio Ltw z'
  intro j hj
  exact h j (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1,
    (Finset.mem_Icc.1 hj).2.trans hzz⟩)

/-- The critical-interval product up to `z` is the product up to `z'` times the product over
`z' < j ≤ z`. -/
theorem lValueProd_eq_lValueProd_mul_prod_Ioc {M : Type*} [CommMonoid M]
    (f : ℕ → M) {z' z : ℕ} (hz : z' ≤ z) :
    lValueProd f z = lValueProd f z' * ∏ j ∈ Finset.Ioc z' z, f j := by
  classical
  unfold lValueProd
  rw [← Finset.prod_union]
  · congr 1
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · exact Finset.disjoint_left.mpr fun j hj hj' ↦ by
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hj hj'
      omega

/-- A natural number not divisible by `p` has norm one in `ℂ_[p]`. -/
theorem padicComplex_norm_natCast_eq_one (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : ¬p ∣ m) :
    ‖(m : ℂ_[p])‖ = 1 := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
    Padic.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hm

/-- Every integer power of a natural number not divisible by `p` has norm one in `ℂ_[p]`. -/
theorem padicComplex_norm_natCast_zpow_eq_one (p : ℕ) [Fact p.Prime] {m : ℕ}
    (hm : ¬p ∣ m) (k : ℤ) : ‖(m : ℂ_[p]) ^ k‖ = 1 := by
  rw [norm_zpow, padicComplex_norm_natCast_eq_one p hm, one_zpow]

/-- A ring homomorphism from `ℂ` sends an integer power of a natural number not divisible by `p`
to an element of norm one in `ℂ_[p]`. -/
theorem padicComplex_norm_place_natCast_zpow_eq_one (p : ℕ) [Fact p.Prime] {m : ℕ}
    (hm : ¬p ∣ m) (k : ℤ) (place : ℂ →+* ℂ_[p]) : ‖place ((m : ℂ) ^ k)‖ = 1 := by
  rw [map_zpow₀, map_natCast]
  exact padicComplex_norm_natCast_zpow_eq_one p hm k

/-- A height bound is preserved by pointwise multiplication by integer powers of natural numbers
prime to the corresponding places, allowing the new family to vanish at any place. -/
theorem heightLe_of_eq_zpow_mul {y y' : PrimePadicIso → ℂ} {c c' : ℝ}
    (m : PrimePadicIso → ℕ) (k : PrimePadicIso → ℤ) (hy : PrimePadicIso.HeightLe y c)
    (hc : c ≤ c') (hm : ∀ i : PrimePadicIso, i.prime.Coprime (m i))
    (hy' : ∀ i, y' i = 0 ∨ y' i = (m i : ℂ) ^ (k i) * y i) :
    PrimePadicIso.HeightLe y' c' := by
  apply hy.mono hc
  intro i
  rcases hy' i with hi | hi
  · simp [hi]
  · rw [hi, map_mul, norm_mul, map_zpow₀, norm_zpow,
      PrimePadicIso.norm_natCast_eq_one i (hm i), one_zpow, one_mul]

/-- A height bound is also preserved when the integer exponent is allowed to depend on a proof
that the new family value is nonzero. -/
theorem heightLe_of_ne_zero_exists_eq_zpow_mul {y y' : PrimePadicIso → ℂ} {c c' : ℝ}
    (m : PrimePadicIso → ℕ) (hy : PrimePadicIso.HeightLe y c) (hc : c ≤ c')
    (hm : ∀ i : PrimePadicIso, i.prime.Coprime (m i))
    (hy' : ∀ i, y' i ≠ 0 → ∃ k : ℤ, y' i = (m i : ℂ) ^ k * y i) :
    PrimePadicIso.HeightLe y' c' := by
  choose! k hk using hy'
  apply heightLe_of_eq_zpow_mul m k hy hc hm
  intro i
  by_cases hi : y' i = 0
  · exact Or.inl hi
  · exact Or.inr (hk i hi)

end TauCeti.ThetaLift
