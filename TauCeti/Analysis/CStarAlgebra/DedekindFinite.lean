/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Kaplansky's idempotent-to-projection formula and Dedekind finiteness of tracial C⋆-algebras

In a unital C⋆-algebra `A`, `1 + star a * a` is invertible for every `a : A` because the real
spectrum of `star a * a` is nonnegative. Kaplansky observed that for any idempotent `p`
(`p * p = p`), setting `z = 1 + star (p - star p) * (p - star p)` gives
`p * z = p * star p * p = z * p`, so `q = p * star p * z⁻¹` is a star projection sharing its left
ideal with `p` (`q * p = p` and `p * q = q`).

Consequently, if `A` carries an additive tracial map `τ : A →+ G` that vanishes on no nonzero star
projection, then `A` is Dedekind-finite (`a * b = 1 → b * a = 1`): for `a * b = 1`, the idempotent
`p = 1 - b * a` has trace `τ p = τ (a * b) - τ (b * a) = 0`, so its Kaplansky star projection `q`
satisfies `τ q = τ (p * q) = τ (q * p) = τ p = 0`, forcing `q = 0`, `p = 0`, and `b * a = 1`.

## Main results

* `CStarAlgebra.isUnit_one_add_star_mul_self`: `1 + star a * a` is a unit in any unital C⋆-algebra.
* `IsIdempotentElem.exists_isStarProjection_mul_eq`: Kaplansky's formula producing a star
  projection `q` with `q * p = p` and `p * q = q` from an idempotent `p`.
* `CStarAlgebra.isDedekindFiniteMonoid_of_tracial`: a unital C⋆-algebra with a projection-faithful
  additive trace is Dedekind-finite.

## References

* I. Kaplansky, *Projections in Banach algebras*, Ann. of Math. (2) **53** (1951), 235–249,
  Theorem 26.
-/

public section

variable {A : Type*} [CStarAlgebra A]

/-- In a unital C⋆-algebra, `1 + star a * a` is invertible. -/
theorem CStarAlgebra.isUnit_one_add_star_mul_self (a : A) : IsUnit (1 + star a * a) := by
  by_contra h
  have hneg : (-1 : A) - star a * a = -(1 + star a * a) := by abel
  have hmem : (-1 : ℝ) ∈ spectrum ℝ (star a * a) := by
    rw [spectrum.mem_iff, map_neg, map_one, hneg, IsUnit.neg_iff]
    exact h
  linarith [spectrum_star_mul_self_nonneg (-1) hmem]

/-- **Kaplansky's idempotent-to-projection formula.** Every idempotent `p` in a unital C⋆-algebra
admits a star projection `q` with `q * p = p` and `p * q = q`. -/
theorem IsIdempotentElem.exists_isStarProjection_mul_eq {p : A} (hp : IsIdempotentElem p) :
    ∃ q : A, IsStarProjection q ∧ q * p = p ∧ p * q = q := by
  let s : A := Star.star p
  obtain ⟨u, hu⟩ := CStarAlgebra.isUnit_one_add_star_mul_self (p - s)
  have hpp : p * p = p := hp.eq
  have hss : s * s = s := hp.star.eq
  have hz : (u : A) = 1 - p + p * s + s * p - s := by
    rw [hu, star_sub]
    have hss' : Star.star s = p := star_star p
    rw [hss']
    calc 1 + (s - p) * (p - s)
        = 1 - p * p + p * s + s * p - s * s := by noncomm_ring
      _ = 1 - p + p * s + s * p - s := by rw [hpp, hss]
  have hpz : p * (u : A) = p * s * p := by
    rw [hz]
    calc p * (1 - p + p * s + s * p - s)
        = p - p * p + (p * p) * s + p * s * p - p * s := by noncomm_ring
      _ = p * s * p := by rw [hpp]; noncomm_ring
  have hzp : (u : A) * p = p * s * p := by
    rw [hz]
    calc (1 - p + p * s + s * p - s) * p
        = p - p * p + p * s * p + s * (p * p) - s * p := by noncomm_ring
      _ = p * s * p := by rw [hpp]; noncomm_ring
  have hspz : s * (u : A) = s * p * s := by
    rw [hz]
    calc s * (1 - p + p * s + s * p - s)
        = s - s * p + s * p * s + (s * s) * p - s * s := by noncomm_ring
      _ = s * p * s := by rw [hss]; noncomm_ring
  have hpu : (↑u⁻¹ : A) * p = p * ↑u⁻¹ := u.inv_mul_eq_iff_eq_mul.2
    (by rw [← mul_assoc (u : A) p, hzp, ← hpz, mul_assoc, u.mul_inv, mul_one])
  have hpsu : (↑u⁻¹ : A) * (p * s) = p * s * ↑u⁻¹ := by
    refine u.inv_mul_eq_iff_eq_mul.2 ?_
    have hassoc : p * s * p * s = p * (s * p * s) := by simp [mul_assoc]
    rw [← mul_assoc (u : A), ← mul_assoc (u : A) p, hzp, hassoc, ← hspz]
    simp [mul_assoc]
  have huinv_sa : Star.star (↑u⁻¹ : A) = ↑u⁻¹ :=
    (u.mul_eq_one_iff_inv_eq.1 <| by simpa [hu] using congr_arg Star.star u.inv_mul).symm
  have hqp : p * s * ↑u⁻¹ * p = p := by
    rw [mul_assoc (p * s), hpu, ← mul_assoc, ← hpz, mul_assoc, u.mul_inv, mul_one]
  refine ⟨p * s * ↑u⁻¹, ⟨?_, ?_⟩, hqp, by rw [← mul_assoc, ← mul_assoc, hpp]⟩
  · rw [IsIdempotentElem, ← mul_assoc (p * s * ↑u⁻¹), ← mul_assoc (p * s * ↑u⁻¹) p,
      hqp, mul_assoc]
  · have hstar : Star.star (p * s * ↑u⁻¹) = ↑u⁻¹ * (p * s) := by
      have hss' : Star.star s = p := star_star p
      rw [star_mul, star_mul, hss', huinv_sa]
    rw [IsSelfAdjoint, hstar, hpsu]

/-- A unital C⋆-algebra admitting an additive tracial map that vanishes on no nonzero star
projection is Dedekind-finite (`a * b = 1 → b * a = 1`). -/
theorem CStarAlgebra.isDedekindFiniteMonoid_of_tracial {G : Type*} [AddZeroClass G] (τ : A →+ G)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x))
    (hfaith : ∀ q : A, IsStarProjection q → τ q = 0 → q = 0) :
    IsDedekindFiniteMonoid A where
  mul_eq_one_symm {a b} hab := by
    have hp : IsIdempotentElem (1 - b * a) := by
      rw [IsIdempotentElem]
      calc (1 - b * a) * (1 - b * a) = 1 - b * a - b * a + b * (a * b) * a := by noncomm_ring
        _ = 1 - b * a := by rw [hab, mul_one, sub_add_cancel]
    obtain ⟨q, hq, hqp, hpq⟩ := hp.exists_isStarProjection_mul_eq
    have hτp : τ (1 - b * a) = 0 := by
      calc τ (1 - b * a)
          = τ (-(b * a) + (b * a + (1 - b * a))) := by rw [neg_add_cancel_left]
        _ = τ (-(b * a)) + τ (a * b) := by rw [map_add, add_sub_cancel, hab]
        _ = τ (-(b * a) + b * a) := by rw [htr a b, ← map_add]
        _ = 0 := by rw [neg_add_cancel, map_zero]
    have hq0 : q = 0 := hfaith q hq (by rw [← hpq, htr, hqp, hτp])
    have hp0 : 1 - b * a = 0 := by rw [← hqp, hq0, zero_mul]
    exact (sub_eq_zero.mp hp0).symm
