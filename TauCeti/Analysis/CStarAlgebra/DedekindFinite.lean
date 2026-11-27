/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Classes
import TauCeti.Algebra.Algebra.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Tactic.NoncommRing

/-!
# Star projections from idempotents and Dedekind finiteness of tracial C⋆-algebras

Every idempotent `p` (`p * p = p`) in a (possibly non-unital) C⋆-algebra admits a star projection
`q` generating the same principal right ideal (`q * p = p` and `p * q = q`), proved in the unital
case using invertibility of `1 + star a * a` and extended to non-unital C⋆-algebras via
`Unitization ℂ A`.

As an application to operator algebras and group von Neumann algebras, any unital C⋆-algebra
carrying a projection-faithful additive tracial map is Dedekind-finite (`a * b = 1 → b * a = 1`),
which immediately yields von Neumann finiteness for tracial von Neumann algebras such as `L(Γ)`.

## Main results

* `CStarAlgebra.isUnit_one_add_star_mul_self`: `1 + star a * a` is a unit in any unital C⋆-algebra.
* `IsIdempotentElem.exists_isStarProjection_mul_eq`: every idempotent `p` in a (possibly
  non-unital) C⋆-algebra admits a star projection `q` with `q * p = p` and `p * q = q`.
* `CStarAlgebra.isDedekindFiniteMonoid_of_tracial`: a unital C⋆-algebra with a projection-faithful
  additive trace is Dedekind-finite.

## References

* I. Kaplansky, *Projections in Banach algebras*, Ann. of Math. (2) **53** (1951), 235–249,
  Theorem 26.
-/

public section

/-- In a unital C⋆-algebra, `1 + star a * a` is invertible. -/
theorem CStarAlgebra.isUnit_one_add_star_mul_self {A : Type*} [CStarAlgebra A] (a : A) :
    IsUnit (1 + star a * a) := by
  by_contra h
  have hneg : (-1 : A) - star a * a = -(1 + star a * a) := by abel
  have hmem : (-1 : ℝ) ∈ spectrum ℝ (star a * a) := by
    rw [spectrum.mem_iff, map_neg, map_one, hneg, IsUnit.neg_iff]; exact h
  linarith [spectrum_star_mul_self_nonneg (-1) hmem]

private theorem exists_isStarProjection_mul_eq_unital {A : Type*} [CStarAlgebra A] {p : A}
    (hp : IsIdempotentElem p) :
    ∃ q : A, IsStarProjection q ∧ q * p = p ∧ p * q = q := by
  let s : A := Star.star p
  obtain ⟨u, hu⟩ := CStarAlgebra.isUnit_one_add_star_mul_self (p - s)
  have hpp : p * p = p := hp.eq
  have hss : s * s = s := hp.star.eq
  have hss' : Star.star s = p := star_star p
  have hz : (u : A) = 1 - p + p * s + s * p - s := by
    rw [hu, star_sub, hss']
    calc 1 + (s - p) * (p - s) = 1 - p * p + p * s + s * p - s * s := by noncomm_ring
      _ = 1 - p + p * s + s * p - s := by rw [hpp, hss]
  have hpz : p * (u : A) = p * s * p := by
    calc p * (u : A) = p - p * p + (p * p) * s + p * s * p - p * s := by rw [hz]; noncomm_ring
      _ = p * s * p := by rw [hpp]; noncomm_ring
  have hzp : (u : A) * p = p * s * p := by
    calc (u : A) * p = p - p * p + p * s * p + s * (p * p) - s * p := by rw [hz]; noncomm_ring
      _ = p * s * p := by rw [hpp]; noncomm_ring
  have hspz : s * (u : A) = s * p * s := by
    calc s * (u : A) = s - s * p + s * p * s + (s * s) * p - s * s := by rw [hz]; noncomm_ring
      _ = s * p * s := by rw [hss]; noncomm_ring
  have hpu : (↑u⁻¹ : A) * p = p * ↑u⁻¹ := u.inv_mul_eq_iff_eq_mul.2
    (by rw [← mul_assoc (u : A) p, hzp, ← hpz, mul_assoc, u.mul_inv, mul_one])
  have hzps : (u : A) * (p * s) = p * s * (u : A) := by
    calc (u : A) * (p * s) = (u : A) * p * s := (mul_assoc _ _ _).symm
      _ = p * s * p * s := by rw [hzp]
      _ = p * (s * p * s) := by simp only [mul_assoc]
      _ = p * (s * (u : A)) := by rw [← hspz]
      _ = p * s * (u : A) := (mul_assoc _ _ _).symm
  have hpsu : (↑u⁻¹ : A) * (p * s) = p * s * ↑u⁻¹ := u.inv_mul_eq_iff_eq_mul.2
    (by rw [← mul_assoc (u : A), hzps, mul_assoc, u.mul_inv, mul_one])
  have huinv_sa : Star.star (↑u⁻¹ : A) = ↑u⁻¹ :=
    (u.mul_eq_one_iff_inv_eq.1 <| by simpa [hu] using congr_arg Star.star u.inv_mul).symm
  have hqp : p * s * ↑u⁻¹ * p = p := by
    rw [mul_assoc (p * s), hpu, ← mul_assoc, ← hpz, mul_assoc, u.mul_inv, mul_one]
  refine ⟨p * s * ↑u⁻¹, ⟨?_, ?_⟩, hqp, by rw [← mul_assoc, ← mul_assoc, hpp]⟩
  · rw [IsIdempotentElem, ← mul_assoc (p * s * ↑u⁻¹), ← mul_assoc (p * s * ↑u⁻¹) p, hqp, mul_assoc]
  · rw [IsSelfAdjoint, star_mul, star_mul, hss', huinv_sa, hpsu]

/-- **Kaplansky's theorem on idempotents in C⋆-algebras.** Every idempotent `p` in a C⋆-algebra
admits a star projection `q` sharing its principal right ideal (`q * p = p` and `p * q = q`). -/
theorem IsIdempotentElem.exists_isStarProjection_mul_eq {A : Type*} [NonUnitalCStarAlgebra A]
    {p : A} (hp : IsIdempotentElem p) :
    ∃ q : A, IsStarProjection q ∧ q * p = p ∧ p * q = q := by
  obtain ⟨q', hq', hqp, hpq⟩ :=
    exists_isStarProjection_mul_eq_unital (Unitization.IsIdempotentElem.inr ℂ hp)
  have hq'coe : ((q'.snd : A) : Unitization ℂ A) = q' :=
    Unitization.inr_snd_of_fst_eq_zero
      (by rw [← hpq, Unitization.fst_mul, Unitization.fst_inr, zero_mul])
  refine ⟨q'.snd, Unitization.isStarProjection_inr_iff.1 (hq'coe.symm ▸ hq'), ?_, ?_⟩
  · exact Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_mul, hq'coe, hqp])
  · exact Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_mul, hq'coe, hpq])

/-- A unital C⋆-algebra admitting an additive tracial map that vanishes on no nonzero star
projection is Dedekind-finite (`a * b = 1 → b * a = 1`). -/
theorem CStarAlgebra.isDedekindFiniteMonoid_of_tracial {A F G : Type*} [CStarAlgebra A]
    [AddZero G] [FunLike F A G] [AddMonoidHomClass F A G] (τ : F)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x))
    (hfaith : ∀ q : A, IsStarProjection q → τ q = 0 → q = 0) :
    IsDedekindFiniteMonoid A where
  mul_eq_one_symm {a b} hab := by
    have hp : IsIdempotentElem (1 - b * a) := by
      calc (1 - b * a) * (1 - b * a) = 1 - b * a - b * a + b * (a * b) * a := by noncomm_ring
        _ = 1 - b * a := by rw [hab, mul_one, sub_add_cancel]
    obtain ⟨q, hq, hqp, hpq⟩ := hp.exists_isStarProjection_mul_eq
    have hτp : τ (1 - b * a) = 0 := by
      calc τ (1 - b * a) = τ (-(b * a) + (b * a + (1 - b * a))) := by rw [neg_add_cancel_left]
        _ = τ (-(b * a)) + τ (a * b) := by rw [map_add, add_sub_cancel, hab]
        _ = τ (-(b * a) + b * a) := by rw [htr a b, ← map_add]
        _ = 0 := by rw [neg_add_cancel, map_zero]
    have hq0 : q = 0 := hfaith q hq (by rw [← hpq, htr, hqp, hτp])
    exact (sub_eq_zero.mp (by rw [← hqp, hq0, zero_mul])).symm
