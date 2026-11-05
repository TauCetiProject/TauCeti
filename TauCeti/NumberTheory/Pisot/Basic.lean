/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.Real.GoldenRatio

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# Pisot numbers

A *Pisot number* is a real algebraic integer `θ > 1` all of whose other complex conjugates lie in
the open unit disc: every complex root `z ≠ θ` of `minpoly ℤ θ` satisfies `‖z‖ < 1`. Degree one is
allowed, so the integers `n ≥ 2` are Pisot numbers, while `1` is not. Integrality is part of the
definition: `3 / 2` has no other conjugate but is not a Pisot number.

The powers of a Pisot number are close to integers, and the smallest Pisot number, the real root
of `X³ - X - 1`, is the constant in Smyth's lower bound for the Mahler measure of a nonreciprocal
algebraic integer. A conjugate on the unit circle instead leads to Salem numbers.

## Main definitions

* `TauCeti.IsPisot θ`: `θ` is a Pisot number.

## Main results

* `TauCeti.IsPisot.eq_of_one_le_norm`: `θ` is the only conjugate of a Pisot number `θ` outside the
  open unit disc.
* `TauCeti.isPisot_iff_minpoly_rat`: the definition read with the minimal polynomial over `ℚ`.
* `TauCeti.IsPisot.of_monic`: a real root `θ > 1` of a monic integer polynomial, all of whose
  other complex roots lie in the open unit disc, is a Pisot number; the polynomial need not be
  irreducible.
* `TauCeti.isPisot_intCast_iff`, `TauCeti.isPisot_natCast_iff`: an integer is a Pisot number
  exactly when it is at least `2`.
* `TauCeti.isPisot_goldenRatio`: the golden ratio is a Pisot number.

## References

* C. Smyth, *Seventy years of Salem numbers*, Bull. Lond. Math. Soc. 47 (2015), §1.
* C. Smyth, *The Mahler measure of algebraic numbers: a survey* (2008), §§1, 5.1.
* V. Srivastava, S. Gollapudi, *Pisot numbers*, Euler Circle (2018), §§1–2.
-/

public section

open Polynomial

namespace TauCeti

/-- A real number `θ` is a *Pisot number* if it is an algebraic integer, `1 < θ`, and every other
complex conjugate of `θ`, that is, every complex root `z ≠ θ` of `minpoly ℤ θ`, satisfies
`‖z‖ < 1`. -/
structure IsPisot (θ : ℝ) : Prop where
  /-- A Pisot number is an algebraic integer. -/
  isIntegral : IsIntegral ℤ θ
  /-- A Pisot number is greater than `1`. -/
  one_lt : 1 < θ
  /-- Every conjugate of a Pisot number other than itself lies in the open unit disc. -/
  norm_lt_one ⦃z : ℂ⦄ : z ∈ (minpoly ℤ θ).aroots ℂ → z ≠ θ → ‖z‖ < 1

namespace IsPisot

variable {θ : ℝ}

/-- A Pisot number `θ` is the only conjugate of `θ` outside the open unit disc. -/
theorem eq_of_one_le_norm (h : IsPisot θ) {z : ℂ} (hz : z ∈ (minpoly ℤ θ).aroots ℂ)
    (hz1 : 1 ≤ ‖z‖) : z = θ :=
  of_not_not fun hne ↦ (h.norm_lt_one hz hne).not_ge hz1

/-- A real root `θ > 1` of a monic integer polynomial `P`, all of whose complex roots other than
`θ` lie in the open unit disc, is a Pisot number. The polynomial `P` need not be irreducible, and
the hypothesis only concerns the roots different from `θ`. -/
theorem of_monic {P : ℤ[X]} (hP : P.Monic) (hθ : aeval θ P = 0) (h1 : 1 < θ)
    (hroots : ∀ z ∈ P.aroots ℂ, z ≠ θ → ‖z‖ < 1) : IsPisot θ := by
  have hint : IsIntegral ℤ θ := ⟨P, hP, by rwa [← aeval_def]⟩
  have hle : (minpoly ℤ θ).aroots ℂ ≤ P.aroots ℂ :=
    roots.le_of_dvd ((hP.map _).ne_zero) <|
      Polynomial.map_dvd _ (minpoly.isIntegrallyClosed_dvd hint hθ)
  exact ⟨hint, h1, fun z hz hne ↦ hroots z (Multiset.mem_of_le hle hz) hne⟩

end IsPisot

/-- A real number is a Pisot number if and only if it is an algebraic integer, it is greater
than `1`, and every complex root `z ≠ θ` of its minimal polynomial over `ℚ` satisfies
`‖z‖ < 1`. -/
theorem isPisot_iff_minpoly_rat {θ : ℝ} :
    IsPisot θ ↔ IsIntegral ℤ θ ∧ 1 < θ ∧ ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ θ → ‖z‖ < 1 := by
  refine ⟨fun h ↦ ⟨h.isIntegral, h.one_lt, ?_⟩, fun ⟨hint, h1, h⟩ ↦ ⟨hint, h1, ?_⟩⟩
  · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ h.isIntegral, aroots_map]
    exact h.norm_lt_one
  · rwa [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, aroots_map] at h

/-- An integer is a Pisot number exactly when it is at least `2`. -/
@[simp]
theorem isPisot_intCast_iff {n : ℤ} : IsPisot n ↔ 2 ≤ n := by
  refine ⟨fun h ↦ by exact_mod_cast h.one_lt, fun hn ↦ ?_⟩
  refine IsPisot.of_monic (monic_X_sub_C n) (by simp) (by exact_mod_cast hn) fun z hz hne ↦ ?_
  rw [aroots_X_sub_C, Multiset.mem_singleton, eq_intCast] at hz
  exact absurd (hz.trans (Complex.ofReal_intCast n).symm) hne

/-- A natural number is a Pisot number exactly when it is at least `2`. -/
@[simp]
theorem isPisot_natCast_iff {n : ℕ} : IsPisot n ↔ 2 ≤ n := by
  simpa using isPisot_intCast_iff (n := n)

/-- A numeral `n ≥ 2` is a Pisot number. -/
@[simp]
theorem isPisot_ofNat (n : ℕ) [n.AtLeastTwo] : IsPisot (ofNat(n) : ℝ) :=
  isPisot_natCast_iff.mpr Nat.AtLeastTwo.prop

/-- The complex roots of `X² - X - 1` are the golden ratio `φ` and its conjugate `ψ`. -/
private theorem aroots_X_sq_sub_X_sub_one :
    (X ^ 2 - X - 1 : ℤ[X]).aroots ℂ = {(Real.goldenRatio : ℂ), (Real.goldenConj : ℂ)} := by
  have hsum : ((Real.goldenRatio : ℂ) + Real.goldenConj) = 1 := by
    exact_mod_cast Real.goldenRatio_add_goldenConj
  have hprod : ((Real.goldenRatio : ℂ) * Real.goldenConj) = -1 := by
    exact_mod_cast Real.goldenRatio_mul_goldenConj
  have hfac : (X ^ 2 - X - 1 : ℤ[X]).map (algebraMap ℤ ℂ) =
      (X - C (Real.goldenRatio : ℂ)) * (X - C (Real.goldenConj : ℂ)) := by
    have : (X - C (Real.goldenRatio : ℂ)) * (X - C (Real.goldenConj : ℂ)) =
        X ^ 2 - C ((Real.goldenRatio : ℂ) + Real.goldenConj) * X +
          C ((Real.goldenRatio : ℂ) * Real.goldenConj) := by
      simp only [map_add, map_mul]
      ring
    rw [this, hsum, hprod]
    simp [sub_eq_add_neg]
  rw [aroots_def, hfac, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

/-- The golden ratio `φ = (1 + √5) / 2` is a Pisot number: its conjugate `ψ = (1 - √5) / 2`
satisfies `|ψ| < 1`. -/
theorem isPisot_goldenRatio : IsPisot Real.goldenRatio := by
  refine IsPisot.of_monic (P := X ^ 2 - X - 1) (by monicity!) ?_ Real.one_lt_goldenRatio ?_
  · simp [Real.goldenRatio_sq]
  · intro z hz hne
    rw [aroots_X_sq_sub_X_sub_one, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hz
    obtain rfl | rfl := hz
    · exact absurd rfl hne
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
      exact ⟨Real.neg_one_lt_goldenConj, Real.goldenConj_neg.trans one_pos⟩

/-- The Mahler measure of `X² - X - 1` is the golden ratio. -/
example : (X ^ 2 - X - 1 : ℂ[X]).mahlerMeasure = Real.goldenRatio := by
  have h := aroots_X_sq_sub_X_sub_one
  rw [aroots_def] at h
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one] at h
  have hlead : (X ^ 2 - X - 1 : ℂ[X]).leadingCoeff = 1 := by monicity!
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hlead, h]
  have hψ : ‖(Real.goldenConj : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨Real.neg_one_lt_goldenConj.le, Real.goldenConj_neg.le.trans zero_le_one⟩
  have hφ : ‖(Real.goldenRatio : ℂ)‖ = Real.goldenRatio := by
    rw [Complex.norm_real, Real.norm_of_nonneg Real.goldenRatio_pos.le]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, hφ, max_eq_right Real.one_lt_goldenRatio.le,
    max_eq_left hψ, norm_one, one_mul, mul_one]

/-- `2` is a Pisot number of degree one. -/
example : IsPisot 2 := isPisot_ofNat 2

/-- `1` is not a Pisot number: the inequality `1 < θ` is strict. -/
example : ¬IsPisot 1 := fun h ↦ h.one_lt.false

/-- `3 / 2` is not a Pisot number: it has no other conjugate, but it is not an algebraic
integer. -/
example : ¬IsPisot (3 / 2) := by
  intro h
  have hq : IsIntegral ℤ (3 / 2 : ℚ) := by
    rw [← isIntegral_algebraMap_iff (B := ℝ)]
    simpa using h.isIntegral
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have : (2 * n : ℚ) = 3 := by rw [eq_intCast] at hn; rw [hn]; norm_num
  have : 2 * n = 3 := by exact_mod_cast this
  omega

/-- `√2` is not a Pisot number: its conjugate `-√2` lies outside the unit disc. -/
example : ¬IsPisot √2 := by
  intro h
  have hmin : minpoly ℤ √2 = X ^ 2 - C 2 := by
    have hP : (X ^ 2 - C 2 : ℤ[X]).Monic := by monicity!
    have hdeg : (X ^ 2 - C 2 : ℤ[X]).natDegree = 2 := by compute_degree!
    have hirr : √2 ∉ (algebraMap ℤ ℝ).range := by
      rintro ⟨n, hn⟩
      exact irrational_sqrt_two.ne_int n (by simpa using hn.symm)
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic h.isIntegral) hP
      (minpoly.isIntegrallyClosed_dvd h.isIntegral ?_) ?_).symm
    · rw [map_sub, map_pow, aeval_X, aeval_C, Real.sq_sqrt zero_le_two]
      simp
    rw [hdeg]
    exact (minpoly.two_le_natDegree_iff h.isIntegral).mpr hirr
  have hroot : (-√2 : ℂ) ∈ (minpoly ℤ √2).aroots ℂ := by
    rw [hmin, mem_aroots]
    refine ⟨by simpa using X_pow_sub_C_ne_zero two_pos (2 : ℤ), ?_⟩
    have : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt zero_le_two
    rw [map_sub, map_pow, aeval_X, aeval_C, neg_sq, this]
    simp
  have hne : (-√2 : ℂ) ≠ (√2 : ℝ) := by
    rw [ne_eq, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero, not_or]
    exact ⟨two_ne_zero, by exact_mod_cast (Real.sqrt_pos.mpr zero_lt_two).ne'⟩
  have hlt := h.norm_lt_one hroot hne
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr two_pos)] at hlt
  exact absurd hlt (not_lt.mpr (Real.one_lt_sqrt_two).le)

end TauCeti
