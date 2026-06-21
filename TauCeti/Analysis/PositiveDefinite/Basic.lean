/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Positive-definite functions on an involutive additive monoid

A complex-valued function `F` on an additive monoid `M` equipped with an involution `star`
(an `AddCommMonoid` with a `StarAddMonoid` structure) is **positive definite** when, for every
finite family `(cᵢ, aᵢ)` of scalars `cᵢ : ℂ` and points `aᵢ : M`, the Hermitian form
`∑_{i,j} cᵢ · conj(cⱼ) · F(aᵢ + aⱼ⋆)` is a nonnegative real number. The involution `aⱼ⋆` inside
the argument is what makes this the right notion on an involutive semigroup (Berg–Christensen–
Ressel): on a finite-dimensional real inner-product space with `a⋆ = -a` it specialises to the
classical translation-invariant positive-definiteness `∑ cᵢ conj(cⱼ) F(aᵢ - aⱼ) ≥ 0`, and on the
product monoid `ℝ≥0 × V` it produces the BCR involution `(t, a)⋆ = (t, -a)`.

This file introduces the predicate `TauCeti.IsPositiveDefinite` at this general level and develops
its basic algebraic API: the value at `0` is real and nonnegative, the function is conjugate
symmetric in the involution, it satisfies the Cauchy–Schwarz inequality coming from the `2 × 2`
sub-form, and the class is closed under sums and nonnegative real scalar multiples, with the
nonnegative constants as examples.

This is the `Objects` and first `API to develop` slice of Part C of the `OneParameterSemigroups`
roadmap (`PositiveDefinite/README.md` in TauCetiRoadmap: "positive-definite functions and
Bochner's theorem"). Mathlib has positive-definiteness only for matrices and quadratic forms
(`Matrix.PosSemidef`), not for functions on an involutive monoid, so the predicate and its API are
built here. The continuity theory and Bochner's representation theorem are later milestones.

## Main declarations

* `TauCeti.IsPositiveDefinite`: the positive-definiteness predicate for `F : M → ℂ`.
* `TauCeti.IsPositiveDefinite.quadForm_two_nonneg`: nonnegativity of the `2 × 2` sub-form, the
  workhorse behind the pointwise properties.
* `TauCeti.IsPositiveDefinite.map_zero_nonneg`: `0 ≤ F 0`.
* `TauCeti.IsPositiveDefinite.conj_symm`: `conj (F (b + a⋆)) = F (a + b⋆)`.
* `TauCeti.IsPositiveDefinite.normSq_le`: the Cauchy–Schwarz inequality
  `‖F (a + b⋆)‖² ≤ (F (a + a⋆)).re * (F (b + b⋆)).re`.
* `TauCeti.IsPositiveDefinite.add`, `TauCeti.IsPositiveDefinite.const_mul`,
  `TauCeti.isPositiveDefinite_const`: closure properties and examples.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {M : Type*} [AddCommMonoid M] [StarAddMonoid M] {F G : M → ℂ}

/-- A function `F : M → ℂ` on an involutive additive monoid is **positive definite** when, for
every finite family of scalars `c : Fin n → ℂ` and points `v : Fin n → M`, the Hermitian form
`∑_{i,j} c i · conj (c j) · F (v i + star (v j))` is a nonnegative real number (using the order on
`ℂ` for which `0 ≤ z` means `z` is real and nonnegative). -/
def IsPositiveDefinite (F : M → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → M),
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F (v i + star (v j))

namespace IsPositiveDefinite

/-- The `2 × 2` Hermitian sub-form of a positive-definite function is nonnegative. This is the
specialisation of the definition to the two points `a, b` with scalars `c₀, c₁`; the pointwise
properties below all follow from it by choosing suitable scalars. -/
theorem quadForm_two_nonneg (hF : IsPositiveDefinite F) (a b : M) (c₀ c₁ : ℂ) :
    0 ≤ c₀ * conj c₀ * F (a + star a) + c₀ * conj c₁ * F (a + star b)
      + c₁ * conj c₀ * F (b + star a) + c₁ * conj c₁ * F (b + star b) := by
  have h := hF 2 ![c₀, c₁] ![a, b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact le_of_le_of_eq h (by ring)

/-- A positive-definite function takes a real, nonnegative value at every "norm point"
`a + star a`. -/
theorem nonneg_self (hF : IsPositiveDefinite F) (a : M) : 0 ≤ F (a + star a) := by
  have h := hF 1 ![1] ![a]
  simpa [Fin.sum_univ_one] using h

/-- The value of a positive-definite function at `0` is real and nonnegative. -/
theorem map_zero_nonneg (hF : IsPositiveDefinite F) : 0 ≤ F 0 := by
  simpa [star_zero] using hF.nonneg_self 0

/-- A positive-definite function is conjugate symmetric in the involution:
`conj (F (b + star a)) = F (a + star b)`. -/
theorem conj_symm (hF : IsPositiveDefinite F) (a b : M) :
    conj (F (b + star a)) = F (a + star b) := by
  -- The diagonal entries `F (a + star a)`, `F (b + star b)` are real.
  have hp : (F (a + star a)).im = 0 := ((Complex.nonneg_iff.mp (hF.nonneg_self a)).2).symm
  have hq : (F (b + star b)).im = 0 := ((Complex.nonneg_iff.mp (hF.nonneg_self b)).2).symm
  -- Two choices of scalars force the off-diagonal entries to be conjugate.
  have h11 := (Complex.nonneg_iff.mp (hF.quadForm_two_nonneg a b 1 1)).2
  have h1i := (Complex.nonneg_iff.mp (hF.quadForm_two_nonneg a b 1 Complex.I)).2
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at h11 h1i
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

/-- The Cauchy–Schwarz inequality for a positive-definite function: the squared norm of an
off-diagonal value is bounded by the product of the two diagonal values. -/
theorem normSq_le (hF : IsPositiveDefinite F) (a b : M) :
    Complex.normSq (F (a + star b))
      ≤ (F (a + star a)).re * (F (b + star b)).re := by
  set r := F (a + star b) with hr
  -- The off-diagonal entries are conjugate, and the diagonal entries are real.
  have hconj : F (b + star a) = conj r := by rw [hr, ← hF.conj_symm a b, Complex.conj_conj]
  have hpim : (F (a + star a)).im = 0 := ((Complex.nonneg_iff.mp (hF.nonneg_self a)).2).symm
  have hqim : (F (b + star b)).im = 0 := ((Complex.nonneg_iff.mp (hF.nonneg_self b)).2).symm
  have hpre : 0 ≤ (F (a + star a)).re := (Complex.nonneg_iff.mp (hF.nonneg_self a)).1
  have hqre : 0 ≤ (F (b + star b)).re := (Complex.nonneg_iff.mp (hF.nonneg_self b)).1
  -- For every real `t`, the quadratic `t ↦ pᵣ t² - 2 ‖r‖² t + ‖r‖² qᵣ` is nonnegative.
  have hpoly : ∀ t : ℝ, 0 ≤ (F (a + star a)).re * (t * t)
      + (-2 * Complex.normSq r) * t + Complex.normSq r * (F (b + star b)).re := by
    intro t
    have hQ := hF.quadForm_two_nonneg a b (-(t : ℂ)) r
    have hre := (Complex.nonneg_iff.mp hQ).1
    refine le_of_le_of_eq hre ?_
    rw [hconj]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
    nlinarith [hpim, hqim]
  -- The discriminant of a nonnegative real quadratic is nonpositive.
  have hdisc := discrim_le_zero hpoly
  rw [discrim] at hdisc
  rcases (Complex.normSq_nonneg r).eq_or_lt with hN0 | hN0
  · rw [← hN0]; exact mul_nonneg hpre hqre
  · nlinarith [hdisc, hN0]

/-- Positive-definite functions are closed under addition. -/
theorem add (hF : IsPositiveDefinite F) (hG : IsPositiveDefinite G) :
    IsPositiveDefinite (fun x => F x + G x) := by
  intro n c v
  have hsplit : ∑ i, ∑ j, c i * conj (c j) * (F (v i + star (v j)) + G (v i + star (v j)))
      = (∑ i, ∑ j, c i * conj (c j) * F (v i + star (v j)))
        + ∑ i, ∑ j, c i * conj (c j) * G (v i + star (v j)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  simpa only [hsplit] using add_nonneg (hF n c v) (hG n c v)

/-- Positive-definite functions are closed under multiplication by a nonnegative real scalar. -/
theorem const_mul {c : ℝ} (hc : 0 ≤ c) (hF : IsPositiveDefinite F) :
    IsPositiveDefinite (fun x => (c : ℂ) * F x) := by
  intro n d v
  have hpull : ∑ i, ∑ j, d i * conj (d j) * ((c : ℂ) * F (v i + star (v j)))
      = (c : ℂ) * ∑ i, ∑ j, d i * conj (d j) * F (v i + star (v j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hpull]
  exact mul_nonneg (Complex.zero_le_real.mpr hc) (hF n d v)

end IsPositiveDefinite

/-- A nonnegative real constant is a positive-definite function. -/
theorem isPositiveDefinite_const {k : ℂ} (hk : 0 ≤ k) :
    IsPositiveDefinite (fun _ : M => k) := by
  intro n c v
  have hfactor : ∑ i, ∑ j, c i * conj (c j) * k
      = (∑ i, ∑ j, c i * conj (c j)) * k := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  have hgram : ∑ i, ∑ j, c i * conj (c j) = (∑ i, c i) * conj (∑ i, c i) := by
    rw [map_sum, Fintype.sum_mul_sum]
  rw [hfactor, hgram, Complex.mul_conj]
  exact mul_nonneg (Complex.zero_le_real.mpr (Complex.normSq_nonneg _)) hk

/-- The zero function is positive definite. -/
theorem isPositiveDefinite_zero : IsPositiveDefinite (fun _ : M => (0 : ℂ)) :=
  isPositiveDefinite_const le_rfl

end TauCeti
