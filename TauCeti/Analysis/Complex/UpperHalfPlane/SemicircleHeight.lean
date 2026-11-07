/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Heights above a semicircle centred on the real axis

Let `z ∈ ℍ` lie on or above the semicircle of centre `m ∈ ℝ` and radius `ρ`, that is
`ρ² ≤ |z - m|²`. This file bounds the height `Im z` from below when `Re z` lies between `m` and an
endpoint of an arc of that semicircle.

* If the endpoint is a point `p ∈ ℍ` of the semicircle, then `Im p ≤ Im z`
  (`TauCeti.UpperHalfPlane.im_le_im_of_normSq_sub_le`).
* If the endpoint is the real point `x` where the semicircle meets `ℝ`, the height is not bounded
  below near `x`, but it satisfies `ρ |Re z - x| ≤ (Im z)²`. Hence it is bounded below outside a
  horodisc at `x`: if `Im z ≤ K |z - x|²`, then `min ρ (1 / (2K)) ≤ Im z`
  (`TauCeti.UpperHalfPlane.min_le_im_of_sq_sub_eq`).

These are the estimates that make a convex polygon truncated at its ideal vertices compact.
-/

public section

open UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- A point `z ∈ ℍ` at least as far from `m ∈ ℝ` as `p ∈ ℍ`, that is, on or above the semicircle of
centre `m` through `p`, and whose real part lies between `Re p` and `m`, is at least as high as
`p`. -/
theorem im_le_im_of_normSq_sub_le {m : ℝ} {p z : ℍ}
    (h : Complex.normSq ((p : ℂ) - m) ≤ Complex.normSq ((z : ℂ) - m))
    (hre : (z.re - p.re) * (z.re - m) ≤ 0) : p.im ≤ z.im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, coe_re, coe_im] at h
  -- `Re z` is at least as close to `m` as `Re p`
  have hsq : (z.re - m) ^ 2 ≤ (p.re - m) ^ 2 := by nlinarith
  nlinarith [p.im_pos, z.im_pos]

/-- Above a semicircle of centre `m` and radius `ρ` ending at the real point `x`, a point `z` whose
real part lies between `x` and `m`, and which lies outside the horodisc `Im z > K |z - x|²` at `x`,
has height at least `min ρ (1 / (2K))`. -/
theorem min_le_im_of_sq_sub_eq {m ρ x K : ℝ} {z : ℍ}
    (hx : (x - m) ^ 2 = ρ ^ 2) (hz : ρ ^ 2 ≤ Complex.normSq ((z : ℂ) - m))
    (hre : (z.re - x) * (z.re - m) ≤ 0) (hh : z.im ≤ K * Complex.normSq ((z : ℂ) - x)) :
    min ρ (1 / (2 * K)) ≤ z.im := by
  have hy := z.im_pos
  have hK : 0 < K := pos_of_mul_pos_left (hy.trans_le hh) (Complex.normSq_nonneg _)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, coe_re, coe_im] at hz hh
  by_contra hlt
  obtain ⟨hyρ, hyK⟩ := lt_min_iff.1 (not_le.1 hlt)
  rw [lt_div_iff₀ (by positivity)] at hyK
  set u := z.re - x
  set y := z.im
  -- with `t = m - x`, so that `t² = ρ²`: `u² ≤ u t ≤ y²`
  have h₁ : u ^ 2 ≤ u * (m - x) := by nlinarith
  have h₂ : u * (m - x) ≤ y ^ 2 := by nlinarith
  -- `ρ² u² = (u t)² ≤ y⁴ ≤ ρ² y²`, so `u² ≤ y²`
  have h₃ : u ^ 2 ≤ y ^ 2 := by
    nlinarith [pow_le_pow_left₀ ((sq_nonneg u).trans h₁) h₂ 2, pow_le_pow_left₀ hy.le hyρ.le 2]
  -- outside the horodisc, `y ≤ K (u² + y²) ≤ 2 K y²`, so `1 / (2K) ≤ y`
  nlinarith

end TauCeti.UpperHalfPlane
