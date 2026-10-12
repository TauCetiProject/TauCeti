/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Injectivity from a half-plane constraint on the derivative

A complex function on a convex set is injective if a fixed rotation of its derivative has
strictly positive real part. This gives an analytic univalence criterion that does not require
control of the boundary curve. Along the segment between two points, the real part of the
rotated difference quotient is strictly increasing.

The criterion is commonly called the Noshiro--Warschawski criterion. Here the derivative
condition itself implies differentiability, so the domain need not be open.
-/

public section

open Complex Set

namespace TauCeti

/-- A complex function on a convex set is injective if a fixed complex multiple of its
derivative has strictly positive real part throughout the set. -/
theorem injOn_of_re_mul_deriv_pos {U : Set ℂ} (hU : Convex ℝ U) {f : ℂ → ℂ} (c : ℂ)
    (hf : ∀ z ∈ U, 0 < (c * deriv f z).re) : InjOn f U := by
  intro x hx y hy hxy
  by_contra hne
  have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let p : ℂ → ℂ := fun t => x + t * (y - x)
  let g : ℝ → ℝ := fun t => (c * f (p t) / (y - x)).re
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U := by
    intro t ht
    have h := hU hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    convert h using 1
    simp [p, Complex.real_smul]
    ring
  have hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g (c * deriv f (p t)).re t := by
    intro t ht
    have hfn : deriv f (p t) ≠ 0 := by
      intro h
      simpa [h] using hf (p t) (hp t ht)
    have hpd : HasDerivAt p (y - x) (t : ℂ) := by
      simpa [p] using ((hasDerivAt_id (t : ℂ)).mul_const (y - x)).const_add x
    have hfd := (differentiableAt_of_deriv_ne_zero hfn).hasDerivAt
    have hcomp := ((hfd.comp (t : ℂ) hpd).const_mul c).div_const (y - x)
    have hcancel : c * (deriv f (p t) * (y - x)) / (y - x) =
        c * deriv f (p t) := by field_simp
    rw [hcancel] at hcomp
    exact hcomp.real_of_complex
  have hmono : StrictMonoOn g (Icc (0 : ℝ) 1) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hf (p t) (hp t (interior_subset ht)))
  have hlt := hmono (by simp) (by simp) zero_lt_one
  have heq : g 0 = g 1 := by simp [g, p, hxy]
  exact (ne_of_lt hlt) heq

end TauCeti
