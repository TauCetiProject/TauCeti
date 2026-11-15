/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Injectivity from a half-plane constraint on the derivative

A function `f : 𝕜 → 𝕜` on a convex set, with `𝕜` either `ℝ` or `ℂ`, is injective if a fixed
rotation of its derivative has strictly positive real part. For `𝕜 = ℂ` this is an analytic
univalence criterion that does not require control of the boundary curve. Along the segment
between two points, the real part of the rotated difference quotient is strictly increasing.

The criterion is commonly called the Noshiro--Warschawski criterion. Here the derivative
condition itself implies differentiability, so the domain need not be open.
-/

public section

open RCLike Set

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Noshiro--Warschawski criterion.** A function on a convex set is injective if a fixed
multiple of its derivative has strictly positive real part throughout the set. -/
theorem Convex.injOn_of_re_mul_deriv_pos {U : Set 𝕜} (hU : Convex ℝ U) {f : 𝕜 → 𝕜} (c : 𝕜)
    (hf : ∀ z ∈ U, 0 < re (c * deriv f z)) : InjOn f U := by
  intro x hx y hy hxy
  by_contra hne
  have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let p : ℝ → 𝕜 := fun t => x + t • (y - x)
  let g : ℝ → ℝ := fun t => re (c * f (p t) / (y - x))
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U := fun t ht => hU.add_smul_sub_mem hx hy ht
  -- The real part of the rotated difference quotient has derivative `re (c * deriv f (p t))`.
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (re (c * deriv f (p t))) t := by
    intro t ht
    have hfd : HasDerivAt f (deriv f (p t)) (p t) :=
      (differentiableAt_of_deriv_ne_zero fun h => by simpa [h] using hf _ (hp t ht)).hasDerivAt
    have hpd : HasDerivAt p (y - x) t := by
      simpa [p] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have hcomp := HasFDerivAt.comp_hasDerivAt t reCLM.hasFDerivAt
      (((hfd.comp t hpd).const_mul c).div_const (y - x))
    simpa [g, Function.comp_def, mul_div_assoc, hd] using hcomp
  have hmono : StrictMonoOn g (Icc (0 : ℝ) 1) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hf (p t) (hp t (interior_subset ht)))
  exact (hmono (by simp) (by simp) zero_lt_one).ne (by simp [g, p, hxy])
