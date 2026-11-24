/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.RealDeriv
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.ODE.ScalarLinear

/-!
# Curves in `ℝ³` rotating about the vertical axis

Write a vector `v` of `ℝ³ = EuclideanSpace ℝ (Fin 3)` through its horizontal coordinate
`v₁ + v₂ i ∈ ℂ` and its height `v₃`. The infinitesimal rotation about the vertical axis is
`v ↦ ⟪v, e₁⟫ e₂ - ⟪v, e₂⟫ e₁`; in the horizontal coordinate it is multiplication by `i`, and it
does not move the height.

* `HasDerivWithinAt.ofReal_apply_add_ofReal_apply_mul_I`: the complex coordinate `vᵢ + vⱼ i` of a
  curve in Euclidean space has the complex coordinate of the velocity as derivative.
* `IsPreconnected.ofReal_apply_add_ofReal_apply_mul_I_eq_exp_mul_and_apply_two_eq`: a curve in
  `ℝ³` moving with the infinitesimal rotation about the vertical axis rotates rigidly, by the
  elapsed time as angle.
-/

public section

open Complex Set
open scoped InnerProductSpace

/-- The complex coordinate `vᵢ + vⱼ i` of a curve `v` in Euclidean space has the complex
coordinate of the velocity as derivative. -/
theorem HasDerivWithinAt.ofReal_apply_add_ofReal_apply_mul_I {n : ℕ}
    {c : ℝ → EuclideanSpace ℝ (Fin n)} {c' : EuclideanSpace ℝ (Fin n)} {s : Set ℝ} {t : ℝ}
    (hc : HasDerivWithinAt c c' s t) (i j : Fin n) :
    HasDerivWithinAt (fun t ↦ (c t i : ℂ) + c t j * I) ((c' i : ℂ) + c' j * I) s t :=
  (hc.piLp_apply i).ofReal_comp.add ((hc.piLp_apply j).ofReal_comp.mul_const I)

namespace IsPreconnected

/-- **Rotation about the vertical axis.** A curve in `ℝ³` moving with the infinitesimal rotation
`v ↦ ⟪v, e₁⟫ e₂ - ⟪v, e₂⟫ e₁` about the vertical axis on a preconnected set of times rotates
rigidly: between times `a` and `b` its horizontal coordinate `v₁ + v₂ i` is multiplied by
`exp ((b - a) i)` and its height is unchanged. -/
theorem ofReal_apply_add_ofReal_apply_mul_I_eq_exp_mul_and_apply_two_eq
    {v : ℝ → EuclideanSpace ℝ (Fin 3)} {s : Set ℝ} (hs : IsPreconnected s)
    (hv : ∀ t ∈ s, HasDerivWithinAt v (⟪v t, EuclideanSpace.single 0 1⟫_ℝ •
      EuclideanSpace.single 1 1 - ⟪v t, EuclideanSpace.single 1 1⟫_ℝ • EuclideanSpace.single 0 1)
      s t) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (v b 0 : ℂ) + v b 1 * I = exp (((b - a : ℝ) : ℂ) * I) * ((v a 0 : ℂ) + v a 1 * I) ∧
      v b 2 = v a 2 := by
  constructor
  · -- The horizontal coordinate solves `w' = i w`, and `t i` is a primitive of the coefficient.
    have h := hs.eq_exp_sub_smul_of_hasDerivWithinAt (A := fun t ↦ (t : ℂ) * I) (k := fun _ ↦ I)
      (f := fun t ↦ (v t 0 : ℂ) + v t 1 * I)
      (fun t _ ↦ by simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).hasDerivWithinAt)
      (fun t ht ↦ ((hv t ht).ofReal_apply_add_ofReal_apply_mul_I 0 1).congr_deriv ?_) ha hb
    · rwa [smul_eq_mul, ← sub_mul, ← ofReal_sub] at h
    · simp only [EuclideanSpace.inner_single_right, conj_trivial, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul, PiLp.single_apply]
      push_cast
      linear_combination (-(v t 1 : ℂ)) * I_sq
  · refine hs.eq_of_hasDerivWithinAt_zero (f := fun t ↦ v t 2) (fun t ht ↦ ?_) hb ha
    simpa [EuclideanSpace.inner_single_right] using (hv t ht).piLp_apply 2

end IsPreconnected
