/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Primitives in a constant direction

Given a nonzero vector `v` and a continuous linear functional `ℓ` with `ℓ v = 1`, integrate a
smooth function along the lines parallel to `v`, starting at the point `x - ℓ (x - a) • v`,
which then lies on the affine hyperplane `ℓ (x - a) = 0`. The resulting function is smooth,
vanishes on that hyperplane, and its Fréchet derivative applied to `v` is the original function.
This is the scalar transport equation in flow-box coordinates; the coefficients may also lie in
a complete normed space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 9.22
  (straightening a nonvanishing vector field).
-/

public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrate `f` in direction `v` over the parameter interval `[0, ℓ (x - a)]`, starting at
`x - ℓ (x - a) • v`. When `ℓ v = 1`, this starting point lies on the affine hyperplane
`ℓ (x - a) = 0` and the result is a primitive of `f` in direction `v`. -/
def directionalPrimitive (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) (f : E → F) (x : E) : F :=
  ∫ t in (0 : ℝ)..ℓ (x - a), f (x - ℓ (x - a) • v + t • v)

/-- The directional primitive is the line integral of `f` along `v`, starting at
`x - ℓ (x - a) • v` (a point of the hyperplane `ℓ (x - a) = 0` when `ℓ v = 1`). -/
theorem directionalPrimitive_def (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) (f : E → F) (x : E) :
    directionalPrimitive v ℓ a f x =
      ∫ t in (0 : ℝ)..ℓ (x - a), f (x - ℓ (x - a) • v + t • v) := (rfl)

/-- The directional primitive vanishes on its initial hyperplane. -/
@[simp]
theorem directionalPrimitive_eq_zero (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) (f : E → F)
    {x : E} (hx : ℓ (x - a) = 0) : directionalPrimitive v ℓ a f x = 0 := by
  simp [directionalPrimitive, hx]

/-- Integrating a smooth function in a constant direction gives a smooth function. -/
theorem contDiff_directionalPrimitive {n : ℕ∞} (v : E) (ℓ : E →L[ℝ] ℝ) (a : E)
    {f : E → F} (hf : ContDiff ℝ n f) : ContDiff ℝ n (directionalPrimitive v ℓ a f) := by
  have h : ContDiff ℝ n (fun p : E × ℝ ↦
      f (p.1 - ℓ (p.1 - a) • v + (p.2 * ℓ (p.1 - a)) • v)) :=
    hf.comp (by fun_prop)
  have hint := ContDiff.parametric_integral (μ := volume)
    (f := fun x t ↦ f (x - ℓ (x - a) • v + (t * ℓ (x - a)) • v)) isCompact_Icc
    (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1) (by simp) h
  have hs := (ℓ.contDiff.comp (contDiff_id.sub (contDiff_const (c := a)))).smul hint
  convert hs using 1
  funext x
  symm
  rw [directionalPrimitive_def]
  simpa [intervalIntegral.integral_of_le zero_le_one] using
    (intervalIntegral.smul_integral_comp_mul_right
      (a := 0) (b := 1) (fun t ↦ f (x - ℓ (x - a) • v + t • v)) (ℓ (x - a)))

/-- Translation parallel to `v` changes only the upper endpoint of the line integral. -/
theorem directionalPrimitive_add_smul (v : E) (ℓ : E →L[ℝ] ℝ) (a : E)
    (hℓ : ℓ v = 1) (f : E → F) (x : E) (s : ℝ) :
    directionalPrimitive v ℓ a f (x + s • v) =
      ∫ t in (0 : ℝ)..(ℓ (x - a) + s), f (x - ℓ (x - a) • v + t • v) := by
  have he : ℓ (x + s • v - a) = ℓ (x - a) + s := by
    rw [add_sub_right_comm, map_add, map_smul, hℓ, smul_eq_mul, mul_one]
  rw [directionalPrimitive_def, he]
  congr 1
  ext t
  congr 1
  module

variable [CompleteSpace F]

/-- The derivative of the directional primitive in direction `v` is `f`, with the normalization
`ℓ v = 1`. -/
@[simp]
theorem fderiv_directionalPrimitive_apply (v : E) (ℓ : E →L[ℝ] ℝ) (a : E)
    (hℓ : ℓ v = 1) {f : E → F} (hf : ContDiff ℝ 1 f) (x : E) :
    fderiv ℝ (directionalPrimitive v ℓ a f) x v = f x := by
  have hc : Continuous (fun t : ℝ ↦ f (x - ℓ (x - a) • v + t • v)) :=
    hf.continuous.comp (by fun_prop)
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 (ℓ (x - a)))
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).scomp_of_eq 0
      ((hasDerivAt_id 0).const_add (ℓ (x - a))) (by simp)
  have heq : (fun s : ℝ ↦ directionalPrimitive v ℓ a f (x + s • v)) =
      (fun s ↦ ∫ t in (0 : ℝ)..(ℓ (x - a) + s),
        f (x - ℓ (x - a) • v + t • v)) :=
    funext (directionalPrimitive_add_smul v ℓ a hℓ f x)
  have hcurve : HasDerivAt (fun s : ℝ ↦ x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd' := ((contDiff_directionalPrimitive v ℓ a hf).differentiable one_ne_zero x).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  simp only [Function.comp_def, id_eq] at hd hd'
  rw [heq] at hd'
  have hval : x - ℓ (x - a) • v + ℓ (x - a) • v = x := sub_add_cancel _ _
  simpa only [one_smul, hval] using hd'.unique hd

/-- Integrating the directional derivative recovers a function minus its value at the starting
point `x - ℓ (x - a) • v`, which lies on the transverse hyperplane `ℓ (x - a) = 0` when
`ℓ v = 1`. -/
@[simp]
theorem directionalPrimitive_fderiv_apply (v : E) (ℓ : E →L[ℝ] ℝ) (a : E)
    {g : E → F} (hg : ContDiff ℝ 1 g) (x : E) :
    directionalPrimitive v ℓ a (fun y ↦ fderiv ℝ g y v) x =
      g x - g (x - ℓ (x - a) • v) := by
  have hline (t : ℝ) : HasDerivAt
      (fun t ↦ g (x - ℓ (x - a) • v + t • v))
      (fderiv ℝ g (x - ℓ (x - a) • v + t • v) v) t := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      ((hg.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v).const_add (x - ℓ (x - a) • v)))
  have hcont : Continuous (fun t : ℝ ↦ fderiv ℝ g (x - ℓ (x - a) • v + t • v) v) :=
    (hg.continuous_fderiv one_ne_zero |>.comp (by fun_prop)).clm_apply continuous_const
  simpa only [directionalPrimitive_def, sub_add_cancel, zero_smul, add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hline t)
      (hcont.intervalIntegrable 0 (ℓ (x - a)))

/-- A smooth primitive in direction `v` with zero initial values on the chosen transverse
hyperplane is the line-integral primitive. -/
theorem eq_directionalPrimitive_of_fderiv_apply_eq (v : E) (ℓ : E →L[ℝ] ℝ) (a : E)
    (hℓ : ℓ v = 1) {f g : E → F} (hg : ContDiff ℝ 1 g)
    (hd : ∀ x, fderiv ℝ g x v = f x) (hzero : ∀ x, ℓ (x - a) = 0 → g x = 0) :
    g = directionalPrimitive v ℓ a f := by
  funext x
  have hinit : ℓ (x - ℓ (x - a) • v - a) = 0 := by
    rw [sub_right_comm, map_sub, map_smul, hℓ, smul_eq_mul, mul_one, sub_self]
  rw [← funext hd, directionalPrimitive_fderiv_apply v ℓ a hg,
    hzero _ hinit, sub_zero]

end TauCeti
