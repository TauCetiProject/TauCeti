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

Given a vector `v`, a continuous linear functional `ℓ` and a base point `a`, integrate a function
`f` along the lines parallel to `v`, from the starting point `x - ℓ (x - a) • v` to `x`. When
`ℓ v = 1`, the starting point lies on the affine hyperplane `ℓ (x - a) = 0`. The resulting
function vanishes on that hyperplane, depends only on the values of `f` along these segments, and
is linear in `f`; it is `C^n` when `f` is.

When moreover `ℓ v = 1`, `f` is `C¹` and the coefficients lie in a complete real normed space,
the Fréchet derivative of the primitive applied to `v` is `f`, and on the initial hyperplane its
full derivative is `ℓ.smulRight (f x)`. Conversely, integrating the directional derivative of a
`C¹` function recovers it up to its value at the starting point, so a `C¹` function with
directional derivative `f` and zero values on the hyperplane is the primitive. This is the scalar
transport equation in flow-box coordinates.

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

/-- Integrate `f` in direction `v`, starting at `x - ℓ (x - a) • v`: the oriented interval integral
over the parameter range `0..ℓ (x - a)`, which ends at `x`. When `ℓ v = 1`, the starting point
lies on the affine hyperplane `ℓ (x - a) = 0`; if moreover `f` is `C¹` with values in a complete
space, the result is a primitive of `f` in direction `v` (`fderiv_directionalPrimitive_apply`). -/
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

/-- The integration path from `x - ℓ (x - a) • v` to `x` stays on the segment between them. -/
theorem mapsTo_uIcc_segment (v : E) (ℓ : E →L[ℝ] ℝ) (a x : E) :
    MapsTo (fun t : ℝ ↦ x - ℓ (x - a) • v + t • v) (uIcc 0 (ℓ (x - a)))
      (segment ℝ (x - ℓ (x - a) • v) x) := by
  intro t ht
  let p := x - ℓ (x - a) • v
  have hf (t : ℝ) : AffineMap.lineMap p (p + v) t = p + t • v := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, add_sub_cancel_left, vadd_eq_add, add_comm]
  have hseg := image_segment ℝ (AffineMap.lineMap p (p + v)) 0 (ℓ (x - a))
  rw [segment_eq_uIcc, hf, hf, zero_smul, add_zero, sub_add_cancel] at hseg
  rw [← hseg]
  exact ⟨t, ht, hf t⟩

/-- The directional primitive at `x` only depends on the values of `f` on the segment from the
starting point `x - ℓ (x - a) • v` to `x`. -/
theorem directionalPrimitive_congr (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) {f₁ f₂ : E → F} {x : E}
    (h : EqOn f₁ f₂ (segment ℝ (x - ℓ (x - a) • v) x)) :
    directionalPrimitive v ℓ a f₁ x = directionalPrimitive v ℓ a f₂ x :=
  intervalIntegral.integral_congr fun _ ht ↦ h (mapsTo_uIcc_segment v ℓ a x ht)

/-- The directional primitive of the zero function is zero. -/
@[simp]
theorem directionalPrimitive_zero (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) :
    directionalPrimitive v ℓ a (0 : E → F) = 0 := by
  funext x
  simp [directionalPrimitive_def]

/-- The directional primitive commutes with negation. -/
@[simp]
theorem directionalPrimitive_neg (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) (f : E → F) :
    directionalPrimitive v ℓ a (-f) = -directionalPrimitive v ℓ a f := by
  funext x
  simp [directionalPrimitive_def, intervalIntegral.integral_neg]

/-- The directional primitive commutes with real scalar multiplication. -/
@[simp]
theorem directionalPrimitive_smul (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) (c : ℝ) (f : E → F) :
    directionalPrimitive v ℓ a (c • f) = c • directionalPrimitive v ℓ a f := by
  funext x
  simp [directionalPrimitive_def, intervalIntegral.integral_smul]

/-- The directional primitive is additive in `f`, for functions continuous on the segment of
integration. -/
theorem directionalPrimitive_add_apply (v : E) (ℓ : E →L[ℝ] ℝ) (a : E) {f g : E → F} {x : E}
    (hf : ContinuousOn f (segment ℝ (x - ℓ (x - a) • v) x))
    (hg : ContinuousOn g (segment ℝ (x - ℓ (x - a) • v) x)) :
    directionalPrimitive v ℓ a (f + g) x =
      directionalPrimitive v ℓ a f x + directionalPrimitive v ℓ a g x := by
  have hline : ContinuousOn (fun t : ℝ ↦ x - ℓ (x - a) • v + t • v) (uIcc 0 (ℓ (x - a))) := by
    fun_prop
  exact intervalIntegral.integral_add
    (hf.comp hline (mapsTo_uIcc_segment v ℓ a x)).intervalIntegrable
    (hg.comp hline (mapsTo_uIcc_segment v ℓ a x)).intervalIntegrable

/-- Integrating a `C^n` function in a constant direction gives a `C^n` function. -/
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

/-- The derivative of the directional primitive in direction `v` is `f`, for a `C¹` function `f`
with values in a complete space and the normalization `ℓ v = 1`. -/
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

/-- On the initial hyperplane `ℓ (x - a) = 0`, where the primitive vanishes, its full derivative
is `ℓ.smulRight (f x)`, for a `C¹` function `f` with values in a complete space and `ℓ v = 1`. -/
theorem fderiv_directionalPrimitive_of_eq_zero (v : E) (ℓ : E →L[ℝ] ℝ) (a : E)
    (hℓ : ℓ v = 1) {f : E → F} (hf : ContDiff ℝ 1 f) {x : E} (hx : ℓ (x - a) = 0) :
    fderiv ℝ (directionalPrimitive v ℓ a f) x = ℓ.smulRight (f x) := by
  have hd := (contDiff_directionalPrimitive v ℓ a hf).differentiable one_ne_zero x
  ext w
  -- Along `ker ℓ` the primitive stays on the hyperplane, where it vanishes.
  have hw : fderiv ℝ (directionalPrimitive v ℓ a f) x (w - ℓ w • v) = 0 := by
    have hcurve : HasDerivAt (fun t : ℝ ↦ x + t • (w - ℓ w • v)) (w - ℓ w • v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (w - ℓ w • v)).const_add x
    have hzero : (directionalPrimitive v ℓ a f ∘ fun t : ℝ ↦ x + t • (w - ℓ w • v)) = 0 := by
      funext t
      exact directionalPrimitive_eq_zero v ℓ a f (by simp [add_sub_right_comm, hx, hℓ])
    have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
    rw [hzero] at h1
    exact h1.unique (hasDerivAt_const 0 0)
  have hsplit : w = (w - ℓ w • v) + ℓ w • v := (sub_add_cancel _ _).symm
  rw [hsplit, map_add, hw, map_smul, fderiv_directionalPrimitive_apply v ℓ a hℓ hf]
  simp

/-- Integrating the directional derivative of a `C¹` function `g` with values in a complete space
recovers `g` minus its value at the starting point `x - ℓ (x - a) • v`, which lies on the
transverse hyperplane `ℓ (x - a) = 0` when `ℓ v = 1`. -/
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

/-- With `ℓ v = 1`, a `C¹` function with values in a complete space whose derivative in direction
`v` is `f` and which vanishes on the transverse hyperplane `ℓ (x - a) = 0` is the line-integral
primitive. -/
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
