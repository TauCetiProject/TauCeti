/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Iterated derivatives in one variable of a product

The iterated derivative of a slice `x ↦ f (p, x)` is the total iterated derivative of `f`
restricted to directions in the second factor. Consequently these partial derivatives vary
continuously in both variables when `f` is sufficiently differentiable. This gives the
joint derivative continuity needed for smooth families in function spaces.

The within-set versions apply to products of sets with unique derivatives, so they also
handle coordinate domains of manifolds with boundary or corners. They use Mathlib's
`HasFTaylorSeriesUpToOn.comp_continuousAffineMap` to restrict the Taylor series to a slice.
-/

public section

namespace _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : P × E → F}

/-- The iterated derivative in the second variable is the total iterated derivative restricted
to directions with zero first component. -/
theorem iteratedFDeriv_prod_right (hf : ContDiff 𝕜 n f) (m : ℕ) (hm : m ≤ n)
    (p : P) (x : E) :
    iteratedFDeriv 𝕜 m (fun y ↦ f (p, y)) x =
      (iteratedFDeriv 𝕜 m f (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr 𝕜 P E) := by
  have h := (ContinuousLinearMap.inr 𝕜 P E).iteratedFDeriv_comp_right
    (hf.comp (contDiff_const.add contDiff_id) :
      ContDiff 𝕜 n (fun z : P × E ↦ f ((p, 0) + z))) x hm
  simpa only [Function.comp_def, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add, iteratedFDeriv_comp_add_left] using h

/-- The iterated derivatives in the second variable of a `C^n` function are jointly continuous
in the parameter and the evaluation point, through order `n`. -/
theorem continuous_iteratedFDeriv_prod_right (hf : ContDiff 𝕜 n f) (m : ℕ) (hm : m ≤ n) :
    Continuous (fun z : P × E ↦ iteratedFDeriv 𝕜 m (fun y ↦ f (z.1, y)) z.2) := by
  simp_rw [iteratedFDeriv_prod_right hf m hm]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin m ↦ ContinuousLinearMap.inr 𝕜 P E)).continuous.comp
      (hf.continuous_iteratedFDeriv hm)

end ContDiff
end _root_

namespace TauCeti

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : P × E → F} {s : Set P} {t : Set E}

/-- On a product of sets with unique derivatives, differentiation in the second variable
restricts the total derivative to directions with zero first component. -/
theorem iteratedFDerivWithin_prod_right (hf : ContDiffOn 𝕜 n f (s ×ˢ t))
    (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (m : ℕ) (hm : m ≤ n)
    {p : P} (hp : p ∈ s) {x : E} (hx : x ∈ t) :
    iteratedFDerivWithin 𝕜 m (fun y ↦ f (p, y)) t x =
      (iteratedFDerivWithin 𝕜 m f (s ×ˢ t) (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr 𝕜 P E) := by
  let g : E →ᴬ[𝕜] P × E :=
    (ContinuousAffineMap.const 𝕜 E p).prod (ContinuousAffineMap.id 𝕜 E)
  have hpre : g ⁻¹' (s ×ˢ t) = t := by ext y; simp [g, hp]
  have hg : g.contLinear = ContinuousLinearMap.inr 𝕜 P E := by
    rfl
  have h := ((hf.of_le hm).ftaylorSeriesWithin (hs.prod ht)).comp_continuousAffineMap g
  rw [hpre] at h
  simpa only [hg, ftaylorSeriesWithin, g, ContinuousAffineMap.prod_apply,
    ContinuousAffineMap.coe_const, ContinuousAffineMap.coe_id, Function.const_apply,
    id_eq, Function.comp_def] using
    (h.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl ht hx).symm

/-- Partial iterated derivatives on a product of sets with unique derivatives vary jointly
continuously, including at boundary points of either set. -/
theorem continuousOn_iteratedFDerivWithin_prod_right (hf : ContDiffOn 𝕜 n f (s ×ˢ t))
    (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (m : ℕ) (hm : m ≤ n) :
    ContinuousOn (fun z : P × E ↦ iteratedFDerivWithin 𝕜 m (fun y ↦ f (z.1, y)) t z.2)
      (s ×ˢ t) := by
  refine ((ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin m ↦ ContinuousLinearMap.inr 𝕜 P E)).continuous.comp_continuousOn
      (hf.continuousOn_iteratedFDerivWithin hm (hs.prod ht))).congr ?_
  intro z hz
  exact iteratedFDerivWithin_prod_right hf hs ht m hm hz.1 hz.2

end TauCeti
