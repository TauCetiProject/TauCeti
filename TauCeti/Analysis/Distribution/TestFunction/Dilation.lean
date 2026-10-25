/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Divergence
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Dilation of test functions

Dilating the support of a test function by a nonzero real scalar amounts to precomposing with
its inverse. The derivative and divergence acquire the inverse scalar. These formulas transport
the test-field pairings that define distributional variation and perimeter under dilations.
-/

public section

noncomputable section

namespace TauCeti

open Set TestFunction TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω V : Opens E} {r : ℝ}

/-- Dilate the support of a test function by `r`, regarding it as a test function on any open
set containing the dilated original domain. -/
def dilateTestFunction (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω) (φ : 𝓓(V, F)) :
    𝓓(Ω, F) :=
  ⟨fun y => φ (r⁻¹ • y), φ.contDiff.comp (contDiff_const.smul contDiff_id),
    by
      simpa only [Homeomorph.smulOfNeZero_apply, Function.comp_def] using
        φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)),
    by
      intro y hy
      have hy' : r⁻¹ • y ∈ tsupport (φ : E → F) := by
        -- Composition with this homeomorphism is definitionally the lambda defining the dilation.
        have hycomp : y ∈ tsupport
            ((φ : E → F) ∘ Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)) := hy
        rw [tsupport_comp_eq_preimage] at hycomp
        exact hycomp
      simpa only [smul_inv_smul₀ hr] using hVO (φ.tsupport_subset hy')⟩

/-- Evaluation of a test function whose support has been dilated. -/
@[simp]
theorem dilateTestFunction_apply (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (φ : 𝓓(V, F)) (y : E) : dilateTestFunction hr hVO φ y = φ (r⁻¹ • y) :=
  (rfl)

/-- The derivative of a dilated test function acquires the inverse dilation factor. -/
@[simp]
theorem fderiv_dilateTestFunction (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (φ : 𝓓(V, F)) (y : E) :
    fderiv ℝ (dilateTestFunction hr hVO φ : E → F) y =
      r⁻¹ • fderiv ℝ (φ : E → F) (r⁻¹ • y) :=
  fderiv_comp_smul _

/-- The directional derivative of a dilated test function acquires the inverse dilation factor. -/
@[simp]
theorem lineDeriv_dilateTestFunction (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (φ : 𝓓(V, F)) (y w : E) :
    lineDeriv ℝ (dilateTestFunction hr hVO φ : E → F) y w =
      r⁻¹ • lineDeriv ℝ (φ : E → F) (r⁻¹ • y) w := by
  have hd := (dilateTestFunction hr hVO φ).contDiff.differentiable (by simp)
  rw [(hd y).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) (r⁻¹ • y)).lineDeriv_eq_fderiv,
    fderiv_dilateTestFunction]
  simp only [smul_apply]

/-- The divergence of a dilated test vector field acquires the inverse dilation factor. -/
@[simp]
theorem divergenceCLM_dilateTestFunction [FiniteDimensional ℝ E]
    (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω) (φ : 𝓓(V, E)) :
    divergenceCLM (dilateTestFunction hr hVO φ) =
      r⁻¹ • dilateTestFunction hr hVO (divergenceCLM φ) := by
  ext y
  simp

end TauCeti
