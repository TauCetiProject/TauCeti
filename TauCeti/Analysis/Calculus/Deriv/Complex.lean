/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Real coordinate slices and complex derivatives

A real Fréchet derivative determines the derivatives of the horizontal and vertical slices
(`HasFDerivAt.hasDerivAt_re_slice`, `HasFDerivAt.hasDerivAt_im_slice`). Without requiring
completeness of the target space, symmetry of the second real Fréchet derivative shows that the
complex derivative `deriv g` of a real `C²` holomorphic function `g : ℂ → G` is again holomorphic
(`ContDiffAt.differentiableAt_complex_deriv`, `ContDiffOn.differentiableOn_complex_deriv`).
-/

public section

namespace HasFDerivAt

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousAdd F]
  [ContinuousSMul ℝ F] {P : ℂ → F} {L : ℂ →L[ℝ] F} {z : ℂ}

/-- A real Fréchet derivative gives the derivative of the horizontal coordinate slice. -/
theorem hasDerivAt_re_slice (hP : HasFDerivAt P L z) :
    HasDerivAt (fun x : ℝ ↦ P ⟨x, z.im⟩) (L 1) z.re := by
  have h : HasDerivAt (fun x : ℝ ↦ (⟨x, z.im⟩ : ℂ)) 1 z.re := by
    simpa [Complex.mk_eq_add_mul_I] using
      (Complex.ofRealCLM.hasDerivAt (x := z.re)).add_const (z.im * Complex.I)
  simpa [hasDerivAt_iff_hasFDerivAt, ContinuousLinearMap.comp_toSpanSingleton, Function.comp_def]
    using HasFDerivAt.comp z.re hP h.hasFDerivAt

/-- A real Fréchet derivative gives the derivative of the vertical coordinate slice. -/
theorem hasDerivAt_im_slice (hP : HasFDerivAt P L z) :
    HasDerivAt (fun y : ℝ ↦ P ⟨z.re, y⟩) (L Complex.I) z.im := by
  have h : HasDerivAt (fun y : ℝ ↦ (⟨z.re, y⟩ : ℂ)) Complex.I z.im := by
    simpa [Complex.mk_eq_add_mul_I] using
      ((Complex.ofRealCLM.hasDerivAt (x := z.im)).mul_const Complex.I).const_add (z.re : ℂ)
  simpa [hasDerivAt_iff_hasFDerivAt, ContinuousLinearMap.comp_toSpanSingleton, Function.comp_def]
    using HasFDerivAt.comp z.im hP h.hasFDerivAt

end HasFDerivAt

section ComplexDeriv

open scoped Topology

/-- If `g : ℂ → G` is real `C²` at `z` and holomorphic near `z`, then `deriv g` is complex
differentiable at `z`, without requiring completeness of `G`. -/
theorem ContDiffAt.differentiableAt_complex_deriv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] {g : ℂ → G} {z : ℂ} (hg : ContDiffAt ℝ 2 g z)
    (hhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g w) :
    DifferentiableAt ℂ (deriv g) z := by
  have hDfd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : DifferentiableAt ℝ (fun w ↦ fderiv ℝ g w 1) z :=
    (ContinuousLinearMap.apply ℝ G (1 : ℂ)).differentiableAt.comp z hDfd
  have hcr : (fun w ↦ fderiv ℝ g w Complex.I) =ᶠ[𝓝 z]
      fun w ↦ Complex.I • fderiv ℝ g w (1 : ℂ) := by
    filter_upwards [hhol] with w hw
    have hfw := (hw.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
    simp [hfw]
  have heq_deriv : deriv g =ᶠ[𝓝 z] fun w ↦ fderiv ℝ g w (1 : ℂ) := by
    filter_upwards [hhol] with w hw
    have hfw := (hw.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
    simp [hfw]
  have hdr : DifferentiableAt ℝ (deriv g) z := h1.congr_of_eventuallyEq heq_deriv
  have hsymm := hg.isSymmSndFDerivAt (by norm_num)
  have h1_1 : fderiv ℝ (fun w ↦ fderiv ℝ g w (1 : ℂ)) z (1 : ℂ) =
      fderiv ℝ (fderiv ℝ g) z (1 : ℂ) (1 : ℂ) := by
    simpa [Function.comp_def] using congrArg (fun L : ℂ →L[ℝ] G ↦ L 1)
      ((ContinuousLinearMap.apply ℝ G (1 : ℂ)).hasFDerivAt.comp z hDfd.hasFDerivAt).fderiv
  have hL1 : fderiv ℝ (deriv g) z (1 : ℂ) = fderiv ℝ (fderiv ℝ g) z (1 : ℂ) (1 : ℂ) := by
    rw [heq_deriv.fderiv_eq, h1_1]
  have hLI : fderiv ℝ (deriv g) z Complex.I = Complex.I • fderiv ℝ (deriv g) z (1 : ℂ) := by
    have hL1I : fderiv ℝ (deriv g) z Complex.I = fderiv ℝ (fderiv ℝ g) z Complex.I (1 : ℂ) := by
      rw [heq_deriv.fderiv_eq]
      simpa [Function.comp_def] using congrArg (fun L : ℂ →L[ℝ] G ↦ L Complex.I)
        ((ContinuousLinearMap.apply ℝ G (1 : ℂ)).hasFDerivAt.comp z hDfd.hasFDerivAt).fderiv
    have hLHS : fderiv ℝ (fun w ↦ fderiv ℝ g w Complex.I) z (1 : ℂ) =
        fderiv ℝ (fderiv ℝ g) z (1 : ℂ) Complex.I := by
      simpa [Function.comp_def] using congrArg (fun L : ℂ →L[ℝ] G ↦ L 1)
        ((ContinuousLinearMap.apply ℝ G Complex.I).hasFDerivAt.comp z hDfd.hasFDerivAt).fderiv
    have hRHS : fderiv ℝ (fun w ↦ Complex.I • fderiv ℝ g w (1 : ℂ)) z (1 : ℂ) =
        Complex.I • fderiv ℝ (fderiv ℝ g) z (1 : ℂ) (1 : ℂ) := by
      have hc := ((ContinuousLinearMap.lsmul ℝ ℂ (E := G) Complex.I).hasFDerivAt.comp z
        h1.hasFDerivAt).fderiv
      have hcr1 : fderiv ℝ (fun w ↦ Complex.I • fderiv ℝ g w (1 : ℂ)) z (1 : ℂ) =
          Complex.I • fderiv ℝ (fun w ↦ fderiv ℝ g w (1 : ℂ)) z (1 : ℂ) := by
        simpa [Function.comp_def] using congrArg (fun L : ℂ →L[ℝ] G ↦ L 1) hc
      rw [hcr1, h1_1]
    rw [hL1I, hsymm Complex.I (1 : ℂ), ← hLHS, hcr.fderiv_eq, hRHS, hL1]
  let L' : ℂ →L[ℂ] G := (ContinuousLinearMap.id ℂ ℂ).smulRight (fderiv ℝ (deriv g) z (1 : ℂ))
  have hres : L'.restrictScalars ℝ = fderiv ℝ (deriv g) z := by
    ext v
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simp [Complex.real_smul]
    conv_rhs => rw [hv]
    rw [map_add, map_smul, map_smul, hLI]
    simp only [L', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
    conv_lhs => rw [hv]
    rw [add_smul, smul_assoc, smul_assoc, one_smul]
  refine ⟨L', hasFDerivAt_iff_isLittleO_nhds_zero.mpr ?_⟩
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.mp hdr.hasFDerivAt
  simpa only [← hres, ContinuousLinearMap.coe_restrictScalars'] using ho

/-- If `g : ℂ → G` is real `C²` and holomorphic on an open set `V ⊆ ℂ`, then `deriv g` is
holomorphic on `V`, without requiring completeness of `G`. -/
theorem ContDiffOn.differentiableOn_complex_deriv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] {g : ℂ → G} {V : Set ℂ} (hg : ContDiffOn ℝ 2 g V) (hV : IsOpen V)
    (hhol : DifferentiableOn ℂ g V) :
    DifferentiableOn ℂ (deriv g) V := fun _ hz ↦
  ((hg.contDiffAt (hV.mem_nhds hz)).differentiableAt_complex_deriv
    (Filter.eventually_of_mem (hV.mem_nhds hz) fun _ hw ↦
      hhol.differentiableAt (hV.mem_nhds hw))).differentiableWithinAt

end ComplexDeriv
