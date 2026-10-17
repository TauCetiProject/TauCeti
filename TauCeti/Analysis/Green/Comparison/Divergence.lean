/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.RectangleComparison
public import TauCeti.LinearAlgebra.Trace.Complex

/-!
# Rectangle flux and the existing Euclidean divergence theorem

The divergence of a real differentiable complex vector field is the actual trace of its real
Fréchet derivative. On a rectangle, its complex-area integral agrees with the existing Mathlib
divergence theorem and Green's finite-chain flux. The rectangle's four side integrals use the
actual outward unit vectors `-I, 1, I, -1`.
-/

public section

noncomputable section

open MeasureTheory Set Complex
open scoped InnerProductSpace

namespace TauCeti.Green

/-- Green's rectangle flux is the actual outward-unit-normal functional on its four sides. -/
theorem integral_rectangle_flux_eq_outward {a b c e : ℝ} (hab : a < b) (hce : c < e)
    {F : ℂ → ℂ} (hF : ContinuousOn F (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e))) :
    let C := (Division.rectangleRe a b c e hab hce).boundary
    BoundaryChain.Integrable Complex.reCLM (fun z ↦ -(F z).im) C ∧
      BoundaryChain.Integrable Complex.imCLM (fun z ↦ (F z).re) C ∧
      BoundaryChain.integral Complex.reCLM (fun z ↦ -(F z).im) C +
        BoundaryChain.integral Complex.imCLM (fun z ↦ (F z).re) C =
          ((∫ x in a..b, ⟪F ⟨x, c⟩, -I⟫_ℝ) + ∫ y in c..e, ⟪F ⟨b, y⟩, 1⟫_ℝ) +
            ((∫ x in a..b, ⟪F ⟨x, e⟩, I⟫_ℝ) + ∫ y in c..e, ⟪F ⟨a, y⟩, -1⟫_ℝ) := by
  have h := integral_rectangle_boundary hab hce
    (Complex.continuous_im.comp_continuousOn hF).neg
    (Complex.continuous_re.comp_continuousOn hF)
  simp only [Function.comp_apply, Pi.neg_apply] at h
  refine ⟨h.1, h.2.1, ?_⟩
  have hh := h.2.2
  refine hh.trans ?_
  simp [Complex.inner]
  ring

/-- The actual trace-divergence integral against complex area equals Green's rectangle flux.
Integrability is derived from local `C¹` regularity; the equality consumes the existing Euclidean
rectangle divergence theorem through its established finite-chain comparison. -/
theorem integral_rectangle_flux_eq_trace {a b c e : ℝ} (hab : a < b) (hce : c < e)
    {F : ℂ → ℂ} (hF : ∀ z ∈ verticalRegion a b (fun _ ↦ c) (fun _ ↦ e), ContDiffAt ℝ 1 F z) :
    let C := (Division.rectangleRe a b c e hab hce).boundary
    BoundaryChain.Integrable Complex.reCLM (fun z ↦ -(F z).im) C ∧
      BoundaryChain.Integrable Complex.imCLM (fun z ↦ (F z).re) C ∧
      IntegrableOn (fun z ↦ LinearMap.trace ℝ ℂ (fderiv ℝ F z).toLinearMap)
        (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e)) ∧
      BoundaryChain.integral Complex.reCLM (fun z ↦ -(F z).im) C +
        BoundaryChain.integral Complex.imCLM (fun z ↦ (F z).re) C =
          ∫ z in verticalRegion a b (fun _ ↦ c) (fun _ ↦ e),
            LinearMap.trace ℝ ℂ (fderiv ℝ F z).toLinearMap := by
  let T := Complex.equivRealProdCLM.symm
  let f := fun p : ℝ × ℝ ↦ (F (T p)).re
  let g := fun p : ℝ × ℝ ↦ (F (T p)).im
  let f' := fun p ↦ Complex.reCLM.comp ((fderiv ℝ F (T p)).comp T.toContinuousLinearMap)
  let g' := fun p ↦ Complex.imCLM.comp ((fderiv ℝ F (T p)).comp T.toContinuousLinearMap)
  have hmem {p : ℝ × ℝ} (hp : p ∈ Icc (a, c) (b, e)) :
      T p ∈ verticalRegion a b (fun _ ↦ c) (fun _ ↦ e) := by
    simpa [mem_verticalRegion, T, Complex.equivRealProdCLM_symm_apply] using
      ⟨⟨hp.1.1, hp.2.1⟩, hp.1.2, hp.2.2⟩
  have hd {p : ℝ × ℝ} (hp : p ∈ Icc (a, c) (b, e)) :
      HasFDerivAt (fun q ↦ F (T q)) ((fderiv ℝ F (T p)).comp T.toContinuousLinearMap) p :=
    ((hF _ (hmem hp)).differentiableAt one_ne_zero).hasFDerivAt.comp p T.hasFDerivAt
  have hcf : ContinuousOn f (Icc (a, c) (b, e)) :=
    fun p hp ↦ ((Complex.reCLM.hasFDerivAt.comp p (hd hp)).continuousAt).continuousWithinAt
  have hcg : ContinuousOn g (Icc (a, c) (b, e)) :=
    fun p hp ↦ ((Complex.imCLM.hasFDerivAt.comp p (hd hp)).continuousAt).continuousWithinAt
  have heq (p : ℝ × ℝ) : f' p (1, 0) + g' p (0, 1) =
      LinearMap.trace ℝ ℂ (fderiv ℝ F (T p)).toLinearMap := by
    rw [LinearMap.trace_complex_apply]
    simp [f', g', T, Complex.equivRealProdCLM_symm_apply]
  have hcont : ContinuousOn (fun z ↦ LinearMap.trace ℝ ℂ (fderiv ℝ F z).toLinearMap)
      (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e)) := by
    simp_rw [LinearMap.trace_complex_apply]
    intro z hz
    have hdF := (hF z hz).continuousAt_fderiv (by norm_num)
    exact ((Complex.continuous_re.continuousAt.comp
      (hdF.clm_apply (g := fun _ ↦ (1 : ℂ)) continuousAt_const)).add
        (Complex.continuous_im.continuousAt.comp
          (hdF.clm_apply (g := fun _ ↦ I) continuousAt_const))).continuousWithinAt
  have hi := hcont.integrableOn_compact (μ := volume)
    (isCompact_verticalRegion continuousOn_const continuousOn_const)
  have hpre : Complex.measurableEquivRealProd ⁻¹' Icc (a, c) (b, e) =
      verticalRegion a b (fun _ ↦ c) (fun _ ↦ e) := by
    ext z
    simp only [mem_preimage, Complex.measurableEquivRealProd_apply, mem_Icc,
      Prod.le_def, mem_verticalRegion]
    tauto
  have hprod : IntegrableOn (fun p ↦ f' p (1, 0) + g' p (0, 1)) (Icc (a, c) (b, e)) := by
    apply (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mp
    simpa only [hpre, heq, Function.comp_def, T, Complex.equivRealProdCLM_symm_apply,
      Complex.measurableEquivRealProd_apply, Complex.re_add_im] using hi
  have hcomp := integral_rectangle_boundary_eq_divergence f g f' g' (a, c) (b, e) hab hce
    ∅ countable_empty hcf hcg
    (fun p hp ↦ Complex.reCLM.hasFDerivAt.comp p (hd
      ⟨⟨hp.1.1.1.le, hp.1.2.1.le⟩, hp.1.1.2.le, hp.1.2.2.le⟩))
    (fun p hp ↦ Complex.imCLM.hasFDerivAt.comp p (hd
      ⟨⟨hp.1.1.1.le, hp.1.2.1.le⟩, hp.1.1.2.le, hp.1.2.2.le⟩)) hprod
  have harea := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p ↦ f' p (1, 0) + g' p (0, 1)) (Icc (a, c) (b, e))
  rw [hpre] at harea
  simp only [f, g, T, Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] at hcomp
  have harea' : (∫ p in Icc (a, c) (b, e), f' p (1, 0) + g' p (0, 1)) =
      ∫ z in verticalRegion a b (fun _ ↦ c) (fun _ ↦ e),
        LinearMap.trace ℝ ℂ (fderiv ℝ F z).toLinearMap := by
    rw [← harea]
    apply setIntegral_congr_fun (measurableSet_verticalRegion continuousOn_const continuousOn_const)
    intro z hz
    dsimp only
    rw [heq]
    simp only [T, Complex.measurableEquivRealProd_apply,
      Complex.equivRealProdCLM_symm_apply, Complex.re_add_im]
  exact ⟨hcomp.1, hcomp.2.1, hi, hcomp.2.2.trans harea'⟩

end TauCeti.Green
