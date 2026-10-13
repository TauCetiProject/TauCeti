/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.TopDegree
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Signed top-form integrals in preferred charts

A chart sign is indexed only by points of that chart's source. Signed coefficients are extended
by zero outside the coordinate target. On an actual chart overlap, the signed coefficient
integrals and their integrability agree by the Jacobian theorem and the top-form chart cocycle.
Only the model carries a measurable structure; no measurable structure on the manifold is used.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- A signed top-form coefficient in a preferred chart, extended by zero outside its target.
The sign data have no values outside the source of the chart. -/
def signedInChartAt (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) : ℝ := by
  classical
  exact if hy : y ∈ (extChartAt I α).target then
    (σ ⟨(extChartAt I α).symm y, (extChartAt I α).map_target hy⟩ : ℝ) * φ.inChartAt α y b
  else 0

open scoped Classical in
/-- Evaluation of the signed coefficient, with its zero extension outside the target. -/
theorem signedInChartAt_apply (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E)
    (α : M) (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    φ.signedInChartAt b α σ y =
      if hy : y ∈ (extChartAt I α).target then
        (σ ⟨(extChartAt I α).symm y, (extChartAt I α).map_target hy⟩ : ℝ) *
          φ.inChartAt α y b
      else 0 := (rfl)

/-- Within the chart source, the coefficient uses precisely the sign at the original point. -/
theorem signedInChartAt_apply_of_mem_source (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) {x : M}
    (hx : x ∈ (extChartAt I α).source) :
    φ.signedInChartAt b α σ (extChartAt I α x) =
      (σ ⟨x, hx⟩ : ℝ) * φ.inChartAt α (extChartAt I α x) b := by
  rw [signedInChartAt, dite_eq_left ((extChartAt I α).map_source hx)]
  have he :
      (⟨(extChartAt I α).symm (extChartAt I α x),
        (extChartAt I α).map_target ((extChartAt I α).map_source hx)⟩ :
          {x : M // x ∈ (extChartAt I α).source}) = ⟨x, hx⟩ :=
    Subtype.ext ((extChartAt I α).left_inv hx)
  rw [he]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Signed preferred-chart integrals and integrability agree on an actual overlap. The
compatibility condition is the signed transition Jacobian, not an assumed integral identity.
The derivatives are taken within `range I`, so the result includes boundary and corner models. -/
theorem signedInChartAt_changeChart [IsManifold I 1 M]
    (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α β : M)
    (σα : {x : M // x ∈ (extChartAt I α).source} → ℤˣ)
    (σβ : {x : M // x ∈ (extChartAt I β).source} → ℤˣ)
    {s : Set M} (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s))
    (hσ : ∀ x (hx : x ∈ s),
      (σα ⟨x, (hsub hx).1⟩ : ℝ) *
        (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
          (extChartAt I α x)).toLinearMap.det =
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
          (extChartAt I α x)).toLinearMap.det| * (σβ ⟨x, (hsub hx).2⟩ : ℝ))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∫ y in (extChartAt I α) '' s, φ.signedInChartAt b α σα y ∂μ) =
        (∫ y in (extChartAt I β) '' s, φ.signedInChartAt b β σβ y ∂μ) ∧
      (IntegrableOn (φ.signedInChartAt b α σα) ((extChartAt I α) '' s) μ ↔
        IntegrableOn (φ.signedInChartAt b β σβ) ((extChartAt I β) '' s) μ) := by
  let A := (extChartAt I α) '' s
  let e := (extChartAt I α).symm ≫ extChartAt I β
  let D := fun y ↦ fderivWithin ℝ
    (extChartAt I β ∘ (extChartAt I α).symm) (range I) y
  have hA_target : A ⊆ (extChartAt I α).target :=
    (image_mono (hsub.trans inter_subset_left)).trans
      (extChartAt I α).image_source_eq_target.subset
  have hA_range : A ⊆ range I := hA_target.trans (extChartAt_target_subset_range α)
  have hA_source : A ⊆ e.source := by
    rintro _ ⟨x, hx, rfl⟩
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
      (extChartAt I α).left_inv (hsub hx).1]
    exact ⟨(extChartAt I α).map_source (hsub hx).1, (hsub hx).2⟩
  have himage : e '' A = (extChartAt I β) '' s := by
    simp only [A, image_image]
    apply image_congr
    intro x hx
    exact congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)
  have hderiv : ∀ y ∈ A, HasFDerivWithinAt e (D y) A y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hasFDerivWithinAt_tangentCoordChange (I := I) (hsub hx)).mono hA_range
  have hcoef : ∀ y ∈ A,
      |(D y).toLinearMap.det| • φ.signedInChartAt b β σβ (e y) =
        φ.signedInChartAt b α σα y := by
    rintro _ ⟨x, hx, rfl⟩
    have he : e (extChartAt I α x) = extChartAt I β x := by
      exact congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)
    rw [he, signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).1,
      signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).2]
    have hc := φ.inChartAt_apply_basis_eq_det_mul b
      ((extChartAt I α).map_source (hsub hx).1)
      (show (extChartAt I α).symm (extChartAt I α x) ∈ (extChartAt I β).source by
        rw [(extChartAt I α).left_inv (hsub hx).1]; exact (hsub hx).2)
    rw [(extChartAt I α).left_inv (hsub hx).1] at hc
    rw [hc, smul_eq_mul, ← mul_assoc, ← mul_assoc, hσ x hx]
  constructor
  · rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul μ hs hderiv
      (e.injOn.mono hA_source)]
    exact setIntegral_congr_fun hs fun y hy ↦ (hcoef y hy).symm
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hderiv
      (e.injOn.mono hA_source)]
    exact (integrableOn_congr_fun (fun y hy ↦ hcoef y hy) hs).symm

end TauCeti.RoughForm
