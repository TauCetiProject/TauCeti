/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.L1Space.Integrable
public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import Mathlib.MeasureTheory.Function.Jacobian
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

/-- A chart coefficient with constant positive sign is the evaluation of the coordinate
form extended by zero outside the target. -/
theorem signedInChartAt_one {j : ℕ} (ψ : RoughForm I M ℝ j)
    (b : Module.Basis (Fin j) ℝ E) (α : M) (y : E) :
    ψ.signedInChartAt b α (fun _ ↦ 1) y =
      ((extChartAt I α).target.indicator (ψ.inChartAt α) y) b := by
  classical
  rw [RoughForm.signedInChartAt_apply]
  split_ifs with hy
  · rw [indicator_of_mem hy]
    simp
  · rw [indicator_of_notMem hy]
    rfl

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
  have himage := TauCeti.extChartAt_coordChange_image α β hsub
  have hinj := TauCeti.injOn_extChartAt_coordChange α β hsub
  have hderiv := TauCeti.hasFDerivWithinAt_extChartAt_coordChange α β hsub
  have hcoef : ∀ y ∈ A,
      |(D y).toLinearMap.det| • φ.signedInChartAt b β σβ (e y) =
        φ.signedInChartAt b α σα y := by
    rintro _ ⟨x, hx, rfl⟩
    have he : e (extChartAt I α x) = extChartAt I β x := by
      exact congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)
    rw [he, signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).1,
      signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).2]
    have hβ : (extChartAt I α).symm (extChartAt I α x) ∈ (extChartAt I β).source := by
      rw [(extChartAt I α).left_inv (hsub hx).1]
      exact (hsub hx).2
    have hc := φ.inChartAt_apply_basis_eq_det_mul b
      ((extChartAt I α).map_source (hsub hx).1)
      hβ
    rw [(extChartAt I α).left_inv (hsub hx).1] at hc
    rw [hc, smul_eq_mul, ← mul_assoc, ← mul_assoc, hσ x hx]
  constructor
  · rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul μ hs hderiv
      hinj]
    exact setIntegral_congr_fun hs fun y hy ↦ (hcoef y hy).symm
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hderiv
      hinj]
    exact (integrableOn_congr_fun (fun y hy ↦ hcoef y hy) hs).symm

/-- Actual integrability of unsigned top-form coefficients is invariant under a chart change.
The absolute Jacobian theorem and a measurable determinant sign preserve both strong
measurability and integrability, even for arbitrary rough forms on nonorientable manifolds. -/
theorem integrableOn_signedInChartAt_one_changeChart [IsManifold I 1 M]
    (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α β : M)
    {s : Set M} (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    IntegrableOn (φ.signedInChartAt b α (fun _ ↦ 1)) ((extChartAt I α) '' s) μ ↔
      IntegrableOn (φ.signedInChartAt b β (fun _ ↦ 1)) ((extChartAt I β) '' s) μ := by
  let A := (extChartAt I α) '' s
  let e := (extChartAt I α).symm ≫ extChartAt I β
  let D := fun y ↦ fderivWithin ℝ
    (extChartAt I β ∘ (extChartAt I α).symm) (range I) y
  have himage := TauCeti.extChartAt_coordChange_image α β hsub
  have hinj := TauCeti.injOn_extChartAt_coordChange α β hsub
  have hderiv := TauCeti.hasFDerivWithinAt_extChartAt_coordChange α β hsub
  rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hderiv hinj]
  have hd : AEStronglyMeasurable (fun y ↦ (D y).toLinearMap.det) (μ.restrict A) :=
    (ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
      (aemeasurable_fderivWithin μ hs hderiv)).aestronglyMeasurable
  have hc : ∀ y ∈ A, φ.signedInChartAt b α (fun _ ↦ 1) y =
      (D y).toLinearMap.det * φ.signedInChartAt b β (fun _ ↦ 1) (e y) := by
    rintro _ ⟨x, hx, rfl⟩
    have he : e (extChartAt I α x) = extChartAt I β x :=
      congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)
    rw [he, signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).1,
      signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).2]
    simp only [Units.val_one, Int.cast_one, one_mul]
    have hβ : (extChartAt I α).symm (extChartAt I α x) ∈ (extChartAt I β).source := by
      rw [(extChartAt I α).left_inv (hsub hx).1]
      exact (hsub hx).2
    have ht := φ.inChartAt_apply_basis_eq_det_mul b
      ((extChartAt I α).map_source (hsub hx).1)
      hβ
    simpa only [(extChartAt I α).left_inv (hsub hx).1] using ht
  rw [integrableOn_congr_fun hc hs]
  simpa only [IntegrableOn, smul_eq_mul] using
    MeasureTheory.integrable_smul_iff_abs_smul (F := ℝ) hd

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A source sign constant on the form's support factors out of the actual chart coefficient. -/
theorem signedInChartAt_eq_const_mul_unsigned
    (ψ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : (extChartAt I α).source → ℤˣ) (c : ℤˣ)
    (hσ : ∀ x : (extChartAt I α).source, (x : M) ∈
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) ψ) → σ x = c) :
    ψ.signedInChartAt b α σ = fun y ↦ (c : ℝ) * ψ.signedInChartAt b α (fun _ ↦ 1) y := by
  classical
  funext y
  rw [signedInChartAt_apply, signedInChartAt_apply]
  by_cases hy : y ∈ (extChartAt I α).target
  · simp only [dite_eq_left hy, Units.val_one, Int.cast_one, one_mul]
    by_cases hx : (extChartAt I α).symm y ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) ψ)
    · rw [hσ ⟨(extChartAt I α).symm y, (extChartAt I α).map_target hy⟩ hx]
    · have hz := _root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) hx
      rw [inChartAt_apply, hz]
      -- The zero form has dependent bundle instances; identify its evaluated model fibre
      -- before scalar rewriting, which cannot match that dependent coercion directly.
      change _ * (0 : ℝ) = _ * 0
      simp only [mul_zero]
  · simp only [dite_eq_right hy, mul_zero]

end TauCeti.RoughForm
