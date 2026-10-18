/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Closed smooth differential two-forms

Closedness is the vanishing of the generic manifold exterior derivative of the underlying smooth
form. This keeps the symplectic API on the common `SmoothForm` representation and reuses the
coordinate and model-space derivative theorems supplied by the differential-form library.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable (form : SmoothTwoForm I M)

/-- A smooth two-form is closed when its generic manifold exterior derivative vanishes. -/
def IsClosed : Prop := mextDeriv form.1 = 0

private theorem mextDeriv_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) :
    mextDeriv (const B hB).1 = 0 := by
  let A := (2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B
  have hconst : (fun y : V => A.compContinuousLinearMap
      (NormedSpace.fromTangentSpace y).toContinuousLinearMap) = fun _ => A := by
    funext y
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    simp [NormedSpace.fromTangentSpace, tangentSpaceCastModel]
    congr 1
  have hform : (const B hB).1 = fun y => A.compContinuousLinearMap
      (NormedSpace.fromTangentSpace y).toContinuousLinearMap := by
    funext y
    ext v
    have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
    rw [hv]
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    dsimp [A]
    rw [ContinuousAlternatingMap.alternatizeBilinCLM_apply]
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc := const_apply B hB y
      ((NormedSpace.fromTangentSpace y).symm (v 0))
      ((NormedSpace.fromTangentSpace y).symm (v 1))
    rw [SmoothForm.eval₂_apply] at hc
    have hv0 : (NormedSpace.fromTangentSpace y).symm (v 0) = v 0 := rfl
    have hv1 : (NormedSpace.fromTangentSpace y).symm (v 1) = v 1 := rfl
    rw [hv0, hv1] at hc
    have hneg := LinearMap.IsAlt.neg
      (show LinearMap.IsAlt B.toBilinForm from fun z ↦ by
        simpa only [ContinuousLinearMap.toBilinForm_apply] using hB z)
      ((NormedSpace.fromTangentSpace y) (v 0))
      ((NormedSpace.fromTangentSpace y) (v 1))
    have hneg' :
        -B ((NormedSpace.fromTangentSpace y) (v 0))
            ((NormedSpace.fromTangentSpace y) (v 1)) =
          B ((NormedSpace.fromTangentSpace y) (v 1))
            ((NormedSpace.fromTangentSpace y) (v 0)) := by
      simpa only [ContinuousLinearMap.toBilinForm_apply] using hneg
    rw [hc]
    rw [← hneg']
    ring
  rw [hform]
  funext x
  simp only [Pi.zero_apply]
  rw [mextDeriv_eq_extDeriv]
  rw [hconst]
  exact ContinuousAlternatingMap.extDeriv_const A x

/-- Constant forms on a model space are closed. -/
theorem isClosed_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) :
    (const B hB : SmoothTwoForm (modelWithCornersSelf ℝ V) V).IsClosed := by
  change mextDeriv (const B hB).1 = 0
  exact mextDeriv_const B hB

end SmoothTwoForm

end TauCeti

end
