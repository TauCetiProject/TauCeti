/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

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

/-! ### Closure properties -/

/-- The zero smooth two-form is closed. -/
theorem isClosed_zero : (0 : SmoothTwoForm I M).IsClosed := by
  change mextDeriv (0 : SmoothTwoForm I M).1 = (0 : RoughForm I M ℝ (2 + 1))
  have h := congrArg Subtype.val
    ((mextDerivₗ (F := ℝ) I 2).map_zero :
      (mextDerivₗ (F := ℝ) I 2) (0 : SmoothForm I M ℝ 2) = 0)
  rw [mextDerivₗ_apply] at h
  change mextDeriv (0 : SmoothTwoForm I M).1 = (0 : SmoothForm I M ℝ (2 + 1)).1
  exact h

/-- The sum of two closed smooth two-forms is closed. -/
theorem IsClosed.add {form' : SmoothTwoForm I M} (h : form.IsClosed)
    (h' : form'.IsClosed) : (form + form').IsClosed := by
  change mextDeriv (form + form').1 = 0
  have hsum : mextDeriv (form + form').1 = mextDeriv form.1 + mextDeriv form'.1 := by
    rw [← mextDerivₗ_apply (F := ℝ), ← mextDerivₗ_apply (F := ℝ),
      ← mextDerivₗ_apply (F := ℝ)]
    exact congrArg Subtype.val ((mextDerivₗ (F := ℝ) I 2).map_add form form')
  rw [hsum, h, h', add_zero]

/-- A real scalar multiple of a closed smooth two-form is closed. -/
theorem IsClosed.smul (c : ℝ) (h : form.IsClosed) : (c • form).IsClosed := by
  change mextDeriv (c • form).1 = 0
  have hsmul : mextDeriv (c • form).1 = c • mextDeriv form.1 := by
    rw [← mextDerivₗ_apply (F := ℝ), ← mextDerivₗ_apply (F := ℝ)]
    exact congrArg Subtype.val ((mextDerivₗ (F := ℝ) I 2).map_smul c form)
  rw [hsmul, h, smul_zero]

/-- The negative of a closed smooth two-form is closed. -/
theorem IsClosed.neg (h : form.IsClosed) : (-form).IsClosed := by
  change mextDeriv (-form.1) = 0
  rw [mextDeriv_neg, h, neg_zero]

/-- The difference of two closed smooth two-forms is closed. -/
theorem IsClosed.sub {form' : SmoothTwoForm I M} (h : form.IsClosed)
    (h' : form'.IsClosed) : (form - form').IsClosed := by
  rw [sub_eq_add_neg]
  exact SmoothTwoForm.IsClosed.add (form := form) h
    (SmoothTwoForm.IsClosed.neg (form := form') h')

end SmoothTwoForm

end TauCeti

end
