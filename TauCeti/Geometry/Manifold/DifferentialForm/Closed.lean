/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Closed smooth differential forms

Closedness is the vanishing of the generic manifold exterior derivative of a smooth form.  The
degree-two specialization in `TwoForm.Closed` only supplies its constant-form convenience
theorem; the predicate and its generic API live here so they can be reused at every degree.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
variable {form : SmoothForm I M F k}

/-- A smooth form is closed when the generic manifold exterior derivative vanishes. -/
def IsClosed (form : SmoothForm I M F k) : Prop := mextDeriv form.1 = 0

/-- The zero smooth form is closed. -/
theorem isClosed_zero : (0 : SmoothForm I M F k).IsClosed := by
  change mextDeriv (0 : RoughForm I M F k) = 0
  exact mextDeriv_zero

/-- The sum of two closed smooth forms is closed. -/
theorem IsClosed.add {form' : SmoothForm I M F k} (h : form.IsClosed)
    (h' : form'.IsClosed) : (form + form').IsClosed := by
  change mextDeriv (form + form').1 = 0
  change mextDeriv (form.1 + form'.1) = 0
  have hform : IsSmoothForm I ∞ form.1 := by
    exact (isSmoothForm_def ∞ _).mpr
      ((isSmoothBundleForm_def ∞ _).mp (mem_smoothForms.mp form.2))
  have hform' : IsSmoothForm I ∞ form'.1 := by
    exact (isSmoothForm_def ∞ _).mpr
      ((isSmoothBundleForm_def ∞ _).mp (mem_smoothForms.mp form'.2))
  funext x
  rw [mextDeriv_add
    ((hform.contDiffWithinAt_inChartAt_self x).differentiableWithinAt (by simp))
    ((hform'.contDiffWithinAt_inChartAt_self x).differentiableWithinAt (by simp)), h, h']
  simp

/-- A real scalar multiple of a closed smooth form is closed. -/
theorem IsClosed.smul (c : ℝ) (h : form.IsClosed) : (c • form).IsClosed := by
  change mextDeriv (c • form.1) = 0
  rw [mextDeriv_smul, h, smul_zero]

/-- The negative of a closed smooth form is closed. -/
theorem IsClosed.neg (h : form.IsClosed) : (-form).IsClosed := by
  change mextDeriv (-form.1) = 0
  rw [mextDeriv_neg, h, neg_zero]

/-- The difference of two closed smooth forms is closed. -/
theorem IsClosed.sub {form' : SmoothForm I M F k} (h : form.IsClosed)
    (h' : form'.IsClosed) : (form - form').IsClosed := by
  rw [sub_eq_add_neg]
  exact SmoothForm.IsClosed.add (form := form) h
    (SmoothForm.IsClosed.neg (form := form') h')

/-- Constant forms on a model space are closed. -/
theorem isClosed_const {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : V [⋀^Fin k]→L[ℝ] F) :
    (SmoothForm.const A : SmoothForm (modelWithCornersSelf ℝ V) V F k).IsClosed := by
  change mextDeriv (SmoothForm.const A).1 = 0
  have hconst : (fun y : V => A.compContinuousLinearMap
      (NormedSpace.fromTangentSpace y).toContinuousLinearMap) = fun _ => A := by
    funext y
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    simp [NormedSpace.fromTangentSpace, tangentSpaceCastModel]
    congr 1
  rw [SmoothForm.const_toRoughForm]
  funext x
  rw [mextDeriv_eq_extDeriv, hconst]
  exact ContinuousAlternatingMap.extDeriv_const A x

end SmoothForm

end TauCeti

end
