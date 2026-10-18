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

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
variable {form : SmoothForm I M F k}

/-- A smooth form is closed when the generic manifold exterior derivative vanishes. -/
def IsClosed (form : SmoothForm I M F k) : Prop := mextDeriv form.1 = 0

/-- The zero smooth form is closed. -/
theorem isClosed_zero : (0 : SmoothForm I M F k).IsClosed := by
  -- Unfold the predicate and expose the underlying rough-form zero for `mextDeriv_zero`.
  change mextDeriv (0 : RoughForm I M F k) = 0
  exact mextDeriv_zero

/-- The sum of two closed smooth forms is closed. -/
theorem IsClosed.add {form' : SmoothForm I M F k} (h : form.IsClosed)
    (h' : form'.IsClosed) : (form + form').IsClosed := by
  -- The subtype operation has the pointwise rough-form operation as its value.
  change mextDeriv (form + form').1 = 0
  have hsum : mextDeriv (form + form').1 = mextDeriv form.1 + mextDeriv form'.1 := by
    rw [← mextDerivₗ_apply (F := F) (I := I), ← mextDerivₗ_apply (F := F) (I := I),
      ← mextDerivₗ_apply (F := F) (I := I)]
    exact congrArg Subtype.val ((mextDerivₗ (F := F) I k).map_add form form')
  rw [hsum, h, h', add_zero]

/-- A real scalar multiple of a closed smooth form is closed. -/
theorem IsClosed.smul (c : ℝ) (h : form.IsClosed) : (c • form).IsClosed := by
  -- As above, expose the pointwise scalar operation before applying linearity.
  change mextDeriv (c • form).1 = 0
  have hsmul : mextDeriv (c • form).1 = c • mextDeriv form.1 := by
    rw [← mextDerivₗ_apply (F := F) (I := I), ← mextDerivₗ_apply (F := F) (I := I)]
    exact congrArg Subtype.val ((mextDerivₗ (F := F) I k).map_smul c form)
  rw [hsmul, h, smul_zero]

/-- The negative of a closed smooth form is closed. -/
theorem IsClosed.neg (h : form.IsClosed) : (-form).IsClosed := by
  -- Expose the rough-form negation so the existing derivative law applies directly.
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

namespace SmoothTwoForm

variable (form : SmoothTwoForm I M)

/-- Constant forms on a model space are closed. -/
theorem isClosed_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) :
    (const B hB : SmoothTwoForm (modelWithCornersSelf ℝ V) V).IsClosed := by
  rw [const_eq]
  exact SmoothForm.isClosed_const
    ((2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B)

end SmoothTwoForm

end TauCeti

end
