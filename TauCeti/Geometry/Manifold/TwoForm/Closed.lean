/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Symplectic.Liouville.Linear

/-!
# Closed smooth differential two-forms

This module supplies the constant-form convenience theorems for smooth two-forms: a constant
two-form `SmoothTwoForm.const B` on a model space is closed, and it is even exact, the exterior
derivative of the radial one-form `λₓ(v) = B(x, v) / 2` (`ContinuousLinearMap.liouvilleFormCLM`).
The generic closedness predicate and its chartwise API are defined in `DifferentialForm.Closed`.
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

/-- Constant forms on a model space are closed. -/
theorem isClosed_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    (const B : SmoothTwoForm (modelWithCornersSelf ℝ V) V).IsClosed := by
  rw [const_eq]
  exact SmoothForm.isClosed_const
    ((2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B)

/-- Constant forms on a model space are exact: `const B` is the exterior derivative of the radial
one-form `λₓ(v) = B(x, v) / 2`. -/
theorem val_const_eq_mextDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    (const B : SmoothTwoForm 𝓘(ℝ, V) V).val =
      mextDeriv (fun x ↦ B.liouvilleFormCLM x : RoughForm 𝓘(ℝ, V) V ℝ 1) := by
  funext x
  refine Eq.trans ?_ (mextDeriv_eq_extDeriv (E := V) (F := ℝ) (k := 1) _ x).symm
  rw [ContinuousLinearMap.extDeriv_liouvilleFormCLM, const_eq]
  ext v
  simp only [SmoothForm.const_apply, NormedSpace.fromTangentSpace_apply]
  -- The two sides differ by the eta-expansion `fun i ↦ v i` of the tuple of tangent vectors.
  rfl

end SmoothTwoForm

end TauCeti

end
