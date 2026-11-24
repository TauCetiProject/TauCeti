/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Tangent coordinate changes of the Riemann sphere

The Riemann sphere `OnePoint ℂ`, regarded as a real surface through its holomorphic charts, has
two charts whose transition map is `w ↦ w⁻¹`. This file computes the resulting tangent coordinate
change from the chart at `∞` to the affine chart: at a nonzero finite point `z` it is
multiplication by `-z²` (`OnePoint.tangentCoordChange_infty_coe`).

For the complex tangent bundle, it also reads tangent vectors in the preferred trivializations:
at a finite point in the affine chart and at `∞` in the inverted chart a tangent vector reads as
itself, while a tangent vector `v` at a nonzero finite point `z` reads in the trivialization at `∞`
as `-z⁻² v` (`OnePoint.trivializationAt_infty_apply_coe`). The base point of such a reading can be
rewritten along an equality of points with `OnePoint.trivializationAt_snd_congr`.

Read in the affine chart, the inclusion `ℂ → OnePoint ℂ` is the identity, so its derivative at
every point is the identity of `ℂ` (`OnePoint.hasMFDerivAt_coe`). The inverses of both charts, the
inclusion and `w ↦ w⁻¹`, are smooth for the real structure (`OnePoint.contMDiff_coe_real`,
`OnePoint.contMDiff_invChart_symm_real`), since they are holomorphic.
-/

public section

open scoped Manifold TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

/-- On the Riemann sphere regarded as a real surface, the inclusion `ℂ → OnePoint ℂ`, the inverse
of the affine chart, is smooth. -/
theorem contMDiff_coe_real {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n ((↑) : ℂ → OnePoint ℂ) := by
  simpa using ((contMDiff_coe (𝕜 := ℂ)).restrictScalars ℝ).of_le le_top

/-- On the Riemann sphere regarded as a real surface, the inverse of the inverted chart,
`0 ↦ ∞` and `w ↦ w⁻¹` for `w ≠ 0`, is smooth. -/
theorem contMDiff_invChart_symm_real {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (invChart.symm : ℂ → OnePoint ℂ) := by
  simpa using ((contMDiff_invChart_symm (𝕜 := ℂ)).restrictScalars ℝ).of_le le_top

/-- On the Riemann sphere regarded as a real surface, the inclusion `ℂ → OnePoint ℂ`, the inverse
of the affine chart, has the identity of `ℂ` as derivative at every point. -/
theorem hasMFDerivAt_coe (z : ℂ) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : ℂ → OnePoint ℂ) z (ContinuousLinearMap.id ℝ ℂ) := by
  refine ⟨continuous_coe.continuousAt, ?_⟩
  -- In the preferred charts, the affine chart at `z` and the identity of the model, the
  -- inclusion reads as the identity.
  have h : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z ((↑) : ℂ → OnePoint ℂ) = id :=
    funext fun _ ↦ by simp [writtenInExtChartAt]
  rw [h]
  exact (hasFDerivAt_id _).hasFDerivWithinAt

/-- On the Riemann sphere regarded as a real surface, the tangent coordinate change from the chart
at `∞` to the chart at a nonzero finite point `z` is multiplication by `-z²`, the derivative of
the chart transition `w ↦ w⁻¹` at `w = z⁻¹`. -/
theorem tangentCoordChange_infty_coe {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    tangentCoordChange 𝓘(ℝ, ℂ) (∞ : OnePoint ℂ) (z : OnePoint ℂ) (z : OnePoint ℂ) v =
      -z ^ 2 * v := by
  have h : HasFDerivAt (fun w : ℂ ↦ w⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z⁻¹ ^ 2)⁻¹)).restrictScalars ℝ) z⁻¹ :=
    (hasDerivAt_inv (inv_ne_zero hz)).hasFDerivAt.restrictScalars ℝ
  simp [affineChart_comp_invChart_symm, h.fderiv, mul_comm]

/-- In the preferred trivialization of the tangent bundle of the Riemann sphere at a finite point,
a tangent vector at a finite point reads as itself: both charts are the affine chart. -/
theorem trivializationAt_coe_apply_coe (z₀ z v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z₀ : OnePoint ℂ) ⟨(z : OnePoint ℂ), v⟩).2 = v := by
  have h : (affineChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∘ affineChart.symm = id :=
    funext fun _ ↦ by simp
  simp [TangentBundle.trivializationAt_apply, h]

/-- In the preferred trivialization of the tangent bundle of the Riemann sphere at `∞`, a tangent
vector at `∞` reads as itself. -/
theorem trivializationAt_infty_apply_infty (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : OnePoint ℂ) ⟨∞, v⟩).2 = v := by
  have h : (invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∘ invChart.symm = id :=
    funext fun _ ↦ invChart.right_inv (by simp)
  simp [TangentBundle.trivializationAt_apply, h]

/-- In the preferred trivialization of the tangent bundle of the Riemann sphere at `∞`, a tangent
vector `v` at a nonzero finite point `z` reads as `-z⁻² v`: the derivative of the chart transition
`z ↦ z⁻¹`. -/
theorem trivializationAt_infty_apply_coe {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : OnePoint ℂ) ⟨(z : OnePoint ℂ), v⟩).2 =
      -(z ^ 2)⁻¹ * v := by
  have h : (invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∘ affineChart.symm = fun w ↦ w⁻¹ :=
    funext fun _ ↦ by simp
  simp [TangentBundle.trivializationAt_apply, h, (hasDerivAt_inv hz).hasFDerivAt.fderiv, mul_comm]

/-- Transport the value of a trivialization of the tangent bundle of the Riemann sphere along an
equality `x = x'` of base points. The fibre `TangentSpace 𝓘(ℂ, ℂ) x` of the point `⟨x, w⟩` of the
total space depends on `x`, so `rw` cannot rewrite `x` there directly: the motive would not be
type-correct. Once the vector `w` is read as an element of `ℂ`, this lemma rewrites the base point
together with the vector. -/
theorem trivializationAt_snd_congr (b : OnePoint ℂ) {x x' : OnePoint ℂ} (h : x = x') (w : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) b ⟨x, w⟩).2 =
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) b ⟨x', w⟩).2 := by
  subst h
  rfl

end OnePoint
