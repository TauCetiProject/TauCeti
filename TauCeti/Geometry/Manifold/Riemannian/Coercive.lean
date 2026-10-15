/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Riemannian metrics on a vector space from coercive bilinear forms

A real normed space `F` is a manifold modelled on itself, and its tangent space at every point is
`F`. Many Riemannian metrics are written in such global coordinates, as a field
`g : F → F →L[ℝ] F →L[ℝ] ℝ` of symmetric bilinear forms; examples are the left-invariant metrics
of the three-dimensional model geometries Nil and Sol on `ℝ³`. This file shows that such a field
is a `C^n` Riemannian metric as soon as it is `C^n` and each `g x` is coercive
(`IsCoercive (g x)`: `C ‖v‖² ≤ g x v v` for some `C > 0` depending on `x`). Coercivity makes `g x`
positive definite and its unit ball bounded, as `ContMDiffRiemannianMetric` requires. Mathlib's
`riemannianMetricVectorSpace` is the constant field given by the inner product of an inner product
space.

## Main definitions

* `TauCeti.coerciveRiemannianMetric`: the `C^n` Riemannian metric on `F` given by a `C^n` field of
  symmetric coercive bilinear forms.
-/

public section

open Bundle Bornology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

private theorem trivializationAt_symm_vectorSpace (x y : F) (v : F) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F) : F → Type _) x).symm y v =
      (tangentSpaceCastModel 𝓘(ℝ, F) y).symm v := by
  rw [← Trivialization.symmL_apply (R := ℝ) _ (by simp),
    TangentBundle.symmL_trivializationAt_eq_core (by simp)]
  exact tangentCoordChange_self (x := y) (I := 𝓘(ℝ, F)) (by simp)

/-- A `C^n` field of symmetric coercive bilinear forms on a real normed space `F` is a `C^n`
Riemannian metric on `F`, with inner product `g x` on the tangent space at `x`. -/
def coerciveRiemannianMetric (g : F → F →L[ℝ] F →L[ℝ] ℝ) (hg : ContDiff ℝ n g)
    (symm : ∀ x v w, g x v w = g x w v) (coercive : ∀ x, IsCoercive (g x)) :
    ContMDiffRiemannianMetric 𝓘(ℝ, F) n F (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) where
  inner x :=
    let e := tangentSpaceCastModel 𝓘(ℝ, F) x
    e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g x)
  symm x v w := by
    simpa [ContinuousLinearEquiv.arrowCongr_apply] using symm x _ _
  pos x v hv := by
    obtain ⟨C, hC, h⟩ := coercive x
    have : 0 < ‖tangentSpaceCastModel 𝓘(ℝ, F) x v‖ := by simpa using hv
    simpa [ContinuousLinearEquiv.arrowCongr_apply] using
      lt_of_lt_of_le (by positivity) (h (tangentSpaceCastModel 𝓘(ℝ, F) x v))
  isVonNBounded x := by
    obtain ⟨C, hC, h⟩ := coercive x
    let e := tangentSpaceCastModel 𝓘(ℝ, F) x
    refine ((NormedSpace.isVonNBounded_closedBall ℝ F (1 + C⁻¹)).image
      e.symm.toContinuousLinearMap).subset ?_
    intro v hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    have hv : g x (e v) (e v) < 1 := by
      simpa [ContinuousLinearEquiv.arrowCongr_apply, e] using hv
    rw [mem_closedBall_zero_iff]
    by_contra! hlt
    have h1 : 1 < ‖e v‖ := lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hlt
    have h2 : C * (1 + C⁻¹) < C * ‖e v‖ := mul_lt_mul_of_pos_left hlt hC
    rw [mul_add, mul_inv_cancel₀ hC.ne'] at h2
    nlinarith [h (e v)]
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert hg.contMDiff.contMDiffAt (x := x) using 1
    ext y v w
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]
    simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      trivializationAt_symm_vectorSpace, ContinuousLinearEquiv.arrowCongr_apply]

/-- The metric `coerciveRiemannianMetric g` is `g x` on the tangent space at `x`, read in the
model space `F`. -/
@[simp]
theorem coerciveRiemannianMetric_inner (g : F → F →L[ℝ] F →L[ℝ] ℝ) (hg : ContDiff ℝ n g)
    (symm : ∀ x v w, g x v w = g x w v) (coercive : ∀ x, IsCoercive (g x)) (x : F)
    (v w : TangentSpace 𝓘(ℝ, F) x) :
    (coerciveRiemannianMetric g hg symm coercive).inner x v w =
      g x (tangentSpaceCastModel 𝓘(ℝ, F) x v) (tangentSpaceCastModel 𝓘(ℝ, F) x w) :=
  (rfl)

end TauCeti
