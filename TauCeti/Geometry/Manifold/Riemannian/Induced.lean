/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Pullback

/-!
# Riemannian metrics induced by immersions into inner product spaces

A `C^(n+1)` map `f : M → F` from a finite-dimensional manifold to a real inner product space whose
differential is injective at every point pulls the inner product of `F` back to a `C^n` Riemannian
metric on `M`:

`g_x(v, w) = ⟪df_x v, df_x w⟫`.

This is the first fundamental form of an immersed submanifold of Euclidean space, and the way
the classical model spaces such as the round sphere receive their metrics.

## Main definitions

* `TauCeti.inducedRiemannianMetric`: the `C^n` Riemannian metric induced by such a map.

## Main statements

* `TauCeti.inducedRiemannianMetric_inner`: the induced inner product of two tangent vectors is the
  inner product of their images under the differential.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics on immersed submanifolds).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ∞ω}
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The Riemannian metric induced on `M` by a `C^(n+1)` map `f : M → F` into a real inner product
space whose differential is injective at every point: the inner product of two tangent vectors is
the inner product of their images under the differential `mvfderiv I f x` of `f`, read in `F`. -/
def inducedRiemannianMetric (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) (n + 1) f)
    (hinj : ∀ x, Function.Injective (mvfderiv I f x)) :
    ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x) where
  inner x := (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).bilinearComp
    (E' := E) (F' := E) (mvfderiv I f x) (mvfderiv I f x)
  symm _ _ _ := real_inner_comm _ _
  pos x _ hv := real_inner_self_pos.2
    ((map_ne_zero_iff (mvfderiv I f x : E →L[ℝ] F) (hinj x)).2 hv)
  isVonNBounded x := by
    -- An injective linear map from a finite-dimensional space is antilipschitz, so the
    -- preimage of the ambient unit ball is bounded.
    -- Use the model norm on `E`, since the Riemannian norm on the tangent space is being built.
    let A : E →L[ℝ] F := mvfderiv I f x
    obtain ⟨K, -, hK⟩ := A.toLinearMap.exists_antilipschitzWith
      (LinearMap.ker_eq_bot.2 (hinj x))
    refine NormedSpace.isVonNBounded_of_isBounded ℝ (E := E)
      ((hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : F)) (r := 1))).subset ?_)
    intro v hv
    have hv' : inner ℝ (A v) (A v) < 1 := hv
    rw [real_inner_self_eq_norm_sq] at hv'
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, ContinuousLinearMap.coe_coe]
    nlinarith only [hv']
  contMDiff x := by
    -- This is the pullback of the standard Riemannian metric on `F`.
    exact contMDiffAt_bilinearForm_pullback
      ((riemannianMetricVectorSpace F).contMDiff (f x) |>.of_le le_top) (hf x)

/-- The induced inner product of two tangent vectors is the inner product of their images under
the differential. -/
@[simp]
theorem inducedRiemannianMetric_inner (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) (n + 1) f)
    (hinj : ∀ x, Function.Injective (mvfderiv I f x)) (x : M) (v w : TangentSpace I x) :
    (inducedRiemannianMetric f hf hinj).inner x v w =
      inner ℝ (mvfderiv I f x v) (mvfderiv I f x w) :=
  (rfl)

end TauCeti
