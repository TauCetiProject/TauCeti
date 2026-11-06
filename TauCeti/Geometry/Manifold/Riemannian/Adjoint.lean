/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Regularity of the metric adjoint of a differential

For a map between finite-dimensional Riemannian manifolds, the metric adjoint of its
differential sends a regular tangent field along the map to a regular vector field on the
source. The map needs one more derivative than the metrics and the field.

This is the regularity input for the horizontal lift of a Riemannian submersion. The proof
uses the fibrewise Riesz dual and its inverse-Gram-matrix regularity theorem, rather than
identifying the bundle adjoint with the adjoint for a fixed model-space inner product.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.
-/

public section

open Bundle Manifold Riemannian.Tensor
open scoped ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {W : (x : M) → TangentSpace J (f x)} {x : M}

/-- If `f` is `C^(n+1)` at `x` and `W` is a `C^n` tangent field along `f` at `x`, then
`y ↦ (mfderiv I J f y).adjoint (W y)` is `C^n` at `x`, for `C^n` Riemannian metrics. -/
theorem ContMDiffAt.mfderiv_adjoint_apply (hf : ContMDiffAt I J (n + 1) f x)
    (hW : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n (fun y ↦ TotalSpace.mk' F (f y) (W y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y ((mfderiv I J f y).adjoint (W y))) x := by
  let Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ :=
    fun y ↦ (innerSL ℝ (E := TangentSpace J (f y)) (W y)).comp (mfderiv I J f y)
  have hΦ : ∀ j, ContMDiffAt I 𝓘(ℝ) n
      (fun y ↦ Φ y (chartLocalFrame (I := I) x j y)) x := by
    intro j
    have hframe := (contMDiffOn_chartLocalFrame (I := I) (n := n) x j).contMDiffAt
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x))
    exact ContMDiffAt.inner_bundle (E := TangentSpace J) (F := F) (v := W)
      (w := fun y ↦ mfderiv I J f y (chartLocalFrame (I := I) x j y))
      hW (by
        -- The tangent map applied to a section is the bundled differential applied to its field.
        simpa only [Function.comp_def, tangentMap] using
          (hf.contMDiffAt_tangentMap le_rfl).comp x hframe)
  have heq (y : M) : (mfderiv I J f y).adjoint (W y) =
      Riemannian.Tensor.rieszDual (I := I) y (Φ y) := by
    apply Riemannian.Tensor.eq_rieszDual_iff_inner_eq.mpr
    intro v
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  simp_rw [heq]
  exact Riemannian.Tensor.contMDiffAt_rieszDual x (mem_chart_source H x) hΦ

/-- The metric adjoint differential preserves `C^n` regularity of tangent fields along a
`C^(n+1)` map, for `C^n` metrics. -/
theorem ContMDiff.mfderiv_adjoint_apply (hf : ContMDiff I J (n + 1) f)
    (hW : ContMDiff I (J.prod 𝓘(ℝ, F)) n (fun y ↦ TotalSpace.mk' F (f y) (W y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y ((mfderiv I J f y).adjoint (W y))) :=
  fun x ↦ (hf x).mfderiv_adjoint_apply (hW x)
