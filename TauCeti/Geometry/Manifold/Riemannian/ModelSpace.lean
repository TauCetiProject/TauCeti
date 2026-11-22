/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Riemannian metric coefficients on a model space

The metric on the tangent bundle of a real normed space is a field of continuous bilinear
forms on the model space. Its coefficients have the regularity of the metric, and its
Christoffel symbols lose at most one derivative.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- The metric coefficients in the canonical coordinates of a model space have the
regularity of the Riemannian metric. -/
theorem contDiff_riemannianMetric_inner {n : ℕ∞ω}
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) n E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] :
    -- Fix the operator norm before elaborating the dependent fibrewise inner product.
    ContDiff ℝ n (show E → E →L[ℝ] E →L[ℝ] ℝ from fun x ↦
      (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner x) := by
  refine contDiff_clm_apply_iff.2 fun v ↦ contDiff_clm_apply_iff.2 fun w ↦ ?_
  rw [← contDiffOn_univ]
  have h := (contMDiff_id : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) (n + 1) (id : E → E)).contMDiffOn
    |>.contDiffOn_inner_mfderiv le_rfl isOpen_univ v w
  simp only [mfderiv_id] at h
  exact h.congr fun _ _ ↦ rfl

/-- The Christoffel symbols of a `C^m` Riemannian metric on a model space are `C^n`
when `n + 1 ≤ m`. -/
theorem contDiff_christoffelSecondKind_riemannianMetric {m n : ℕ∞ω}
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) m E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]
    (hnm : n + 1 ≤ m) :
    ContDiff ℝ n (christoffelSecondKind
      (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner) := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ contDiffAt_christoffelSecondKind
    (contDiff_riemannianMetric_inner (n := m)).contDiffAt hnm ?_
  apply ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.mp
  apply ContinuousLinearMap.isInvertible_of_pos
  intro v hv
  have hv' : (tangentSpaceCastModel 𝓘(ℝ, E) x).symm v ≠ 0 := by simpa using hv
  exact RiemannianBundle.g.pos x _ hv'

end TauCeti.Manifold
