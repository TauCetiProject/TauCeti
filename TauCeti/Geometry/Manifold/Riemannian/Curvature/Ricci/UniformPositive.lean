/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
import TauCeti.Topology.VectorBundle.Riemannian.Comparison

/-!
# Uniform positive Ricci bounds on compact sets

A continuous positive-definite Ricci tensor has a uniform positive lower bound on each compact
set of a Riemannian manifold. The connection may be any smooth tangent connection, and the
background metric need only be continuous. Specializing to the Levi-Civita connection of a smooth
metric supplies the uniform Ricci hypothesis in Bonnet–Myers;
the global consequences of that theorem are outside this module.

This proof originated in
[`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/dc053c9/ForTauCeti/Geometry/Manifold/Riemannian/Curvature/Ricci/UniformPositive.lean).
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A compact set with positive Ricci tensor for a smooth tangent connection has a uniform
bound `k ‖v‖² ≤ Ric(v,v)` with `k > 0`, measured in a continuous background metric. -/
theorem IsCompact.exists_pos_mul_norm_sq_le_ricciTensor
    {K : Set M} (hK : IsCompact K)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (hpos : ∀ (x : M), x ∈ K → ∀ (v : TangentSpace I x), v ≠ 0 →
      0 < cov.ricciTensor x v v) :
    ∃ k > 0, ∀ (x : M), x ∈ K → ∀ (v : TangentSpace I x),
      k * ‖v‖ ^ 2 ≤ cov.ricciTensor x v v := by
  have hcont : Continuous (fun x : M ↦
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
        (cov.ricciTensor x).toContinuousBilinearMap) :=
    cov.contMDiff_ricciTensor.continuous
  obtain ⟨k, hk, hle⟩ := hK.exists_pos_forall_mul_norm_sq_le_bundle
    (b := id) hcont.continuousOn
      (fun x hx v hv ↦ by
        simpa only [LinearMap.toContinuousBilinearMap_apply] using hpos x hx v hv)
  exact ⟨k, hk, fun x hx v ↦ by
    simpa only [LinearMap.toContinuousBilinearMap_apply] using hle x hx v⟩

/-- Pointwise positive Ricci curvature of a smooth tangent connection on a compact manifold
has a uniform positive bound measured in a continuous background metric. -/
theorem CovariantDerivative.exists_pos_mul_norm_sq_le_ricciTensor_of_compactSpace
    [CompactSpace M] (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < cov.ricciTensor x v v) :
    ∃ k > 0, ∀ (x : M) (v : TangentSpace I x),
      k * ‖v‖ ^ 2 ≤ cov.ricciTensor x v v := by
  obtain ⟨k, hk, hle⟩ := isCompact_univ.exists_pos_mul_norm_sq_le_ricciTensor cov
    (fun x _ v hv ↦ hpos x v hv)
  exact ⟨k, hk, fun x v ↦ hle x (mem_univ x) v⟩
