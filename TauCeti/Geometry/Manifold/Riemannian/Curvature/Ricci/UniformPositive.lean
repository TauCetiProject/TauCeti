/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Topology.VectorBundle.Riemannian.Comparison

/-!
# Uniform positive Ricci bounds on compact sets

A continuous positive-definite Ricci tensor has a uniform positive lower bound on each compact
set of a Riemannian manifold. The bound supplies the uniform Ricci hypothesis in Bonnet–Myers;
the global consequences of that theorem are outside this module.

This proof originated in
[`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/dc053c9/ForTauCeti/Geometry/Manifold/Riemannian/Curvature/Ricci/UniformPositive.lean).
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A compact set with positive Ricci tensor has a uniform bound
`k ‖v‖² ≤ Ric(v,v)` with `k > 0` over that set. -/
theorem exists_pos_mul_norm_sq_le_ricciTensor_on_compact
    {K : Set M} (hK : IsCompact K)
    (hpos : ∀ (x : M), x ∈ K → ∀ (v : TangentSpace I x), v ≠ 0 →
      0 < (leviCivitaConnection I M).ricciTensor x v v) :
    ∃ k > 0, ∀ (x : M), x ∈ K → ∀ (v : TangentSpace I x),
      k * ‖v‖ ^ 2 ≤ (leviCivitaConnection I M).ricciTensor x v v := by
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
      (F := E) (V := fun x : M ↦ TangentSpace I x)
  have hcont : Continuous (fun x : M ↦
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
        ((leviCivitaConnection I M).ricciTensor x).toContinuousBilinearMap) :=
    (CovariantDerivative.contMDiff_ricciTensor
      (I := I) (M := M) (leviCivitaConnection I M)).continuous
  obtain ⟨k, hk, hle⟩ := hK.exists_pos_forall_mul_norm_sq_le_bundle
    (b := id) hcont.continuousOn
      (fun x hx v hv ↦ by
        simpa only [LinearMap.toContinuousBilinearMap_apply] using hpos x hx v hv)
  exact ⟨k, hk, fun x hx v ↦ by
    simpa only [LinearMap.toContinuousBilinearMap_apply] using hle x hx v⟩

/-- Pointwise positive Ricci curvature on a compact manifold has a uniform positive bound. -/
theorem exists_pos_mul_norm_sq_le_ricciTensor_of_compactSpace [CompactSpace M]
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (leviCivitaConnection I M).ricciTensor x v v) :
    ∃ k > 0, ∀ (x : M) (v : TangentSpace I x),
      k * ‖v‖ ^ 2 ≤ (leviCivitaConnection I M).ricciTensor x v v := by
  obtain ⟨k, hk, hle⟩ := exists_pos_mul_norm_sq_le_ricciTensor_on_compact
    (I := I) (M := M) isCompact_univ (fun x _ v hv ↦ hpos x v hv)
  exact ⟨k, hk, fun x v ↦ hle x (mem_univ x) v⟩

end TauCeti.Manifold
