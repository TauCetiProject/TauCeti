/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curvature.Ricci.Continuity
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Topology.VectorBundle.Riemannian.Comparison

/-!
# Uniform positive Ricci bounds on compact manifolds

A continuous positive-definite Ricci tensor has a uniform positive lower bound on a compact
Riemannian manifold. The native Ricci tensor is read as a section of the bilinear-form bundle,
so the compact-bundle coercivity theorem applies directly.
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Compactness turns a pointwise positive Ricci tensor into a uniform bound
`k ‖v‖² ≤ Ric(v,v)` with `k > 0`. -/
theorem exists_pos_mul_norm_sq_le_ricciTensor_of_compactSpace
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (leviCivitaConnection I M).ricciTensor x v v) :
    ∃ k > 0, ∀ (x : M) (v : TangentSpace I x),
      k * ‖v‖ ^ 2 ≤ (leviCivitaConnection I M).ricciTensor x v v := by
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
      (F := E) (V := fun x : M ↦ TangentSpace I x)
  have hcont : Continuous (fun x : M ↦
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
        ((leviCivitaConnection I M).ricciTensor x).toContinuousBilinearMap) :=
    continuous_leviCivita_ricciTensor (I := I) (M := M)
  obtain ⟨k, hk, hle⟩ := isCompact_univ.exists_pos_forall_mul_norm_sq_le_bundle
    (b := id) hcont.continuousOn
      (fun x _ v hv ↦ hpos x v hv)
  exact ⟨k, hk, fun x v ↦ hle x (mem_univ x) v⟩

end TauCeti.Manifold
