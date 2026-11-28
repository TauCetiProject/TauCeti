/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Constructions
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Dense range, surjectivity, and injectivity of evaluation against dual families

For a `K`-linearly independent family `f : ι → (V →ₗ[K] K)` over a field `K` equipped with any
topology, the product map `LinearMap.pi f : V →ₗ[K] (ι → K)` surjects onto every finite
subfamily of coordinates and hence has dense range (`LinearIndependent.denseRange_pi`). When `V`
is compact and `f : ι → (V →L[K] K)` consists of continuous linear forms into a Hausdorff space
`K`, the evaluation map `ContinuousLinearMap.pi f : V →L[K] (ι → K)` has closed dense range and
is therefore surjective (`LinearIndependent.surjective_continuousLinearMap_pi`). When continuous
linear forms separate points (`SeparatingDual R V`), evaluation against any `R`-spanning family
`f : ι → (V →L[R] R)` is injective (`SeparatingDual.injective_continuousLinearMap_pi`).
-/

public section

open Filter Topology

namespace LinearIndependent

section Field

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {f : ι → (V →ₗ[K] K)}

/-- Evaluation against any `K`-linearly independent family of linear forms `V →ₗ[K] K` has dense
range in `ι → K` for any topology on `K`. -/
theorem denseRange_pi [TopologicalSpace K] (hf : LinearIndependent K f) :
    DenseRange (LinearMap.pi f) := fun y ↦ mem_closure_iff_nhds.mpr fun W hW ↦ by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨s, t, ht, hst⟩ := hW
  obtain ⟨v, hv⟩ := (hf.comp Subtype.val Subtype.val_injective).pi_surjective fun i : s ↦ y i.val
  refine ⟨LinearMap.pi f v, hst fun i hi ↦ ?_, v, rfl⟩
  have hfi : f i v = y i := by simpa [LinearMap.pi_apply] using congr_fun hv ⟨i, hi⟩
  rw [LinearMap.pi_apply, hfi]
  exact mem_of_mem_nhds (ht i)

/-- Evaluation against a `K`-linearly independent family of continuous linear forms `V →L[K] K` on
a compact space `V` is surjective onto `ι → K` when `K` is Hausdorff with continuous addition and
constant scalar multiplication. -/
theorem surjective_continuousLinearMap_pi [TopologicalSpace K] [ContinuousAdd K]
    [ContinuousConstSMul K K] [T2Space K] [TopologicalSpace V] [CompactSpace V]
    {f : ι → (V →L[K] K)} (hf : LinearIndependent K f) :
    Function.Surjective (ContinuousLinearMap.pi f) := by
  rw [← Set.range_eq_univ]
  have hclosed : IsClosed (Set.range (ContinuousLinearMap.pi f)) :=
    (isCompact_range (ContinuousLinearMap.pi f).continuous).isClosed
  rw [← hclosed.closure_eq]
  have hf' : LinearIndependent K fun i ↦ (f i).toLinearMap :=
    hf.map_injOn (ContinuousLinearMap.coeLM K) ContinuousLinearMap.coe_injective.injOn
  have hrange : Set.range (ContinuousLinearMap.pi f) =
      Set.range (LinearMap.pi fun i ↦ (f i).toLinearMap) := by
    rw [← ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_coe]
  rw [hrange]
  exact hf'.denseRange_pi.closure_eq

end Field

end LinearIndependent

namespace SeparatingDual

section CommRing

variable {R V ι : Type*} [CommRing R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousConstSMul R R] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [SeparatingDual R V]

/-- Evaluation against a spanning family of continuous linear forms `V →L[R] R` is injective
whenever continuous linear forms separate points (`SeparatingDual R V`). -/
theorem injective_continuousLinearMap_pi {f : ι → (V →L[R] R)}
    (hf : Submodule.span R (Set.range f) = ⊤) :
    Function.Injective (ContinuousLinearMap.pi f) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := R) fun φ ↦ ?_
  have hmem : φ ∈ Submodule.span R (Set.range f) := hf ▸ Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    simpa [ContinuousLinearMap.pi_apply] using congr_fun hv i
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul r _ _ hx => simp [hx]

end CommRing

end SeparatingDual
