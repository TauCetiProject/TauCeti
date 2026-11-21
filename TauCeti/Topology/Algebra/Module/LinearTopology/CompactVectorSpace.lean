/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.Algebra.Module.Compact
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Topology.Algebra.Module.Dual
import TauCeti.Topology.Algebra.Module.LinearTopology.Dual

/-!
# Lefschetz linear duality for compact linearly topologized vector spaces

Every compact Hausdorff linearly topologized vector space `V : Type v` over a `T₂` topological
field `K` is topologically isomorphic to a product `I → K` via evaluation against a basis of its
continuous dual `V →L[K] K` (`Module.Basis.continuousDualEquivPi`,
`TauCeti.exists_continuousLinearEquiv_pi_of_isLinearTopology`). Over a compact `T₂` field `K`,
`TauCeti.IsCompactModule K V` is equivalent to `∃ I : Type v, Nonempty (V ≃L[K] (I → K))`
(`TauCeti.IsCompactModule.iff_exists_continuousLinearEquiv_pi_of_field`), and any discrete division
ring admitting a nontrivial compact `T₁` linearly topologized vector space is finite
(`TauCeti.finite_of_compactSpace_of_isLinearTopology`).

## References

* [S. Lefschetz, *Algebraic Topology*], Ch. II, §6, (25.4)–(27.1).
* [N. Bourbaki, *Algebra I*], Ch. II, §7, Exercises, and *Commutative Algebra*, Ch. III, §2, Ex.
-/

public section

open Filter Topology

namespace TauCeti

section DivisionRing

variable (K : Type*) {V : Type*} [DivisionRing K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [T1Space V]

/-- If a nontrivial compact `T₁` vector space over a discrete division ring `K` carries a
`K`-linear topology, then `K` must be finite. -/
theorem finite_of_compactSpace_of_isLinearTopology [DiscreteTopology K] [CompactSpace V]
    [Nontrivial V] : Finite K := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_ne_zero K hv
  have := (φ.toLinearMap.surjective fun h ↦ hφ (DFunLike.congr_fun h v)).compactSpace φ.continuous
  exact finite_of_compact_of_discrete

end DivisionRing

end TauCeti

namespace Module.Basis

variable {K V ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [CompactSpace V] [T2Space V] [T2Space K]

omit [CompactSpace V] [T2Space K] in
private theorem pi_injective (b : Module.Basis ι K (V →L[K] K)) :
    Function.Injective (ContinuousLinearMap.pi b).toLinearMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  obtain ⟨φ, hφ⟩ := TauCeti.exists_continuousLinearMap_apply_ne_zero K hv0
  have hbv : ∀ i : ι, b i v = 0 := fun i ↦ by
    simpa [ContinuousLinearMap.pi_apply] using congr_fun (LinearMap.mem_ker.mp hv) i
  refine hφ ?_
  conv_lhs => rw [← b.linearCombination_repr φ]
  simp [Finsupp.linearCombination_apply, Finsupp.sum, hbv]

omit [IsTopologicalAddGroup V] [IsLinearTopology K V] [T2Space V] in
private theorem pi_surjective (b : Module.Basis ι K (V →L[K] K)) :
    Function.Surjective (ContinuousLinearMap.pi b).toLinearMap := by
  rw [ContinuousLinearMap.coe_pi, ← Set.range_eq_univ]
  have hclosed : IsClosed (Set.range (LinearMap.pi fun i ↦ (b i).toLinearMap)) := by
    rw [← ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_coe]
    exact (isCompact_range (ContinuousLinearMap.pi b).continuous).isClosed
  rw [← hclosed.closure_eq]
  exact (b.linearIndependent.map' (ContinuousLinearMap.coeLM K)
    (LinearMap.ker_eq_bot_of_injective ContinuousLinearMap.coe_injective)).denseRange_pi.closure_eq

/-- **Lefschetz product decomposition from a continuous dual basis**: a `K`-basis
`b : Module.Basis ι K (V →L[K] K)` induces `V ≃L[K] (ι → K)` sending `v` to `fun i ↦ b i v`. -/
noncomputable def continuousDualEquivPi (b : Module.Basis ι K (V →L[K] K)) :
    V ≃L[K] (ι → K) :=
  let e := LinearEquiv.ofBijective (ContinuousLinearMap.pi b).toLinearMap
    ⟨pi_injective b, pi_surjective b⟩
  { toLinearEquiv := e
    continuous_toFun := (ContinuousLinearMap.pi b).continuous
    continuous_invFun :=
      (ContinuousLinearMap.pi b).continuous.continuous_symm_of_equiv_compact_to_t2
        (f := e.toEquiv) }

@[simp, grind =]
theorem continuousDualEquivPi_apply (b : Module.Basis ι K (V →L[K] K)) (v : V) (i : ι) :
    b.continuousDualEquivPi v i = b i v := (rfl)

@[simp, grind =]
theorem apply_continuousDualEquivPi_symm (b : Module.Basis ι K (V →L[K] K)) (c : ι → K)
    (i : ι) : b i (b.continuousDualEquivPi.symm c) = c i := by
  rw [← continuousDualEquivPi_apply, ContinuousLinearEquiv.apply_symm_apply]

end Module.Basis

namespace TauCeti

section ExistsPi

universe u v

variable (K : Type u) (V : Type v) [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]

/-- **Every compact Hausdorff linearly topologized vector space `V : Type v` over a `T₂`
topological field `K` is topologically isomorphic to a product `I → K` for some `I : Type v`.** -/
theorem exists_continuousLinearEquiv_pi_of_isLinearTopology
    [IsTopologicalRing K] [T2Space K] [IsTopologicalAddGroup V] [IsLinearTopology K V]
    [CompactSpace V] [T2Space V] :
    ∃ I : Type v, Nonempty (V ≃L[K] (I → K)) := by
  have : Small.{v} (V →L[K] K) := small_strongDual K V
  let b₀ := Module.Free.chooseBasis K (V →L[K] K)
  have : Small.{v} (Module.Free.ChooseBasisIndex K (V →L[K] K)) :=
    small_of_injective b₀.injective
  exact ⟨_, ⟨(b₀.reindex (equivShrink _)).continuousDualEquivPi⟩⟩

namespace IsCompactModule

variable {K V}

/-- Every compact module `V : Type v` over a compact Hausdorff topological field `K` is
topologically isomorphic to `I → K` for some `I : Type v`. -/
theorem exists_continuousLinearEquiv_pi_of_field [IsTopologicalRing K] [CompactSpace K]
    [T2Space K] (hV : IsCompactModule K V) :
    ∃ I : Type v, Nonempty (V ≃L[K] (I → K)) := by
  have := hV.isTopologicalAddGroup; have := hV.isLinearTopology
  have := hV.compactSpace; have := hV.t2Space
  exact exists_continuousLinearEquiv_pi_of_isLinearTopology K V

/-- Over a compact Hausdorff topological field `K`, a topological `K`-vector space `V : Type v` is
a compact module if and only if it is topologically isomorphic to `I → K` for some `I : Type v`. -/
theorem iff_exists_continuousLinearEquiv_pi_of_field [IsTopologicalRing K] [CompactSpace K]
    [T2Space K] :
    IsCompactModule K V ↔ ∃ I : Type v, Nonempty (V ≃L[K] (I → K)) :=
  ⟨fun hV ↦ hV.exists_continuousLinearEquiv_pi_of_field, fun ⟨I, ⟨e⟩⟩ ↦
    have : DiscreteTopology K :=
      discreteTopology_iff_isOpen_singleton_zero.mpr GroupWithZero.isOpen_singleton_zero
    (IsCompactModule.pi fun _ : I ↦ IsCompactModule.self (R := K)).of_continuousLinearEquiv
      e.symm⟩

end IsCompactModule

end ExistsPi

end TauCeti
