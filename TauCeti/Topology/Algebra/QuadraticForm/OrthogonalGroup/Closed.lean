/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity
public import TauCeti.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup

/-!
# Closedness and local compactness of the orthogonal group

For a quadratic form with separating polar form on a finite free module over a domain, every
endomorphism preserving the form is automatically invertible. Thus the orthogonal group, viewed
in the space of linear endomorphisms, is the common zero set of the equations `Q (f x) = Q x`.
When the form is continuous, this image is closed. This description is useful when passing from
the topology of linear endomorphisms to local orthogonal point groups.

The result holds over a Hausdorff commutative domain with module topologies and a finite free
module, provided the form is continuous. A topological ring structure on the scalars supplies
continuity; the theorem takes continuity directly. Local compactness is not needed
for closedness, but separation is: over a semiring with the indiscrete topology the module topology
on the endomorphisms is indiscrete, and the orthogonal group of any form on a nontrivial module is
a nonempty proper subset of it, since it omits `0`. So it is never closed there, already for
`Q x = x ^ 2` on a field `K` in dimension one, where it is `{1, -1}`.

Over a Hausdorff topological field, the orthogonal group of a
finite-dimensional quadratic space is also closed in the linear automorphism group with its
canonical topology, the one recording an automorphism and its inverse: it is the preimage of the
closed set of form-preserving endomorphisms under the continuous forgetful map. When the field is
moreover locally compact, the automorphism group is locally compact, so the orthogonal group is a
locally compact Hausdorff topological group. This is the topology in which the orthogonal point
groups over `ℝ` and `ℚ_p` are studied.

## Main results

* `TauCeti.QuadraticMap.isClosed_range_orthogonalGroup_toLinearMap`: the orthogonal group is
  closed in the endomorphism space, through its underlying linear maps.
* `QuadraticMap.not_isClosed_range_orthogonalGroup_toLinearMap_of_indiscreteTopology`:
  over scalars with the indiscrete topology this fails for every quadratic map on a nontrivial
  module, so the `T2Space` hypothesis cannot be dropped.
* `TauCeti.QuadraticMap.isClosed_orthogonalGroup`: the orthogonal group is closed in the linear
  automorphism group.
* `TauCeti.QuadraticMap.instLocallyCompactSpaceOrthogonalGroup`: the orthogonal group is locally
  compact over a locally compact field.
* `QuadraticMap.continuous_specialOrthogonalToOrthogonal`: the inclusion of the special
  orthogonal group into the orthogonal group is continuous.
-/

public section

namespace TauCeti

namespace QuadraticMap

open scoped Topology

section Endomorphism

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [TopologicalSpace M] [IsModuleTopology R M]
  [TopologicalSpace (Module.End R M)] [IsModuleTopology R (Module.End R M)]

variable [IsDomain R] [Module.Free R M]

/-- The orthogonal group of a continuous quadratic form with separating polar form on a finite
free module is closed in the endomorphism space, through its underlying linear maps. -/
theorem isClosed_range_orthogonalGroup_toLinearMap
    (Q : QuadraticForm R M) (hQ : Q.polarBilin.SeparatingLeft) (hcont : Continuous Q) :
    IsClosed (Set.range (fun g : orthogonalGroup Q => (g : M ≃ₗ[R] M).toLinearMap)) := by
  have : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  rw [range_orthogonalGroup_toLinearMap Q hQ]
  exact Q.isClosed_setOfPred_forall_map_app hcont

end Endomorphism

section Indiscrete

variable {R M N : Type*} [CommSemiring R] [TopologicalSpace R] [IndiscreteTopology R]
  [AddCommMonoid M] [Module R M] [Nontrivial M] [AddCommMonoid N] [Module R N]
  [TopologicalSpace (Module.End R M)] [IsModuleTopology R (Module.End R M)]

/-- Over a semiring with the indiscrete topology, the orthogonal group of any quadratic map on a
nontrivial module is not closed in the endomorphism space: that space is indiscrete, and the
orthogonal group is nonempty and does not contain `0`. Thus the separation hypothesis of
`isClosed_range_orthogonalGroup_toLinearMap` cannot be dropped. -/
theorem _root_.QuadraticMap.not_isClosed_range_orthogonalGroup_toLinearMap_of_indiscreteTopology
    (Q : QuadraticMap R M N) :
    ¬ IsClosed (Set.range (fun g : orthogonalGroup Q => (g : M ≃ₗ[R] M).toLinearMap)) := by
  have := IsModuleTopology.toContinuousSMul R (Module.End R M)
  have := IndiscreteTopology.of_continuousSMul R (Module.End R M)
  rw [IndiscreteTopology.isClosed_iff, not_or]
  refine ⟨(Set.range_nonempty _).ne_empty, fun h ↦ ?_⟩
  obtain ⟨g, hg⟩ : (0 : Module.End R M) ∈ Set.range _ := h ▸ Set.mem_univ _
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  exact hm ((g : M ≃ₗ[R] M).injective (by simpa using LinearMap.congr_fun hg m))

end Indiscrete

section Automorphism

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- The orthogonal group of a finite-dimensional quadratic space over a Hausdorff topological
field is closed in the linear automorphism group with its canonical
topology. No topology on the space itself is assumed. -/
theorem isClosed_orthogonalGroup : IsClosed (orthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  let _ : TopologicalSpace V := moduleTopology K V
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
  have h : (orthogonalGroup Q : Set (V ≃ₗ[K] V)) =
      (fun g : V ≃ₗ[K] V => (g : Module.End K V)) ⁻¹'
        {f : Module.End K V | ∀ x, Q (f x) = Q x} := by
    ext g
    simp [mem_orthogonalGroup_iff]
  rw [h]
  exact (Q.isClosed_setOfPred_forall_map_app Q.continuous).preimage
    continuous_linearEquiv_toLinearMap

/-- The orthogonal group of a finite-dimensional quadratic space over a Hausdorff locally compact
topological field is locally compact, being closed in the locally
compact linear automorphism group. -/
instance instLocallyCompactSpaceOrthogonalGroup [LocallyCompactSpace K] :
    LocallyCompactSpace (orthogonalGroup Q) :=
  (isClosed_orthogonalGroup Q).locallyCompactSpace

end Automorphism

section Inclusion

variable {R M N : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N] (Q : QuadraticMap R M N)

/-- The inclusion `SO(Q) →* O(Q)` is continuous, both groups carrying the subspace topology from
the linear automorphism group. -/
@[fun_prop]
theorem _root_.QuadraticMap.continuous_specialOrthogonalToOrthogonal :
    Continuous (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q) :=
  (Subgroup.continuous_inclusion (specialOrthogonalGroup_le_orthogonalGroup Q)).congr
    fun g ↦ Subtype.ext (_root_.QuadraticMap.coe_specialOrthogonalToOrthogonal g).symm

end Inclusion

end QuadraticMap

end TauCeti
