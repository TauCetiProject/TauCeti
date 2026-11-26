/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.LocallyCompact
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# The infinite star

The infinite star is the simplicial complex on the vertex set `Option ℕ` in which the vertex
`none` is joined by an edge `{none, some i}` to each vertex `some i`. This file checks the
infinite-star example of QuasiregularMaps §6.1:

* the complex is not locally finite: the vertex `none` is a face of infinitely many simplices
  (`TauCeti.InfiniteStar.infinite_setOf_mem_none`);
* nevertheless every compact subset of its realization lies in a finite subcomplex: the carriers
  of its points lie in one finite vertex set (`TauCeti.InfiniteStar.exists_finset_support_subset`);
* no neighbourhood of the vertex `none` is compact
  (`TauCeti.InfiniteStar.not_isCompact_of_mem_nhds_vertex_none`), so the realization is not
  locally compact (`TauCeti.InfiniteStar.not_weaklyLocallyCompactSpace`);
* hence the realization is not homeomorphic to any manifold modelled on a finite-dimensional
  real space (`TauCeti.InfiniteStar.isEmpty_homeomorph_manifold`), in particular not to a
  `1`-manifold. Local finiteness of a triangulated manifold is a consequence of the manifold, not
  of the realization.
-/

public section

noncomputable section

open Set Topology AbstractSimplicialComplex TauCeti.SetLike

namespace TauCeti.InfiniteStar

/-- The infinite star: the vertex `none` joined by an edge to every vertex `some i`. -/
def infiniteStar : _root_.AbstractSimplicialComplex (Option ℕ) :=
  TauCeti.AbstractSimplicialComplex.ofGenerators (range fun i : ℕ ↦ {none, some i})
    fun v ↦ ⟨{none, some (v.getD 0)}, ⟨v.getD 0, rfl⟩, by cases v <;> simp⟩

/-- The edges `{none, some i}` are faces of the infinite star. -/
theorem edge_mem (i : ℕ) : ({none, some i} : Finset (Option ℕ)) ∈ infiniteStar :=
  TauCeti.AbstractSimplicialComplex.mem_ofGenerators_of_mem ⟨i, rfl⟩ (by simp)

/-- **The infinite star is not locally finite**: the vertex `none` lies in infinitely many
faces. -/
theorem infinite_setOf_mem_none :
    {σ : Finset (Option ℕ) | σ ∈ infiniteStar ∧ none ∈ σ}.Infinite := by
  have hinj : Function.Injective fun i : ℕ ↦ ({none, some i} : Finset (Option ℕ)) := by
    intro i j hij
    have : some i ∈ ({none, some j} : Finset (Option ℕ)) := by
      rw [← show ({none, some i} : Finset (Option ℕ)) = {none, some j} from hij]
      simp
    simpa using this
  exact (Set.infinite_range_of_injective hinj).mono
    (range_subset_iff.mpr fun i ↦ ⟨edge_mem i, by simp⟩)

/-- Every compact subset of the realization of the infinite star lies in a finite subcomplex: the
carriers of its points lie in one finite vertex set. -/
theorem exists_finset_support_subset {s : Set (Realization infiniteStar)} (hs : IsCompact s) :
    ∃ V : Finset (Option ℕ), ∀ x ∈ s, x.val.support ⊆ V :=
  AbstractSimplicialComplex.exists_finset_support_subset_of_isCompact hs

/-- **No neighbourhood of the centre of the infinite star is compact**: a compact neighbourhood
of the vertex `none` would use only finitely many vertices, while it contains points of every
open edge. -/
theorem not_isCompact_of_mem_nhds_vertex_none {C : Set (Realization infiniteStar)}
    (hC : C ∈ 𝓝 (vertex infiniteStar none)) : ¬ IsCompact C := by
  intro hCc
  obtain ⟨V, hV⟩ := exists_finset_support_subset hCc
  -- `none` lies in only the faces contained in `V`, finitely many.
  refine infinite_setOf_mem_none (((V.powerset : Set (Finset (Option ℕ))).toFinite).subset ?_)
  rintro σ ⟨hσ, hnone⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (subset_of_mem_nhds_vertex hC hV hσ hnone))

/-- The realization of the infinite star is not locally compact. -/
theorem not_weaklyLocallyCompactSpace :
    ¬ WeaklyLocallyCompactSpace (Realization infiniteStar) := by
  intro h
  obtain ⟨C, hCc, hC⟩ := h.exists_compact_mem_nhds (vertex infiniteStar none)
  exact not_isCompact_of_mem_nhds_vertex_none hC hCc

/-- **The infinite star is not a manifold**: its realization is homeomorphic to no manifold
modelled on a finite-dimensional real normed space, in particular to no `1`-manifold. -/
theorem isEmpty_homeomorph_manifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    IsEmpty (Realization infiniteStar ≃ₜ M) := by
  refine ⟨fun κ ↦ ?_⟩
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  exact infinite_setOf_mem_none (finite_setOf_mem_of_homeomorph κ none)

end TauCeti.InfiniteStar
