/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Compact
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Homeomorph
import Mathlib.Data.Fintype.Card

/-!
# Vertex sets of compact triangulations

A compact triangulable space admits a triangulation with vertices in any universe by
relabelling its finite vertex set.

A compact infinite triangulable space admits finite triangulations with arbitrarily many
vertices. Barycentric subdivision adds vertices because a finite complex with infinite
realization cannot consist only of singleton faces. This permits choosing distinct vertices
for a finite configuration of marked points before moving the configuration by a homeomorphism.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (barycentric subdivision).
-/

public section

open AbstractSimplicialComplex TauCeti.SetLike

namespace TauCeti

universe u v w

/-- A compact triangulable space admits a triangulation with vertices in any universe,
by relabelling its finite vertex set. -/
theorem IsTriangulable.lift_of_compactSpace {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : IsTriangulable.{v} X) : IsTriangulable.{w} X := by
  classical
  obtain ⟨ι, K, ⟨e⟩⟩ := (isTriangulable_iff X).mp h
  have := e.symm.compactSpace
  have : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  let := Fintype.ofFinite ι
  let f : ι ≃ ULift.{w} (Fin (Fintype.card ι)) :=
    (Fintype.equivFin ι).trans Equiv.ulift.symm
  let L : AbstractSimplicialComplex (ULift.{w} (Fin (Fintype.card ι))) :=
    { K.toPreAbstractSimplicialComplex.map f with
      singleton_mem := fun v => PreAbstractSimplicialComplex.mem_map_iff.mpr
        ⟨{f.symm v}, K.singleton_mem _, by simp⟩ }
  let r := K.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph
    (L := L) f.toEmbedding rfl rfl le_rfl
  have hr : {y : AbstractSimplicialComplex.Realization L |
      y.1.support ∈ L.toPreAbstractSimplicialComplex} = Set.univ :=
    Set.eq_univ_of_forall (AbstractSimplicialComplex.support_mem L)
  exact (isTriangulable_iff X).mpr ⟨_, L, ⟨(r.trans
    ((Homeomorph.setCongr hr).trans (Homeomorph.Set.univ _))).symm.trans e⟩⟩

/-- A compact infinite triangulable space has a finite triangulation with at least any
prescribed number of vertices. No local finiteness of the original triangulation is assumed. -/
theorem IsTriangulable.exists_finite_triangulation_card_ge
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [Infinite X]
    (h : IsTriangulable.{v} X) (n : ℕ) :
    ∃ (ι : Type v) (K : AbstractSimplicialComplex ι),
      Finite ι ∧ Nonempty (Realization K ≃ₜ X) ∧ n ≤ Nat.card ι := by
  classical
  induction n with
  | zero =>
    obtain ⟨ι, K, ⟨e⟩⟩ := (isTriangulable_iff X).mp h
    have := e.symm.compactSpace
    exact ⟨ι, K, (K.compactSpace_realization_iff_finite).mp inferInstance, ⟨e⟩,
      Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨ι, K, hι, ⟨e⟩, hn⟩ := ih
    let := Fintype.ofFinite ι
    let := Fintype.ofFinite (Face K)
    let f : ι → Face K := fun i => ⟨{i}, K.singleton_mem i⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Finset.singleton_injective (congrArg Subtype.val hij)
    have hns : ¬ Function.Surjective f := by
      intro hs
      have hK : K = ⊥ := K.eq_bot_of_surjective_singleton hs
      subst K
      have hsurj : Function.Surjective (e ∘ vertex (⊥ : AbstractSimplicialComplex ι)) :=
        e.surjective.comp vertex_bot_surjective
      have : Finite X := Finite.of_surjective _ hsurj
      exact not_finite X
    have hlt : Nat.card ι < Nat.card (Face K) := by
      simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_lt_of_injective_not_surjective f hf hns
    exact ⟨Face K, TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex, inferInstance,
      ⟨(barycentricSubdivisionRealizationHomeomorph K).trans e⟩,
      (Nat.succ_le_of_lt hlt).trans' (Nat.succ_le_succ hn)⟩

end TauCeti
