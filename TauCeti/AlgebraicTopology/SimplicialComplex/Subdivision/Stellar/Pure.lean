/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Pure
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Stellar equivalence preserves purity

Starring a face at a fresh vertex preserves and reflects purity in every dimension.
Consequently purity is invariant under stellar equivalence, including injective relabelings.
This transfers purity of standard simplices and simplex boundaries to combinatorial balls
and spheres.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 2--3.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {σ τ : Finset ι} {v w : ι} {n : ℕ}

/-- Replacing one vertex of the starred set in a containing face `τ` by a vertex absent from `τ`
gives a face of the stellar subdivision. -/
theorem insert_erase_mem_stellarSubdivision (hτ : τ ∈ K) (hv : v ∉ τ)
    (hστ : σ ⊆ τ) (hw : w ∈ σ) : insert v (τ.erase w) ∈ stellarSubdivision K σ v := by
  refine (insert_mem_stellarSubdivision_iff
    (fun h => hv (mem_of_mem_erase h))).mpr ⟨?_, ?_⟩
  · exact fun h => notMem_erase w τ (h hw)
  · rwa [(erase_union_of_mem hw τ).trans (union_eq_left.mpr hστ)]

/-- Starring at a fresh vertex preserves purity. -/
theorem IsPure.stellarSubdivision (h : IsPure K n) (hv : ({v} : Finset ι) ∉ K) :
    IsPure (stellarSubdivision K σ v) n := by
  rw [isPure_iff]
  intro ρ hρ
  rcases mem_stellarSubdivision_iff.mp hρ with ⟨hvρ, hρK, havoid⟩ | ⟨hvρ, havoid, hρK⟩
  · obtain ⟨τ, hτ, hρτ, hcard⟩ := h.exists_coface hρK
    by_cases hστ : σ ⊆ τ
    · obtain ⟨w, hw, hwρ⟩ := not_subset.mp havoid
      have hvτ := notMem_of_singleton_notMem hv hτ
      refine ⟨insert v (τ.erase w), insert_erase_mem_stellarSubdivision hτ hvτ hστ hw,
        (subset_erase.mpr ⟨hρτ, hwρ⟩).trans (subset_insert _ _), ?_⟩
      rw [card_insert_of_notMem (fun h => hvτ (mem_of_mem_erase h)),
        card_erase_of_mem (hστ hw), hcard]
      omega
    · exact ⟨τ, (mem_stellarSubdivision_iff_of_notMem
        (notMem_of_singleton_notMem hv hτ)).mpr ⟨hτ, hστ⟩, hρτ, hcard⟩
  · obtain ⟨τ, hτ, hsub, hcard⟩ := h.exists_coface hρK
    obtain ⟨w, hw, hwerase⟩ := not_subset.mp havoid
    have hστ : σ ⊆ τ := subset_union_right.trans hsub
    have hwτ := hστ hw
    have hvτ := notMem_of_singleton_notMem hv hτ
    have hρτ : ρ.erase v ⊆ τ.erase w :=
      subset_erase.mpr ⟨subset_union_left.trans hsub, hwerase⟩
    refine ⟨insert v (τ.erase w), insert_erase_mem_stellarSubdivision hτ hvτ hστ hw, ?_, ?_⟩
    · rw [← insert_erase hvρ]
      exact insert_subset_insert v hρτ
    · rw [card_insert_of_notMem (fun h => hvτ (mem_of_mem_erase h)),
        card_erase_of_mem hwτ, hcard]
      omega

/-- Purity is also reflected by a genuine stellar subdivision: no lower-dimensional
maximal face can be hidden by starring. -/
@[simp]
theorem isPure_stellarSubdivision_iff (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsPure (stellarSubdivision K σ v) n ↔ IsPure K n := by
  refine ⟨fun h => ?_, fun h => h.stellarSubdivision hv⟩
  have hdim : dimension K ≤ (n : WithBot ℕ∞) := by
    rw [← dimension_stellarSubdivision hv (K.isRelLowerSet_faces hσ).1]
    exact h.dimension_le
  have hbound (τ : Finset ι) (hτ : τ ∈ K) : τ.card ≤ n + 1 := by
    have hle := dimension_le_iff.mp hdim τ hτ
    have hnat : τ.card - 1 ≤ n := by exact_mod_cast hle
    omega
  -- Recover an old coface from a coface containing the fresh vertex. Its old hull contains
  -- at least as many vertices, and the dimension bound forces equality.
  have recover (ρ ω : Finset ι) (hρω : ρ ⊆ ω.erase v ∪ σ)
      (hω : ω ∈ stellarSubdivision K σ v) (hvω : v ∈ ω) (hcard : ω.card = n + 1) :
      ∃ τ ∈ K, ρ ⊆ τ ∧ τ.card = n + 1 := by
    obtain ⟨havoid, hface⟩ :=
      (insert_mem_stellarSubdivision_iff (notMem_erase v ω)).mp
        (by rwa [insert_erase hvω])
    obtain ⟨w, hw, hwω⟩ := not_subset.mp havoid
    have hle : n + 1 ≤ (ω.erase v ∪ σ).card := by
      have := card_le_card
        (insert_subset (mem_union_right (ω.erase v) hw) subset_union_left)
      rw [card_insert_of_notMem hwω, card_erase_of_mem hvω, hcard] at this
      omega
    exact ⟨ω.erase v ∪ σ, hface, hρω, le_antisymm (hbound _ hface) hle⟩
  rw [isPure_iff]
  intro ρ hρ
  have hvρ := notMem_of_singleton_notMem hv hρ
  by_cases hσρ : σ ⊆ ρ
  · obtain ⟨w, hw⟩ := (K.isRelLowerSet_faces hσ).1
    obtain ⟨ω, hω, hsub, hcard⟩ := h.exists_coface
      (insert_erase_mem_stellarSubdivision hρ hvρ hσρ hw)
    have hvω : v ∈ ω := hsub (mem_insert_self v _)
    apply recover ρ ω ?_ hω hvω hcard
    intro x hx
    by_cases hxw : x = w
    · exact mem_union_right _ (hxw ▸ hw)
    · exact mem_union_left _ (mem_erase.mpr ⟨fun hxv => hvρ (hxv ▸ hx),
        hsub (mem_insert_of_mem (mem_erase.mpr ⟨hxw, hx⟩))⟩)
  · obtain ⟨ω, hω, hsub, hcard⟩ := h.exists_coface
      ((mem_stellarSubdivision_iff_of_notMem hvρ).mpr ⟨hρ, hσρ⟩)
    by_cases hvω : v ∈ ω
    · exact recover ρ ω ((subset_erase.mpr ⟨hsub, hvρ⟩).trans subset_union_left)
        hω hvω hcard
    · exact ⟨ω, ((mem_stellarSubdivision_iff_of_notMem hvω).mp hω).1, hsub, hcard⟩

/-- Stellar equivalent complexes are pure in exactly the same dimensions. -/
theorem StellarEquivalent.isPure_iff (h : StellarEquivalent K L) : IsPure K n ↔ IsPure L n := by
  apply h.induction_on
  · intro A B hAB
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hAB
    exact (isPure_stellarSubdivision_iff hσ hv).symm
  · intro A
    rfl
  · intro A B ih
    exact ih.symm
  · intro A B C ih ih'
    exact ih.trans ih'

/-- Intrinsic stellar equivalence, allowing arbitrary injective relabelings, preserves
and reflects purity. -/
theorem StellarEquivalentUpToRelabeling.isPure_iff (h : StellarEquivalentUpToRelabeling K L) :
    IsPure K n ↔ IsPure L n := by
  apply h.induction_on
  · intro A B f g he
    exact (isPure_map_iff f f.injective).symm.trans
      (he.isPure_iff.trans (isPure_map_iff g g.injective))
  · intro A
    rfl
  · intro A B ih
    exact ih.symm
  · intro A B C ih ih'
    exact ih.trans ih'

end PreAbstractSimplicialComplex
