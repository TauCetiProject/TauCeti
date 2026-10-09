/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Dimension
public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Pure simplicial complexes and dimensions of links

A complex is pure of dimension `n` if every face is contained in a face with `n + 1`
vertices. This formulation works for infinite complexes as well: it gives both a uniform
dimension bound and extension to a top-dimensional face. The void complex is pure in every
dimension; dimension equalities consequently require nonvoidness.

Links of faces of a pure complex are pure in the complementary dimension. A top-dimensional
face has void link, whose dimension is `⊥`, rather than a truncated natural-number dimension.
These facts provide the dimension indices for sphere-or-ball link classifications.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 2--3.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι κ : Type*} {K : PreAbstractSimplicialComplex ι} {n : ℕ} {σ : Finset ι}

/-- A complex is pure of dimension `n` when every face extends to a face with `n + 1`
vertices. The void complex satisfies this condition in every dimension. -/
def IsPure (K : PreAbstractSimplicialComplex ι) (n : ℕ) : Prop :=
  ∀ ⦃σ⦄, σ ∈ K → ∃ τ ∈ K, σ ⊆ τ ∧ τ.card = n + 1

/-- The coface characterization of purity. -/
theorem isPure_iff : IsPure K n ↔ ∀ σ ∈ K, ∃ τ ∈ K, σ ⊆ τ ∧ τ.card = n + 1 :=
  ⟨fun h _ hσ => h hσ, fun h _ hσ => h _ hσ⟩

/-- Every face of a pure complex extends to a face of the prescribed dimension. -/
theorem IsPure.exists_coface (h : IsPure K n) (hσ : σ ∈ K) :
    ∃ τ ∈ K, σ ⊆ τ ∧ τ.card = n + 1 :=
  h hσ

/-- Every face of a pure `n`-complex has at most `n + 1` vertices. -/
theorem IsPure.card_le (h : IsPure K n) (hσ : σ ∈ K) : σ.card ≤ n + 1 := by
  obtain ⟨τ, -, hστ, hτ⟩ := h hσ
  exact hτ ▸ card_le_card hστ

/-- Purity bounds the dimension, even for the void complex. -/
theorem IsPure.dimension_le (h : IsPure K n) : dimension K ≤ (n : WithBot ℕ∞) := by
  refine dimension_le_iff.mpr fun σ hσ => ?_
  exact_mod_cast (by have := h.card_le hσ; omega : σ.card - 1 ≤ n)

/-- A nonvoid pure `n`-complex has dimension `n`. -/
theorem IsPure.dimension_eq (h : IsPure K n) (hK : K ≠ ⊥) :
    dimension K = (n : WithBot ℕ∞) := by
  obtain ⟨σ, hσ, -⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hK)
  obtain ⟨τ, hτ, -, hcard⟩ := h hσ
  refine le_antisymm h.dimension_le ?_
  simpa [hcard] using le_dimension hτ

/-- A maximal face of a pure `n`-complex has exactly `n + 1` vertices. -/
theorem IsPure.card_eq_of_maximal (h : IsPure K n) (hσ : Maximal (· ∈ K) σ) :
    σ.card = n + 1 := by
  obtain ⟨τ, hτ, hστ, hcard⟩ := h hσ.prop
  exact (le_antisymm hστ (hσ.2 hτ hστ)) ▸ hcard

/-- Injective relabeling preserves and reflects purity, including for infinite vertex types. -/
@[simp]
theorem isPure_map_iff [DecidableEq κ] (f : ι → κ) (hf : Function.Injective f) :
    IsPure (K.map f) n ↔ IsPure K n := by
  constructor
  · intro h σ hσ
    obtain ⟨ω, hω, hσω, hcard⟩ := h (mem_map_iff.mpr ⟨σ, hσ, rfl⟩)
    obtain ⟨τ, hτ, rfl⟩ := mem_map_iff.mp hω
    refine ⟨τ, hτ, (image_subset_image_iff hf).mp hσω, ?_⟩
    rwa [card_image_iff.mpr hf.injOn] at hcard
  · intro h ω hω
    obtain ⟨σ, hσ, rfl⟩ := mem_map_iff.mp hω
    obtain ⟨τ, hτ, hστ, hcard⟩ := h hσ
    exact ⟨τ.image f, mem_map_iff.mpr ⟨τ, hτ, rfl⟩,
      image_subset_image hστ, by rwa [card_image_iff.mpr hf.injOn]⟩

/-- A nonempty simplex is pure of its expected dimension. -/
theorem isPure_simplex {V : Finset ι} (hV : V.card = n + 1) : IsPure (simplex V) n := by
  intro σ hσ
  exact ⟨V, self_mem_simplex.mpr (card_pos.mp (by omega)), (mem_simplex.mp hσ).2, hV⟩

/-- The boundary of an `(n + 1)`-simplex is pure of dimension `n`. -/
theorem isPure_simplexBoundary {V : Finset ι} (hV : V.card = n + 2) :
    IsPure (simplexBoundary V) n := by
  classical
  intro σ hσ
  obtain ⟨-, hσV⟩ := mem_simplexBoundary.mp hσ
  obtain ⟨τ, hστ, hτV, hcard⟩ := exists_subsuperset_card_eq hσV.subset
    (by have := card_lt_card hσV; omega : σ.card ≤ n + 1) (by omega : n + 1 ≤ V.card)
  refine ⟨τ, mem_simplexBoundary.mpr ⟨card_pos.mp (by omega), ?_⟩, hστ, hcard⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hτV, fun h => by rw [h] at hcard; omega⟩

/-- The link of any vertex set in a pure `n`-complex is pure of dimension `n - σ.card`.
For a top-dimensional face the link is void, so the purity conclusion is vacuous. -/
theorem IsPure.link [DecidableEq ι] (h : IsPure K n) :
    IsPure (PreAbstractSimplicialComplex.link K σ) (n - σ.card) := by
  intro ρ hρ
  obtain ⟨hne, hdis, hρσ⟩ := mem_link_nonempty.mp hρ
  obtain ⟨τ, hτ, hsub, hcard⟩ := h hρσ
  have hστ : σ ⊆ τ := subset_union_right.trans hsub
  have hρτ : ρ ⊆ τ \ σ := subset_sdiff.mpr ⟨subset_union_left.trans hsub, hdis⟩
  have hpos : 0 < (τ \ σ).card := card_pos.mpr (hne.mono hρτ)
  have hsdiff : (τ \ σ).card = n + 1 - σ.card := by
    rw [card_sdiff_of_subset hστ, hcard]
  refine ⟨τ \ σ, mem_link_nonempty.mpr
    ⟨hne.mono hρτ, sdiff_disjoint, by rwa [sdiff_union_of_subset hστ]⟩, hρτ, ?_⟩
  omega

/-- A face of a pure complex has void link exactly when it is top-dimensional. -/
theorem IsPure.link_eq_bot_iff [DecidableEq ι] (h : IsPure K n) (hσ : σ ∈ K) :
    PreAbstractSimplicialComplex.link K σ = ⊥ ↔ σ.card = n + 1 := by
  constructor
  · intro hbot
    obtain ⟨τ, hτ, hστ, hcard⟩ := h hσ
    by_contra hne
    have hsdiff : (τ \ σ).Nonempty := card_pos.mp (by
      rw [card_sdiff_of_subset hστ, hcard]
      have := h.card_le hσ
      omega)
    have hmem := mem_link_nonempty.mpr
      ⟨hsdiff, sdiff_disjoint, by rwa [sdiff_union_of_subset hστ]⟩
    rw [hbot] at hmem
    exact hmem.elim
  · intro hcard
    refine eq_bot_iff.mpr fun ρ hρ => ?_
    obtain ⟨hne, hdis, hρσ⟩ := mem_link_nonempty.mp hρ
    have hle := h.card_le hρσ
    rw [card_union_of_disjoint hdis, hcard] at hle
    have := card_pos.mpr hne
    omega

/-- The link of a face below top dimension in a pure `n`-complex has dimension
`n - σ.card`. The separate top-dimensional case has void link and dimension `⊥`. -/
theorem IsPure.dimension_link [DecidableEq ι] (h : IsPure K n) (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    dimension (PreAbstractSimplicialComplex.link K σ) = ((n - σ.card : ℕ) : WithBot ℕ∞) :=
  h.link.dimension_eq fun hbot => by
    have := (h.link_eq_bot_iff hσ).mp hbot
    omega

end PreAbstractSimplicialComplex
