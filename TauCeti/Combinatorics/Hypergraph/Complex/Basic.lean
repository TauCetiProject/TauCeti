/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Finite bounded hypergraph complexes

This file defines finite augmented complexes whose faces have cardinality at most a fixed rank.
Unlike Mathlib's `PreAbstractSimplicialComplex`, a `HypergraphComplex` includes the empty face and
records faces in finite cardinality levels. The conversions in this file identify bounded
pre-abstract simplicial complexes on finite vertex types with these finite graded complexes after
forgetting or adjoining the empty face.

The grading uses face cardinality: a triple lies in level `3`, corresponding to simplicial
dimension `2`.
-/

public section

open Finset

namespace TauCeti

/-- A finite augmented complex of rank `r` on `V`.

Its level `k` is a finite collection of `k`-element faces, the collections are downward closed,
and the empty face belongs to level zero. -/
structure HypergraphComplex (r : ℕ) (V : Type*) where
  /-- The faces of cardinality `k`, for `k ≤ r`. -/
  faces : ∀ k : ℕ, k ≤ r → Finset (Finset V)
  /-- Every face in level `k` has cardinality `k`. -/
  face_card : ∀ k (hk : k ≤ r), ∀ s ∈ faces k hk, s.card = k
  /-- Every subset of a face occurs in the level given by its cardinality. -/
  down_closed : ∀ k (hk : k ≤ r), ∀ s ∈ faces k hk, ∀ t ⊆ s,
    ∀ htr : t.card ≤ r, t ∈ faces t.card htr
  /-- The empty face belongs to every complex. -/
  empty_mem : ∅ ∈ faces 0 (Nat.zero_le r)

namespace HypergraphComplex

variable {r : ℕ} {V : Type*}

/-- A bounded hypergraph complex is determined by its graded face collections. -/
@[ext]
theorem ext {C D : HypergraphComplex r V}
    (h : ∀ k (hk : k ≤ r), C.faces k hk = D.faces k hk) : C = D := by
  cases C
  cases D
  simp only [mk.injEq]
  funext k hk
  exact h k hk

/-- The empty face is the unique face in level zero. -/
@[simp]
theorem faces_zero (C : HypergraphComplex r V) : C.faces 0 (Nat.zero_le r) = {∅} := by
  ext s
  constructor
  · intro hs
    simp only [mem_singleton]
    exact card_eq_zero.mp (C.face_card 0 (Nat.zero_le r) s hs)
  · intro hs
    rw [mem_singleton.mp hs]
    exact C.empty_mem

/-- Forget the empty face and finite grading of a hypergraph complex.

The resulting Mathlib complex consists of exactly the nonempty faces of the graded complex. -/
def toPreAbstractSimplicialComplex (C : HypergraphComplex r V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ ∃ h : s.card ≤ r, s ∈ C.faces s.card h}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    obtain ⟨hcard, hface⟩ := hs.2
    exact ⟨ht, ⟨(Finset.card_le_card hts).trans hcard,
      C.down_closed _ hcard s hface t hts _⟩⟩

/-- The underlying pre-abstract simplicial complex contains exactly the nonempty graded faces. -/
@[simp]
theorem mem_toPreAbstractSimplicialComplex (C : HypergraphComplex r V) (s : Finset V) :
    s ∈ C.toPreAbstractSimplicialComplex ↔
      s.Nonempty ∧ ∃ h : s.card ≤ r, s ∈ C.faces s.card h :=
  Iff.rfl

/-- Every face of the underlying pre-abstract simplicial complex has cardinality at most the
rank. -/
theorem card_le_of_mem_toPreAbstractSimplicialComplex (C : HypergraphComplex r V) {s : Finset V}
    (hs : s ∈ C.toPreAbstractSimplicialComplex) : s.card ≤ r :=
  hs.2.choose

end HypergraphComplex

end TauCeti

namespace PreAbstractSimplicialComplex

open TauCeti

variable {V : Type*}

/-- The rank-`r` hypergraph complex of a pre-abstract simplicial complex on a finite vertex type:
its faces of cardinality at most `r`, together with the adjoined empty face. -/
noncomputable def toHypergraphComplex [Fintype V] (K : PreAbstractSimplicialComplex V) (r : ℕ) :
    HypergraphComplex r V := by
  classical
  exact {
    faces := fun k _ ↦ (univ.powersetCard k).filter fun s ↦ s = ∅ ∨ s ∈ K
    face_card := by
      intro k hk s hs
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
    down_closed := by
      intro k hk s hs t hts htr
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨subset_univ _, rfl⟩, ?_⟩
      rcases (Finset.mem_filter.mp hs).2 with rfl | hs
      · exact Or.inl (Finset.subset_empty.mp hts)
      · by_cases ht : t = ∅
        · exact Or.inl ht
        · exact Or.inr ((K.isRelLowerSet_faces hs).2 hts (Finset.nonempty_iff_ne_empty.mpr ht))
    empty_mem := by simp }

/-- Membership in the rank-`r` hypergraph complex of a pre-abstract simplicial complex is
membership in the original complex, except that the empty face is adjoined. -/
@[simp]
theorem mem_faces_toHypergraphComplex [Fintype V] (K : PreAbstractSimplicialComplex V) (r : ℕ)
    (k : ℕ) (hk : k ≤ r) (s : Finset V) :
    s ∈ (K.toHypergraphComplex r).faces k hk ↔ s.card = k ∧ (s = ∅ ∨ s ∈ K) := by
  classical
  simp only [toHypergraphComplex, mem_filter, mem_powersetCard, subset_univ, true_and]

/-- Forgetting the adjoined empty face recovers a pre-abstract simplicial complex whose faces have
cardinality at most the rank. -/
@[simp]
theorem toPreAbstractSimplicialComplex_toHypergraphComplex [Fintype V] {r : ℕ}
    (K : PreAbstractSimplicialComplex V) (hK : ∀ s ∈ K, s.card ≤ r) :
    (K.toHypergraphComplex r).toPreAbstractSimplicialComplex = K := by
  ext s
  constructor
  · rintro ⟨hs, hle, hface⟩
    rcases (K.mem_faces_toHypergraphComplex r s.card hle s).mp hface with ⟨-, hs0 | hsK⟩
    · exact ((hs0 ▸ hs).ne_empty rfl).elim
    · exact hsK
  · intro hs
    refine ⟨(K.isRelLowerSet_faces hs).1, hK s hs, ?_⟩
    exact (K.mem_faces_toHypergraphComplex r s.card (hK s hs) s).mpr ⟨rfl, Or.inr hs⟩

end PreAbstractSimplicialComplex

namespace TauCeti.HypergraphComplex

variable {r : ℕ} {V : Type*}

/-- Adjoining the empty face after forgetting the grading recovers the original hypergraph
complex. -/
@[simp]
theorem toHypergraphComplex_toPreAbstractSimplicialComplex [Fintype V]
    (C : HypergraphComplex r V) : C.toPreAbstractSimplicialComplex.toHypergraphComplex r = C := by
  ext k hk s
  constructor
  · intro hface
    rcases (C.toPreAbstractSimplicialComplex.mem_faces_toHypergraphComplex r k hk s).mp hface with
      ⟨hcard, rfl | ⟨-, hle, hs⟩⟩
    · simp only [card_empty] at hcard
      subst k
      exact C.empty_mem
    · simpa only [hcard] using hs
  · intro hs
    have hcard := C.face_card k hk s hs
    subst k
    apply (C.toPreAbstractSimplicialComplex.mem_faces_toHypergraphComplex r s.card hk s).mpr
    refine ⟨rfl, ?_⟩
    by_cases hs0 : s = ∅
    · exact Or.inl hs0
    · exact Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr hs0, ⟨hk, hs⟩⟩

end TauCeti.HypergraphComplex

end
