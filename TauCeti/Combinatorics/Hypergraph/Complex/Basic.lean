/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite bounded hypergraph complexes

This file defines finite augmented complexes whose faces have cardinality at most a fixed rank.
Unlike Mathlib's `PreAbstractSimplicialComplex`, a `HypergraphComplex` includes the empty face and
records faces in finite cardinality levels. The conversions in this file identify bounded
pre-abstract simplicial complexes with finitely many faces with these finite graded complexes after
forgetting or adjoining the empty face. Neither conversion requires a finite ambient vertex type.

Use `HypergraphComplex.ofPreAbstractSimplicialComplex` to construct a finite graded complex and
`HypergraphComplex.toPreAbstractSimplicialComplex` to forget its empty face and grading.

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

/-- Forgetting the empty face leaves finitely many faces, even on an infinite ambient type. -/
theorem finite_faces_toPreAbstractSimplicialComplex (C : HypergraphComplex r V) :
    C.toPreAbstractSimplicialComplex.faces.Finite := by
  classical
  let allFaces := (univ : Finset (Fin (r + 1))).biUnion
    (fun k => C.faces k (Nat.le_of_lt_succ k.isLt))
  apply allFaces.finite_toSet.subset
  intro s hs
  obtain ⟨-, hle, hface⟩ := hs
  exact mem_biUnion.mpr ⟨⟨s.card, Nat.lt_succ_of_le hle⟩, mem_univ _, hface⟩

private theorem mem_preAbstractSimplicialComplex_faces (K : PreAbstractSimplicialComplex V)
    {s : Finset V} : s ∈ K.faces ↔ s ∈ K :=
  Iff.rfl

/-- Keep the faces of cardinality at most `r` of a finite precomplex and adjoin the empty face.
On a finite ambient type, the finiteness proof can be supplied by `Set.toFinite _`.
With an expected `HypergraphComplex r V` type, use `.ofPreAbstractSimplicialComplex K hfinite`. -/
noncomputable def ofPreAbstractSimplicialComplex (K : PreAbstractSimplicialComplex V)
    (hfinite : K.faces.Finite) : HypergraphComplex r V := by
  classical
  exact {
    faces := fun k _ => (insert ∅ hfinite.toFinset).filter (fun s => s.card = k)
    face_card := by
      intro k hk s hs
      exact (mem_filter.mp hs).2
    down_closed := by
      intro k hk s hs t hts htr
      refine mem_filter.mpr ⟨?_, rfl⟩
      rcases mem_insert.mp (mem_filter.mp hs).1 with rfl | hs
      · simp [subset_empty.mp hts]
      · by_cases ht : t = ∅
        · simp [ht]
        · have hsK := (mem_preAbstractSimplicialComplex_faces K).mp
            (hfinite.mem_toFinset.mp hs)
          have htK := (K.isRelLowerSet_faces hsK).2 hts (nonempty_iff_ne_empty.mpr ht)
          exact mem_insert_of_mem (hfinite.mem_toFinset.mpr
            ((mem_preAbstractSimplicialComplex_faces K).mpr htK))
    empty_mem := by simp }

/-- The finite conversion adds exactly the empty face and groups faces by cardinality. -/
@[simp]
theorem mem_faces_ofPreAbstractSimplicialComplex (K : PreAbstractSimplicialComplex V)
    (hfinite : K.faces.Finite) (k : ℕ) (hk : k ≤ r) {s : Finset V} :
    s ∈ (ofPreAbstractSimplicialComplex K hfinite).faces k hk ↔
      (s = ∅ ∨ s ∈ K) ∧ s.card = k := by
  classical
  simp only [ofPreAbstractSimplicialComplex, mem_filter, mem_insert, Set.Finite.mem_toFinset,
    mem_preAbstractSimplicialComplex_faces]

/-- Adjoining and then forgetting the empty face recovers the original finite precomplex. -/
@[simp]
theorem toPreAbstractSimplicialComplex_ofPreAbstractSimplicialComplex
    (K : PreAbstractSimplicialComplex V) (hfinite : K.faces.Finite)
    (hcard : ∀ s ∈ K, s.card ≤ r) :
    (ofPreAbstractSimplicialComplex (r := r) K hfinite).toPreAbstractSimplicialComplex = K := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hne, hle, hs⟩
    rcases (mem_faces_ofPreAbstractSimplicialComplex K hfinite s.card hle).mp hs with
      ⟨rfl | hs, -⟩
    · exact (not_nonempty_empty hne).elim
    · exact hs
  · intro hs
    refine ⟨(K.isRelLowerSet_faces
      ((mem_preAbstractSimplicialComplex_faces K).mpr hs)).1, hcard s hs, ?_⟩
    exact (mem_faces_ofPreAbstractSimplicialComplex K hfinite s.card (hcard s hs)).mpr
      ⟨Or.inr hs, rfl⟩

/-- Forgetting and then adjoining the empty face recovers the finite graded complex,
including rank zero. -/
@[simp]
theorem ofPreAbstractSimplicialComplex_toPreAbstractSimplicialComplex (C : HypergraphComplex r V) :
    ofPreAbstractSimplicialComplex C.toPreAbstractSimplicialComplex
      C.finite_faces_toPreAbstractSimplicialComplex = C := by
  ext k hk s
  rw [mem_faces_ofPreAbstractSimplicialComplex]
  constructor
  · rintro ⟨rfl | ⟨-, hle, hs⟩, hcard⟩
    · simp only [card_empty] at hcard
      subst k
      exact C.empty_mem
    · simpa only [hcard] using hs
  · intro hs
    have hcard := C.face_card k hk s hs
    refine ⟨?_, hcard⟩
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨hne, hcard ▸ hk, by simpa only [hcard] using hs⟩

end HypergraphComplex

end TauCeti

end
