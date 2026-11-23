/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Set.Finite.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Basic

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
  congr
  exact funext₂ h

/-- The empty face is the unique face in level zero. -/
@[simp]
theorem faces_zero (C : HypergraphComplex r V) : C.faces 0 (Nat.zero_le r) = {∅} :=
  eq_singleton_iff_unique_mem.mpr
    ⟨C.empty_mem, fun s hs => card_eq_zero.mp (C.face_card 0 (Nat.zero_le r) s hs)⟩

/-- Forget the empty face and finite grading of a hypergraph complex.

The resulting Mathlib complex consists of exactly the nonempty faces of the graded complex. -/
def toPreAbstractSimplicialComplex (C : HypergraphComplex r V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ ∃ h : s.card ≤ r, s ∈ C.faces s.card h}
  isRelLowerSet_faces := fun {s} ⟨hs, hcard, hface⟩ => ⟨hs, fun t hts ht =>
    ⟨ht, (card_le_card hts).trans hcard, C.down_closed _ hcard s hface t hts _⟩⟩

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
  ((C.mem_toPreAbstractSimplicialComplex s).mp hs).2.fst

/-- Forgetting the empty face leaves finitely many faces, even on an infinite ambient type. -/
theorem finite_faces_toPreAbstractSimplicialComplex (C : HypergraphComplex r V) :
    C.toPreAbstractSimplicialComplex.faces.Finite := by
  classical
  refine ((univ : Finset (Fin (r + 1))).biUnion fun k => C.faces k k.is_le).finite_toSet.subset ?_
  rintro s ⟨-, hle, hface⟩
  exact mem_biUnion.mpr ⟨⟨s.card, Nat.lt_succ_of_le hle⟩, mem_univ _, hface⟩

/-- Keep the faces of cardinality at most `r` of a finite precomplex and adjoin the empty face.
On a finite ambient type, the finiteness proof can be supplied by `Set.toFinite _`.
With an expected `HypergraphComplex r V` type, use `.ofPreAbstractSimplicialComplex K hfinite`. -/
noncomputable def ofPreAbstractSimplicialComplex (K : PreAbstractSimplicialComplex V)
    (hfinite : K.faces.Finite) : HypergraphComplex r V := by
  classical
  exact {
    faces := fun k _ => (insert ∅ hfinite.toFinset).filter (fun s => s.card = k)
    face_card := by
      intro k _ s hs
      exact (mem_filter.mp hs).2
    down_closed := by
      intro k _ s hs t hts _
      refine mem_filter.mpr ⟨?_, rfl⟩
      rcases mem_insert.mp (mem_filter.mp hs).1 with rfl | hs
      · simp [subset_empty.mp hts]
      · rcases t.eq_empty_or_nonempty with rfl | ht
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (hfinite.mem_toFinset.mpr
            ((K.isRelLowerSet_faces (hfinite.mem_toFinset.mp hs)).2 hts ht))
    empty_mem := by simp }

/-- The finite conversion adds exactly the empty face and groups faces by cardinality. -/
@[simp]
theorem mem_faces_ofPreAbstractSimplicialComplex (K : PreAbstractSimplicialComplex V)
    (hfinite : K.faces.Finite) (k : ℕ) (hk : k ≤ r) {s : Finset V} :
    s ∈ (ofPreAbstractSimplicialComplex K hfinite).faces k hk ↔
      (s = ∅ ∨ s ∈ K) ∧ s.card = k := by
  classical
  simp only [ofPreAbstractSimplicialComplex, mem_filter, mem_insert, Set.Finite.mem_toFinset,
    PreAbstractSimplicialComplex.mem_faces]

/-- Adjoining and then forgetting the empty face recovers the original finite precomplex. -/
@[simp]
theorem toPreAbstractSimplicialComplex_ofPreAbstractSimplicialComplex
    (K : PreAbstractSimplicialComplex V) (hfinite : K.faces.Finite)
    (hcard : ∀ s ∈ K, s.card ≤ r) :
    (ofPreAbstractSimplicialComplex (r := r) K hfinite).toPreAbstractSimplicialComplex = K := by
  refine SetLike.ext fun s => ?_
  simp only [mem_toPreAbstractSimplicialComplex, mem_faces_ofPreAbstractSimplicialComplex, and_true]
  constructor
  · rintro ⟨hne, -, rfl | hs⟩
    · exact (not_nonempty_empty hne).elim
    · exact hs
  · exact fun hs => ⟨(K.isRelLowerSet_faces (PreAbstractSimplicialComplex.mem_faces.mpr hs)).1,
      hcard s hs, Or.inr hs⟩

/-- Forgetting and then adjoining the empty face recovers the finite graded complex,
including rank zero. -/
@[simp]
theorem ofPreAbstractSimplicialComplex_toPreAbstractSimplicialComplex (C : HypergraphComplex r V) :
    ofPreAbstractSimplicialComplex C.toPreAbstractSimplicialComplex
      C.finite_faces_toPreAbstractSimplicialComplex = C := by
  ext k hk s
  rw [mem_faces_ofPreAbstractSimplicialComplex, mem_toPreAbstractSimplicialComplex]
  constructor
  · rintro ⟨rfl | ⟨-, _, hs⟩, rfl⟩
    · simpa only [card_empty] using C.empty_mem
    · exact hs
  · intro hs
    obtain rfl := C.face_card k hk s hs
    exact ⟨s.eq_empty_or_nonempty.imp_right fun hne => ⟨hne, hk, hs⟩, rfl⟩

end HypergraphComplex

end TauCeti

end
