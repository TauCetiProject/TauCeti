/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite bounded hypergraph complexes

A `HypergraphComplex r V` is a finite downward-closed family of finite vertex sets, containing
the empty face and with face cardinalities bounded by `r`. Its `level n` consists of the faces
with exactly `n` vertices: in particular, triples have level three, not level two.
These finite levels provide the uncolored face data underlying colored hypergraph decompositions.

`toPreAbstractSimplicialComplex` forgets the empty face and the cardinality bound. Conversely,
`ofPreAbstractSimplicialComplex` adjoins the empty face to a Mathlib precomplex with finitely many
faces and a given cardinality bound. The two constructions are inverse. Finiteness of the vertex
type is not needed; on a finite vertex type the finite-face hypothesis is supplied by
`Set.toFinite`.

The bridge uses Mathlib's `PreAbstractSimplicialComplex` rather than introducing another
set-based simplicial carrier. Unused ambient vertices are allowed on both sides.
-/

public section

namespace TauCeti

/-- A finite family of faces of cardinality at most `r`, closed under taking all subsets and
containing the empty face. The bound is on cardinality, not simplicial dimension. -/
@[ext]
structure HypergraphComplex (r : ℕ) (V : Type*) where
  /-- The finite family of faces, including the empty face. -/
  faces : Finset (Finset V)
  /-- The empty face is always present. -/
  empty_mem : ∅ ∈ faces
  /-- Every subset of a face is a face. -/
  downward_closed : ∀ {s t}, s ⊆ t → t ∈ faces → s ∈ faces
  /-- Face cardinalities are bounded by the rank. -/
  card_le : ∀ s ∈ faces, s.card ≤ r

namespace HypergraphComplex

variable {r : ℕ} {V : Type*} (C : HypergraphComplex r V)

/-- The faces with exactly `n` vertices. Level zero contains just the empty face. -/
def level (n : ℕ) : Finset (Finset V) :=
  C.faces.filter (fun s => s.card = n)

/-- Membership in a level specifies both face membership and cardinality. -/
@[simp]
theorem mem_level {s : Finset V} {n : ℕ} :
    s ∈ C.level n ↔ s ∈ C.faces ∧ s.card = n := by
  simp [level]

/-- The unique face of cardinality zero is the empty face. -/
@[simp]
theorem level_zero : C.level 0 = {∅} := by
  classical
  ext s
  simp only [mem_level, Finset.card_eq_zero, Finset.mem_singleton]
  exact ⟨And.right, by rintro rfl; exact ⟨C.empty_mem, rfl⟩⟩

/-- Levels above the cardinality bound are empty. -/
theorem level_eq_empty_of_lt {n : ℕ} (hn : r < n) : C.level n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hs, hcard⟩ := C.mem_level.mp hs
  exact (not_le_of_gt hn) (hcard ▸ C.card_le s hs)

/-- Distinct levels have no common faces. -/
theorem disjoint_level {m n : ℕ} (h : m ≠ n) : Disjoint (C.level m) (C.level n) := by
  rw [Finset.disjoint_left]
  intro s hm hn
  exact h ((C.mem_level.mp hm).2.symm.trans (C.mem_level.mp hn).2)

/-- The levels from zero to the cardinality bound enumerate every face. -/
theorem biUnion_level [DecidableEq V] :
    (Finset.range (r + 1)).biUnion C.level = C.faces := by
  unfold level
  exact Finset.biUnion_filter_eq_of_maps_to
    (fun s hs => Finset.mem_range.mpr (Nat.lt_succ_of_le (C.card_le s hs)))

/-- Forget the empty face and the cardinality bound, retaining the nonempty simplicial faces. -/
def toPreAbstractSimplicialComplex : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ C.faces ∧ s.Nonempty}
  isRelLowerSet_faces := fun {_} hs =>
    ⟨hs.2, fun _ hst ht => ⟨C.downward_closed hst hs.1, ht⟩⟩

/-- The simplicial bridge retains exactly the nonempty faces. -/
@[simp]
theorem mem_toPreAbstractSimplicialComplex {s : Finset V} :
    s ∈ C.toPreAbstractSimplicialComplex ↔ s ∈ C.faces ∧ s.Nonempty := Iff.rfl

/-- Forgetting the empty face leaves a finite face set, even on an infinite ambient type. -/
theorem finite_faces_toPreAbstractSimplicialComplex :
    C.toPreAbstractSimplicialComplex.faces.Finite :=
  C.faces.finite_toSet.subset (fun _ hs => hs.1)

/-- The nonempty faces retain the cardinality bound. -/
theorem card_le_toPreAbstractSimplicialComplex {s : Finset V}
    (hs : s ∈ C.toPreAbstractSimplicialComplex) : s.card ≤ r :=
  C.card_le s (C.mem_toPreAbstractSimplicialComplex.mp hs).1

/-- Adjoin the empty face to a precomplex with finitely many faces and bounded face cardinalities.
On a finite ambient type, the finiteness proof can be supplied by `Set.toFinite _`. -/
noncomputable def ofPreAbstractSimplicialComplex (K : PreAbstractSimplicialComplex V)
    (hfinite : K.faces.Finite) (hcard : ∀ s ∈ K, s.card ≤ r) : HypergraphComplex r V := by
  classical
  exact
    { faces := insert ∅ hfinite.toFinset
      empty_mem := Finset.mem_insert_self _ _
      downward_closed := by
        intro s t hst ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · simp only [Finset.subset_empty] at hst
          simp [hst]
        · by_cases hs : s = ∅
          · simp [hs]
          · exact Finset.mem_insert_of_mem (hfinite.mem_toFinset.mpr
              ((K.isRelLowerSet_faces (hfinite.mem_toFinset.mp ht)).2 hst
                (Finset.nonempty_iff_ne_empty.mpr hs)))
      card_le := by
        intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · simp
        · exact hcard s (hfinite.mem_toFinset.mp hs) }

/-- The finite conversion adds exactly the empty face to the original faces. -/
@[simp]
theorem mem_faces_ofPreAbstractSimplicialComplex (K : PreAbstractSimplicialComplex V)
    (hfinite : K.faces.Finite) (hcard : ∀ s ∈ K, s.card ≤ r) {s : Finset V} :
    s ∈ (ofPreAbstractSimplicialComplex K hfinite hcard).faces ↔ s = ∅ ∨ s ∈ K := by
  classical
  simp only [ofPreAbstractSimplicialComplex, Finset.mem_insert, Set.Finite.mem_toFinset]
  -- Mathlib's set-like membership is membership in its face set.
  rfl

/-- Adjoining and then forgetting the empty face recovers the original precomplex. -/
@[simp]
theorem toPreAbstractSimplicialComplex_ofPreAbstractSimplicialComplex
    (K : PreAbstractSimplicialComplex V) (hfinite : K.faces.Finite)
    (hcard : ∀ s ∈ K, s.card ≤ r) :
    (ofPreAbstractSimplicialComplex K hfinite hcard).toPreAbstractSimplicialComplex = K := by
  apply SetLike.ext
  intro s
  rw [mem_toPreAbstractSimplicialComplex, mem_faces_ofPreAbstractSimplicialComplex]
  constructor
  · rintro ⟨rfl | hs, hne⟩
    · exact (Finset.not_nonempty_empty hne).elim
    · exact hs
  · intro hs
    exact ⟨Or.inr hs, (K.isRelLowerSet_faces hs).1⟩

/-- Forgetting and then adjoining the empty face recovers the finite complex,
including rank zero. -/
@[simp]
theorem ofPreAbstractSimplicialComplex_toPreAbstractSimplicialComplex :
    ofPreAbstractSimplicialComplex C.toPreAbstractSimplicialComplex
      C.finite_faces_toPreAbstractSimplicialComplex
      (fun _ hs => C.card_le_toPreAbstractSimplicialComplex hs) = C := by
  classical
  ext s
  rw [mem_faces_ofPreAbstractSimplicialComplex, mem_toPreAbstractSimplicialComplex]
  constructor
  · rintro (rfl | ⟨hs, _⟩)
    · exact C.empty_mem
    · exact hs
  · intro hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨hs, hne⟩

end HypergraphComplex

end TauCeti
