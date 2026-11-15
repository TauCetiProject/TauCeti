/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Edge and triangle carriers for group-valued cochains

A `TwoComplex` records the edges and filled triangles of a finite two-dimensional complex.
It is the edge/triangle presentation of a rank-three `HypergraphComplex`: adjoining all
vertices and the empty face, or forgetting those two levels, gives inverse conversions
when the graded complex contains all vertices. Thus an isolated vertex is retained by the
ambient vertex type rather than by extra data in the carrier.

The complete complex contains every pair and triple. Its face counts are provided both as
binomial coefficients and as polynomial formulas in division rings, for use in normalizing sums over
edges and triangles.
-/

public section

open Finset

namespace TauCeti

/-- The edge and triangle levels of a finite two-dimensional complex on `V`.
Every pair contained in a triangle must be an edge. -/
structure TwoComplex (V : Type*) where
  /-- The unoriented edges. -/
  edges : Finset (Finset V)
  /-- The unoriented filled triangles. -/
  triangles : Finset (Finset V)
  /-- Edges have exactly two vertices. -/
  edge_card : ∀ e ∈ edges, e.card = 2
  /-- Triangles have exactly three vertices. -/
  triangle_card : ∀ t ∈ triangles, t.card = 3
  /-- Every two-element subset of a triangle is an edge. -/
  edge_mem_of_subset : ∀ t ∈ triangles, ∀ e ⊆ t, e.card = 2 → e ∈ edges

namespace TwoComplex

variable {V : Type*}

/-- A two-complex is determined by its edges and triangles. -/
@[ext]
theorem ext {X Y : TwoComplex V} (he : X.edges = Y.edges)
    (ht : X.triangles = Y.triangles) : X = Y := by
  cases X
  cases Y
  simp_all

/-- Retain the edge and triangle levels of a rank-three graded complex. -/
def ofHypergraphComplex (C : HypergraphComplex 3 V) : TwoComplex V where
  edges := C.faces 2 (by decide)
  triangles := C.faces 3 (by decide)
  edge_card := C.face_card 2 (by decide)
  triangle_card := C.face_card 3 (by decide)
  edge_mem_of_subset := by
    intro t ht e het he
    simpa only [he] using C.down_closed 3 (by decide) t ht e het (by omega)

@[simp]
theorem edges_ofHypergraphComplex (C : HypergraphComplex 3 V) :
    (ofHypergraphComplex C).edges = C.faces 2 (by decide) := (rfl)

@[simp]
theorem triangles_ofHypergraphComplex (C : HypergraphComplex 3 V) :
    (ofHypergraphComplex C).triangles = C.faces 3 (by decide) := (rfl)

section DecidableEq

variable [DecidableEq V]

/-- The three vertices of a filled triangle are pairwise distinct. -/
theorem ne_of_triple_mem_triangles {X : TwoComplex V} {u v z : V}
    (ht : ({u, v, z} : Finset V) ∈ X.triangles) : u ≠ v ∧ u ≠ z ∧ v ≠ z :=
  card_triple_eq_three_iff.mp (X.triangle_card _ ht)

/-- The first two listed vertices of a filled triangle span an edge. Permuting `{u, v, z}` yields
the other two boundary edges as well. -/
theorem pair_mem_edges_of_triple_mem_triangles {X : TwoComplex V} {u v z : V}
    (ht : ({u, v, z} : Finset V) ∈ X.triangles) : ({u, v} : Finset V) ∈ X.edges :=
  X.edge_mem_of_subset _ ht {u, v} (by simp [insert_subset_iff])
    (card_pair (ne_of_triple_mem_triangles ht).1)

/-- A binary weight symmetric on the edges of `X` takes the same value on any two presentations of
the same edge. -/
theorem apply_eq_of_pair_eq {B : Sort*} (X : TwoComplex V) (w : V → V → B)
    (hw : ∀ ⦃u v⦄, ({u, v} : Finset V) ∈ X.edges → w u v = w v u) {u₁ v₁ u₂ v₂ : V}
    (he : ({u₁, v₁} : Finset V) ∈ X.edges) (hp : ({u₁, v₁} : Finset V) = {u₂, v₂}) :
    w u₁ v₁ = w u₂ v₂ := by
  have hne : u₁ ≠ v₁ := card_pair_eq_two_iff.mp (X.edge_card _ he)
  have h₁ : u₁ = u₂ ∨ u₁ = v₂ := by simpa using Finset.ext_iff.mp hp u₁
  have h₂ : v₁ = u₂ ∨ v₁ = v₂ := by simpa using Finset.ext_iff.mp hp v₁
  rcases h₁ with rfl | rfl
  · rcases h₂ with rfl | rfl
    · exact (hne rfl).elim
    · rfl
  · rcases h₂ with rfl | rfl
    · exact hw he
    · exact (hne rfl).elim

/-- A ternary weight on `V` that is invariant on the triangles of `X` under cyclic rotation
`(u, v, z) ↦ (v, z, u)` and transposition `(u, v, z) ↦ (v, u, z)` takes the same value on all six
presentations of any filled triangle. -/
theorem apply_eq_of_triple_eq {B : Sort*} (X : TwoComplex V) (w : V → V → V → B)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z)
    {u₁ v₁ z₁ u₂ v₂ z₂ : V} (ht : ({u₁, v₁, z₁} : Finset V) ∈ X.triangles)
    (hp : ({u₁, v₁, z₁} : Finset V) = {u₂, v₂, z₂}) :
    w u₁ v₁ z₁ = w u₂ v₂ z₂ := by
  have ht_vzu : ({v₁, z₁, u₁} : Finset V) ∈ X.triangles := by
    rwa [pair_comm z₁ u₁, insert_comm v₁ u₁]
  have ht_zuv : ({z₁, u₁, v₁} : Finset V) ∈ X.triangles := by
    rwa [insert_comm z₁ u₁, pair_comm z₁ v₁]
  have h_vzu : w v₁ z₁ u₁ = w u₁ v₁ z₁ := hrot ht
  have h_zuv : w z₁ u₁ v₁ = w u₁ v₁ z₁ := (hrot ht_vzu).trans h_vzu
  have h_vuz : w v₁ u₁ z₁ = w u₁ v₁ z₁ := hswap ht
  have h_zvu : w z₁ v₁ u₁ = w u₁ v₁ z₁ := (hswap ht_vzu).trans h_vzu
  have h_uzv : w u₁ z₁ v₁ = w u₁ v₁ z₁ := (hswap ht_zuv).trans h_zuv
  obtain ⟨hne₁₂, hne₁₃, hne₂₃⟩ := ne_of_triple_mem_triangles (hp ▸ ht)
  have hu₂ : u₂ = u₁ ∨ u₂ = v₁ ∨ u₂ = z₁ := by
    simpa using (Finset.ext_iff.mp hp u₂).mpr (by simp)
  have hv₂ : v₂ = u₁ ∨ v₂ = v₁ ∨ v₂ = z₁ := by
    simpa using (Finset.ext_iff.mp hp v₂).mpr (by simp)
  have hz₂ : z₂ = u₁ ∨ z₂ = v₁ ∨ z₂ = z₁ := by
    simpa using (Finset.ext_iff.mp hp z₂).mpr (by simp)
  rcases hu₂ with rfl | rfl | rfl <;>
    rcases hv₂ with rfl | rfl | rfl <;>
    rcases hz₂ with rfl | rfl | rfl <;>
    first
    | contradiction
    | rfl
    | exact h_vzu.symm
    | exact h_zuv.symm
    | exact h_vuz.symm
    | exact h_zvu.symm
    | exact h_uzv.symm

end DecidableEq

section FiniteVertices

variable [Fintype V]

/-- Adjoin the empty face and every singleton to the edge and triangle levels.
Finiteness of the ambient vertex type is needed to adjoin even isolated vertices. -/
noncomputable def toHypergraphComplex (X : TwoComplex V) : HypergraphComplex 3 V := by
  classical
  exact {
    faces := fun k _ =>
      if k = 0 then {∅}
      else if k = 1 then univ.powersetCard 1
      else if k = 2 then X.edges else X.triangles
    face_card := by
      intro k hk s hs
      interval_cases k <;> simp_all [mem_powersetCard, X.edge_card, X.triangle_card]
    down_closed := by
      intro k hk s hs t hts ht
      have hcard : s.card = k := by
        interval_cases k <;> simp_all [mem_powersetCard, X.edge_card, X.triangle_card]
      have hle := card_le_card hts
      by_cases ht0 : t.card = 0
      · simp [card_eq_zero.mp ht0]
      by_cases ht1 : t.card = 1
      · simp [ht1, mem_powersetCard]
      by_cases ht2 : t.card = 2
      · simp only [ht2, ite_true]
        by_cases hk2 : k = 2
        · have hts_eq : t = s := eq_of_subset_of_card_le hts (by omega)
          subst t
          simpa [hk2] using hs
        · have hk3 : k = 3 := by omega
          exact X.edge_mem_of_subset s (by simpa [hk3] using hs) t hts ht2
      · have ht3 : t.card = 3 := by omega
        have hk3 : k = 3 := by omega
        have hts_eq : t = s := eq_of_subset_of_card_le hts (by omega)
        subst t
        simpa [hk3, ht3] using hs
    empty_mem := by simp }

/-- The conversion to graded complexes has exactly the specified four levels. -/
@[simp]
theorem mem_faces_toHypergraphComplex (X : TwoComplex V) (k : ℕ) (hk : k ≤ 3)
    (s : Finset V) :
    s ∈ X.toHypergraphComplex.faces k hk ↔
      (k = 0 ∧ s = ∅) ∨ (k = 1 ∧ s.card = 1) ∨
      (k = 2 ∧ s ∈ X.edges) ∨ (k = 3 ∧ s ∈ X.triangles) := by
  classical
  interval_cases k <;> simp [toHypergraphComplex, mem_powersetCard]

@[simp]
theorem faces_one_toHypergraphComplex (X : TwoComplex V) :
    X.toHypergraphComplex.faces 1 (by decide) = univ.powersetCard 1 := by
  classical
  ext s
  simp [mem_powersetCard]

@[simp]
theorem faces_two_toHypergraphComplex (X : TwoComplex V) :
    X.toHypergraphComplex.faces 2 (by decide) = X.edges := by
  ext s
  simp

@[simp]
theorem faces_three_toHypergraphComplex (X : TwoComplex V) :
    X.toHypergraphComplex.faces 3 (by decide) = X.triangles := by
  ext s
  simp

/-- Adjoining lower faces and then retaining edges and triangles changes nothing. -/
@[simp]
theorem ofHypergraphComplex_toHypergraphComplex (X : TwoComplex V) :
    ofHypergraphComplex X.toHypergraphComplex = X := by
  ext <;> simp

/-- Forgetting and adjoining lower faces recovers a graded complex containing every vertex. -/
theorem toHypergraphComplex_ofHypergraphComplex (C : HypergraphComplex 3 V)
    (h : C.faces 1 (by decide) = univ.powersetCard 1) :
    (ofHypergraphComplex C).toHypergraphComplex = C := by
  classical
  ext k hk
  interval_cases k <;> simp [h]

/-- The complete two-complex contains every pair and triple of vertices. -/
noncomputable def complete (V : Type*) [Fintype V] : TwoComplex V := by
  classical
  exact {
    edges := univ.powersetCard 2
    triangles := univ.powersetCard 3
    edge_card := by simp [mem_powersetCard]
    triangle_card := by simp [mem_powersetCard]
    edge_mem_of_subset := by simp [mem_powersetCard] }

@[simp]
theorem mem_edges_complete (e : Finset V) : e ∈ (complete V).edges ↔ e.card = 2 := by
  classical
  simp [complete, mem_powersetCard]

@[simp]
theorem mem_triangles_complete (t : Finset V) :
    t ∈ (complete V).triangles ↔ t.card = 3 := by
  classical
  simp [complete, mem_powersetCard]

/-- The complete complex has one edge for each two-element subset. -/
@[simp]
theorem card_edges_complete : (complete V).edges.card = (Fintype.card V).choose 2 := by
  classical
  exact card_powersetCard 2 univ

/-- The complete complex has one triangle for each three-element subset. -/
@[simp]
theorem card_triangles_complete : (complete V).triangles.card = (Fintype.card V).choose 3 := by
  classical
  exact card_powersetCard 3 univ

/-- The edge count in a division ring, with subtraction there rather than in `ℕ`. -/
theorem natCast_card_edges_complete {K : Type*} [DivisionRing K] [NeZero (2 : K)] :
    ((complete V).edges.card : K) = Fintype.card V * (Fintype.card V - 1) / 2 := by
  rw [card_edges_complete, Nat.cast_choose_two]

/-- The triangle count in a characteristic-zero division ring, valid also below three vertices. -/
theorem natCast_card_triangles_complete {K : Type*} [DivisionRing K] [CharZero K] :
    ((complete V).triangles.card : K) =
      Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 2) / 6 := by
  rw [card_triangles_complete, Nat.cast_choose_eq_descPochhammer_div]
  norm_num [descPochhammer_succ_eval, Nat.factorial_succ]

end FiniteVertices

end TwoComplex

end TauCeti

end
