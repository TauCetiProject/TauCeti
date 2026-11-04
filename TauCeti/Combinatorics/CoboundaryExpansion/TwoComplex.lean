/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Edge and triangle carriers for group-valued cochains

A `TwoComplex` records the edges and filled triangles of a finite two-dimensional complex.
It is the edge/triangle presentation of a rank-three `HypergraphComplex`: adjoining all
vertices and the empty face, or forgetting those two levels, gives inverse conversions
when the graded complex contains all vertices. Thus an isolated vertex is retained by the
ambient vertex type rather than by extra data in the carrier.

The complete complex contains every pair and triple. Its face counts are provided both as
binomial coefficients and as real polynomial formulas, for use in normalizing sums over
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

/-- The real edge count, with subtraction in `ℝ` rather than in `ℕ`. -/
theorem card_edges_complete_cast :
    ((complete V).edges.card : ℝ) = Fintype.card V * (Fintype.card V - 1) / 2 := by
  rw [card_edges_complete, Nat.cast_choose_two]

/-- The real triangle count, valid also when fewer than three vertices are available. -/
theorem card_triangles_complete_cast :
    ((complete V).triangles.card : ℝ) =
      Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 2) / 6 := by
  rw [card_triangles_complete]
  by_cases hn : 2 ≤ Fintype.card V
  · have h := congrArg (Nat.cast : ℕ → ℝ)
      (Nat.descFactorial_eq_factorial_mul_choose (Fintype.card V) 3)
    norm_num [Nat.descFactorial_succ, Nat.factorial_succ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_sub hn] at h
    nlinarith
  · have hn' : Fintype.card V < 3 := by omega
    rw [Nat.choose_eq_zero_of_lt hn']
    have hsmall : Fintype.card V = 0 ∨ Fintype.card V = 1 := by omega
    rcases hsmall with h | h <;> simp [h]

end FiniteVertices

end TwoComplex

end TauCeti

end
