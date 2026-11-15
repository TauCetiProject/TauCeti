/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Fintype.Fin

/-!
# Oriented edges and triangles of a finite two-complex

Given a linear order on the vertices `V`, each edge of a `TwoComplex V` has a unique increasing
presentation `(u, v)` with `u < v`, and each triangle has a unique increasing presentation
`(u, v, w)` with `u < v < w`. Defining these oriented face sets directly from `X.edges` and
`X.triangles` avoids assuming `Fintype V`, while agreeing on finite vertex types with filtering
`univ`.

When an edge weight is symmetric under reversing endpoints, twice the sum over increasing edges
equals the unoriented sum over all ordered pairs in each edge. Likewise, when a triangle weight is
invariant under all six vertex reorderings of each triangle, six times the sum over increasing
triangles equals the unoriented sum over all ordered triples of distinct vertices in each triangle.
These two identities separate combinatorics from group algebra in orientation-independence and
relabelling proofs for 1-cochains.
-/

public section

open Finset

namespace TauCeti.TwoComplex

variable {V A : Type*}

section LinearOrder

variable [LinearOrder V]

/-- The edges of `X`, each oriented in increasing vertex order `(u, v)` with `u < v`. -/
def orderedEdges (X : TwoComplex V) : Finset (V × V) :=
  X.edges.biUnion fun e => (e ×ˢ e).filter fun p => p.1 < p.2

/-- A pair lies in `orderedEdges` precisely when it is strictly increasing and spans an edge. -/
@[simp]
theorem mem_orderedEdges (X : TwoComplex V) (p : V × V) :
    p ∈ X.orderedEdges ↔ p.1 < p.2 ∧ X.Adj p.1 p.2 := by
  simp only [orderedEdges, mem_biUnion, mem_filter, mem_product]
  constructor
  · rintro ⟨e, he, ⟨hp1, hp2⟩, hlt⟩
    refine ⟨hlt, ?_⟩
    rw [← X.pair_mem_edges_iff]
    have hsub : ({p.1, p.2} : Finset V) ⊆ e :=
      insert_subset_iff.mpr ⟨hp1, singleton_subset_iff.mpr hp2⟩
    rwa [eq_of_subset_of_card_le hsub (by rw [X.edge_card e he, card_pair hlt.ne])]
  · rintro ⟨hlt, hadj⟩
    rw [← X.pair_mem_edges_iff] at hadj
    exact ⟨{p.1, p.2}, hadj, ⟨by simp, by simp⟩, hlt⟩

/-- On a finite vertex type, `orderedEdges` agrees with filtering all vertex pairs. -/
theorem orderedEdges_eq_filter_univ [Fintype V] (X : TwoComplex V) :
    X.orderedEdges =
      univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges := by
  ext p
  simp

/-- The triangles of `X`, each oriented in increasing vertex order `(u, v, w)` with
`u < v < w`. -/
def orderedTriangles (X : TwoComplex V) : Finset (V × V × V) :=
  X.triangles.biUnion fun t =>
    (t ×ˢ t ×ˢ t).filter fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2

/-- A triple lies in `orderedTriangles` precisely when it is strictly increasing and spans a
triangle. -/
@[simp]
theorem mem_orderedTriangles (X : TwoComplex V) (p : V × V × V) :
    p ∈ X.orderedTriangles ↔
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles := by
  simp only [orderedTriangles, mem_biUnion, mem_filter, mem_product]
  constructor
  · rintro ⟨t, ht, ⟨hp1, hp2, hp3⟩, hlt12, hlt23⟩
    have hlt13 : p.1 < p.2.2 := hlt12.trans hlt23
    refine ⟨hlt12, hlt23, ?_⟩
    have hsub : ({p.1, p.2.1, p.2.2} : Finset V) ⊆ t :=
      insert_subset_iff.mpr ⟨hp1, insert_subset_iff.mpr ⟨hp2, singleton_subset_iff.mpr hp3⟩⟩
    have hcard : ({p.1, p.2.1, p.2.2} : Finset V).card = 3 := by
      rw [card_insert_of_notMem, card_pair hlt23.ne]
      simp [hlt12.ne, hlt13.ne]
    rwa [eq_of_subset_of_card_le hsub (by rw [X.triangle_card t ht, hcard])]
  · rintro ⟨hlt12, hlt23, ht⟩
    exact ⟨{p.1, p.2.1, p.2.2}, ht, ⟨by simp, by simp, by simp⟩, hlt12, hlt23⟩

/-- On a finite vertex type, `orderedTriangles` agrees with filtering all vertex triples. -/
theorem orderedTriangles_eq_filter_univ [Fintype V] (X : TwoComplex V) :
    X.orderedTriangles =
      univ.filter fun p : V × V × V =>
        p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles := by
  ext p
  simp

/-- Twice the sum of a symmetric edge weight over increasing edges equals the sum over both
directions of every unoriented edge. -/
theorem two_nsmul_sum_orderedEdges [AddCommMonoid A] (X : TwoComplex V) (f : V → V → A)
    (hf : ∀ {u v : V}, X.Adj u v → f v u = f u v) :
    2 • ∑ p ∈ X.orderedEdges, f p.1 p.2 =
      ∑ e ∈ X.edges, ∑ u ∈ e, ∑ v ∈ e.erase u, f u v := by
  rw [orderedEdges, sum_biUnion, smul_sum]
  · refine sum_congr rfl fun e he => ?_
    have hc := X.edge_card e he
    obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hc
    have hadj : X.Adj u v := (X.pair_mem_edges_iff u v).mp he
    have he1 : ({u, v} : Finset V).erase u = {v} := by
      ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
    have he2 : ({u, v} : Finset V).erase v = {u} := by
      ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · have hfilt : (({u, v} ×ˢ {u, v} : Finset (V × V)).filter fun p => p.1 < p.2) = {(u, v)} := by
        ext ⟨a, b⟩
        simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
        grind
      rw [hfilt, sum_singleton, two_nsmul, sum_pair huv, he1, he2, sum_singleton, sum_singleton,
        hf hadj]
    · have hfilt : (({u, v} ×ˢ {u, v} : Finset (V × V)).filter fun p => p.1 < p.2) = {(v, u)} := by
        ext ⟨a, b⟩
        simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
        grind
      rw [hfilt, sum_singleton, two_nsmul, sum_pair huv, he1, he2, sum_singleton, sum_singleton,
        hf hadj]
  · intro e₁ he₁ e₂ he₂ hne
    refine disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
    simp only [mem_filter, mem_product] at hp₁ hp₂
    have h1 : ({p.1, p.2} : Finset V) = e₁ :=
      eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hp₁.1.1, singleton_subset_iff.mpr hp₁.1.2⟩)
        (by rw [X.edge_card e₁ he₁, card_pair hp₁.2.ne])
    have h2 : ({p.1, p.2} : Finset V) = e₂ :=
      eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hp₂.1.1, singleton_subset_iff.mpr hp₂.1.2⟩)
        (by rw [X.edge_card e₂ he₂, card_pair hp₂.2.ne])
    exact h1.symm.trans h2

/-- Orienting edges in increasing order preserves their count. -/
@[simp]
theorem card_orderedEdges (X : TwoComplex V) : X.orderedEdges.card = X.edges.card := by
  have h := X.two_nsmul_sum_orderedEdges (fun _ _ => (1 : ℕ)) (fun _ => rfl)
  have hrhs : (∑ e ∈ X.edges, ∑ u ∈ e, ∑ _v ∈ e.erase u, (1 : ℕ)) = 2 * X.edges.card := by
    calc
      (∑ e ∈ X.edges, ∑ u ∈ e, ∑ _v ∈ e.erase u, (1 : ℕ))
        = ∑ e ∈ X.edges, 2 := by
          refine sum_congr rfl fun e he => ?_
          have hc := X.edge_card e he
          calc
            (∑ u ∈ e, ∑ _v ∈ e.erase u, (1 : ℕ))
              = ∑ u ∈ e, (e.erase u).card := by simp
            _ = ∑ u ∈ e, 1 := sum_congr rfl fun u hu => by rw [card_erase_of_mem hu, hc]
            _ = 2 := by simp [hc]
      _ = 2 * X.edges.card := by simp [mul_comm]
  rw [hrhs] at h
  simp only [sum_const, smul_eq_mul, mul_one] at h
  omega

/-- Six times the sum of a permutation-invariant triangle weight over increasing triangles equals
the sum over all six ordered vertex triples of every unoriented triangle. -/
theorem six_nsmul_sum_orderedTriangles [AddCommMonoid A] (X : TwoComplex V)
    (g : V → V → V → A)
    (hrot : ∀ {t : Finset V}, t ∈ X.triangles → ∀ {u v w : V},
      u ∈ t → v ∈ t → w ∈ t → u ≠ v → v ≠ w → w ≠ u → g v w u = g u v w)
    (hswap : ∀ {t : Finset V}, t ∈ X.triangles → ∀ {u v w : V},
      u ∈ t → v ∈ t → w ∈ t → u ≠ v → v ≠ w → w ≠ u → g u w v = g u v w) :
    6 • ∑ p ∈ X.orderedTriangles, g p.1 p.2.1 p.2.2 =
      ∑ t ∈ X.triangles, ∑ u ∈ t, ∑ v ∈ t.erase u, ∑ w ∈ (t.erase u).erase v, g u v w := by
  rw [orderedTriangles, sum_biUnion, smul_sum]
  · refine sum_congr rfl fun t ht => ?_
    have hc := X.triangle_card t ht
    let iso := t.orderEmbOfFin hc
    let u := iso 0
    let v := iso 1
    let w := iso 2
    have huv : u < v := iso.strictMono (by decide)
    have hvw : v < w := iso.strictMono (by decide)
    have huw : u < w := huv.trans hvw
    have ht_eq : t = {u, v, w} := by
      ext x
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hx
        obtain ⟨i, rfl⟩ := (range_orderEmbOfFin t hc).symm ▸ (mem_coe.mpr hx)
        match i with
        | ⟨0, _⟩ => left; rfl
        | ⟨1, _⟩ => right; left; rfl
        | ⟨2, _⟩ => right; right; rfl
      · rintro (rfl | rfl | rfl) <;> exact orderEmbOfFin_mem t hc _
    have hu : u ∈ t := ht_eq ▸ by simp
    have hv : v ∈ t := ht_eq ▸ by simp
    have hw : w ∈ t := ht_eq ▸ by simp
    have hfilt :
        ((t ×ˢ t ×ˢ t).filter fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2) = {(u, v, w)} := by
      ext ⟨a, b, c⟩
      simp only [ht_eq, mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
      grind
    rw [hfilt, sum_singleton]
    have hvwu : g v w u = g u v w := hrot ht hu hv hw huv.ne hvw.ne huw.ne'
    have hwuv : g w u v = g u v w :=
      (hrot ht hv hw hu hvw.ne huw.ne' huv.ne).trans hvwu
    have huwv : g u w v = g u v w := hswap ht hu hv hw huv.ne hvw.ne huw.ne'
    have hwvu : g w v u = g u v w :=
      (hrot ht hu hw hv huw.ne hvw.ne' huv.ne').trans huwv
    have hvuw : g v u w = g u v w :=
      (hrot ht hw hv hu hvw.ne' huv.ne' huw.ne).trans hwvu
    have htu : t.erase u = {v, w} := by
      ext x; simp only [ht_eq, mem_erase, mem_insert, mem_singleton]; grind
    have htv : t.erase v = {u, w} := by
      ext x; simp only [ht_eq, mem_erase, mem_insert, mem_singleton]; grind
    have htw : t.erase w = {u, v} := by
      ext x; simp only [ht_eq, mem_erase, mem_insert, mem_singleton]; grind
    have h_u : ∑ b ∈ t.erase u, ∑ c ∈ (t.erase u).erase b, g u b c = g u v w + g u w v := by
      have htuv : ({v, w} : Finset V).erase v = {w} := by
        ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
      have htuw : ({v, w} : Finset V).erase w = {v} := by
        ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
      rw [htu, sum_pair hvw.ne, htuv, htuw, sum_singleton, sum_singleton]
    have h_v : ∑ b ∈ t.erase v, ∑ c ∈ (t.erase v).erase b, g v b c = g v u w + g v w u := by
      have htvu : ({u, w} : Finset V).erase u = {w} := by
        ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
      have htvw : ({u, w} : Finset V).erase w = {u} := by
        ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
      rw [htv, sum_pair huw.ne, htvu, htvw, sum_singleton, sum_singleton]
    have h_w : ∑ b ∈ t.erase w, ∑ c ∈ (t.erase w).erase b, g w b c = g w u v + g w v u := by
      have htwu : ({u, v} : Finset V).erase u = {v} := by
        ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
      have htwv : ({u, v} : Finset V).erase v = {u} := by
        ext x; simp only [mem_erase, mem_insert, mem_singleton]; grind
      rw [htw, sum_pair huv.ne, htwu, htwv, sum_singleton, sum_singleton]
    have hsumt : ∀ f : V → A, ∑ x ∈ t, f x = f u + f v + f w := by
      intro f
      rw [ht_eq, sum_insert (by simp [huv.ne, huw.ne]), sum_pair hvw.ne, add_assoc]
    rw [hsumt, h_u, h_v, h_w, huwv, hvuw, hvwu, hwuv, hwvu]
    have h6 : (6 : ℕ) = 2 + 2 + 2 := rfl
    rw [h6, add_nsmul, add_nsmul, two_nsmul]
  · intro t₁ ht₁ t₂ ht₂ hne
    refine disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
    simp only [mem_filter, mem_product] at hp₁ hp₂
    have hcard : ({p.1, p.2.1, p.2.2} : Finset V).card = 3 := by
      rw [card_insert_of_notMem, card_pair hp₁.2.2.ne]
      simp [hp₁.2.1.ne, (hp₁.2.1.trans hp₁.2.2).ne]
    have h1 : ({p.1, p.2.1, p.2.2} : Finset V) = t₁ :=
      eq_of_subset_of_card_le
        (insert_subset_iff.mpr ⟨hp₁.1.1,
          insert_subset_iff.mpr ⟨hp₁.1.2.1, singleton_subset_iff.mpr hp₁.1.2.2⟩⟩)
        (by rw [X.triangle_card t₁ ht₁, hcard])
    have h2 : ({p.1, p.2.1, p.2.2} : Finset V) = t₂ :=
      eq_of_subset_of_card_le
        (insert_subset_iff.mpr ⟨hp₂.1.1,
          insert_subset_iff.mpr ⟨hp₂.1.2.1, singleton_subset_iff.mpr hp₂.1.2.2⟩⟩)
        (by rw [X.triangle_card t₂ ht₂, hcard])
    exact h1.symm.trans h2

/-- Orienting triangles in increasing order preserves their count. -/
@[simp]
theorem card_orderedTriangles (X : TwoComplex V) :
    X.orderedTriangles.card = X.triangles.card := by
  have h := X.six_nsmul_sum_orderedTriangles (fun _ _ _ => (1 : ℕ))
    (by intros; rfl) (by intros; rfl)
  have hrhs :
      (∑ t ∈ X.triangles, ∑ u ∈ t, ∑ v ∈ t.erase u, ∑ _w ∈ (t.erase u).erase v, (1 : ℕ)) =
        6 * X.triangles.card := by
    calc
      (∑ t ∈ X.triangles, ∑ u ∈ t, ∑ v ∈ t.erase u, ∑ _w ∈ (t.erase u).erase v, (1 : ℕ))
        = ∑ t ∈ X.triangles, 6 := by
          refine sum_congr rfl fun t ht => ?_
          have hc := X.triangle_card t ht
          calc
            (∑ u ∈ t, ∑ v ∈ t.erase u, ∑ _w ∈ (t.erase u).erase v, (1 : ℕ))
              = ∑ u ∈ t, ∑ v ∈ t.erase u, ((t.erase u).erase v).card := by simp
            _ = ∑ u ∈ t, ∑ _v ∈ t.erase u, 1 := by
                refine sum_congr rfl fun u hu => sum_congr rfl fun v hv => ?_
                rw [card_erase_of_mem hv, card_erase_of_mem hu, hc]
            _ = ∑ u ∈ t, 2 := by
                refine sum_congr rfl fun u hu => ?_
                have hc' : (t.erase u).card = 2 := by rw [card_erase_of_mem hu, hc]
                simp [hc']
            _ = 6 := by simp [hc]
      _ = 6 * X.triangles.card := by simp [mul_comm]
  rw [hrhs] at h
  simp only [sum_const, smul_eq_mul, mul_one] at h
  omega

/-- On `TwoComplex.complete V`, the oriented edges are precisely the strictly increasing pairs. -/
@[simp]
theorem orderedEdges_complete [Fintype V] :
    (complete V).orderedEdges = univ.filter fun p : V × V => p.1 < p.2 := by
  ext ⟨u, v⟩
  simp only [mem_orderedEdges, adj_complete_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, h.ne⟩⟩

/-- On `TwoComplex.complete V`, the oriented triangles are precisely the strictly increasing
triples. -/
@[simp]
theorem orderedTriangles_complete [Fintype V] :
    (complete V).orderedTriangles =
      univ.filter fun q : V × V × V => q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
  ext ⟨u, v, w⟩
  simp only [mem_orderedTriangles, mem_triangles_complete, mem_filter, mem_univ, true_and]
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨huv, hvw⟩ => ⟨huv, hvw, ?_⟩⟩
  rw [card_insert_of_notMem, card_pair hvw.ne]
  simp [huv.ne, (huv.trans hvw).ne]

end LinearOrder

end TauCeti.TwoComplex
