/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Line
public import TauCeti.GroupTheory.LambdaTree.Basic
public import Mathlib.Data.List.GetD

/-!
# The path metric of a Serre graph

The distance between two vertices of a preconnected Serre graph, the least length of a path
joining them, is a `ℤ`-valued metric on the set of vertices: the *path metric* of the graph. Its
segments are exactly the sets of vertices of the shortest paths, a shortest path being
parametrised by the positions of its vertices. In particular the path metric is geodesic.

In a graph without circuits the reduced paths are the shortest paths, so the set of vertices of a
reduced path of a tree is a segment. This is the first step in identifying the `ℤ`-trees with the
sets of vertices of simplicial trees, with their path metric.

The path metric of the line, whose vertices are the integers, is the metric `|a - b|`.

## Main definitions

* `TauCeti.SerreGraph.Preconnected.pathMetric`: the path metric of a preconnected Serre graph.

## Main results

* `TauCeti.SerreGraph.Preconnected.isSegment_setOf_mem_vertices`: the set of vertices of a
  shortest path is a segment of the path metric.
* `TauCeti.SerreGraph.Preconnected.isSegment_pathMetric_iff`: the segments of the path metric are
  the sets of vertices of the shortest paths.
* `TauCeti.SerreGraph.Preconnected.isGeodesic_pathMetric`: the path metric is geodesic.
* `TauCeti.SerreGraph.IsAcyclic.isSegment_setOf_mem_vertices`: in a graph without circuits, the
  set of vertices of a reduced path is a segment.
* `TauCeti.SerreGraph.pathMetric_line`: the path metric of the line is `|a - b|`.

## References

* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §4.2, Example 10.
* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §2.1.
* J.-P. Serre, *Trees*, Chapter I, §2.2.
-/

public section

namespace TauCeti
namespace SerreGraph

open Set

variable {Γ : SerreGraph}

/-- The path metric of a preconnected Serre graph: the `ℤ`-valued metric on its vertices whose
value at two vertices is the least length of a path joining them. -/
noncomputable def Preconnected.pathMetric (h : Γ.Preconnected) : LambdaMetric ℤ Γ.V where
  toFun a b := Γ.dist a b
  refl' a := by simp
  symm' a b := by rw [dist_comm]
  triangle' a b c :=
    mod_cast dist_triangle ((preconnected_iff Γ).1 h a b) ((preconnected_iff Γ).1 h b c)
  eq_of_eq_zero' {a b} hab :=
    (dist_eq_zero_iff ((preconnected_iff Γ).1 h a b)).1 (mod_cast hab)

namespace Preconnected

variable (h : Γ.Preconnected) {a b : Γ.V}

@[simp]
theorem pathMetric_apply (a b : Γ.V) : h.pathMetric a b = Γ.dist a b :=
  (rfl)

/-- Along a shortest path, two vertices are at distance the difference of their positions. -/
private theorem dist_getD_vertices {p : Γ.Path a b} (hp : p.length = Γ.dist a b) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    (Γ.dist (p.vertices.getD i b) (p.vertices.getD j b) : ℤ) = |(i : ℤ) - j| := by
  have hlen := p.vertices_length
  wlog hij : i ≤ j generalizing i j
  · rw [dist_comm, abs_sub_comm]
    exact this hj hi (by omega)
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
    dist_getElem_vertices hp hij (by omega), abs_sub_comm, abs_of_nonneg (by omega)]
  omega

/-- The vertices of a shortest path from `a` to `b` form a segment from `a` to `b` for the path
metric. -/
theorem isSegment_setOf_mem_vertices {p : Γ.Path a b} (hp : p.length = Γ.dist a b) :
    h.pathMetric.IsSegment {v | v ∈ p.vertices} a b := by
  have hlen := p.vertices_length
  -- Parametrise the path by the positions of its vertices.
  refine LambdaMetric.isSegment_iff.2 ⟨fun t => p.vertices.getD t.toNat b, ?_, ?_,
    (LambdaMetric.isometricOn_iff _).2 ?_, ?_⟩
  · simpa only [Int.toNat_zero, p.getElem_vertices_zero] using
      List.getD_eq_getElem _ b p.length_vertices_pos
  · simp only [pathMetric_apply, ← hp, Int.toNat_natCast]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simpa only [Quiver.Path.comp_nil, List.get_eq_getElem] using
      p.vertices_comp_get_length_eq .nil
  · rintro s ⟨hs₀, hs⟩ t ⟨ht₀, ht⟩
    rw [pathMetric_apply, ← hp] at hs ht
    rw [pathMetric_apply]
    lift s to ℕ using hs₀
    lift t to ℕ using ht₀
    exact dist_getD_vertices hp (by omega) (by omega)
  · ext v
    simp only [pathMetric_apply, ← hp, mem_image, mem_Icc, mem_ofPred_eq, List.mem_iff_getElem]
    constructor
    · rintro ⟨t, ⟨ht₀, ht⟩, rfl⟩
      exact ⟨t.toNat, by omega, (List.getD_eq_getElem _ _ _).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, ⟨by omega, by omega⟩, by
        simpa only [Int.toNat_natCast] using List.getD_eq_getElem _ _ hi⟩

/-- An isometric map `f` of the interval `[0, n]` of `ℤ` into the vertices of a graph, for its
path metric, runs along a path: for `k ≤ n` the vertices `f 0, …, f k` are those of a path of
length `k`. -/
private theorem exists_path_of_isometricOn {f : ℤ → Γ.V} {n : ℕ}
    (hf : h.pathMetric.IsometricOn f (Icc 0 n)) (k : ℕ) (hk : k ≤ n) (c : Γ.V) (hc : f k = c) :
    ∃ p : Γ.Path (f 0) c, p.length = k ∧ {v | v ∈ p.vertices} = f '' Icc 0 (k : ℤ) := by
  induction k generalizing c with
  | zero =>
    subst hc
    exact ⟨.nil, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨p, hpl, hpv⟩ := ih (by omega) _ rfl
    -- The vertices in positions `k` and `k + 1` are at distance one, hence joined by a dart.
    have hd : Γ.dist (f k) c = 1 := by
      have := hf.dist_eq (a := k) (b := (k + 1 : ℕ)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      rw [pathMetric_apply, hc] at this
      simpa using this
    obtain ⟨q, hq⟩ := exists_length_eq_dist ((preconnected_iff Γ).1 h (f k) c)
    rw [hd] at hq
    cases q with
    | nil => simp at hq
    | cons q e =>
      obtain rfl := q.eq_of_length_zero (by simpa using hq)
      refine ⟨p.cons e, by simp [hpl], ?_⟩
      ext v
      have hv := Set.ext_iff.1 hpv v
      simp only [mem_ofPred_eq, mem_image, mem_Icc] at hv
      simp only [mem_ofPred_eq, Quiver.Path.mem_vertices_cons, hv, mem_image, mem_Icc]
      constructor
      · rintro (⟨t, ht, rfl⟩ | rfl)
        · exact ⟨t, ⟨ht.1, by omega⟩, rfl⟩
        · exact ⟨(k + 1 : ℕ), ⟨by omega, le_rfl⟩, hc⟩
      · rintro ⟨t, ⟨ht₀, ht⟩, rfl⟩
        rcases ht.eq_or_lt with rfl | hlt
        · exact .inr hc
        · exact .inl ⟨t, ⟨ht₀, by omega⟩, rfl⟩

/-- The segments of the path metric from `a` to `b` are the sets of vertices of the shortest paths
from `a` to `b`. -/
theorem isSegment_pathMetric_iff {σ : Set Γ.V} :
    h.pathMetric.IsSegment σ a b ↔
      ∃ p : Γ.Path a b, p.length = Γ.dist a b ∧ {v | v ∈ p.vertices} = σ := by
  refine ⟨?_, fun ⟨p, hp, hσ⟩ => hσ ▸ h.isSegment_setOf_mem_vertices hp⟩
  rw [LambdaMetric.isSegment_iff]
  rintro ⟨f, rfl, hfD, hf, rfl⟩
  rw [pathMetric_apply] at hfD hf ⊢
  exact h.exists_path_of_isometricOn hf _ le_rfl b hfD

/-- The path metric of a preconnected Serre graph is geodesic. -/
theorem isGeodesic_pathMetric : h.pathMetric.IsGeodesic := by
  refine LambdaMetric.isGeodesic_iff.2 fun a b => ?_
  obtain ⟨p, hp⟩ := exists_length_eq_dist ((preconnected_iff Γ).1 h a b)
  exact ⟨_, h.isSegment_setOf_mem_vertices hp⟩

end Preconnected

/-- In a graph without circuits, the vertices of a reduced path from `a` to `b` form a segment
from `a` to `b` for the path metric. -/
theorem IsAcyclic.isSegment_setOf_mem_vertices (hΓ : Γ.IsAcyclic) (h : Γ.Preconnected) {a b : Γ.V}
    {p : Γ.Path a b} (hp : Path.IsReduced Γ p) : h.pathMetric.IsSegment {v | v ∈ p.vertices} a b :=
  h.isSegment_setOf_mem_vertices (hΓ.dist_eq_length hp).symm

/-- The path metric of the line is the metric `|a - b|` on the integers. -/
theorem pathMetric_line (h : line.Preconnected) (a b : line.V) :
    h.pathMetric a b = |lineVertexEquiv a - lineVertexEquiv b| := by
  rw [h.pathMetric_apply, line_dist]

end SerreGraph
end TauCeti
