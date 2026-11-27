/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.LocallyFinite
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The union of the faces of a region

The union `regionUnion R` of the faces of a region is the union of the closed triangles
`TriFace.triangle f ⊆ ℝ²` of its faces, the convex hulls of their three vertices under
`ℤ² ⊆ ℝ²`.

Every triangle lies in the slab `m ≤ x ≤ m + 1`, `n ≤ y ≤ n + 1`, `k ≤ x − y ≤ k + 1`, where
`(m, n)` is the base vertex of the face and `k`, its `TauCeti.TriFace.diagIndex`, is `m − n` for
a white face and `m − n − 1` for a black one (`TauCeti.TriFace.triangle_subset_slab`); as the
integer data of two faces whose triangles meet differ by at most one in each of `m`, `n`, `k`,
two such faces share a vertex (`TauCeti.TriFace.exists_mem_vertices_of_triangle_inter_nonempty`).
The triangles are compact and form a locally finite family (`TauCeti.TriFace.isCompact_triangle`,
`TauCeti.TriFace.locallyFinite_triangle`), so the union of the faces of every region, finite or
infinite, is closed (`TauCeti.isClosed_regionUnion`).

**Connectedness.** If the union of the faces of `R` is preconnected, then `R` is connected through
its edges (`TauCeti.IsConnectedRegion.of_isPreconnected_regionUnion`): the faces whose vertices
are reachable from a fixed vertex, and the other faces, have closed unions, which are disjoint
because two faces whose triangles meet share a vertex
(`TauCeti.TriFace.exists_mem_vertices_of_triangle_inter_nonempty`). This is the first step of
the passage from topological to combinatorial simple connectivity.
-/

public section

open Set

namespace TauCeti

namespace TriFace

/-- The triangle of a face lies in the slab `m ≤ x ≤ m + 1`, `n ≤ y ≤ n + 1`,
`k ≤ x − y ≤ k + 1` of its base vertex `(m, n)` and its `diagIndex` `k`. -/
theorem triangle_subset_slab (f : TriFace) :
    f.triangle ⊆ {p : ℝ × ℝ | (f.v.1 : ℝ) ≤ p.1 ∧ p.1 ≤ f.v.1 + 1 ∧ (f.v.2 : ℝ) ≤ p.2 ∧
      p.2 ≤ f.v.2 + 1 ∧ (f.diagIndex : ℝ) ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ f.diagIndex + 1} := by
  rw [triangle_def]
  refine convexHull_min ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨⟨a, b⟩, c⟩ := f
    cases c <;> simp only [vertices_mk_true, vertices_mk_false, Finset.coe_insert,
      Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hu <;>
      rcases hu with rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  · have h1 := (LinearMap.fst ℝ ℝ ℝ).isLinear
    have h2 := (LinearMap.snd ℝ ℝ ℝ).isLinear
    have h3 := (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ).isLinear
    exact (convex_halfSpace_ge h1 _).inter <| (convex_halfSpace_le h1 _).inter <|
      (convex_halfSpace_ge h2 _).inter <| (convex_halfSpace_le h2 _).inter <|
      (convex_halfSpace_ge h3 _).inter (convex_halfSpace_le h3 _)

/-- **Meeting triangles share a vertex.** If the triangles of two faces meet, the faces have a
common vertex. -/
theorem exists_mem_vertices_of_triangle_inter_nonempty {f g : TriFace}
    (h : (f.triangle ∩ g.triangle).Nonempty) : ∃ u, u ∈ f.vertices ∧ u ∈ g.vertices := by
  obtain ⟨p, hpf, hpg⟩ := h
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := triangle_subset_slab f hpf
  obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ := triangle_subset_slab g hpg
  -- the integer data of the two faces differ by at most one
  have h1 : f.v.1 ≤ g.v.1 + 1 := by exact_mod_cast hf1.trans hg2
  have h2 : g.v.1 ≤ f.v.1 + 1 := by exact_mod_cast hg1.trans hf2
  have h3 : f.v.2 ≤ g.v.2 + 1 := by exact_mod_cast hf3.trans hg4
  have h4 : g.v.2 ≤ f.v.2 + 1 := by exact_mod_cast hg3.trans hf4
  have h5 : f.diagIndex ≤ g.diagIndex + 1 := by exact_mod_cast hf5.trans hg6
  have h6 : g.diagIndex ≤ f.diagIndex + 1 := by exact_mod_cast hg5.trans hf6
  simp only [mem_vertices_iff]
  obtain ⟨⟨a, b⟩, c⟩ := f
  obtain ⟨⟨a', b'⟩, c'⟩ := g
  dsimp only at h1 h2 h3 h4 h5 h6 ⊢
  cases c <;> cases c' <;> simp only [diagIndex_mk_true, diagIndex_mk_false] at h5 h6 ⊢
  -- a common vertex among the four corners of the square of `f`
  all_goals
    rcases (show a' = a - 1 ∨ a' = a ∨ a' = a + 1 by omega) with h | h | h <;>
    rcases (show b' = b - 1 ∨ b' = b ∨ b' = b + 1 by omega) with h' | h' | h' <;>
    first
    | exact ⟨(a, b), by dsimp only; omega⟩
    | exact ⟨(a + 1, b), by dsimp only; omega⟩
    | exact ⟨(a, b + 1), by dsimp only; omega⟩
    | exact ⟨(a + 1, b + 1), by dsimp only; omega⟩

/-- The triangle of a face is compact. -/
theorem isCompact_triangle (f : TriFace) : IsCompact f.triangle := by
  rw [triangle_def]
  exact ((f.vertices.finite_toSet).image _).isCompact_convexHull (𝕜 := ℝ)

/-- The triangles of the faces of the lattice form a locally finite family. -/
theorem locallyFinite_triangle : LocallyFinite fun f : TriFace => f.triangle := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  -- a face whose triangle meets the ball has its base vertex in a bounded box
  set A : Finset ℤ := Finset.Icc (⌊x.1⌋ - 2) (⌊x.1⌋ + 2)
  set B : Finset ℤ := Finset.Icc (⌊x.2⌋ - 2) (⌊x.2⌋ + 2)
  refine ((A ×ˢ B ×ˢ (Finset.univ : Finset Bool)).finite_toSet.image
    fun t => (⟨(t.1, t.2.1), t.2.2⟩ : TriFace)).subset ?_
  rintro ⟨⟨a, b⟩, c⟩ ⟨p, hpf, hpx⟩
  obtain ⟨h1, h2, h3, h4, -, -⟩ := triangle_subset_slab _ hpf
  rw [Metric.mem_closedBall, Prod.dist_eq, sup_le_iff, Real.dist_eq, Real.dist_eq] at hpx
  obtain ⟨hx1, hx2⟩ := hpx
  rw [abs_le] at hx1 hx2
  refine ⟨(a, b, c), ?_, rfl⟩
  simp only [Finset.coe_product, Finset.coe_univ, mem_prod, Finset.coe_Icc, mem_Icc, mem_univ,
    and_true, A, B]
  simp only at h1 h2 h3 h4
  have key (m : ℤ) (t : ℝ) (hm1 : (m : ℝ) ≤ t + 1) (hm2 : t - 2 ≤ m) :
      ⌊t⌋ - 2 ≤ m ∧ m ≤ ⌊t⌋ + 2 := by
    have := Int.floor_le t
    have := Int.lt_floor_add_one t
    constructor
    · have : ((⌊t⌋ - 2 : ℤ) : ℝ) < m + 1 := by push_cast; linarith
      exact Int.lt_add_one_iff.1 (by exact_mod_cast this)
    · have : (m : ℝ) < ((⌊t⌋ + 2 : ℤ) : ℝ) + 1 := by push_cast; linarith
      exact Int.lt_add_one_iff.1 (by exact_mod_cast this)
  exact ⟨key a x.1 (by linarith) (by linarith), key b x.2 (by linarith) (by linarith)⟩

end TriFace

/-- The union of the faces of a region, finite or infinite, is closed. -/
theorem isClosed_regionUnion (R : Set TriFace) : IsClosed (regionUnion R) := by
  rw [regionUnion_def, biUnion_eq_iUnion]
  exact (TriFace.locallyFinite_triangle.comp_injective Subtype.val_injective).isClosed_iUnion
    fun f => (TriFace.isCompact_triangle f).isClosed

/-- **A region whose union of faces is preconnected is connected.** If `F(R) ⊆ ℝ²` is
preconnected, then any two vertices of `R` are joined by a path of edges of `R`. -/
theorem IsConnectedRegion.of_isPreconnected_regionUnion {R : Set TriFace}
    (hR : IsPreconnected (regionUnion R)) : IsConnectedRegion R := by
  rw [isConnectedRegion_def]
  intro u₀ hu₀ u hu
  -- the faces of `R` with a vertex reachable from `u₀`, and the others
  set A := {f ∈ R | ∃ w ∈ f.vertices, (regionGraph R).Reachable u₀ w}
  set B := {f ∈ R | ∀ w ∈ f.vertices, ¬ (regionGraph R).Reachable u₀ w}
  have hclosed (S : Set TriFace) : IsClosed (⋃ f ∈ S, f.triangle) := by
    rw [← regionUnion_def]
    exact isClosed_regionUnion S
  have hsub : regionUnion R ⊆ (⋃ f ∈ A, f.triangle) ∪ ⋃ f ∈ B, f.triangle := by
    rw [regionUnion_def]
    refine iUnion₂_subset fun f hf => ?_
    by_cases h : ∃ w ∈ f.vertices, (regionGraph R).Reachable u₀ w
    · exact (subset_biUnion_of_mem (u := fun f => f.triangle) (show f ∈ A from ⟨hf, h⟩)).trans
        subset_union_left
    · simp only [not_exists, not_and] at h
      exact (subset_biUnion_of_mem (u := fun f => f.triangle) (show f ∈ B from ⟨hf, h⟩)).trans
        subset_union_right
  obtain ⟨f₀, hf₀, hu₀f⟩ := mem_regionVertices.1 hu₀
  obtain ⟨f, hf, huf⟩ := mem_regionVertices.1 hu
  by_contra hne
  have hfB : f ∈ B := ⟨hf, fun w hw hw' =>
    hne (hw'.trans (reachable_of_mem_vertices hf hw huf))⟩
  obtain ⟨p, -, hpA, hpB⟩ := isPreconnected_closed_iff.1 hR _ _ (hclosed A) (hclosed B) hsub
    ⟨latticeToReal u₀, mk_mem_regionUnion hu₀,
      mem_biUnion (x := f₀) ⟨hf₀, u₀, hu₀f, .refl _⟩ (TriFace.latticeToReal_mem_triangle hu₀f)⟩
    ⟨latticeToReal u, mk_mem_regionUnion hu,
      mem_biUnion hfB (TriFace.latticeToReal_mem_triangle huf)⟩
  obtain ⟨g, ⟨hgR, w, hw, hwr⟩, hpg⟩ := mem_iUnion₂.1 hpA
  obtain ⟨g', ⟨-, hg'B⟩, hpg'⟩ := mem_iUnion₂.1 hpB
  obtain ⟨w', hw'g, hw'g'⟩ :=
    TriFace.exists_mem_vertices_of_triangle_inter_nonempty ⟨p, hpg, hpg'⟩
  exact hg'B w' hw'g' (hwr.trans (reachable_of_mem_vertices hgR hw hw'g))

end TauCeti
