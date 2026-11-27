/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.LocallyFinite
import TauCeti.Topology.Connected.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The union of the faces of a region

The union `regionUnion R` of the faces of a region is the union of the closed triangles
`TriFace.triangle f ⊆ ℝ²` of its faces, the convex hulls of their three vertices under
`ℤ² ⊆ ℝ²`.

Every triangle is the slab `m ≤ x ≤ m + 1`, `n ≤ y ≤ n + 1`, `k ≤ x − y ≤ k + 1`, where
`(m, n)` is the base vertex of the face and `k`, its `TauCeti.TriFace.diagIndex`, is `m − n` for
a white face and `m − n − 1` for a black one (`TauCeti.TriFace.mem_triangle_iff`); as the
integer data of two faces whose triangles meet differ by at most one in each of `m`, `n`, `k`,
two such faces share a vertex (`TauCeti.TriFace.exists_mem_vertices_of_triangle_inter_nonempty`).
The triangles are compact and form a locally finite family (`TauCeti.TriFace.isCompact_triangle`,
`TauCeti.TriFace.locallyFinite_triangle`), so the union of the faces of every region, finite or
infinite, is closed (`TauCeti.isClosed_regionUnion`).

**Connectedness.** If the union of the faces of `R` is preconnected, then `R` is connected through
its edges (`TauCeti.IsConnectedRegion.of_isPreconnected_regionUnion`): as the triangles are
closed and locally finite, any two faces of `R` are joined by a chain of faces of `R` in which
consecutive triangles meet (`IsPreconnected.transGen_of_iUnion_of_isClosed`), and consecutive
faces of such a chain share a vertex
(`TauCeti.TriFace.exists_mem_vertices_of_triangle_inter_nonempty`). This is the first step of
the passage from topological to combinatorial simple connectivity.
-/

public section

open Set

namespace TauCeti

namespace TriFace

/-- **The triangle of a face is its slab.** A point lies in the triangle of a face with base vertex
`(m, n)` and `diagIndex` `k` if and only if `m ≤ x ≤ m + 1`, `n ≤ y ≤ n + 1` and
`k ≤ x − y ≤ k + 1`. -/
theorem mem_triangle_iff {f : TriFace} {p : ℝ × ℝ} :
    p ∈ f.triangle ↔ (f.v.1 : ℝ) ≤ p.1 ∧ p.1 ≤ f.v.1 + 1 ∧ (f.v.2 : ℝ) ≤ p.2 ∧
      p.2 ≤ f.v.2 + 1 ∧ (f.diagIndex : ℝ) ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ f.diagIndex + 1 := by
  refine ⟨fun hp => ?_, fun h => ?_⟩
  · rw [triangle_def] at hp
    refine convexHull_min (t := {p : ℝ × ℝ | (f.v.1 : ℝ) ≤ p.1 ∧ p.1 ≤ f.v.1 + 1 ∧
      (f.v.2 : ℝ) ≤ p.2 ∧ p.2 ≤ f.v.2 + 1 ∧ (f.diagIndex : ℝ) ≤ p.1 - p.2 ∧
      p.1 - p.2 ≤ f.diagIndex + 1}) ?_ ?_ hp
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
  · -- `p` is an explicit convex combination `∑ wᵢ • zᵢ` of the three vertices
    obtain ⟨w, z, hw, hz, rfl⟩ : ∃ (w : Fin 3 → ℝ) (z : Fin 3 → ℤ × ℤ),
        ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) ∧ (∀ i, z i ∈ f.vertices) ∧
        ∑ i, w i • latticeToReal (z i) = p := by
      obtain ⟨⟨a, b⟩, c⟩ := f
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      cases c <;> simp only [diagIndex_mk_true, diagIndex_mk_false, Int.cast_sub,
        Int.cast_one] at h1 h2 h3 h4 h5 h6
      on_goal 1 => refine ⟨![1 - (p.2 - b), (p.2 - b) - (p.1 - a), p.1 - a],
        ![(a, b), (a, b) + (0, 1), (a, b) + (1, 1)], ?_⟩
      on_goal 2 => refine ⟨![1 - (p.1 - a), (p.1 - a) - (p.2 - b), p.2 - b],
        ![(a, b), (a, b) + (1, 0), (a, b) + (1, 1)], ?_⟩
      all_goals
        refine ⟨⟨fun i => ?_, by simp [Fin.sum_univ_three]⟩, fun i => ?_, ?_⟩
        · fin_cases i <;> simp <;> linarith
        · fin_cases i <;> simp
        · ext <;> simp [Fin.sum_univ_three] <;> ring
    exact (convex_triangle f).sum_mem (fun i _ => hw.1 i) hw.2
      fun i _ => latticeToReal_mem_triangle (hz i)

/-- **Meeting triangles share a vertex.** If the triangles of two faces meet, the faces have a
common vertex. -/
theorem exists_mem_vertices_of_triangle_inter_nonempty {f g : TriFace}
    (h : (f.triangle ∩ g.triangle).Nonempty) : ∃ u, u ∈ f.vertices ∧ u ∈ g.vertices := by
  obtain ⟨p, hpf, hpg⟩ := h
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := mem_triangle_iff.1 hpf
  obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ := mem_triangle_iff.1 hpg
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
  obtain ⟨h1, h2, h3, h4, -, -⟩ := mem_triangle_iff.1 hpf
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
  obtain ⟨f₀, hf₀, hu₀f⟩ := mem_regionVertices.1 hu₀
  obtain ⟨f, hf, huf⟩ := mem_regionVertices.1 hu
  rw [regionUnion_def, biUnion_eq_iUnion] at hR
  -- a chain of faces of `R` from `f₀` to `f` in which consecutive triangles meet
  have hchain := hR.transGen_of_iUnion_of_isClosed
    (TriFace.locallyFinite_triangle.comp_injective Subtype.val_injective)
    (fun g => (TriFace.isCompact_triangle g.val).isClosed) ⟨f₀, hf₀⟩ ⟨f, hf⟩
    ⟨_, TriFace.latticeToReal_mem_triangle hu₀f⟩ ⟨_, TriFace.latticeToReal_mem_triangle huf⟩
  -- along the chain, every vertex of every face is reachable from `u₀`, as consecutive faces
  -- share a vertex
  have step {g g' : R} (hg : ∀ w ∈ g.val.vertices, (regionGraph R).Reachable u₀ w)
      (h : (g.val.triangle ∩ g'.val.triangle).Nonempty) :
      ∀ w ∈ g'.val.vertices, (regionGraph R).Reachable u₀ w := fun w hw => by
    obtain ⟨w', hw'g, hw'g'⟩ := TriFace.exists_mem_vertices_of_triangle_inter_nonempty h
    exact (hg w' hw'g).trans (reachable_of_mem_vertices g'.property hw'g' hw)
  have hf₀' : ∀ w ∈ f₀.vertices, (regionGraph R).Reachable u₀ w :=
    fun w hw => reachable_of_mem_vertices hf₀ hu₀f hw
  generalize hg : (⟨f, hf⟩ : R) = g at hchain
  have key : ∀ w ∈ g.val.vertices, (regionGraph R).Reachable u₀ w := by
    clear hg
    induction hchain with
    | single h => exact step hf₀' h
    | tail _ h ih => exact step ih h
  exact key u (hg ▸ huf)

end TauCeti
