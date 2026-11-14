/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Line
public import TauCeti.GroupTheory.LambdaTree.GromovProduct
public import Mathlib.Data.List.GetD

/-!
# Simplicial trees and `ℤ`-trees

The distance between two vertices of a preconnected Serre graph, the least length of a path
joining them, is a `ℤ`-valued metric on the set of vertices: the *path metric* of the graph. Its
segments are exactly the sets of vertices of the shortest paths, a shortest path being
parametrised by the positions of its vertices. In particular the path metric is geodesic.

In a graph without circuits the reduced paths are the shortest paths, so the set of vertices of a
reduced path is the unique segment between its endpoints, and when the graph is a tree its path
metric makes the set of vertices a `ℤ`-tree (`TauCeti.SerreGraph.IsTree.isTree_pathMetric`).

Conversely, every `ℤ`-metric `d` on `X` defines a Serre graph `d.toSerreGraph` on `X` whose darts
are the ordered pairs of points at distance `1`. When `d` is geodesic, `d.toSerreGraph` is
preconnected and its path metric recovers `d`; when `d` makes `X` a `ℤ`-tree, every reduced path of
`d.toSerreGraph` realises the distance between its endpoints, so `d.toSerreGraph` is a simplicial
tree (`TauCeti.LambdaMetric.IsTree.isTree_toSerreGraph`). Thus `ℤ`-trees are up to bijection the
vertex sets of simplicial trees with their path metric
(`TauCeti.LambdaMetric.isTree_iff_exists_serreGraph`).

The path metric of the line, whose vertices are the integers, is the metric `|a - b|`.

## Main definitions

* `TauCeti.SerreGraph.Preconnected.pathMetric`: the path metric of a preconnected Serre graph.
* `TauCeti.LambdaMetric.toSerreGraph`: the Serre graph on `X` with darts the pairs at distance `1`
  for a `ℤ`-metric `d`, with coordinate equivalences `TauCeti.LambdaMetric.toSerreGraphVertexEquiv`
  and `TauCeti.LambdaMetric.toSerreGraphDartEquiv`.

## Main results

* `TauCeti.SerreGraph.Preconnected.isSegment_pathMetric_iff`: the segments of the path metric are
  the sets of vertices of the shortest paths.
* `TauCeti.SerreGraph.Preconnected.isGeodesic_pathMetric`: the path metric is geodesic.
* `TauCeti.SerreGraph.IsAcyclic.isSegment_setOf_mem_vertices`,
  `TauCeti.SerreGraph.IsAcyclic.isSegment_pathMetric_unique`: in a graph without circuits, the set
  of vertices of a reduced path is the unique segment between its endpoints.
* `TauCeti.SerreGraph.IsTree.isTree_pathMetric`: the path metric of a simplicial tree makes its
  vertex set a `ℤ`-tree.
* `TauCeti.LambdaMetric.IsGeodesic.toSerreGraph_dist`,
  `TauCeti.LambdaMetric.IsGeodesic.comap_pathMetric_toSerreGraph`: for a geodesic `ℤ`-metric `d`,
  the path metric of `d.toSerreGraph` recovers `d`.
* `TauCeti.LambdaMetric.IsTree.isTree_toSerreGraph`,
  `TauCeti.LambdaMetric.isTree_iff_toSerreGraph`,
  `TauCeti.LambdaMetric.isTree_iff_exists_serreGraph`: characterisation of `ℤ`-trees as simplicial
  trees with their path metrics.
* `TauCeti.SerreGraph.pathMetric_line`: the path metric of the line is `|a - b|`.

## References

* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §4.2, Example 10.
* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §2.1, Example 2.1.2.
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

/-! ### Path metrics of acyclic graphs and trees -/

/-- In a graph without circuits, the vertices of a reduced path from `a` to `b` form a segment
from `a` to `b` for the path metric. -/
theorem IsAcyclic.isSegment_setOf_mem_vertices (hΓ : Γ.IsAcyclic) (h : Γ.Preconnected) {a b : Γ.V}
    {p : Γ.Path a b} (hp : Path.IsReduced Γ p) :
    h.pathMetric.IsSegment {v | v ∈ p.vertices} a b :=
  h.isSegment_setOf_mem_vertices (hΓ.dist_eq_length hp).symm

/-- In a preconnected graph without circuits, two vertices are joined by a unique segment for the
path metric. -/
theorem IsAcyclic.isSegment_pathMetric_unique (hΓ : Γ.IsAcyclic) (h : Γ.Preconnected)
    {σ τ : Set Γ.V} {a b : Γ.V} (hσ : h.pathMetric.IsSegment σ a b)
    (hτ : h.pathMetric.IsSegment τ a b) : σ = τ := by
  obtain ⟨p, hp, rfl⟩ := h.isSegment_pathMetric_iff.1 hσ
  obtain ⟨q, hq, rfl⟩ := h.isSegment_pathMetric_iff.1 hτ
  rw [hΓ.eq_of_isReduced (Path.isReduced_of_length_le_dist hp.le)
    (Path.isReduced_of_length_le_dist hq.le)]

/-- In a nonempty preconnected graph without circuits, the path metric makes the vertex set a
`ℤ`-tree. -/
theorem IsAcyclic.isTree_pathMetric [Nonempty Γ.V] (hΓ : Γ.IsAcyclic) (h : Γ.Preconnected) :
    h.pathMetric.IsTree where
  nonempty := ‹_›
  isGeodesic := h.isGeodesic_pathMetric
  exists_isSegment_union {σ τ x y z} hσ hτ hστ := by
    obtain ⟨p, hp, rfl⟩ := h.isSegment_pathMetric_iff.1 hσ
    obtain ⟨q, hq, rfl⟩ := h.isSegment_pathMetric_iff.1 hτ
    have hp' := Path.isReduced_of_length_le_dist hp.le
    have hq' := Path.isReduced_of_length_le_dist hq.le
    -- Since `σ ∩ τ = {y}`, `p` and `q` cannot cancel at `y`, so `p.comp q` is reduced.
    have hpq : Path.IsReduced Γ (p.comp q) := by
      refine (Path.isReduced_comp_iff Γ p q).2 ⟨hp', hq', fun e he f hf hfe => ?_⟩
      have hsrc : Γ.src e ∈ {v | v ∈ p.vertices} ∩ {v | v ∈ q.vertices} := by
        refine ⟨Path.src_mem_vertices_of_mem_darts (List.mem_of_mem_getLast? he), ?_⟩
        have htf := Path.tgt_mem_vertices_of_mem_darts (List.mem_of_mem_head? hf)
        rwa [hfe, tgt_rev] at htf
      have hsy : Γ.src e = y := mem_singleton_iff.1 (hστ ▸ hsrc)
      exact hΓ.src_ne_tgt e (hsy.trans (Path.tgt_eq_of_mem_getLast?_darts Γ p he).symm)
    refine ⟨x, z, ?_⟩
    have hunion : {v | v ∈ p.vertices} ∪ {v | v ∈ q.vertices} = {v | v ∈ (p.comp q).vertices} := by
      ext v
      exact (Quiver.Path.mem_vertices_comp p q).symm
    exact hunion ▸ hΓ.isSegment_setOf_mem_vertices h hpq
  exists_isSegment_inter {σ τ x y z} hσ hτ := by
    classical
    -- Choose `w ∈ σ ∩ τ` at maximal distance from `x` by minimising `Γ.dist x y - Γ.dist x w`.
    have hex : ∃ k, ∃ w ∈ σ ∩ τ, Γ.dist x w + k = Γ.dist x y :=
      ⟨Γ.dist x y, x, ⟨hσ.left_mem, hτ.left_mem⟩, by simp⟩
    obtain ⟨w, hw, hwk⟩ := Nat.find_spec hex
    have hmax (u : Γ.V) (hu : u ∈ σ ∩ τ) : h.pathMetric x u ≤ h.pathMetric x w := by
      have huy : Γ.dist x u + Γ.dist u y = Γ.dist x y := by
        have := hσ.dist_add_dist hu.1
        simp only [h.pathMetric_apply] at this
        exact_mod_cast this
      have hmin := Nat.find_min' hex ⟨u, hu, huy⟩
      rw [h.pathMetric_apply, h.pathMetric_apply]
      omega
    have hρ₁ := hσ.isSegment_sep hσ.left_mem hw.1
    have hρ₂ := hτ.isSegment_sep hτ.left_mem hw.2
    have hρeq := hΓ.isSegment_pathMetric_unique h hρ₁ hρ₂
    rw [h.pathMetric.refl] at hρeq
    refine ⟨x, w, ?_⟩
    suffices h_eq : σ ∩ τ = {u ∈ σ | h.pathMetric x u ∈ uIcc (h.pathMetric x x) (h.pathMetric x w)}
      from h_eq ▸ hρ₁
    ext u
    simp only [mem_inter_iff, mem_sep_iff, h.pathMetric.refl]
    refine ⟨fun hu => ⟨hu.1, mem_uIcc_of_le (h.pathMetric.nonneg x u) (hmax u hu)⟩, fun hu => ?_⟩
    have hu₂ : u ∈ {u ∈ τ | h.pathMetric x u ∈ uIcc 0 (h.pathMetric x w)} := by
      rw [← hρeq]
      exact hu
    exact ⟨hu.1, hu₂.1⟩

/-- The path metric of a simplicial tree makes its set of vertices a `ℤ`-tree. -/
theorem IsTree.isTree_pathMetric (hΓ : Γ.IsTree) {h : Γ.Preconnected} :
    h.pathMetric.IsTree :=
  have : Nonempty Γ.V := (Γ.connected_iff.1 hΓ.connected).1
  hΓ.isAcyclic.isTree_pathMetric h

/-- The path metric of the line is the metric `|a - b|` on the integers. -/
theorem pathMetric_line (h : line.Preconnected) (a b : line.V) :
    h.pathMetric a b = |lineVertexEquiv a - lineVertexEquiv b| := by
  rw [h.pathMetric_apply, line_dist]

end SerreGraph

/-! ### The Serre graph of a `ℤ`-metric space -/

namespace LambdaMetric

open Set

variable {X : Type*}

/-- The Serre graph attached to a `ℤ`-metric `d` on `X`: its vertices are the points of `X`, and
its darts are the ordered pairs `(x, y)` at distance `1`, with reversal swapping the endpoints.
The body is exposed so that the coordinate equivalences `toSerreGraphVertexEquiv` and
`toSerreGraphDartEquiv` compile under the `module` code generator; use those equivalences rather
than unfolding `toSerreGraph`. -/
@[expose] def toSerreGraph (d : LambdaMetric ℤ X) : SerreGraph where
  V := X
  E := { p : X × X // d p.1 p.2 = 1 }
  src e := e.1.1
  rev e := ⟨e.1.swap, by rw [Prod.fst_swap, Prod.snd_swap, d.symm]; exact e.2⟩
  rev_rev e := Subtype.ext (Prod.swap_swap e.1)
  rev_ne e he := by
    have hxy : e.1.2 = e.1.1 := congrArg (fun f : { p : X × X // d p.1 p.2 = 1 } => f.1.1) he
    have h1 := e.2
    rw [hxy, d.refl] at h1
    omega

/-- The vertices of `d.toSerreGraph` are the points of `X`. -/
def toSerreGraphVertexEquiv (d : LambdaMetric ℤ X) : d.toSerreGraph.V ≃ X :=
  Equiv.refl X

/-- The darts of `d.toSerreGraph` are the ordered pairs of points at distance `1`. -/
def toSerreGraphDartEquiv (d : LambdaMetric ℤ X) :
    d.toSerreGraph.E ≃ { p : X × X // d p.1 p.2 = 1 } :=
  Equiv.refl _

variable {d : LambdaMetric ℤ X}

@[simp]
theorem toSerreGraphVertexEquiv_src (e : d.toSerreGraph.E) :
    d.toSerreGraphVertexEquiv (d.toSerreGraph.src e) = (d.toSerreGraphDartEquiv e).1.1 :=
  (rfl)

@[simp]
theorem toSerreGraphVertexEquiv_tgt (e : d.toSerreGraph.E) :
    d.toSerreGraphVertexEquiv (d.toSerreGraph.tgt e) = (d.toSerreGraphDartEquiv e).1.2 :=
  (rfl)

@[simp]
theorem toSerreGraphDartEquiv_rev (e : d.toSerreGraph.E) :
    (d.toSerreGraphDartEquiv (d.toSerreGraph.rev e)).1 =
      (d.toSerreGraphDartEquiv e).1.swap :=
  (rfl)

private theorem toSerreGraph_hom_dist {a b : d.toSerreGraph.V} (e : Quiver.Hom a b) :
    d (d.toSerreGraphVertexEquiv a) (d.toSerreGraphVertexEquiv b) = 1 := by
  rcases e with ⟨⟨⟨_, _⟩, hxy⟩, rfl, rfl⟩
  exact hxy

/-- Every path in `d.toSerreGraph` has length at least the `d`-distance between its endpoints. -/
theorem dist_le_toSerreGraph_length {u v : d.toSerreGraph.V} (p : d.toSerreGraph.Path u v) :
    d (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv v) ≤ p.length := by
  induction p with
  | nil =>
    rw [Quiver.Path.length_nil]
    exact (d.refl _).le
  | @cons b c p e ih =>
    have he := toSerreGraph_hom_dist e
    have htri := d.triangle (d.toSerreGraphVertexEquiv u)
      (d.toSerreGraphVertexEquiv b) (d.toSerreGraphVertexEquiv c)
    rw [Quiver.Path.length_cons]
    push_cast
    omega

private theorem exists_toSerreGraph_path_of_isometricOn {f : ℤ → X} {n : ℕ}
    (hf : d.IsometricOn f (Icc 0 n)) (k : ℕ) (hk : k ≤ n) :
    ∃ p : d.toSerreGraph.Path (d.toSerreGraphVertexEquiv.symm (f 0))
        (d.toSerreGraphVertexEquiv.symm (f k)),
      p.length = k := by
  induction k with
  | zero => exact ⟨.nil, rfl⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih (by omega)
    have hstep : d (f k) (f (k + 1 : ℕ)) = 1 := by
      have := hf.dist_eq (a := k) (b := (k + 1 : ℕ)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      simpa using this
    let e : Quiver.Hom (V := d.toSerreGraph.V) (d.toSerreGraphVertexEquiv.symm (f k))
        (d.toSerreGraphVertexEquiv.symm (f (k + 1 : ℕ))) :=
      ⟨⟨(f k, f (k + 1 : ℕ)), hstep⟩, rfl, rfl⟩
    exact ⟨p.cons e, by rw [Quiver.Path.length_cons, hp]⟩

/-- For a geodesic `ℤ`-metric `d`, any two vertices of `d.toSerreGraph` are joined by a path whose
length is their `d`-distance. -/
theorem IsGeodesic.exists_toSerreGraph_path (hgeo : d.IsGeodesic) (u v : d.toSerreGraph.V) :
    ∃ p : d.toSerreGraph.Path u v,
      (p.length : ℤ) = d (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv v) := by
  obtain ⟨σ, hσ⟩ := d.isGeodesic_iff.1 hgeo
    (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv v)
  obtain ⟨f, hf0, hfD, hf, -⟩ := d.isSegment_iff.1 hσ
  have hnn := d.nonneg (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv v)
  lift d (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv v) to ℕ using hnn with n hn
  obtain ⟨p, hp⟩ := exists_toSerreGraph_path_of_isometricOn (d := d) hf n le_rfl
  have hu : d.toSerreGraphVertexEquiv.symm (f 0) = u := by
    rw [hf0, Equiv.symm_apply_apply]
  have hv : d.toSerreGraphVertexEquiv.symm (f n) = v := by
    rw [hfD, Equiv.symm_apply_apply]
  have hlen : (p.cast hu hv).length = p.length := by
    cases hu
    cases hv
    rfl
  exact ⟨p.cast hu hv, mod_cast hlen.trans hp⟩

/-- For a geodesic `ℤ`-metric `d`, the graph `d.toSerreGraph` is preconnected. -/
theorem IsGeodesic.preconnected_toSerreGraph (hgeo : d.IsGeodesic) :
    d.toSerreGraph.Preconnected :=
  (d.toSerreGraph.preconnected_iff).2 fun u v => ⟨(hgeo.exists_toSerreGraph_path u v).choose⟩

/-- For a geodesic `ℤ`-metric `d`, the graph distance in `d.toSerreGraph` agrees with `d` along
`d.toSerreGraphVertexEquiv`. -/
@[simp]
theorem IsGeodesic.toSerreGraph_dist (hgeo : d.IsGeodesic) (u v : d.toSerreGraph.V) :
    (d.toSerreGraph.dist u v : ℤ) =
      d (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv v) := by
  obtain ⟨p, hp⟩ := hgeo.exists_toSerreGraph_path u v
  have hle : (d.toSerreGraph.dist u v : ℤ) ≤ p.length := mod_cast SerreGraph.dist_le_length p
  obtain ⟨q, hq⟩ := SerreGraph.exists_length_eq_dist ⟨p⟩
  have hge := dist_le_toSerreGraph_length q
  omega

/-- For a geodesic `ℤ`-metric `d`, pulling back the path metric of `d.toSerreGraph` along
`d.toSerreGraphVertexEquiv.symm` recovers `d`. -/
@[simp]
theorem IsGeodesic.comap_pathMetric_toSerreGraph (hgeo : d.IsGeodesic) :
    hgeo.preconnected_toSerreGraph.pathMetric.comap d.toSerreGraphVertexEquiv.symm
      d.toSerreGraphVertexEquiv.symm.injective = d := by
  ext x y
  simp [hgeo.toSerreGraph_dist]

/-- In a `ℤ`-tree, every reduced path of `d.toSerreGraph` has length equal to the distance between
its endpoints. -/
theorem IsTree.dist_eq_toSerreGraph_length (hd : d.IsTree) {u v : d.toSerreGraph.V}
    {p : d.toSerreGraph.Path u v} (hp : SerreGraph.Path.IsReduced d.toSerreGraph p) :
    d (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv v) = p.length := by
  suffices key : ∀ (n : ℕ) {w : d.toSerreGraph.V} (q : d.toSerreGraph.Path u w),
      q.length = n → SerreGraph.Path.IsReduced d.toSerreGraph q →
        d (d.toSerreGraphVertexEquiv u) (d.toSerreGraphVertexEquiv w) = n from
    key p.length p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro w r hrlen hr
    cases r with
    | nil =>
      subst hrlen
      exact_mod_cast d.refl _
    | @cons b w q f =>
      cases q with
      | nil =>
        rw [Quiver.Path.length_cons, Quiver.Path.length_nil] at hrlen
        subst hrlen
        simpa using toSerreGraph_hom_dist f
      | @cons a b q e =>
        rw [Quiver.Path.length_cons, Quiver.Path.length_cons] at hrlen
        subst hrlen
        obtain ⟨hqe, hne⟩ := (SerreGraph.Path.isReduced_cons_cons d.toSerreGraph q e f).1 hr
        set φ := d.toSerreGraphVertexEquiv
        have dua : d (φ u) (φ a) = q.length :=
          ih q.length (by omega) q rfl (hqe.of_cons d.toSerreGraph)
        have dub : d (φ u) (φ b) = (q.length : ℤ) + 1 := by
          simpa using ih (q.length + 1) (by omega) (q.cons e) (by rw [Quiver.Path.length_cons]) hqe
        have dab : d (φ a) (φ b) = 1 := toSerreGraph_hom_dist e
        have dbw : d (φ b) (φ w) = 1 := toSerreGraph_hom_dist f
        -- Non-backtracking `f.1 ≠ rev e.1` means `a ≠ w`, so `1 ≤ d a w ≤ 2`; parity forces
        -- `d a w = 2`, and four-point `0`-hyperbolicity gives `d u w = q.length + 2`.
        have haw_ne : φ a ≠ φ w := by
          intro haw
          obtain rfl := φ.injective haw
          refine hne (Subtype.ext (Prod.ext ?_ ?_))
          · exact f.2.1.trans e.2.2.symm
          · exact f.2.2.trans e.2.1.symm
        have haw_pos : 0 < d (φ a) (φ w) := d.pos_iff.2 haw_ne
        have haw_le : d (φ a) (φ w) ≤ 2 := by
          have := d.triangle (φ a) (φ b) (φ w)
          omega
        obtain ⟨k, hk⟩ := hd.even_dist_add_dist_sub_dist (φ b) (φ a) (φ w)
        rw [d.symm (φ b) (φ a), dab, dbw] at hk
        have : d (φ a) (φ w) = 2 := by omega
        have h₄ := hd.four_point (φ a) (φ w) (φ u) (φ b)
        rw [d.symm (φ a) (φ u), d.symm (φ w) (φ b), d.symm (φ w) (φ u)] at h₄
        have htri := d.triangle (φ u) (φ b) (φ w)
        push_cast
        grind

/-- For a `ℤ`-tree `(X, d)`, the graph `d.toSerreGraph` is a simplicial tree. -/
theorem IsTree.isTree_toSerreGraph (hd : d.IsTree) : d.toSerreGraph.IsTree := by
  refine d.toSerreGraph.isTree_iff.2
    ⟨d.toSerreGraph.connected_iff.2 ⟨⟨d.toSerreGraphVertexEquiv.symm hd.nonempty.some⟩,
        hd.isGeodesic.preconnected_toSerreGraph⟩,
      (d.toSerreGraph.isAcyclic_iff).2 fun u p hp => Quiver.Path.eq_nil_of_length_zero p ?_⟩
  have hlen := hd.dist_eq_toSerreGraph_length hp
  have h0 := d.refl (d.toSerreGraphVertexEquiv u)
  omega

/-- A `ℤ`-metric `d` makes `X` a `ℤ`-tree if and only if `d` is geodesic and `d.toSerreGraph` is a
simplicial tree. -/
theorem isTree_iff_toSerreGraph : d.IsTree ↔ d.IsGeodesic ∧ d.toSerreGraph.IsTree := by
  refine ⟨fun hd => ⟨hd.isGeodesic, hd.isTree_toSerreGraph⟩, fun ⟨hgeo, hΓ⟩ => ?_⟩
  rw [← hgeo.comap_pathMetric_toSerreGraph]
  have hV : Nonempty d.toSerreGraph.V := (d.toSerreGraph.connected_iff.1 hΓ.connected).1
  have hX : Nonempty X := ⟨d.toSerreGraphVertexEquiv hV.some⟩
  exact hΓ.isTree_pathMetric.isTree_comap_iff.2
    ⟨hX, fun x y => by simp [d.toSerreGraphVertexEquiv.symm.range_eq_univ]⟩

/-- A `ℤ`-metric `d` on `X` makes `X` a `ℤ`-tree if and only if `(X, d)` is isometric via a
bijection to the vertex set of a simplicial tree equipped with its path metric. -/
theorem isTree_iff_exists_serreGraph {X : Type u} {d : LambdaMetric ℤ X} :
    d.IsTree ↔ ∃ (Γ : SerreGraph.{u, u}) (hΓ : Γ.IsTree) (e : X ≃ Γ.V),
      d = (Γ.connected_iff.1 hΓ.connected).2.pathMetric.comap e e.injective := by
  refine ⟨fun hd => ⟨d.toSerreGraph, hd.isTree_toSerreGraph, d.toSerreGraphVertexEquiv.symm,
    hd.isGeodesic.comap_pathMetric_toSerreGraph.symm⟩, ?_⟩
  rintro ⟨Γ, hΓ, e, rfl⟩
  have hV : Nonempty Γ.V := (Γ.connected_iff.1 hΓ.connected).1
  have hX : Nonempty X := ⟨e.symm hV.some⟩
  exact hΓ.isTree_pathMetric.isTree_comap_iff.2 ⟨hX, fun x y => by simp [e.range_eq_univ]⟩

end LambdaMetric

end TauCeti
