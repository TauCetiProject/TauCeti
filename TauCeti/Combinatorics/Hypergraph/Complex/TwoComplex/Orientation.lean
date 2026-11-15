/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Link
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Relabel
public import Mathlib.Data.Fintype.Prod
import TauCeti.Order.Hom.PowersetCard

/-!
# Oriented enumerations, order independence, and star double counts on two-complexes

Given a linear order on the vertex type `V`, each edge of a `TwoComplex V` is listed once as an
increasing pair `u < v` in `TwoComplex.orderedEdges`, and each filled triangle is listed once as an
increasing triple `u < v < z` in `TwoComplex.orderedTriangles`. This matches the increasing-pair and
increasing-triple sums used to evaluate group-valued 1-cochains, gauge costs, and triangle
holonomies while `TwoComplex` itself remains unoriented.

When an edge weight `w : V → V → A` is symmetric on the edges of `X` (`w u v = w v u`), its value
depends only on the underlying two-element edge. Likewise, when a triangle weight
`w : V → V → V → A` is invariant on the triangles of `X` under cyclic rotation (`w v z u = w u v z`)
and swapping the first two vertices (`w v u z = w u v z`), all six orderings of a triangle's
vertices agree. For group-valued 1-cochains under a conjugation-invariant norm, edge gauge terms
satisfy the symmetry condition by inversion invariance, and triangle holonomy norms satisfy cyclic
rotation by conjugation invariance and swap invariance by reversing and inverting the loop.

From these two symmetry principles we deduce:

* `TwoComplex.sum_orderedEdges_congr_order` and `TwoComplex.sum_orderedTriangles_congr_order`:
  oriented edge and triangle sums are unchanged by replacing the `LinearOrder` on `V`;
* `TwoComplex.sum_orderedEdges_relabel` and `TwoComplex.sum_orderedTriangles_relabel` (with
  specializations `TwoComplex.sum_orderedEdges_complete_equiv` and
  `TwoComplex.sum_orderedTriangles_complete_equiv`): oriented edge and triangle sums are invariant
  under relabelling the vertices along any bijection `V ≃ W`, whether or not it preserves the order;
* `TwoComplex.sum_orderedEdges_link`, `TwoComplex.sum_vertex_orderedEdges`, and
  `TwoComplex.sum_vertex_orderedEdges_complete`: the oriented vertex-link identity and the
  complete-complex star double count, equating the sum over star vertices `x` and non-incident
  oriented edges `u < v` of `w x u v` with three times the oriented triangle sum of `w`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles I: equivalence*,
  arXiv:2310.17474v2, §5.1, and *II: examples, applications and open problems*, arXiv:2311.06706v3,
  Proposition 3.2.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, doi:10.5281/zenodo.23245792, Proposition 1.
-/

public section

open Finset

namespace TauCeti.TwoComplex

variable {V W A : Type*}

/-! ### Oriented edges and triangles in a linear order -/

section OrderedFaces

variable [LinearOrder V]

/-- Embed each edge of `X` as its unique increasing pair `u < v`. -/
private noncomputable def edgeOrderEmb (X : TwoComplex V) : X.edges ↪ V × V where
  toFun e := (Set.powersetCard.ofLtPair.symm ⟨e.1, X.edge_card e.1 e.2⟩).1
  inj' e₁ e₂ h := by
    have hsub := Set.powersetCard.ofLtPair.symm.injective (Subtype.ext h)
    exact Subtype.ext (congrArg (Subtype.val : Set.powersetCard V 2 → Finset V) hsub)

@[simp]
private theorem edgeOrderEmb_apply (X : TwoComplex V) (e : X.edges) :
    edgeOrderEmb X e = (Set.powersetCard.ofLtPair.symm ⟨e.1, X.edge_card e.1 e.2⟩).1 :=
  rfl

private theorem edgeOrderEmb_of_lt (X : TwoComplex V) {u v : V} (hlt : u < v)
    (he : ({u, v} : Finset V) ∈ X.edges) :
    edgeOrderEmb X ⟨{u, v}, he⟩ = (u, v) := by
  have hq : (⟨{u, v}, X.edge_card _ he⟩ : Set.powersetCard V 2) =
      Set.powersetCard.ofLtPair ⟨(u, v), hlt⟩ :=
    Subtype.ext (Set.powersetCard.val_ofLtPair ⟨(u, v), hlt⟩).symm
  rw [edgeOrderEmb_apply, hq, Equiv.symm_apply_apply]

/-- The edges of `X`, each oriented as its unique increasing pair `(u, v)` with `u < v`. -/
noncomputable def orderedEdges (X : TwoComplex V) : Finset (V × V) :=
  X.edges.attach.map (edgeOrderEmb X)

/-- A pair `(u, v)` is an oriented edge of `X` precisely when `u < v` and `{u, v}` is an edge. -/
@[simp]
theorem mem_orderedEdges (X : TwoComplex V) (p : V × V) :
    p ∈ X.orderedEdges ↔ p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges := by
  simp only [orderedEdges, mem_map, mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨e, he, rfl⟩
    let s : Set.powersetCard V 2 := ⟨e, X.edge_card e he⟩
    have hs : ({(Set.powersetCard.ofLtPair.symm s).1.1,
        (Set.powersetCard.ofLtPair.symm s).1.2} : Finset V) = e :=
      Set.powersetCard.pair_ofLtPair_symm s
    exact ⟨(Set.powersetCard.ofLtPair.symm s).2, by simpa [edgeOrderEmb_apply, hs] using he⟩
  · exact fun ⟨hlt, he⟩ => ⟨{p.1, p.2}, he, edgeOrderEmb_of_lt X hlt he⟩

/-- The first vertex of an oriented edge strictly precedes the second. -/
theorem fst_lt_snd_of_mem_orderedEdges {X : TwoComplex V} {p : V × V} (hp : p ∈ X.orderedEdges) :
    p.1 < p.2 :=
  ((X.mem_orderedEdges p).mp hp).1

/-- The two vertices of an oriented edge are distinct. -/
theorem fst_ne_snd_of_mem_orderedEdges {X : TwoComplex V} {p : V × V} (hp : p ∈ X.orderedEdges) :
    p.1 ≠ p.2 :=
  (fst_lt_snd_of_mem_orderedEdges hp).ne

/-- Forgetting orientation carries an oriented edge to an edge of `X`. -/
theorem pair_mem_edges_of_mem_orderedEdges {X : TwoComplex V} {p : V × V}
    (hp : p ∈ X.orderedEdges) : ({p.1, p.2} : Finset V) ∈ X.edges :=
  ((X.mem_orderedEdges p).mp hp).2

/-- Over a finite vertex type, `orderedEdges` is the filter of increasing pairs spanning an edge. -/
theorem orderedEdges_eq_filter [Fintype V] (X : TwoComplex V) :
    X.orderedEdges =
      univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges) := by
  ext p
  simp

/-- Oriented edges correspond bijectively to unoriented edges by `(u, v) ↦ {u, v}`. -/
noncomputable def orderedEdgesEquiv (X : TwoComplex V) : X.orderedEdges ≃ X.edges where
  toFun p := ⟨{p.1.1, p.1.2}, pair_mem_edges_of_mem_orderedEdges p.2⟩
  invFun e := ⟨edgeOrderEmb X e, mem_map_of_mem _ (mem_attach _ e)⟩
  left_inv p := Subtype.ext (edgeOrderEmb_of_lt X
    (fst_lt_snd_of_mem_orderedEdges p.2) (pair_mem_edges_of_mem_orderedEdges p.2))
  right_inv e := by
    apply Subtype.ext
    exact Set.powersetCard.pair_ofLtPair_symm ⟨e.1, X.edge_card e.1 e.2⟩

/-- The underlying finset of `orderedEdgesEquiv p` is the pair `{p.1.1, p.1.2}`. -/
@[simp]
theorem val_orderedEdgesEquiv (X : TwoComplex V) (p : X.orderedEdges) :
    (X.orderedEdgesEquiv p : Finset V) = {p.1.1, p.1.2} := (rfl)

/-- Orienting an edge `e` produces a pair whose underlying finset is `e`. -/
@[simp]
theorem pair_orderedEdgesEquiv_symm (X : TwoComplex V) (e : X.edges) :
    ({((X.orderedEdgesEquiv.symm e) : V × V).1,
      ((X.orderedEdgesEquiv.symm e) : V × V).2} : Finset V) = e.1 :=
  congrArg Subtype.val (X.orderedEdgesEquiv.apply_symm_apply e)

/-- Orienting edges preserves their count. -/
@[simp]
theorem card_orderedEdges (X : TwoComplex V) : X.orderedEdges.card = X.edges.card := by
  simp [orderedEdges]

/-- In the complete complex, `(u, v)` is an oriented edge precisely when `u < v`. -/
@[simp 1100]
theorem mem_orderedEdges_complete [Fintype V] (p : V × V) :
    p ∈ (complete V).orderedEdges ↔ p.1 < p.2 := by
  rw [mem_orderedEdges, mem_edges_complete, and_iff_left_iff_imp]
  exact fun h => card_pair h.ne

/-- The oriented edges of the complete complex are all strictly increasing pairs. -/
theorem orderedEdges_complete [Fintype V] :
    (complete V).orderedEdges = univ.filter (fun p : V × V => p.1 < p.2) := by
  ext p
  simp

/-- Embed each filled triangle of `X` as its unique increasing triple `u < v < z`. -/
private noncomputable def triangleOrderEmb (X : TwoComplex V) : X.triangles ↪ V × V × V where
  toFun t := (Set.powersetCard.ofLtTriple.symm ⟨t.1, X.triangle_card t.1 t.2⟩).1
  inj' t₁ t₂ h := by
    have hsub := Set.powersetCard.ofLtTriple.symm.injective (Subtype.ext h)
    exact Subtype.ext (congrArg (Subtype.val : Set.powersetCard V 3 → Finset V) hsub)

@[simp]
private theorem triangleOrderEmb_apply (X : TwoComplex V) (t : X.triangles) :
    triangleOrderEmb X t =
      (Set.powersetCard.ofLtTriple.symm ⟨t.1, X.triangle_card t.1 t.2⟩).1 :=
  rfl

private theorem triangleOrderEmb_of_lt (X : TwoComplex V) {u v z : V} (hlt₁ : u < v) (hlt₂ : v < z)
    (ht : ({u, v, z} : Finset V) ∈ X.triangles) :
    triangleOrderEmb X ⟨{u, v, z}, ht⟩ = (u, v, z) := by
  have hq : (⟨{u, v, z}, X.triangle_card _ ht⟩ : Set.powersetCard V 3) =
      Set.powersetCard.ofLtTriple ⟨(u, v, z), hlt₁, hlt₂⟩ :=
    Subtype.ext (Set.powersetCard.val_ofLtTriple ⟨(u, v, z), hlt₁, hlt₂⟩).symm
  rw [triangleOrderEmb_apply, hq, Equiv.symm_apply_apply]

/-- The filled triangles of `X`, each oriented as its unique increasing triple `(u, v, z)` with
`u < v < z`. -/
noncomputable def orderedTriangles (X : TwoComplex V) : Finset (V × V × V) :=
  X.triangles.attach.map (triangleOrderEmb X)

/-- A triple `(u, v, z)` is an oriented triangle of `X` precisely when `u < v < z` and `{u, v, z}`
is a filled triangle. -/
@[simp]
theorem mem_orderedTriangles (X : TwoComplex V) (t : V × V × V) :
    t ∈ X.orderedTriangles ↔
      t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ ({t.1, t.2.1, t.2.2} : Finset V) ∈ X.triangles := by
  simp only [orderedTriangles, mem_map, mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    let q : Set.powersetCard V 3 := ⟨s, X.triangle_card s hs⟩
    have hq : ({(Set.powersetCard.ofLtTriple.symm q).1.1,
        (Set.powersetCard.ofLtTriple.symm q).1.2.1,
        (Set.powersetCard.ofLtTriple.symm q).1.2.2} : Finset V) = s :=
      Set.powersetCard.triple_ofLtTriple_symm q
    exact ⟨(Set.powersetCard.ofLtTriple.symm q).2.1, (Set.powersetCard.ofLtTriple.symm q).2.2,
      by simpa [triangleOrderEmb_apply, hq] using hs⟩
  · exact fun ⟨hlt₁, hlt₂, ht⟩ => ⟨{t.1, t.2.1, t.2.2}, ht, triangleOrderEmb_of_lt X hlt₁ hlt₂ ht⟩

/-- In an oriented triangle, the first vertex strictly precedes the second. -/
theorem fst_lt_snd_fst_of_mem_orderedTriangles {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : t.1 < t.2.1 :=
  ((X.mem_orderedTriangles t).mp ht).1

/-- In an oriented triangle, the second vertex strictly precedes the third. -/
theorem snd_fst_lt_snd_snd_of_mem_orderedTriangles {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : t.2.1 < t.2.2 :=
  ((X.mem_orderedTriangles t).mp ht).2.1

/-- In an oriented triangle, the first vertex strictly precedes the third. -/
theorem fst_lt_snd_snd_of_mem_orderedTriangles {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : t.1 < t.2.2 :=
  (fst_lt_snd_fst_of_mem_orderedTriangles ht).trans (snd_fst_lt_snd_snd_of_mem_orderedTriangles ht)

/-- Forgetting orientation carries an oriented triangle to a filled triangle of `X`. -/
theorem triple_mem_triangles_of_mem_orderedTriangles {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : ({t.1, t.2.1, t.2.2} : Finset V) ∈ X.triangles :=
  ((X.mem_orderedTriangles t).mp ht).2.2

/-- The first two vertices of an oriented triangle form an oriented edge. -/
theorem mk_fst_snd_fst_mem_orderedEdges {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : (t.1, t.2.1) ∈ X.orderedEdges :=
  (X.mem_orderedEdges _).mpr ⟨fst_lt_snd_fst_of_mem_orderedTriangles ht,
    pair_mem_edges_of_triple_mem_triangles (triple_mem_triangles_of_mem_orderedTriangles ht)⟩

/-- The last two vertices of an oriented triangle form an oriented edge. -/
theorem snd_mem_orderedEdges {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : (t.2.1, t.2.2) ∈ X.orderedEdges := by
  refine (X.mem_orderedEdges _).mpr ⟨snd_fst_lt_snd_snd_of_mem_orderedTriangles ht,
    pair_mem_edges_of_triple_mem_triangles (z := t.1) ?_⟩
  have hmem := triple_mem_triangles_of_mem_orderedTriangles ht
  rwa [pair_comm t.2.2 t.1, insert_comm t.2.1 t.1]

/-- The first and third vertices of an oriented triangle form an oriented edge. -/
theorem mk_fst_snd_snd_mem_orderedEdges {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : (t.1, t.2.2) ∈ X.orderedEdges := by
  refine (X.mem_orderedEdges _).mpr ⟨fst_lt_snd_snd_of_mem_orderedTriangles ht,
    pair_mem_edges_of_triple_mem_triangles (z := t.2.1) ?_⟩
  have hmem := triple_mem_triangles_of_mem_orderedTriangles ht
  rwa [pair_comm t.2.2 t.2.1]

/-- Over a finite vertex type, `orderedTriangles` is the filter of increasing triples spanning a
filled triangle. -/
theorem orderedTriangles_eq_filter [Fintype V] (X : TwoComplex V) :
    X.orderedTriangles =
      univ.filter (fun p : V × V × V =>
        p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles) := by
  ext t
  simp

/-- Oriented triangles correspond bijectively to unoriented triangles by
`(u, v, z) ↦ {u, v, z}`. -/
noncomputable def orderedTrianglesEquiv (X : TwoComplex V) :
    X.orderedTriangles ≃ X.triangles where
  toFun t := ⟨{t.1.1, t.1.2.1, t.1.2.2}, triple_mem_triangles_of_mem_orderedTriangles t.2⟩
  invFun s := ⟨triangleOrderEmb X s, mem_map_of_mem _ (mem_attach _ s)⟩
  left_inv t := Subtype.ext (triangleOrderEmb_of_lt X
    (fst_lt_snd_fst_of_mem_orderedTriangles t.2) (snd_fst_lt_snd_snd_of_mem_orderedTriangles t.2)
    (triple_mem_triangles_of_mem_orderedTriangles t.2))
  right_inv s := by
    apply Subtype.ext
    exact Set.powersetCard.triple_ofLtTriple_symm ⟨s.1, X.triangle_card s.1 s.2⟩

/-- The underlying finset of `orderedTrianglesEquiv t` is the triple `{t.1.1, t.1.2.1, t.1.2.2}`. -/
@[simp]
theorem val_orderedTrianglesEquiv (X : TwoComplex V) (t : X.orderedTriangles) :
    (X.orderedTrianglesEquiv t : Finset V) = {t.1.1, t.1.2.1, t.1.2.2} := (rfl)

/-- Orienting a filled triangle `s` produces a triple whose underlying finset is `s`. -/
@[simp]
theorem triple_orderedTrianglesEquiv_symm (X : TwoComplex V) (s : X.triangles) :
    ({((X.orderedTrianglesEquiv.symm s) : V × V × V).1,
      ((X.orderedTrianglesEquiv.symm s) : V × V × V).2.1,
      ((X.orderedTrianglesEquiv.symm s) : V × V × V).2.2} : Finset V) = s.1 :=
  congrArg Subtype.val (X.orderedTrianglesEquiv.apply_symm_apply s)

/-- Orienting triangles preserves their count. -/
@[simp]
theorem card_orderedTriangles (X : TwoComplex V) :
    X.orderedTriangles.card = X.triangles.card := by
  simp [orderedTriangles]

/-- In the complete complex, `(u, v, z)` is an oriented triangle precisely when `u < v < z`. -/
@[simp 1100]
theorem mem_orderedTriangles_complete [Fintype V] (t : V × V × V) :
    t ∈ (complete V).orderedTriangles ↔ t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
  rw [mem_orderedTriangles, mem_triangles_complete, card_triple_eq_three_iff, ← and_assoc,
    and_iff_left_iff_imp]
  exact fun ⟨h₁, h₂⟩ => ⟨h₁.ne, (h₁.trans h₂).ne, h₂.ne⟩

/-- The oriented triangles of the complete complex are all strictly increasing triples. -/
theorem orderedTriangles_complete [Fintype V] :
    (complete V).orderedTriangles =
      univ.filter (fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2) := by
  ext t
  simp

end OrderedFaces

/-! ### Reindexing between oriented and unoriented sums -/

section Sums

variable [LinearOrder V] [AddCommMonoid A]

/-- Summing a function of unoriented edges over `orderedEdges` agrees with summing over `edges`. -/
theorem sum_orderedEdges_pair (X : TwoComplex V) (f : Finset V → A) :
    ∑ p ∈ X.orderedEdges, f {p.1, p.2} = ∑ e ∈ X.edges, f e := by
  rw [← sum_attach (s := X.orderedEdges), ← sum_attach (s := X.edges)]
  exact Fintype.sum_equiv X.orderedEdgesEquiv _ _ fun _ => rfl

/-- An unoriented edge sum agrees with an oriented edge sum whenever the two integrands agree on
increasing edge pairs. -/
theorem sum_edges_eq_sum_orderedEdges (X : TwoComplex V) (f : Finset V → A) (w : V → V → A)
    (hw : ∀ ⦃u v⦄, u < v → ({u, v} : Finset V) ∈ X.edges → f {u, v} = w u v) :
    ∑ e ∈ X.edges, f e = ∑ p ∈ X.orderedEdges, w p.1 p.2 := by
  rw [← X.sum_orderedEdges_pair f]
  exact sum_congr rfl fun p hp =>
    hw (fst_lt_snd_of_mem_orderedEdges hp) (pair_mem_edges_of_mem_orderedEdges hp)

/-- Summing a function of unoriented triangles over `orderedTriangles` agrees with summing over
`triangles`. -/
theorem sum_orderedTriangles_triple (X : TwoComplex V) (f : Finset V → A) :
    ∑ t ∈ X.orderedTriangles, f {t.1, t.2.1, t.2.2} = ∑ s ∈ X.triangles, f s := by
  rw [← sum_attach (s := X.orderedTriangles), ← sum_attach (s := X.triangles)]
  exact Fintype.sum_equiv X.orderedTrianglesEquiv _ _ fun _ => rfl

/-- An unoriented triangle sum agrees with an oriented triangle sum whenever the two integrands
agree on increasing triangle triples. -/
theorem sum_triangles_eq_sum_orderedTriangles (X : TwoComplex V) (f : Finset V → A)
    (w : V → V → V → A)
    (hw : ∀ ⦃u v z⦄, u < v → v < z → ({u, v, z} : Finset V) ∈ X.triangles →
      f {u, v, z} = w u v z) :
    ∑ s ∈ X.triangles, f s = ∑ t ∈ X.orderedTriangles, w t.1 t.2.1 t.2.2 := by
  rw [← X.sum_orderedTriangles_triple f]
  exact sum_congr rfl fun t ht =>
    hw (fst_lt_snd_fst_of_mem_orderedTriangles ht) (snd_fst_lt_snd_snd_of_mem_orderedTriangles ht)
      (triple_mem_triangles_of_mem_orderedTriangles ht)

/-- Extend a binary weight `w : V → V → A` to `Finset V` by evaluating `w` on the increasing
presentation of each edge of `X`, and `0` outside `X.edges`. -/
private noncomputable def edgeLift (X : TwoComplex V) (w : V → V → A) (e : Finset V) : A :=
  if he : e ∈ X.edges then
    let q : V × V := (X.orderedEdgesEquiv.symm ⟨e, he⟩).1
    w q.1 q.2
  else 0

private theorem edgeLift_pair (X : TwoComplex V) (w : V → V → A)
    (hw : ∀ ⦃u v⦄, ({u, v} : Finset V) ∈ X.edges → w u v = w v u) {u v : V}
    (he : ({u, v} : Finset V) ∈ X.edges) :
    edgeLift X w {u, v} = w u v := by
  simp only [edgeLift, he, ↓reduceDIte]
  set q : V × V := (X.orderedEdgesEquiv.symm ⟨{u, v}, he⟩).1
  have hqp : ({q.1, q.2} : Finset V) = {u, v} :=
    X.pair_orderedEdgesEquiv_symm ⟨{u, v}, he⟩
  exact X.apply_eq_of_pair_eq w hw (hqp ▸ he) hqp

private theorem sum_edges_edgeLift (X : TwoComplex V) (w : V → V → A)
    (hw : ∀ ⦃u v⦄, ({u, v} : Finset V) ∈ X.edges → w u v = w v u) :
    ∑ e ∈ X.edges, edgeLift X w e = ∑ p ∈ X.orderedEdges, w p.1 p.2 :=
  X.sum_edges_eq_sum_orderedEdges _ w fun _ _ _ he => edgeLift_pair X w hw he

/-- Extend a ternary weight `w : V → V → V → A` to `Finset V` by evaluating `w` on the increasing
presentation of each filled triangle of `X`, and `0` outside `X.triangles`. -/
private noncomputable def triangleLift (X : TwoComplex V) (w : V → V → V → A)
    (s : Finset V) : A :=
  if hs : s ∈ X.triangles then
    let q : V × V × V := (X.orderedTrianglesEquiv.symm ⟨s, hs⟩).1
    w q.1 q.2.1 q.2.2
  else 0

private theorem triangleLift_triple (X : TwoComplex V) (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z) {u v z : V}
    (ht : ({u, v, z} : Finset V) ∈ X.triangles) :
    triangleLift X w {u, v, z} = w u v z := by
  simp only [triangleLift, ht, ↓reduceDIte]
  set q : V × V × V := (X.orderedTrianglesEquiv.symm ⟨{u, v, z}, ht⟩).1
  have hqp : ({q.1, q.2.1, q.2.2} : Finset V) = {u, v, z} :=
    X.triple_orderedTrianglesEquiv_symm ⟨{u, v, z}, ht⟩
  exact X.apply_eq_of_triple_eq w hrot hswap (hqp ▸ ht) hqp

private theorem sum_triangles_triangleLift (X : TwoComplex V) (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z) :
    ∑ s ∈ X.triangles, triangleLift X w s = ∑ t ∈ X.orderedTriangles, w t.1 t.2.1 t.2.2 :=
  X.sum_triangles_eq_sum_orderedTriangles _ w fun _ _ _ _ _ ht =>
    triangleLift_triple X w hrot hswap ht

end Sums

/-! ### Independence of the vertex linear order -/

section OrderIndependence

/-- An oriented edge sum whose summand is symmetric on the edges of `X` does not depend on the
linear order used to orient the edges. -/
theorem sum_orderedEdges_congr_order [DecidableEq V] (l₁ l₂ : LinearOrder V) [AddCommMonoid A]
    (X : TwoComplex V) (w : V → V → A)
    (hw : ∀ ⦃u v⦄, ({u, v} : Finset V) ∈ X.edges → w u v = w v u) :
    ∑ p ∈ @orderedEdges V l₁ X, w p.1 p.2 = ∑ p ∈ @orderedEdges V l₂ X, w p.1 p.2 := by
  -- Identify `DecidableEq V` instances via `Subsingleton.elim` so pair finsets agree.
  obtain rfl : ‹DecidableEq V› = l₁.toDecidableEq := Subsingleton.elim _ _
  rw [← @sum_edges_edgeLift V A l₁ _ X w hw]
  refine @sum_edges_eq_sum_orderedEdges V A l₂ _ X (@edgeLift V A l₁ _ X w) w fun u v _ he => ?_
  rw [Subsingleton.elim l₂.toDecidableEq l₁.toDecidableEq] at he ⊢
  exact @edgeLift_pair V A l₁ _ X w hw u v he

/-- An oriented triangle sum whose summand is invariant under cyclic rotation and vertex swap on the
triangles of `X` does not depend on the linear order used to orient the triangles. -/
theorem sum_orderedTriangles_congr_order [DecidableEq V] (l₁ l₂ : LinearOrder V) [AddCommMonoid A]
    (X : TwoComplex V) (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z) :
    ∑ t ∈ @orderedTriangles V l₁ X, w t.1 t.2.1 t.2.2 =
      ∑ t ∈ @orderedTriangles V l₂ X, w t.1 t.2.1 t.2.2 := by
  -- Identify `DecidableEq V` instances via `Subsingleton.elim` so triple finsets agree.
  obtain rfl : ‹DecidableEq V› = l₁.toDecidableEq := Subsingleton.elim _ _
  rw [← @sum_triangles_triangleLift V A l₁ _ X w hrot hswap]
  refine @sum_triangles_eq_sum_orderedTriangles V A l₂ _ X (@triangleLift V A l₁ _ X w) w
    fun u v z _ _ ht => ?_
  rw [Subsingleton.elim l₂.toDecidableEq l₁.toDecidableEq] at ht ⊢
  exact @triangleLift_triple V A l₁ _ X w hrot hswap u v z ht

end OrderIndependence

/-! ### Invariance under relabelling along arbitrary vertex bijections -/

section Relabel

variable [LinearOrder V] [LinearOrder W] [AddCommMonoid A]

/-- Reindex an oriented edge sum along any bijection `e : V ≃ W`, without assuming that `e`
preserves the linear order. -/
theorem sum_orderedEdges_relabel (X : TwoComplex V) (e : V ≃ W) (w : W → W → A)
    (hw : ∀ ⦃u v⦄, ({u, v} : Finset W) ∈ (X.relabel e).edges → w u v = w v u) :
    ∑ p ∈ (X.relabel e).orderedEdges, w p.1 p.2 =
      ∑ p ∈ X.orderedEdges, w (e p.1) (e p.2) := by
  rw [← sum_edges_edgeLift (X.relabel e) w hw, X.sum_edges_relabel e,
    ← X.sum_orderedEdges_pair (fun s => edgeLift (X.relabel e) w (s.map e.toEmbedding))]
  refine sum_congr rfl fun p hp => ?_
  have he : ({p.1, p.2} : Finset V) ∈ X.edges := pair_mem_edges_of_mem_orderedEdges hp
  have hmap : ({p.1, p.2} : Finset V).map e.toEmbedding = {e p.1, e p.2} := by
    ext x; simp
  rw [hmap]
  exact edgeLift_pair (X.relabel e) w hw (hmap ▸ (X.map_mem_edges_relabel e _).mpr he)

/-- Reindex an oriented edge sum on the complete complex along any bijection `e : V ≃ W`. -/
theorem sum_orderedEdges_complete_equiv [Fintype V] [Fintype W] (e : V ≃ W) (w : W → W → A)
    (hw : ∀ ⦃u v⦄, u ≠ v → w u v = w v u) :
    ∑ p ∈ (complete W).orderedEdges, w p.1 p.2 =
      ∑ p ∈ (complete V).orderedEdges, w (e p.1) (e p.2) := by
  rw [← relabel_complete e]
  refine (complete V).sum_orderedEdges_relabel e w fun u v he => hw ?_
  rintro rfl
  simp [relabel_complete] at he

/-- Reindex an oriented triangle sum along any bijection `e : V ≃ W`, without assuming that `e`
preserves the linear order. -/
theorem sum_orderedTriangles_relabel (X : TwoComplex V) (e : V ≃ W) (w : W → W → W → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset W) ∈ (X.relabel e).triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset W) ∈ (X.relabel e).triangles → w v u z = w u v z) :
    ∑ t ∈ (X.relabel e).orderedTriangles, w t.1 t.2.1 t.2.2 =
      ∑ t ∈ X.orderedTriangles, w (e t.1) (e t.2.1) (e t.2.2) := by
  rw [← sum_triangles_triangleLift (X.relabel e) w hrot hswap, X.sum_triangles_relabel e,
    ← X.sum_orderedTriangles_triple (fun s => triangleLift (X.relabel e) w (s.map e.toEmbedding))]
  refine sum_congr rfl fun t ht => ?_
  have hs : ({t.1, t.2.1, t.2.2} : Finset V) ∈ X.triangles :=
    triple_mem_triangles_of_mem_orderedTriangles ht
  have hmap : ({t.1, t.2.1, t.2.2} : Finset V).map e.toEmbedding =
      {e t.1, e t.2.1, e t.2.2} := by
    ext x; simp
  rw [hmap]
  exact triangleLift_triple (X.relabel e) w hrot hswap
    (hmap ▸ (X.map_mem_triangles_relabel e _).mpr hs)

/-- Reindex an oriented triangle sum on the complete complex along any bijection `e : V ≃ W`. -/
theorem sum_orderedTriangles_complete_equiv [Fintype V] [Fintype W] (e : V ≃ W)
    (w : W → W → W → A)
    (hrot : ∀ ⦃u v z⦄, u ≠ v → u ≠ z → v ≠ z → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, u ≠ v → u ≠ z → v ≠ z → w v u z = w u v z) :
    ∑ t ∈ (complete W).orderedTriangles, w t.1 t.2.1 t.2.2 =
      ∑ t ∈ (complete V).orderedTriangles, w (e t.1) (e t.2.1) (e t.2.2) := by
  rw [← relabel_complete e]
  refine (complete V).sum_orderedTriangles_relabel e w (fun u v z ht => ?_) (fun u v z ht => ?_)
  · rw [relabel_complete e] at ht
    obtain ⟨h₁, h₂, h₃⟩ := ne_of_triple_mem_triangles ht
    exact hrot h₁ h₂ h₃
  · rw [relabel_complete e] at ht
    obtain ⟨h₁, h₂, h₃⟩ := ne_of_triple_mem_triangles ht
    exact hswap h₁ h₂ h₃

end Relabel

/-! ### Oriented vertex-link and star double counts -/

section StarDoubleCount

variable [LinearOrder V] [AddCommMonoid A]

private theorem sum_orderedEdges_eq_sum_linkEdges_triangleLift (X : TwoComplex V) (x : V)
    (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z) :
    ∑ p ∈ X.orderedEdges, (if ({x, p.1, p.2} : Finset V) ∈ X.triangles then w x p.1 p.2 else 0) =
      ∑ e ∈ X.linkEdges x, triangleLift X w (insert x e) := by
  have hlink_eq : X.linkEdges x = X.edges.filter (· ∈ X.linkEdges x) := by
    ext e
    rw [mem_filter]
    exact ⟨fun h => ⟨((X.mem_linkEdges x e).mp h).1, h⟩, And.right⟩
  rw [hlink_eq, sum_filter,
    ← X.sum_orderedEdges_pair
      (fun e => if e ∈ X.linkEdges x then triangleLift X w (insert x e) else 0)]
  refine sum_congr rfl fun p hp => ?_
  simp_rw [pair_mem_linkEdges_iff_of_mem_edges (pair_mem_edges_of_mem_orderedEdges hp)]
  by_cases ht : ({x, p.1, p.2} : Finset V) ∈ X.triangles
  · simp [ht, triangleLift_triple X w hrot hswap ht]
  · simp [ht]

/-- For a fixed vertex `x`, summing a permutation-invariant triangle weight `w x p.1 p.2` over the
oriented edges `p` spanning a filled triangle with `x` equals the sum of `w` over the oriented
triangles containing `x`. -/
theorem sum_orderedEdges_link (X : TwoComplex V) (x : V) (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z) :
    ∑ p ∈ X.orderedEdges, (if ({x, p.1, p.2} : Finset V) ∈ X.triangles then w x p.1 p.2 else 0) =
      ∑ t ∈ X.orderedTriangles,
        (if x ∈ ({t.1, t.2.1, t.2.2} : Finset V) then w t.1 t.2.1 t.2.2 else 0) := by
  rw [sum_orderedEdges_eq_sum_linkEdges_triangleLift X x w hrot hswap,
    X.sum_linkEdges x (triangleLift X w), sum_filter,
    ← X.sum_orderedTriangles_triple (fun s => if x ∈ s then triangleLift X w s else 0)]
  refine sum_congr rfl fun t ht => ?_
  have hts := triple_mem_triangles_of_mem_orderedTriangles ht
  by_cases hx : x ∈ ({t.1, t.2.1, t.2.2} : Finset V) <;>
    simp [hx, triangleLift_triple X w hrot hswap hts]

/-- Summing a permutation-invariant triangle weight `w x p.1 p.2` over all vertices `x` and oriented
edges `p` spanning a filled triangle with `x` counts each oriented triangle three times. -/
theorem sum_vertex_orderedEdges [Fintype V] (X : TwoComplex V) (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z) :
    ∑ x : V, ∑ p ∈ X.orderedEdges,
        (if ({x, p.1, p.2} : Finset V) ∈ X.triangles then w x p.1 p.2 else 0) =
      3 • ∑ t ∈ X.orderedTriangles, w t.1 t.2.1 t.2.2 := by
  simp_rw [sum_orderedEdges_eq_sum_linkEdges_triangleLift X _ w hrot hswap]
  rw [X.sum_vertex_linkEdges (triangleLift X w), sum_triangles_triangleLift X w hrot hswap]

/-- The oriented star double count on the complete complex: edges incident to the star vertex `x`
contribute `0`, every non-incident oriented edge `(u, v)` contributes `w x u v`, and summing over
all star vertices `x` gives three times the oriented triangle sum of `w`. -/
theorem sum_vertex_orderedEdges_complete [Fintype V] (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, u ≠ v → u ≠ z → v ≠ z → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, u ≠ v → u ≠ z → v ≠ z → w v u z = w u v z) :
    ∑ x : V, ∑ p ∈ (complete V).orderedEdges,
        (if x = p.1 ∨ x = p.2 then 0 else w x p.1 p.2) =
      3 • ∑ t ∈ (complete V).orderedTriangles, w t.1 t.2.1 t.2.2 := by
  have hrot' : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ (complete V).triangles → w v z u = w u v z :=
    fun _ _ _ ht => let ⟨h₁, h₂, h₃⟩ := ne_of_triple_mem_triangles ht; hrot h₁ h₂ h₃
  have hswap' : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ (complete V).triangles → w v u z = w u v z :=
    fun _ _ _ ht => let ⟨h₁, h₂, h₃⟩ := ne_of_triple_mem_triangles ht; hswap h₁ h₂ h₃
  rw [← sum_triangles_triangleLift (complete V) w hrot' hswap',
    ← sum_vertex_edges_complete (triangleLift (complete V) w)]
  refine sum_congr rfl fun x _ => ((complete V).sum_edges_eq_sum_orderedEdges
    (fun e => if x ∈ e then 0 else triangleLift (complete V) w (insert x e))
    (fun u v => if x = u ∨ x = v then 0 else w x u v)
    fun u v _ he => ?_).symm
  by_cases hx : x ∈ ({u, v} : Finset V)
  · simp [hx, show (x = u ∨ x = v) from by simpa using hx]
  · have ht : ({x, u, v} : Finset V) ∈ (complete V).triangles := by
      rw [mem_triangles_complete, card_insert_of_notMem hx, (mem_edges_complete _).mp he]
    simp [hx, show ¬(x = u ∨ x = v) from by simpa using hx,
      triangleLift_triple (complete V) w hrot' hswap' ht]

end StarDoubleCount

end TauCeti.TwoComplex

end
