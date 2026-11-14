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

/-! ### Face membership and permutation symmetry on unoriented simplices -/

section DecidableEq

variable [DecidableEq V]

/-- The three vertices of a filled triangle are pairwise distinct. -/
theorem ne_of_triple_mem_triangles {X : TwoComplex V} {u v z : V}
    (ht : ({u, v, z} : Finset V) ∈ X.triangles) : u ≠ v ∧ u ≠ z ∧ v ≠ z :=
  card_triple_eq_three_iff.mp (X.triangle_card _ ht)

/-- The first two listed vertices of a filled triangle span an edge. Permuting `{u, v, z}` yields
the other two boundary edges as well. -/
theorem pair_mem_edges_of_triple_mem_triangles {X : TwoComplex V} {u v z : V}
    (ht : ({u, v, z} : Finset V) ∈ X.triangles) : ({u, v} : Finset V) ∈ X.edges := by
  have huv := (ne_of_triple_mem_triangles ht).1
  refine X.edge_mem_of_subset _ ht {u, v} ?_ (card_pair huv)
  intro x hx
  simp only [mem_insert, mem_singleton] at hx ⊢
  tauto

/-- For an edge `{u, v}` of `X`, membership in the link of `x` is equivalent to `{x, u, v}` being a
filled triangle; disjointness `x ∉ {u, v}` follows automatically from the triangle cardinality. -/
theorem pair_mem_linkEdges_iff_of_mem_edges {X : TwoComplex V} {x u v : V}
    (he : ({u, v} : Finset V) ∈ X.edges) :
    ({u, v} : Finset V) ∈ X.linkEdges x ↔ ({x, u, v} : Finset V) ∈ X.triangles := by
  rw [X.mem_linkEdges]
  refine ⟨fun h => h.2.2, fun ht => ⟨he, ?_, ht⟩⟩
  obtain ⟨hxu, hxv, -⟩ := ne_of_triple_mem_triangles ht
  simp [hxu, hxv]

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
    convert ht using 1; ext; simp; tauto
  have ht_zuv : ({z₁, u₁, v₁} : Finset V) ∈ X.triangles := by
    convert ht using 1; ext; simp; tauto
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
  · rintro ⟨hlt, he⟩
    refine ⟨{p.1, p.2}, he, ?_⟩
    have hq : (⟨{p.1, p.2}, X.edge_card _ he⟩ : Set.powersetCard V 2) =
        Set.powersetCard.ofLtPair ⟨p, hlt⟩ :=
      Subtype.ext (Set.powersetCard.val_ofLtPair ⟨p, hlt⟩).symm
    rw [edgeOrderEmb_apply, hq, Equiv.symm_apply_apply]

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
  left_inv p := by
    apply Subtype.ext
    dsimp only
    have hlt := fst_lt_snd_of_mem_orderedEdges p.2
    have he := pair_mem_edges_of_mem_orderedEdges p.2
    have hq : (⟨{p.1.1, p.1.2}, X.edge_card _ he⟩ : Set.powersetCard V 2) =
        Set.powersetCard.ofLtPair ⟨p.1, hlt⟩ :=
      Subtype.ext (Set.powersetCard.val_ofLtPair ⟨p.1, hlt⟩).symm
    rw [edgeOrderEmb_apply, hq, Equiv.symm_apply_apply]
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
  · rintro ⟨hlt₁, hlt₂, ht⟩
    refine ⟨{t.1, t.2.1, t.2.2}, ht, ?_⟩
    have hq : (⟨{t.1, t.2.1, t.2.2}, X.triangle_card _ ht⟩ : Set.powersetCard V 3) =
        Set.powersetCard.ofLtTriple ⟨t, hlt₁, hlt₂⟩ :=
      Subtype.ext (Set.powersetCard.val_ofLtTriple ⟨t, hlt₁, hlt₂⟩).symm
    rw [triangleOrderEmb_apply, hq, Equiv.symm_apply_apply]

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
  refine (X.mem_orderedEdges _).mpr ⟨snd_fst_lt_snd_snd_of_mem_orderedTriangles ht, ?_⟩
  have ht' : ({t.2.1, t.2.2, t.1} : Finset V) ∈ X.triangles := by
    convert triple_mem_triangles_of_mem_orderedTriangles ht using 1
    ext; simp; tauto
  exact pair_mem_edges_of_triple_mem_triangles ht'

/-- The first and third vertices of an oriented triangle form an oriented edge. -/
theorem mk_fst_snd_snd_mem_orderedEdges {X : TwoComplex V} {t : V × V × V}
    (ht : t ∈ X.orderedTriangles) : (t.1, t.2.2) ∈ X.orderedEdges := by
  refine (X.mem_orderedEdges _).mpr ⟨fst_lt_snd_snd_of_mem_orderedTriangles ht, ?_⟩
  have ht' : ({t.1, t.2.2, t.2.1} : Finset V) ∈ X.triangles := by
    convert triple_mem_triangles_of_mem_orderedTriangles ht using 1
    ext; simp; tauto
  exact pair_mem_edges_of_triple_mem_triangles ht'

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
  left_inv t := by
    apply Subtype.ext
    dsimp only
    have hlt₁ := fst_lt_snd_fst_of_mem_orderedTriangles t.2
    have hlt₂ := snd_fst_lt_snd_snd_of_mem_orderedTriangles t.2
    have ht := triple_mem_triangles_of_mem_orderedTriangles t.2
    have hq : (⟨{t.1.1, t.1.2.1, t.1.2.2}, X.triangle_card _ ht⟩ : Set.powersetCard V 3) =
        Set.powersetCard.ofLtTriple ⟨t.1, hlt₁, hlt₂⟩ :=
      Subtype.ext (Set.powersetCard.val_ofLtTriple ⟨t.1, hlt₁, hlt₂⟩).symm
    rw [triangleOrderEmb_apply, hq, Equiv.symm_apply_apply]
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

/-- Pair finsets built under two `DecidableEq` instances are propositionally equal. -/
private theorem pair_congr_decidableEq (d₁ d₂ : DecidableEq V) (u v : V) :
    @insert V (Finset V) (@Finset.instInsert V d₁) u {v} =
      @insert V (Finset V) (@Finset.instInsert V d₂) u {v} := by
  ext x
  simp

/-- Triple finsets built under two `DecidableEq` instances are propositionally equal. -/
private theorem triple_congr_decidableEq (d₁ d₂ : DecidableEq V) (u v z : V) :
    @insert V (Finset V) (@Finset.instInsert V d₁) u
        (@insert V (Finset V) (@Finset.instInsert V d₁) v {z}) =
      @insert V (Finset V) (@Finset.instInsert V d₂) u
        (@insert V (Finset V) (@Finset.instInsert V d₂) v {z}) := by
  ext x
  simp

/-- An oriented edge sum whose summand is symmetric on the edges of `X` does not depend on the
linear order used to orient the edges. -/
theorem sum_orderedEdges_congr_order [DecidableEq V] (l₁ l₂ : LinearOrder V) [AddCommMonoid A]
    (X : TwoComplex V) (w : V → V → A)
    (hw : ∀ ⦃u v⦄, ({u, v} : Finset V) ∈ X.edges → w u v = w v u) :
    ∑ p ∈ @orderedEdges V l₁ X, w p.1 p.2 = ∑ p ∈ @orderedEdges V l₂ X, w p.1 p.2 := by
  have hw₁ : ∀ ⦃u v⦄,
      @insert V (Finset V) (@Finset.instInsert V l₁.toDecidableEq) u {v} ∈ X.edges →
        w u v = w v u := by
    intro u v he
    rw [pair_congr_decidableEq l₁.toDecidableEq ‹DecidableEq V› u v] at he
    exact hw he
  have hf : ∀ (l : LinearOrder V),
      ∑ e ∈ X.edges, @edgeLift V A l₁ _ X w e = ∑ p ∈ @orderedEdges V l X, w p.1 p.2 := by
    intro l
    refine @sum_edges_eq_sum_orderedEdges V A l _ X (@edgeLift V A l₁ _ X w) w fun u v _ he => ?_
    rw [pair_congr_decidableEq l.toDecidableEq l₁.toDecidableEq u v] at he ⊢
    exact @edgeLift_pair V A l₁ _ X w hw₁ u v he
  exact (hf l₁).symm.trans (hf l₂)

/-- An oriented triangle sum whose summand is invariant under cyclic rotation and vertex swap on the
triangles of `X` does not depend on the linear order used to orient the triangles. -/
theorem sum_orderedTriangles_congr_order [DecidableEq V] (l₁ l₂ : LinearOrder V) [AddCommMonoid A]
    (X : TwoComplex V) (w : V → V → V → A)
    (hrot : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v z u = w u v z)
    (hswap : ∀ ⦃u v z⦄, ({u, v, z} : Finset V) ∈ X.triangles → w v u z = w u v z) :
    ∑ t ∈ @orderedTriangles V l₁ X, w t.1 t.2.1 t.2.2 =
      ∑ t ∈ @orderedTriangles V l₂ X, w t.1 t.2.1 t.2.2 := by
  have hrot₁ : ∀ ⦃u v z⦄,
      @insert V (Finset V) (@Finset.instInsert V l₁.toDecidableEq) u
          (@insert V (Finset V) (@Finset.instInsert V l₁.toDecidableEq) v {z}) ∈ X.triangles →
        w v z u = w u v z := by
    intro u v z ht
    rw [triple_congr_decidableEq l₁.toDecidableEq ‹DecidableEq V› u v z] at ht
    exact hrot ht
  have hswap₁ : ∀ ⦃u v z⦄,
      @insert V (Finset V) (@Finset.instInsert V l₁.toDecidableEq) u
          (@insert V (Finset V) (@Finset.instInsert V l₁.toDecidableEq) v {z}) ∈ X.triangles →
        w v u z = w u v z := by
    intro u v z ht
    rw [triple_congr_decidableEq l₁.toDecidableEq ‹DecidableEq V› u v z] at ht
    exact hswap ht
  have hf : ∀ (l : LinearOrder V),
      ∑ s ∈ X.triangles, @triangleLift V A l₁ _ X w s =
        ∑ t ∈ @orderedTriangles V l X, w t.1 t.2.1 t.2.2 := by
    intro l
    refine @sum_triangles_eq_sum_orderedTriangles V A l _ X (@triangleLift V A l₁ _ X w) w
      fun u v z _ _ ht => ?_
    rw [triple_congr_decidableEq l.toDecidableEq l₁.toDecidableEq u v z] at ht ⊢
    exact @triangleLift_triple V A l₁ _ X w hrot₁ hswap₁ u v z ht
  exact (hf l₁).symm.trans (hf l₂)

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
  rw [← (complete V).sum_vertex_orderedEdges w
    (fun u v z ht => by
      obtain ⟨h₁, h₂, h₃⟩ := ne_of_triple_mem_triangles ht
      exact hrot h₁ h₂ h₃)
    (fun u v z ht => by
      obtain ⟨h₁, h₂, h₃⟩ := ne_of_triple_mem_triangles ht
      exact hswap h₁ h₂ h₃)]
  refine sum_congr rfl fun x _ => sum_congr rfl fun p hp => ?_
  have hpne : p.1 ≠ p.2 := fst_ne_snd_of_mem_orderedEdges hp
  by_cases hx : x = p.1 ∨ x = p.2
  · have hnot : ({x, p.1, p.2} : Finset V) ∉ (complete V).triangles := by
      intro ht
      obtain ⟨h₁, h₂, -⟩ := ne_of_triple_mem_triangles ht
      exact hx.elim h₁ h₂
    simp only [hx, hnot, ↓reduceIte]
  · rcases not_or.mp hx with ⟨hx₁, hx₂⟩
    have ht : ({x, p.1, p.2} : Finset V) ∈ (complete V).triangles :=
      (mem_triangles_complete _).mpr (card_triple_eq_three_iff.mpr ⟨hx₁, hx₂, hpne⟩)
    simp only [hx, ht, ↓reduceIte]

end StarDoubleCount

end TauCeti.TwoComplex

end
