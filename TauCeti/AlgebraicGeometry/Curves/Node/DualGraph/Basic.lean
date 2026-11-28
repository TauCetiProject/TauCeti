/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Basic
public import TauCeti.AlgebraicGeometry.Curves.Node.Components
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# The dual graph of a prestable curve

Let `X` be a prestable curve over a separably closed field `K`: a proper connected curve with
at worst nodes (`TauCeti.AlgebraicGeometry.PrestableFamily`). Blowing up its singular subscheme
gives a finite surjective morphism `ν : X^ν ⟶ X` from a regular scheme which is an isomorphism over
the smooth locus. Exactly one point of `X^ν` lies over each smooth point of `X`, and exactly two lie
over each node, one on each branch
(`AlgebraicGeometry.Scheme.natCard_preimage_blowupToBase_singularLocus_eq_two_of_mem_support`). The
irreducible components of the regular scheme `X^ν` are disjoint and open, so each point `b` of
`X^ν` lies on exactly one of them, `TauCeti.irreducibleComponentOf b`.

This file assembles these data into the dual graph of `X` (`AlgebraicGeometry.Scheme.dualGraph`),
a `TauCeti.DualGraph`:

* its vertices are the irreducible components of `X^ν`;
* its edges are the nodes of `X`, that is the points outside the smooth locus;
* the two endpoints of the edge at a node `x` are the components of `X^ν` carrying the two points
  over `x` (`AlgebraicGeometry.Scheme.branchPointEquiv`); a node at which both branches lie on
  the same component is a loop;
* the genus of a vertex is the genus `dim_K H¹(X^ν_v, 𝒪)` of the component `X^ν_v` as an open
  subscheme of `X^ν` (`AlgebraicGeometry.Scheme.blowupComponent`);
* a marking, given by a smooth point of `X`, is attached to the component carrying the point over
  it.

The graph is connected because `X` is. In addition to the defining equivalences, this file proves
choice-free geometric characterizations of incidences, loops, vertex/edge cardinalities, and
component valence (`AlgebraicGeometry.Scheme.valence_dualGraph`), computes the dual graph of a
smooth curve (`AlgebraicGeometry.Scheme.arithmeticGenus_dualGraph_of_smooth`), and defines
geometric rational tails (`AlgebraicGeometry.Scheme.IsRationalTail`) and rational bridges
(`AlgebraicGeometry.Scheme.IsRationalBridge`) and identifies them with the combinatorial predicates.

## Main definitions

* `AlgebraicGeometry.Scheme.branchPointEquiv`: the two points over a node, labelled by `Fin 2`.
* `AlgebraicGeometry.Scheme.dualGraph`: the dual graph of a prestable curve over a separably
  closed field with markings at smooth points.
* `AlgebraicGeometry.Scheme.dualGraphVertexEquiv` and `AlgebraicGeometry.Scheme.dualGraphEdgeEquiv`:
  its vertices are the components of the blowup, and its edges are the nodes.
* `AlgebraicGeometry.Scheme.IsRationalTail` and `AlgebraicGeometry.Scheme.IsRationalBridge`:
  geometric rational tails and rational bridges on a proper nodal curve.

## Main results

* `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_endpoint` and
  `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_endpoint_eq_iff`: the endpoints of an edge are
  the components carrying the two points over the node.
* `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_marking` and
  `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_marking_eq_iff`: a marking is attached to the
  component carrying the point over it.
* `AlgebraicGeometry.Scheme.mem_ends_dualGraph_iff`,
  `AlgebraicGeometry.Scheme.ends_dualGraph_eq_self_iff` and
  `AlgebraicGeometry.Scheme.valence_dualGraph`: choice-free geometric descriptions of incidences,
  loops, and component valence.
* `AlgebraicGeometry.Scheme.firstBetti_dualGraph_of_smooth` and
  `AlgebraicGeometry.Scheme.arithmeticGenus_dualGraph_of_smooth`: specialization to smooth curves.
* `AlgebraicGeometry.Scheme.dualGraph_isRationalTail_iff` and
  `AlgebraicGeometry.Scheme.dualGraph_isRationalBridge_iff`: equivalence between combinatorial and
  geometric rational tails and bridges.

## References

* [The Stacks Project, Section 53.19, Nodal curves](https://stacks.math.columbia.edu/tag/0C46).
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, Section 2, for the dual graph of a pointed nodal curve.
-/

public section

noncomputable section

open CategoryTheory Limits Set TauCeti TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

section Prestable

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [PrestableFamily (X ↘ Spec (.of K))]

variable (K) in
private theorem atWorstNodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)) :=
  PrestableFamily.atWorstNodalOfRelativeDimensionOne

/-! ### The points over a node -/

variable [IsSepClosed K]

private theorem natCard_preimage_blowupToBase_eq_two
    (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)) :
    Nat.card ((X.singularLocus K).blowupToBase ⁻¹' {x.val}) = 2 :=
  X.natCard_preimage_blowupToBase_singularLocus_eq_two_of_mem_support (atWorstNodal K X)
    ((X.mem_support_singularLocus_iff_notMem_smoothLocus x.val).mpr x.property)

/-- The two points of the blowup of a prestable curve along its singular subscheme lying over a
node, one on each branch through the node, labelled by `Fin 2`. The labelling is a choice. -/
def branchPointEquiv (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)) :
    Fin 2 ≃ (X.singularLocus K).blowupToBase ⁻¹' {x.val} :=
  have := Nat.finite_of_card_ne_zero
    ((X.natCard_preimage_blowupToBase_eq_two x).trans_ne two_ne_zero)
  (Finite.equivFinOfCardEq (X.natCard_preimage_blowupToBase_eq_two x)).symm

/-- Each branch point `X.branchPointEquiv x i` lies over the node `x`. -/
theorem blowupToBase_branchPointEquiv (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ))
    (i : Fin 2) : (X.singularLocus K).blowupToBase (X.branchPointEquiv x i) = x.val :=
  (X.branchPointEquiv x i).property

/-- Every point of the blowup lying over a node `x` is one of its two branch points
`X.branchPointEquiv x i`. -/
theorem exists_branchPointEquiv_eq {x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)}
    {b : (X.singularLocus K).blowup} (hb : (X.singularLocus K).blowupToBase b = x.val) :
    ∃ i : Fin 2, (X.branchPointEquiv x i : (X.singularLocus K).blowup) = b :=
  let ⟨i, hi⟩ := (X.branchPointEquiv x).surjective ⟨b, hb⟩
  ⟨i, congr(($hi).val)⟩

/-! ### Finiteness and connectedness -/

omit [IsSepClosed K] in
private theorem finite_irreducibleComponents_blowup :
    (irreducibleComponents (X.singularLocus K).blowup).Finite := by
  have := X.isFinite_blowupToBase_singularLocus (atWorstNodal K X)
  have : CompactSpace (X.singularLocus K).blowup :=
    (quasiCompact_iff_compactSpace
      ((X.singularLocus K).blowupToBase ≫ X ↘ Spec (.of K))).mp inferInstance
  have : IsNoetherian (X.singularLocus K).blowup := {}
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

omit [IsSepClosed K] in
private theorem nonempty_irreducibleComponents_blowup :
    Nonempty (irreducibleComponents (X.singularLocus K).blowup) := by
  obtain ⟨x⟩ : Nonempty X := (X ↘ Spec (.of K)).surjective.nonempty
  obtain ⟨b, -⟩ := X.surjective_blowupToBase_singularLocus
    (atWorstNodal K X) |>.surj x
  exact ⟨irreducibleComponentOf b⟩

/-- Two components of the blowup are adjacent when they carry the two points over some node. -/
private def Adj (v w : irreducibleComponents (X.singularLocus K).blowup) : Prop :=
  ∃ e : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ),
    (irreducibleComponentOf (X.branchPointEquiv e 0 : (X.singularLocus K).blowup) = v ∧
        irreducibleComponentOf (X.branchPointEquiv e 1 : (X.singularLocus K).blowup) = w) ∨
      (irreducibleComponentOf (X.branchPointEquiv e 0 : (X.singularLocus K).blowup) = w ∧
        irreducibleComponentOf (X.branchPointEquiv e 1 : (X.singularLocus K).blowup) = v)

/-- Two components of the blowup meeting over a point of the curve are equal or joined by the
edge of a node. -/
private theorem eq_or_adj_of_blowupToBase_eq {b b' : (X.singularLocus K).blowup}
    (h : (X.singularLocus K).blowupToBase b = (X.singularLocus K).blowupToBase b') :
    irreducibleComponentOf b = irreducibleComponentOf b' ∨
      Adj X (irreducibleComponentOf b) (irreducibleComponentOf b') := by
  let ν := (X.singularLocus K).blowupToBase
  by_cases hx : ν b ∈ (X ↘ Spec (.of K)).smoothLocus
  · -- over a smooth point there is only one point of the blowup
    exact .inl (by rw [X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus h hx])
  · -- over a node the two points are the two branch points
    let e : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ) := ⟨ν b, hx⟩
    obtain ⟨i, hi⟩ := X.exists_branchPointEquiv_eq (x := e) rfl
    obtain ⟨j, hj⟩ := X.exists_branchPointEquiv_eq (x := e) h.symm
    rw [← hi, ← hj]
    by_cases hij : i = j
    · exact .inl (by rw [hij])
    · exact .inr ⟨e, by fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The dual graph of a prestable curve over a separably closed field is connected. -/
private theorem reflTransGen_adj (v w : irreducibleComponents (X.singularLocus K).blowup) :
    Relation.ReflTransGen (Adj X) v w := by
  let ν := (X.singularLocus K).blowupToBase
  have := X.isFinite_blowupToBase_singularLocus (atWorstNodal K X)
  have : ConnectedSpace X :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := X ↘ Spec (.of K))
  let R := Relation.ReflTransGen (Adj X) v
  -- the images of the components reachable from `v`, and of the others
  let A := ⋃ u ∈ {u | R u}, ν '' u
  let B := ⋃ u ∈ {u | ¬ R u}, ν '' u
  have hfin := finite_irreducibleComponents_blowup (K := K) X
  have hclosed (S : Set (irreducibleComponents (X.singularLocus K).blowup)) :
      IsClosed (⋃ u ∈ S, ν '' u) :=
    (hfin.preimage Subtype.val_injective.injOn).subset (by simp) |>.isClosed_biUnion
      fun u _ ↦ ν.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ u.property)
  -- a point in both would give an edge from a reachable component to another one
  have hdisj (x : X) (hA : x ∈ A) (hB : x ∈ B) : False := by
    simp only [A, B, Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq] at hA hB
    obtain ⟨u, hu, b, hb, rfl⟩ := hA
    obtain ⟨u', hu', b', hb', hbb'⟩ := hB
    obtain rfl := irreducibleComponentOf_eq_iff.mpr hb
    obtain rfl := irreducibleComponentOf_eq_iff.mpr hb'
    rcases eq_or_adj_of_blowupToBase_eq X hbb'.symm with h | ⟨e, he⟩
    · exact hu' (h ▸ hu)
    · exact hu' (hu.tail ⟨e, he⟩)
  have hcover (x : X) : x ∈ A ∪ B := by
    obtain ⟨b, rfl⟩ := X.surjective_blowupToBase_singularLocus
      (atWorstNodal K X) |>.surj x
    by_cases hb : R (irreducibleComponentOf b)
    · exact .inl (Set.mem_biUnion hb ⟨b, mem_irreducibleComponentOf b, rfl⟩)
    · exact .inr (Set.mem_biUnion hb ⟨b, mem_irreducibleComponentOf b, rfl⟩)
  have hAB : A = Bᶜ := Set.ext fun x ↦ ⟨fun hA hB ↦ hdisj x hA hB,
    fun hB ↦ (hcover x).resolve_right hB⟩
  have hA : IsClopen A := ⟨hclosed _, hAB ▸ (hclosed _).isOpen_compl⟩
  obtain ⟨b, hb⟩ := v.property.1.1
  rcases isClopen_iff.mp hA with h | h
  · exact (Set.eq_empty_iff_forall_notMem.mp h (ν b)
      (Set.mem_biUnion (Relation.ReflTransGen.refl : R v) ⟨b, hb, rfl⟩)).elim
  · by_contra hw
    obtain ⟨b', hb'⟩ := w.property.1.1
    exact hdisj (ν b') (h ▸ Set.mem_univ _) (Set.mem_biUnion hw ⟨b', hb', rfl⟩)

/-! ### The dual graph -/

/-- The point of the blowup over a smooth point of the curve. -/
private def pointOver (x : (X ↘ Spec (.of K)).smoothLocus) : (X.singularLocus K).blowup :=
  (X.surjective_blowupToBase_singularLocus
    (atWorstNodal K X)).surj x.val |>.choose

omit [IsSepClosed K] in
private theorem blowupToBase_pointOver (x : (X ↘ Spec (.of K)).smoothLocus) :
    (X.singularLocus K).blowupToBase (pointOver X x) = x :=
  ((X.surjective_blowupToBase_singularLocus (atWorstNodal K X)).surj x.val).choose_spec

/-- **The dual graph of a prestable curve** `X` over a separably closed field `K`, with
markings at the smooth points `p i`. Its vertices are the irreducible components of the blowup
`X^ν` of `X` along its singular subscheme (`AlgebraicGeometry.Scheme.dualGraphVertexEquiv`); its
edges are the nodes of `X` (`AlgebraicGeometry.Scheme.dualGraphEdgeEquiv`); the endpoints of the
edge at a node `x` are the components carrying the two points of `X^ν` over `x`, in the order of
`AlgebraicGeometry.Scheme.branchPointEquiv`; the genus of a vertex is the genus of its component;
and the `i`-th marking is the component carrying the point over `p i`. It is connected since `X`
is. -/
def dualGraph {ι : Type v} (p : ι → (X ↘ Spec (.of K)).smoothLocus) : DualGraph.{u} ι where
  Vertex := irreducibleComponents (X.singularLocus K).blowup
  vertexFintype := (finite_irreducibleComponents_blowup X).fintype
  vertexDecidableEq := Classical.decEq _
  vertexNonempty := nonempty_irreducibleComponents_blowup X
  Edge := ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)
  edgeFintype := (X.finite_compl_smoothLocus (atWorstNodal K X)).fintype
  edgeDecidableEq := Classical.decEq _
  endpoint e i := irreducibleComponentOf (X.branchPointEquiv e i : (X.singularLocus K).blowup)
  genus v := (X.blowupComponent v).toScheme.genus K
  marking i := irreducibleComponentOf (pointOver X (p i))
  connected := reflTransGen_adj X

variable {ι : Type v} (p : ι → (X ↘ Spec (.of K)).smoothLocus)

/-- Composing the marked points with a map of index types reindexes the markings of the dual
graph. -/
@[simp]
theorem dualGraph_comp {κ : Type*} (e : κ → ι) :
    X.dualGraph (p ∘ e) = (X.dualGraph p).reindex e :=
  (rfl)

/-- The vertices of the dual graph are the irreducible components of the blowup of the curve
along its singular subscheme. -/
def dualGraphVertexEquiv :
    (X.dualGraph p).Vertex ≃ irreducibleComponents (X.singularLocus K).blowup :=
  Equiv.refl _

/-- The edges of the dual graph are the nodes of the curve, the points outside its smooth
locus. -/
def dualGraphEdgeEquiv :
    (X.dualGraph p).Edge ≃ ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ) :=
  Equiv.refl _

/-- The endpoint of the edge at a node is the component of the blowup through the corresponding
point over the node. -/
@[simp]
theorem dualGraphVertexEquiv_endpoint (e : (X.dualGraph p).Edge) (i : Fin 2) :
    X.dualGraphVertexEquiv p ((X.dualGraph p).endpoint e i) =
      irreducibleComponentOf
        (X.branchPointEquiv (X.dualGraphEdgeEquiv p e) i : (X.singularLocus K).blowup) :=
  (rfl)

/-- The endpoints of the edge at a node are the components of the blowup carrying the two points
over the node. -/
theorem branchPointEquiv_mem_dualGraph_endpoint (e : (X.dualGraph p).Edge) (i : Fin 2) :
    (X.branchPointEquiv (X.dualGraphEdgeEquiv p e) i : (X.singularLocus K).blowup) ∈
      (X.dualGraphVertexEquiv p ((X.dualGraph p).endpoint e i) :
        Set (X.singularLocus K).blowup) :=
  mem_irreducibleComponentOf _

/-- The endpoints of the edge at a node are the components of the blowup carrying the two points
over the node: this determines them, as every point lies on exactly one component. -/
theorem dualGraphVertexEquiv_endpoint_eq_iff (e : (X.dualGraph p).Edge) (i : Fin 2)
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    X.dualGraphVertexEquiv p ((X.dualGraph p).endpoint e i) = v ↔
      (X.branchPointEquiv (X.dualGraphEdgeEquiv p e) i : (X.singularLocus K).blowup) ∈
        (v : Set (X.singularLocus K).blowup) :=
  irreducibleComponentOf_eq_iff

/-- Every point of the blowup whose image lies outside the smooth locus is a branch point over a
dual-graph edge. -/
theorem exists_branchPointEquiv_eq_of_notMem_smoothLocus {b : (X.singularLocus K).blowup}
    (hb : (X.singularLocus K).blowupToBase b ∉ (X ↘ Spec (.of K)).smoothLocus) :
    ∃ (e : (X.dualGraph p).Edge) (i : Fin 2),
      (X.branchPointEquiv (X.dualGraphEdgeEquiv p e) i : (X.singularLocus K).blowup) = b :=
  ⟨(X.dualGraphEdgeEquiv p).symm ⟨(X.singularLocus K).blowupToBase b, hb⟩,
    X.exists_branchPointEquiv_eq (by simp)⟩

/-- A marking is attached to the component of the blowup carrying the point over it. -/
theorem mem_dualGraph_marking (i : ι) {b : (X.singularLocus K).blowup}
    (hb : (X.singularLocus K).blowupToBase b = p i) :
    b ∈ (X.dualGraphVertexEquiv p ((X.dualGraph p).marking i) :
      Set (X.singularLocus K).blowup) := by
  rw [X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus
    (hb.trans (X.blowupToBase_pointOver (p i)).symm) (hb ▸ (p i).property)]
  exact mem_irreducibleComponentOf _

/-- The `i`-th marking is the component of the blowup through any point over `p i`. -/
theorem dualGraphVertexEquiv_marking (i : ι) {b : (X.singularLocus K).blowup}
    (hb : (X.singularLocus K).blowupToBase b = p i) :
    X.dualGraphVertexEquiv p ((X.dualGraph p).marking i) = irreducibleComponentOf b :=
  (irreducibleComponentOf_eq_iff.mpr (X.mem_dualGraph_marking p i hb)).symm

/-- The `i`-th marking is the component of the blowup carrying the point over `p i`: this
determines it, as every point lies on exactly one component. -/
theorem dualGraphVertexEquiv_marking_eq_iff (i : ι) {b : (X.singularLocus K).blowup}
    (hb : (X.singularLocus K).blowupToBase b = p i)
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    X.dualGraphVertexEquiv p ((X.dualGraph p).marking i) = v ↔
      b ∈ (v : Set (X.singularLocus K).blowup) :=
  X.dualGraphVertexEquiv_marking p i hb ▸ irreducibleComponentOf_eq_iff

/-- The genus of a vertex of the dual graph is the genus of its component of the blowup. -/
@[simp]
theorem dualGraph_genus (v : (X.dualGraph p).Vertex) :
    (X.dualGraph p).genus v = (X.blowupComponent (X.dualGraphVertexEquiv p v)).toScheme.genus K :=
  (rfl)

/-! ### Geometric characterizations of incidences, loops, cardinalities, and valence -/

/-- Choice-free characterization of `marking` via membership in the irreducible component of `X`. -/
theorem dualGraph_marking_eq_iff_mem_blowupComponentEquiv (i : ι) (v : (X.dualGraph p).Vertex) :
    (X.dualGraph p).marking i = v ↔
      (p i : X) ∈ ((X.blowupComponentEquiv K
        PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (X.dualGraphVertexEquiv p v) : irreducibleComponents X) : Set X) := by
  obtain ⟨b, hb⟩ :=
    (X.surjective_blowupToBase_singularLocus (atWorstNodal K X)).surj (p i : X)
  rw [← (X.dualGraphVertexEquiv p).apply_eq_iff_eq, X.dualGraphVertexEquiv_marking_eq_iff p i hb,
    ← hb, blowupToBase_mem_coe_blowupComponentEquiv_iff_of_mem_smoothLocus _ (hb ▸ (p i).property)]

/-- The number of vertices of `X.dualGraph p` equals `(irreducibleComponents X).ncard`. -/
theorem natCard_vertex_dualGraph :
    Nat.card (X.dualGraph p).Vertex = (irreducibleComponents X).ncard := by
  rw [Nat.card_congr (X.dualGraphVertexEquiv p),
    Nat.card_congr (X.blowupComponentEquiv K (atWorstNodal K X)), Nat.card_coe_set_eq]

/-- The number of edges of `X.dualGraph p` equals the number of singular points of `X`. -/
theorem natCard_edge_dualGraph :
    Nat.card (X.dualGraph p).Edge = ((X.singularLocus K).support : Set X).ncard := by
  rw [Nat.card_congr (X.dualGraphEdgeEquiv p), ← X.support_singularLocus_eq_compl_smoothLocus,
    Nat.card_coe_set_eq]

/-- `v` is an endpoint of `e` iff the component `v` contains a point of `Bl X` lying over `e`. -/
theorem mem_ends_dualGraph_iff (v : (X.dualGraph p).Vertex) (e : (X.dualGraph p).Edge) :
    v ∈ (X.dualGraph p).ends e ↔
      ∃ b ∈ (X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup),
        (X.singularLocus K).blowupToBase b = (X.dualGraphEdgeEquiv p e : X) := by
  rw [DualGraph.mem_ends_iff]
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨b, hbv, hb⟩ ↦ ?_⟩
  · refine ⟨X.branchPointEquiv (X.dualGraphEdgeEquiv p e) i, ?_,
      X.blowupToBase_branchPointEquiv (X.dualGraphEdgeEquiv p e) i⟩
    exact (X.dualGraphVertexEquiv_endpoint_eq_iff p e i _).mp (congrArg _ hi)
  · obtain ⟨i, rfl⟩ := X.exists_branchPointEquiv_eq hb
    exact ⟨i, (X.dualGraphVertexEquiv p).injective
      ((X.dualGraphVertexEquiv_endpoint_eq_iff p e i _).mpr hbv)⟩

/-- `v` is an endpoint of `e` iff the node `e` lies on the corresponding component of `X`. -/
theorem mem_ends_dualGraph_iff_mem_blowupComponentEquiv
    (v : (X.dualGraph p).Vertex) (e : (X.dualGraph p).Edge) :
    v ∈ (X.dualGraph p).ends e ↔
      (X.dualGraphEdgeEquiv p e : X) ∈ ((X.blowupComponentEquiv K
        PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (X.dualGraphVertexEquiv p v) : irreducibleComponents X) : Set X) := by
  rw [X.mem_ends_dualGraph_iff p v e, X.coe_blowupComponentEquiv, Set.mem_image]

/-- An edge `e` is a loop at `v` iff the entire blowup fibre over `e` lies in `v`. -/
theorem ends_dualGraph_eq_self_iff (v : (X.dualGraph p).Vertex) (e : (X.dualGraph p).Edge) :
    (X.dualGraph p).ends e = s(v, v) ↔
      (X.singularLocus K).blowupToBase ⁻¹' {(X.dualGraphEdgeEquiv p e : X)} ⊆
        (X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup) := by
  rw [DualGraph.ends_def, Sym2.eq_iff, or_self,
    ← Fin.forall_fin_two (p := fun i ↦ (X.dualGraph p).endpoint e i = v)]
  refine ⟨fun h b hb ↦ ?_, fun h i ↦ (X.dualGraphVertexEquiv p).injective ?_⟩
  · obtain ⟨i, rfl⟩ := X.exists_branchPointEquiv_eq hb
    exact (X.dualGraphVertexEquiv_endpoint_eq_iff p e i _).mp (congrArg _ (h i))
  · rw [X.dualGraphVertexEquiv_endpoint_eq_iff]
    exact h (X.blowupToBase_branchPointEquiv (X.dualGraphEdgeEquiv p e) i)

/-- The valence of `v` in `X.dualGraph p` equals the number of points of `v` over `Sing(X/K)`. -/
theorem valence_dualGraph (v : (X.dualGraph p).Vertex) :
    (X.dualGraph p).valence v =
      ((X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup) ∩
        (X.singularLocus K).blowupToBase ⁻¹' (X.singularLocus K).support).ncard := by
  let G := X.dualGraph p
  let := G.edgeFintype; let := G.vertexDecidableEq
  let φ : G.Edge × Fin 2 → (X.singularLocus K).blowup := fun h ↦
    X.branchPointEquiv (X.dualGraphEdgeEquiv p h.1) h.2
  have hφ_inj : Function.Injective φ := fun ⟨e₁, i₁⟩ ⟨e₂, i₂⟩ heq ↦ by
    have heval : (X.dualGraphEdgeEquiv p e₁ : X) = (X.dualGraphEdgeEquiv p e₂ : X) := by
      rw [← X.blowupToBase_branchPointEquiv (X.dualGraphEdgeEquiv p e₁) i₁,
        ← X.blowupToBase_branchPointEquiv (X.dualGraphEdgeEquiv p e₂) i₂]
      exact congrArg (X.singularLocus K).blowupToBase heq
    obtain rfl : e₁ = e₂ := (X.dualGraphEdgeEquiv p).injective (Subtype.ext heval)
    exact Prod.ext rfl ((X.branchPointEquiv _).injective (Subtype.ext heq))
  let S : Finset (G.Edge × Fin 2) := Finset.univ.filter fun h ↦ G.endpoint h.1 h.2 = v
  have himg : φ '' (S : Set (G.Edge × Fin 2)) =
      (X.dualGraphVertexEquiv p v : Set _) ∩
        (X.singularLocus K).blowupToBase ⁻¹' (X.singularLocus K).support := by
    ext b
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_image,
      Set.mem_inter_iff, Set.mem_preimage]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨e, i⟩, hv, rfl⟩
      refine ⟨(X.dualGraphVertexEquiv_endpoint_eq_iff p e i _).mp (congrArg _ hv), ?_⟩
      rw [X.support_singularLocus_eq_compl_smoothLocus]
      exact (X.blowupToBase_branchPointEquiv (X.dualGraphEdgeEquiv p e) i).symm ▸
        (X.dualGraphEdgeEquiv p e).property
    · rintro ⟨hbv, hbSing⟩
      rw [X.support_singularLocus_eq_compl_smoothLocus] at hbSing
      obtain ⟨e, i, rfl⟩ := X.exists_branchPointEquiv_eq_of_notMem_smoothLocus p hbSing
      exact ⟨(e, i), (X.dualGraphVertexEquiv p).injective
        ((X.dualGraphVertexEquiv_endpoint_eq_iff p e i _).mpr hbv), rfl⟩
  rw [G.valence_def, ← himg, Set.ncard_image_of_injective _ hφ_inj, Set.ncard_coe_finset]

/-! ### Smooth curves -/

section Smooth

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of K))]

/-- The dual graph of a smooth prestable curve has no edges. -/
theorem isEmpty_edge_dualGraph_of_smooth : IsEmpty (X.dualGraph p).Edge := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of K))
  refine ⟨fun e ↦ ?_⟩
  let x : X := (X.dualGraphEdgeEquiv p e).val
  have hx : x ∈ (X ↘ Spec (.of K)).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  exact (X.dualGraphEdgeEquiv p e).property hx

/-- The dual graph of a smooth prestable curve has a unique vertex. -/
theorem subsingleton_vertex_dualGraph_of_smooth : Subsingleton (X.dualGraph p).Vertex :=
  have := X.isEmpty_edge_dualGraph_of_smooth p
  ⟨fun v w ↦ ((X.dualGraph p).eq_of_forall_endpoint_zero_eq_iff (v := v) isEmptyElim w).symm⟩

/-- The dual graph of a smooth prestable curve has first Betti number zero. -/
@[simp]
theorem firstBetti_dualGraph_of_smooth : (X.dualGraph p).firstBetti = 0 := by
  have := X.isEmpty_edge_dualGraph_of_smooth p
  have := X.subsingleton_vertex_dualGraph_of_smooth p
  set G := X.dualGraph p
  let := G.vertexFintype; let := G.edgeFintype; let := G.vertexNonempty
  have hadd := G.firstBetti_add_card_vertex
  rw [Fintype.card_eq_zero (α := G.Edge), Fintype.card_eq_one_iff.mpr
    ⟨Classical.arbitrary G.Vertex, fun w ↦ Subsingleton.elim w _⟩] at hadd
  omega

/-- For a smooth prestable curve, the combinatorial arithmetic genus of `X.dualGraph p` equals
`X.genus K`. -/
@[simp]
theorem arithmeticGenus_dualGraph_of_smooth :
    (X.dualGraph p).arithmeticGenus = X.genus K := by
  have := X.isEmpty_edge_dualGraph_of_smooth p
  set G := X.dualGraph p
  let := G.vertexNonempty
  let v : G.Vertex := Classical.arbitrary G.Vertex
  -- With no edges, `2 * G.arithmeticGenus = 2 * G.genus v`, and `X^ν_v ⟶ X^ν ⟶ X` is an `IsIso`.
  have htwo := G.two_mul_arithmeticGenus_of_forall_endpoint_zero_eq_iff (v := v) isEmptyElim
  have hval : G.valence v = 0 := G.valence_eq_zero_iff.mpr isEmptyElim
  have hgen : G.arithmeticGenus = G.genus v := by omega
  let v' := X.dualGraphVertexEquiv p v
  have := X.isIso_blowupComponent_ι_of_smooth v'
  let f : (X.blowupComponent v').toScheme ⟶ X :=
    (X.blowupComponent v').ι ≫ (X.singularLocus K).blowupToBase
  have : f.IsOver (Spec (.of K)) := ⟨rfl⟩
  rw [hgen, X.dualGraph_genus p v]
  exact TauCeti.AlgebraicGeometry.genus_eq_of_isIso K f

end Smooth

end Prestable

/-! ### Geometric rational tails and rational bridges -/

section RationalTailsBridgesDef

variable (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [IsProper (X ↘ Spec (.of K))]

/-- A component `v` of `Bl X` is a **geometric rational tail** if it has genus `0`, no self-nodes
(`blowupToBase` is injective on `v`), and its image in `X` meets the union of the remaining
irreducible components of `X` in a single point. -/
def IsRationalTail (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) : Prop :=
  letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
  haveI := X.isCurveOver_blowupComponent_of_atWorstNodal hnodal v
  let E := X.blowupComponentEquiv K hnodal v
  (X.blowupComponent v).toScheme.genus K = 0 ∧
    Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup) ∧
    ((E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E').ncard = 1

variable {K} in
/-- Restatement of the definition of a geometric rational tail. -/
theorem isRationalTail_iff (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    letI := X.isCurveOver_blowupComponent_of_atWorstNodal hnodal v
    X.IsRationalTail K hnodal v ↔
      (X.blowupComponent v).toScheme.genus K = 0 ∧
        Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup) ∧
        (((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X) ∩
          ⋃ E' ∈ irreducibleComponents X \
            {((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X)}, E').ncard =
          1 :=
  Iff.rfl

/-- A component `v` of `Bl X` is a **geometric rational bridge** if it has genus `0`, no self-nodes
(`blowupToBase` is injective on `v`), and its image in `X` meets the union of the remaining
irreducible components of `X` in two points. -/
def IsRationalBridge (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) : Prop :=
  letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
  haveI := X.isCurveOver_blowupComponent_of_atWorstNodal hnodal v
  let E := X.blowupComponentEquiv K hnodal v
  (X.blowupComponent v).toScheme.genus K = 0 ∧
    Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup) ∧
    ((E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E').ncard = 2

variable {K} in
/-- Restatement of the definition of a geometric rational bridge. -/
theorem isRationalBridge_iff (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    letI := X.isRegular_blowup_singularLocus hnodal
    letI := X.isCurveOver_blowupComponent_of_atWorstNodal hnodal v
    X.IsRationalBridge K hnodal v ↔
      (X.blowupComponent v).toScheme.genus K = 0 ∧
        Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup) ∧
        (((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X) ∩
          ⋃ E' ∈ irreducibleComponents X \
            {((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X)}, E').ncard =
          2 :=
  Iff.rfl

end RationalTailsBridgesDef

section RationalTailsBridges

variable {K : Type u} [Field K] [IsSepClosed K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- When `blowupToBase` is injective on `v`, it maps `v ∩ ν ⁻¹' Sing(X/K)` onto the intersection of
`ν '' v` with the union of the remaining irreducible components of `X`. -/
theorem image_blowupToBase_inter_preimage_singularLocus_of_injOn
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup}
    (hinj : letI := hnodal.syntomic
      Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup)) :
    letI := hnodal.syntomic; let E := X.blowupComponentEquiv K hnodal v
    (X.singularLocus K).blowupToBase ''
        ((v : Set (X.singularLocus K).blowup) ∩
          (X.singularLocus K).blowupToBase ⁻¹' (X.singularLocus K).support) =
      (E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E' := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let ν := (X.singularLocus K).blowupToBase
  let E := X.blowupComponentEquiv K hnodal v; ext x
  simp only [mem_image, mem_inter_iff, mem_preimage, mem_iUnion, mem_sdiff, mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · -- Over a node `ν y`, the second branch point `z ≠ y` lies on a distinct component `w ≠ v`.
    rintro ⟨y, ⟨hyv, hxSing⟩, rfl⟩
    refine ⟨(X.coe_blowupComponentEquiv hnodal v).symm ▸ ⟨y, hyv, rfl⟩, ?_⟩
    have hcard : (ν ⁻¹' {ν y}).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]
      exact X.natCard_preimage_blowupToBase_singularLocus_eq_two_of_mem_support hnodal hxSing
    obtain ⟨z, hz, hzy⟩ := Set.exists_ne_of_one_lt_ncard (s := ν ⁻¹' {ν y}) (by omega) y
    have hzv : z ∉ (v : Set _) := fun hzv ↦ hzy (hinj hzv hyv (mem_singleton_iff.mp hz))
    let w := irreducibleComponentOf z
    have hwv : w ≠ v := fun hw ↦ hzv (hw ▸ mem_irreducibleComponentOf z)
    exact ⟨(X.blowupComponentEquiv K hnodal w : Set X),
      ⟨(X.blowupComponentEquiv K hnodal w).property,
        fun hEq ↦ hwv ((X.blowupComponentEquiv K hnodal).injective (Subtype.ext hEq))⟩,
      (X.coe_blowupComponentEquiv hnodal w).symm ▸
        ⟨z, mem_irreducibleComponentOf z, mem_singleton_iff.mp hz⟩⟩
  · -- Any point lying on two distinct components of `X` cannot be smooth, hence lies in `Sing`.
    rintro ⟨hxE, E', ⟨hE', hE'ne⟩, hxE'⟩
    obtain ⟨y, hyv, rfl⟩ : x ∈ ν '' (v : Set _) := X.coe_blowupComponentEquiv hnodal v ▸ hxE
    refine ⟨y, ⟨hyv, ?_⟩, rfl⟩
    rw [X.support_singularLocus_eq_compl_smoothLocus, mem_compl_iff]
    exact fun hyU ↦ hE'ne (congrArg Subtype.val <|
      (existsUnique_mem_irreducibleComponents_of_mem_smoothLocus hnodal hyU).unique
        (y₁ := ⟨E', hE'⟩) (y₂ := E) hxE' hxE)

variable [PrestableFamily (X ↘ Spec (.of K))] {ι : Type v} (p : ι → (X ↘ Spec (.of K)).smoothLocus)

/-- `blowupToBase` is injective on `v` iff no edge of `X.dualGraph p` is a loop at `v`. -/
theorem injOn_blowupToBase_iff_forall_ends_ne_self (v : (X.dualGraph p).Vertex) :
    Set.InjOn (X.singularLocus K).blowupToBase
        (X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup) ↔
      ∀ e, (X.dualGraph p).ends e ≠ s(v, v) := by
  let ν := (X.singularLocus K).blowupToBase
  simp only [ne_eq, X.ends_dualGraph_eq_self_iff p v]
  refine ⟨fun hinj e hsub ↦ ?_, fun hnoloop y₁ hy₁ y₂ hy₂ heq ↦ ?_⟩
  · let b₀ := X.branchPointEquiv (X.dualGraphEdgeEquiv p e) 0
    let b₁ := X.branchPointEquiv (X.dualGraphEdgeEquiv p e) 1
    have h01 : b₀ ≠ b₁ := (X.branchPointEquiv _).injective.ne (by decide)
    exact h01 (Subtype.ext (hinj (hsub b₀.property) (hsub b₁.property)
      (b₀.property.trans b₁.property.symm)))
  · by_cases hU : ν y₁ ∈ (X ↘ Spec (.of K)).smoothLocus
    · exact X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus heq hU
    · obtain ⟨e, i₁, rfl⟩ := X.exists_branchPointEquiv_eq_of_notMem_smoothLocus p hU
      obtain ⟨i₂, rfl⟩ := X.exists_branchPointEquiv_eq
        (heq.symm.trans (X.blowupToBase_branchPointEquiv (X.dualGraphEdgeEquiv p e) i₁))
      by_contra hne
      have hi : i₁ ≠ i₂ := fun h ↦ hne (by rw [h])
      refine hnoloop e fun b hb ↦ ?_
      obtain ⟨i, rfl⟩ := X.exists_branchPointEquiv_eq hb
      fin_cases i <;> fin_cases i₁ <;> fin_cases i₂ <;> simp_all

/-- For `v` without self-nodes, `valence v` equals the number of intersection points of `ν '' v`
with the union of the remaining irreducible components of `X`. -/
theorem valence_dualGraph_eq_ncard_inter_other_components_of_injOn
    {v : (X.dualGraph p).Vertex}
    (hinj : Set.InjOn (X.singularLocus K).blowupToBase
      (X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup)) :
    let E := X.blowupComponentEquiv K PrestableFamily.atWorstNodalOfRelativeDimensionOne
      (X.dualGraphVertexEquiv p v)
    (X.dualGraph p).valence v =
      ((E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E').ncard := by
  dsimp only
  rw [X.valence_dualGraph p v,
    ← X.image_blowupToBase_inter_preimage_singularLocus_of_injOn _ hinj]
  exact (hinj.mono inter_subset_left).ncard_image.symm

/-- Equivalence between combinatorial and geometric rational tails. -/
theorem dualGraph_isRationalTail_iff (v : (X.dualGraph p).Vertex) :
    (X.dualGraph p).IsRationalTail v ↔
      X.IsRationalTail K PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (X.dualGraphVertexEquiv p v) := by
  let G := X.dualGraph p
  let := G.edgeFintype; let := G.edgeDecidableEq; let := G.vertexDecidableEq
  rw [G.isRationalTail_iff, X.isRationalTail_iff, dualGraph_genus]
  refine and_congr_right fun _ ↦ ⟨fun hval ↦ ?_, fun ⟨hinj, hcard⟩ ↦
    (X.valence_dualGraph_eq_ncard_inter_other_components_of_injOn p hinj).trans hcard⟩
  have hinj : Set.InjOn (X.singularLocus K).blowupToBase
      (X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup) := by
    rw [X.injOn_blowupToBase_iff_forall_ends_ne_self p v]; intro e he
    rw [G.ends_def, Sym2.eq_iff, or_self] at he
    have hsub : ({(e, 0), (e, 1)} : Finset (G.Edge × Fin 2)) ⊆
        Finset.univ.filter fun h ↦ G.endpoint h.1 h.2 = v := by
      simp [Finset.insert_subset_iff, he.1, he.2]
    have hle : 2 ≤ G.valence v := by rw [G.valence_def]; simpa using Finset.card_le_card hsub
    omega
  exact ⟨hinj,
    (X.valence_dualGraph_eq_ncard_inter_other_components_of_injOn p hinj).symm.trans hval⟩

/-- Equivalence between combinatorial and geometric rational bridges. -/
theorem dualGraph_isRationalBridge_iff (v : (X.dualGraph p).Vertex) :
    (X.dualGraph p).IsRationalBridge v ↔
      X.IsRationalBridge K PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (X.dualGraphVertexEquiv p v) := by
  let G := X.dualGraph p
  rw [G.isRationalBridge_iff, G.forall_endpoint_one_ne_iff,
    ← X.injOn_blowupToBase_iff_forall_ends_ne_self p v, X.isRationalBridge_iff, dualGraph_genus]
  refine and_congr_right fun _ ↦ ⟨fun ⟨hval, hinj⟩ ↦ ⟨hinj, ?_⟩, fun ⟨hinj, hcard⟩ ↦ ⟨?_, hinj⟩⟩
  · rwa [← X.valence_dualGraph_eq_ncard_inter_other_components_of_injOn p hinj]
  · rwa [X.valence_dualGraph_eq_ncard_inter_other_components_of_injOn p hinj]

/-- Geometric semistability criterion for an unpointed prestable curve of arithmetic genus `≥ 1`. -/
theorem dualGraph_isSemistable_iff [Fintype ι] [IsEmpty ι]
    (hg : 1 ≤ (X.dualGraph p).arithmeticGenus) :
    (X.dualGraph p).IsSemistable ↔
      ∀ v, ¬ X.IsRationalTail K PrestableFamily.atWorstNodalOfRelativeDimensionOne v := by
  rw [(X.dualGraph p).isSemistable_iff_forall_not_isRationalTail hg]
  simp only [X.dualGraph_isRationalTail_iff p]
  exact (X.dualGraphVertexEquiv p).forall_congr_left

/-- Geometric stability criterion for an unpointed prestable curve of arithmetic genus `≥ 2`. -/
theorem dualGraph_isStable_iff [Fintype ι] [IsEmpty ι]
    (hg : 2 ≤ (X.dualGraph p).arithmeticGenus) :
    (X.dualGraph p).IsStable ↔
      ∀ v, ¬ X.IsRationalTail K PrestableFamily.atWorstNodalOfRelativeDimensionOne v ∧
        ¬ X.IsRationalBridge K PrestableFamily.atWorstNodalOfRelativeDimensionOne v := by
  rw [(X.dualGraph p).isStable_iff_forall_not_isRationalTail_and_not_isRationalBridge_of_isEmpty hg]
  simp only [X.dualGraph_isRationalTail_iff p, X.dualGraph_isRationalBridge_iff p]
  exact (X.dualGraphVertexEquiv p).forall_congr_left

end RationalTailsBridges

end AlgebraicGeometry.Scheme
