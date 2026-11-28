/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Basic
public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization
public import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Curves.Normalization
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
`X^ν` lies on exactly one of them, `TauCeti.irreducibleComponentOf b`. Since `ν` is finite with
regular source, and an isomorphism over the dense smooth locus, `X^ν` is the normalization of `X`
and its components are the normalizations of the components of `X`; this identification is not
used here.

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

The graph is connected because `X` is: the images in `X` of the components reachable from a given
one and of the remaining components are closed, cover `X`, and can only meet at a node joining a
reachable component to a remaining one.

The arithmetic genus formula `pₐ(X) = Σ_v g_v + b₁` relating this graph to `X` is not proved
here.

## Main definitions

* `AlgebraicGeometry.Scheme.branchPointEquiv`: the two points over a node, labelled by `Fin 2`.
* `AlgebraicGeometry.Scheme.blowupComponent`: an irreducible component of the blowup of a
  prestable curve along its singular subscheme, as an open subscheme.
* `AlgebraicGeometry.Scheme.dualGraph`: the dual graph of a prestable curve over a separably
  closed field with markings at smooth points.
* `AlgebraicGeometry.Scheme.dualGraphVertexEquiv` and `AlgebraicGeometry.Scheme.dualGraphEdgeEquiv`:
  its vertices are the components of the blowup, and its edges are the nodes.

## Main results

* `AlgebraicGeometry.Scheme.isIntegral_blowupComponent`,
  `AlgebraicGeometry.Scheme.isProper_blowupComponent` and
  `AlgebraicGeometry.Scheme.topologicalKrullDim_blowupComponent_le_one`: each component of the
  blowup is an integral scheme, proper over `K`, of dimension at most one.
* `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_endpoint` and
  `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_endpoint_eq_iff`: the endpoints of an edge are
  the components carrying the two points over the node.
* `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_marking` and
  `AlgebraicGeometry.Scheme.dualGraphVertexEquiv_marking_eq_iff`: a marking is attached to the
  component carrying the point over it.
* `AlgebraicGeometry.Scheme.dualGraph_genus`: the genus of a vertex is the genus of its component.
* `AlgebraicGeometry.Scheme.dualGraph_comp`: composing the marked points with a map of index
  types reindexes the markings.

## References

* [The Stacks Project, Section 53.19, Nodal curves](https://stacks.math.columbia.edu/tag/0C46).
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, Section 2, for the dual graph of a pointed nodal curve.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [PrestableFamily (X ↘ Spec (.of K))]

/-! ### The components of the blowup -/

variable (K) in
private theorem atWorstNodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)) :=
  PrestableFamily.atWorstNodalOfRelativeDimensionOne

/-- An irreducible component of the blowup of a prestable curve along its singular subscheme, as
an open subscheme: the blowup is regular, so its irreducible components are disjoint and open. Each
is an integral scheme, proper over `K`, of dimension at most one. -/
def blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.singularLocus K).blowup.Opens :=
  ⟨v, isOpen_of_mem_irreducibleComponents_of_unique_minimalPrime_stalk (fun _ ↦ inferInstance)
    v.property⟩

@[simp]
theorem coe_blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.blowupComponent v : Set (X.singularLocus K).blowup) = v :=
  (rfl)

/-- A component of the blowup is a scheme over `K` through the blowup morphism to the curve. -/
instance blowupComponentOver (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.blowupComponent v).toScheme.Over (Spec (.of K)) :=
  ⟨(X.blowupComponent v).ι ≫ (X.singularLocus K).blowupToBase ≫ X ↘ Spec (.of K)⟩

/-- The structure morphism of a component of the blowup to `Spec K` is the composite of its
inclusion, the blowup morphism and the structure morphism of the curve. -/
@[simp]
theorem blowupComponent_over (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.blowupComponent v).toScheme ↘ Spec (.of K) =
      (X.blowupComponent v).ι ≫ (X.singularLocus K).blowupToBase ≫ X ↘ Spec (.of K) :=
  (rfl)

/-- A component of the blowup is an integral scheme: it is irreducible, and reduced as an open
subscheme of a regular scheme. -/
instance isIntegral_blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    IsIntegral (X.blowupComponent v).toScheme := by
  have : IsReduced (X.singularLocus K).blowup := isReduced_of_isReduced_stalk _
  have : IrreducibleSpace (X.blowupComponent v) := Subtype.irreducibleSpace v.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A component of the blowup is proper over `K`: it is also closed in the blowup, which is finite
over the curve. -/
instance isProper_blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    IsProper ((X.blowupComponent v).toScheme ↘ Spec (.of K)) := by
  have := X.isFinite_blowupToBase_singularLocus (atWorstNodal K X)
  have : IsClosedImmersion (X.blowupComponent v).ι :=
    .of_isPreimmersion _ (by
      rw [Opens.range_ι]; exact isClosed_of_mem_irreducibleComponents _ v.property)
  rw [blowupComponent_over]
  infer_instance

/-- A component of the blowup has dimension at most that of the curve, which is at most one. -/
theorem topologicalKrullDim_blowupComponent_le_one
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    topologicalKrullDim (X.blowupComponent v) ≤ 1 := by
  have := X.isFinite_blowupToBase_singularLocus (atWorstNodal K X)
  have hX : topologicalKrullDim X ≤ 1 :=
    ((familyOfCurves_iff_of_field (X ↘ Spec (.of K))).mp inferInstance).2
  exact
    ((X.blowupComponent v).ι ≫ (X.singularLocus K).blowupToBase).topologicalKrullDim_le.trans hX

/-- The cohomology of the structure sheaf of a component of the blowup is finite-dimensional: the
component is a proper integral scheme of dimension at most one. -/
instance (v : irreducibleComponents (X.singularLocus K).blowup) (n : ℕ) :
    FiniteDimensional K (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (InvertibleSheaf.trivial (X.blowupComponent v).toScheme).obj n) :=
  Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one K
    (X.topologicalKrullDim_blowupComponent_le_one v) n

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

theorem blowupToBase_branchPointEquiv (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ))
    (i : Fin 2) : (X.singularLocus K).blowupToBase (X.branchPointEquiv x i) = x.val :=
  (X.branchPointEquiv x i).property

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
    obtain ⟨i, hi⟩ := (X.branchPointEquiv e).surjective ⟨b, rfl⟩
    obtain ⟨j, hj⟩ := (X.branchPointEquiv e).surjective ⟨b', h.symm⟩
    have hi' : (X.branchPointEquiv e i : (X.singularLocus K).blowup) = b := congr(($hi).val)
    have hj' : (X.branchPointEquiv e j : (X.singularLocus K).blowup) = b' := congr(($hj).val)
    rw [← hi', ← hj']
    by_cases hij : i = j
    · exact .inl (by rw [hij])
    · right
      refine ⟨e, ?_⟩
      fin_cases i <;> fin_cases j <;> simp_all

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
  X.dualGraphVertexEquiv_marking p i hb ▸
    irreducibleComponentOf_eq_iff

/-- The genus of a vertex of the dual graph is the genus of its component of the blowup. -/
@[simp]
theorem dualGraph_genus (v : (X.dualGraph p).Vertex) :
    (X.dualGraph p).genus v = (X.blowupComponent (X.dualGraphVertexEquiv p v)).toScheme.genus K :=
  (rfl)

end AlgebraicGeometry.Scheme
