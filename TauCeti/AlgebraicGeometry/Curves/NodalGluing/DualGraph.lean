/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Connected
public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Iso
public import TauCeti.Data.Set.Card

/-!
# The dual graph of a glued nodal curve

A marked nodal curve presented by flag-pair data `d : FlagPairData ι Flag X` with marks
`m : Marking d L` has a dual graph: its vertices are the normalization components `X i`, its
edges are the flag pairs (the nodes), the two endpoints of an edge are the components carrying the
two branches of the node, and each mark is attached to the component on which it lies. Labelling
the vertices by genera `g : ι → ℕ` of the components gives a `TauCeti.DualGraph`. The connectivity
which `DualGraph` requires is that of the glued curve: for connected nonempty components the glued
curve is connected exactly when the graph is (`connectedSpace_gluedCurve_iff`).

This file builds that graph, `NodalGluing.dualGraph g m`, and reads its numerical invariants off
the curve. The valence of a component is the number of flag points on it, its number of markings
is the number of marks on it, and the number of edges is the number of nodes of the glued curve.
Consequently the arithmetic genus of the graph is `∑ᵢ gᵢ + #nodes - #components + 1`, and the
graph is stable exactly when every component satisfies `2 gᵢ - 2 + nᵢ > 0`, where `nᵢ` counts the
special points of `X i`: its flag points and its marks. An isomorphism of marked nodal curves
preserving every label and the genera induces an isomorphism of dual graphs, compatibly with
identities, composition and inverses.

The genera `g` are an input: this file relates the combinatorics of the curve to its dual graph,
and leaves open which genus invariant of a compact Riemann surface is used to label the vertices.

## Main definitions

* `NodalGluing.dualGraph g m`: the dual graph of the marked nodal curve with marks `m`, with
  vertex genera `g`.
* `NodalGluing.Iso.toDualGraphIso`: the isomorphism of dual graphs induced by an isomorphism of
  nodal curves preserving the marks and the genera.

## Main results

* `NodalGluing.valence_dualGraph`, `NodalGluing.numMarkings_dualGraph`: the valence and the
  number of markings of a vertex count the flag points and the marks on the component.
* `NodalGluing.card_edge_dualGraph`: the edges are counted by the nodes of the glued curve.
* `NodalGluing.arithmeticGenus_dualGraph_add_card`: the genus formula
  `pₐ + #components = ∑ᵢ gᵢ + #nodes + 1`.
* `NodalGluing.logCanonicalDegree_dualGraph`, `NodalGluing.isStable_dualGraph_iff`: the
  log-canonical degree of a vertex is `2 gᵢ - 2 + nᵢ`, so stability of the graph is the
  componentwise inequality `2 gᵢ - 2 + nᵢ > 0`.

## References

* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*
  (Grundlehren der mathematischen Wissenschaften 331, Springer, 2011), Chapter X, §2, for the dual
  graph of a pointed nodal curve, its arithmetic genus and stability.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, §3, for nodal Riemann surfaces presented by their nodal
  pairs and for stability as `2 gᵢ - 2 + nᵢ > 0` on every component.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

universe u v

variable {ι Flag : Type u} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ConnectedSpace (X i)]
  {d : FlagPairData ι Flag X} [ConnectedSpace (GluedCurve d)] {L : Type v}

variable [Fintype ι] [DecidableEq ι] [Fintype Flag] [DecidableEq Flag]

/-- **The dual graph of a marked nodal curve.** Its vertices are the normalization components,
labelled by the genera `g`, its edges are the flag pairs, the edge `f` joins the component
`d.fst f` carrying its first branch to the component `d.snd f` carrying its second branch, and the
mark `l` lies on the component of `m.point l`. -/
abbrev dualGraph (g : ι → ℕ) (m : Marking d L) : DualGraph.{u} L where
  Vertex := ι
  vertexNonempty := ((connectedSpace_gluedCurve_iff d).mp ‹_›).1
  Edge := Flag
  endpoint f := ![d.fst f, d.snd f]
  genus := g
  marking l := (m.point l).1
  connected := reflTransGen_of_connectedSpace d

variable (g : ι → ℕ) (m : Marking d L)

/-- The first endpoint of an edge is the component carrying the first branch of the node. -/
@[simp]
theorem endpoint_dualGraph_zero (f : Flag) : (dualGraph g m).endpoint f 0 = d.fst f :=
  rfl

/-- The second endpoint of an edge is the component carrying the second branch of the node. -/
@[simp]
theorem endpoint_dualGraph_one (f : Flag) : (dualGraph g m).endpoint f 1 = d.snd f :=
  rfl

/-- The genus of a vertex is the given genus of its component. -/
@[simp]
theorem genus_dualGraph (i : ι) : (dualGraph g m).genus i = g i :=
  rfl

/-- A mark lies on the component of its point in the normalization. -/
@[simp]
theorem marking_dualGraph (l : L) : (dualGraph g m).marking l = (m.point l).1 :=
  rfl

/-- The endpoint `k` of an edge is the component of the flag point selected by `k`. -/
private theorem fst_flagPoint_finTwoEquiv (f : Flag) (k : Fin 2) :
    (flagPoint d (f, finTwoEquiv k)).1 = (dualGraph g m).endpoint f k := by
  fin_cases k <;> simp [finTwoEquiv, fstPoint_def, sndPoint_def]

/-- **The valence of a vertex counts the flag points on its component.** -/
theorem valence_dualGraph (i : ι) :
    (dualGraph g m).valence i = (Sigma.mk i ⁻¹' flagPointSet d).ncard := by
  let e := Equiv.prodCongr (Equiv.refl Flag) finTwoEquiv
  rw [flagPointSet_eq_range, ← e.surjective.range_comp,
    ncard_preimage_sigmaMk_range ((flagPoint_injective d).comp e.injective),
    DualGraph.valence_def, ← ncard_coe_finset]
  simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  congr 1
  ext ⟨f, k⟩
  exact Iff.of_eq (congrArg (· = i) (fst_flagPoint_finTwoEquiv g m f k)).symm

/-- **The number of markings of a vertex counts the marks on its component.** -/
theorem numMarkings_dualGraph [Fintype L] (i : ι) :
    (dualGraph g m).numMarkings i = (Sigma.mk i ⁻¹' range m.point).ncard := by
  rw [ncard_preimage_sigmaMk_range m.point_injective, DualGraph.numMarkings_def,
    ← ncard_coe_finset]
  simp only [Finset.coe_filter, Finset.mem_univ, true_and]

/-- **The edges of the dual graph are counted by the nodes of the glued curve.** -/
theorem card_edge_dualGraph : Fintype.card (dualGraph g m).Edge = (nodeSet d).ncard := by
  rw [nodeSet_eq_range_nodeOfFlag, ncard_range_of_injective (nodeOfFlag_injective d),
    Nat.card_eq_fintype_card]

/-- **The genus formula.** The arithmetic genus `pₐ = ∑ᵢ gᵢ + b₁` of the dual graph satisfies
`pₐ + #components = ∑ᵢ gᵢ + #nodes + 1`. -/
theorem arithmeticGenus_dualGraph_add_card :
    (dualGraph g m).arithmeticGenus + Fintype.card ι = ∑ i, g i + (nodeSet d).ncard + 1 := by
  rw [← card_edge_dualGraph g m]
  exact (dualGraph g m).arithmeticGenus_add_card_vertex

/-- **The log-canonical degree of a vertex** is `2 gᵢ - 2 + nᵢ`, where `nᵢ` is the number of
special points of the component `X i`: its flag points and its marks. -/
theorem logCanonicalDegree_dualGraph [Fintype L] (i : ι) :
    (dualGraph g m).logCanonicalDegree i =
      2 * g i - 2 + (Sigma.mk i ⁻¹' (flagPointSet d ∪ range m.point)).ncard := by
  have hdisj : Disjoint (flagPointSet d) (range m.point) := by
    rw [disjoint_left]
    rintro _ hx ⟨l, rfl⟩
    exact m.point_notMem_flagPointSet l hx
  have hfin (S : Set (Σ i, X i)) (hS : S.Finite) : (Sigma.mk i ⁻¹' S).Finite :=
    hS.preimage sigma_mk_injective.injOn
  rw [preimage_union, ncard_union_eq (hdisj.preimage _) (hfin _ (flagPointSet_finite d))
    (hfin _ (finite_range _)), DualGraph.logCanonicalDegree_def, valence_dualGraph,
    numMarkings_dualGraph, genus_dualGraph]
  push_cast
  ring

/-- **Stability of the dual graph is componentwise stability.** The dual graph is stable exactly
when every component `X i` satisfies `2 gᵢ - 2 + nᵢ > 0`, where `nᵢ` is the number of its flag
points and marks. -/
theorem isStable_dualGraph_iff [Fintype L] :
    (dualGraph g m).IsStable ↔
      ∀ i, 0 < 2 * (g i : ℤ) - 2 + (Sigma.mk i ⁻¹' (flagPointSet d ∪ range m.point)).ncard := by
  simp only [DualGraph.isStable_iff, logCanonicalDegree_dualGraph]

/-! ### Isomorphisms -/

namespace Iso

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [∀ i, ChartedSpace H (X i)]
  {ι' Flag' : Type u} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ConnectedSpace (X' i)] [∀ i, ChartedSpace H (X' i)]
  [Fintype ι'] [DecidableEq ι'] [Fintype Flag'] [DecidableEq Flag']
  {d' : FlagPairData ι' Flag' X'} [ConnectedSpace (GluedCurve d')]
  {ι'' Flag'' : Type u} {X'' : ι'' → Type*} [∀ i, TopologicalSpace (X'' i)]
  [∀ i, ConnectedSpace (X'' i)] [∀ i, ChartedSpace H (X'' i)]
  [Fintype ι''] [DecidableEq ι''] [Fintype Flag''] [DecidableEq Flag'']
  {d'' : FlagPairData ι'' Flag'' X''} [ConnectedSpace (GluedCurve d'')]
  {g : ι → ℕ} {g' : ι' → ℕ} {g'' : ι'' → ℕ}
  {m : Marking d L} {m' : Marking d' L} {m'' : Marking d'' L}

/-- An isomorphism carries the endpoints of a node to the endpoints of its image node, possibly
exchanging them. -/
theorem ends_dualGraph_edgeEquiv (e : Iso I n d d') (f : Flag) :
    (dualGraph g' m').ends (e.edgeEquiv f) = ((dualGraph g m).ends f).map e.vertexEquiv := by
  have h₀ := e.fst_flagPoint_branchEquiv (f, false)
  have h₁ := e.fst_flagPoint_branchEquiv (f, true)
  have hswap := e.branchEquiv_swap (f, false)
  have hf' := e.edgeEquiv_apply f false
  rcases hb : e.branchEquiv (f, false) with ⟨f', b⟩
  rw [hb] at h₀ hswap hf'
  simp only [Bool.not_false] at hswap
  rw [hswap] at h₁
  rw [hf', DualGraph.ends_def, DualGraph.ends_def, Sym2.map_mk, endpoint_dualGraph_zero,
    endpoint_dualGraph_zero, endpoint_dualGraph_one, endpoint_dualGraph_one]
  cases b <;>
    simp only [flagPoint_false, flagPoint_true, fstPoint_def, sndPoint_def, Bool.not_false,
      Bool.not_true] at h₀ h₁
  · rw [h₀, h₁]
  · rw [h₀, h₁, Sym2.eq_swap]

/-- **The isomorphism of dual graphs induced by an isomorphism of marked nodal curves.** An
isomorphism `e` of nodal curves carrying every mark of `m` to the mark of `m'` with the same label,
and every component of genus `g i` to one of genus `g' (e.vertexEquiv i) = g i`, induces the
isomorphism of dual graphs given by its maps of components and of nodes. -/
def toDualGraphIso (e : Iso I n d d') (hg : ∀ i, g' (e.vertexEquiv i) = g i)
    (hm : ∀ l, e (m.point l) = m'.point l) : (dualGraph g m).Iso (dualGraph g' m') where
  vertexEquiv := e.vertexEquiv
  edgeEquiv := e.edgeEquiv
  ends_edgeEquiv := e.ends_dualGraph_edgeEquiv
  genus_vertexEquiv := hg
  vertexEquiv_marking l := by
    rw [marking_dualGraph, marking_dualGraph, ← hm, fst_apply]

variable (e : Iso I n d d') (hg : ∀ i, g' (e.vertexEquiv i) = g i)
  (hm : ∀ l, e (m.point l) = m'.point l)

/-- The induced isomorphism of dual graphs acts on vertices by the component map. -/
@[simp]
theorem toDualGraphIso_vertexEquiv : (e.toDualGraphIso hg hm).vertexEquiv = e.vertexEquiv :=
  (rfl)

/-- The induced isomorphism of dual graphs acts on edges by the node map. -/
@[simp]
theorem toDualGraphIso_edgeEquiv : (e.toDualGraphIso hg hm).edgeEquiv = e.edgeEquiv :=
  (rfl)

/-- The identity isomorphism of curves induces the identity isomorphism of dual graphs. -/
@[simp]
theorem toDualGraphIso_refl (hg : ∀ i, g ((Iso.refl I n d).vertexEquiv i) = g i)
    (hm : ∀ l, Iso.refl I n d (m.point l) = m.point l) :
    (Iso.refl I n d).toDualGraphIso hg hm = DualGraph.Iso.refl (dualGraph g m) := by
  ext <;> simp

/-- The isomorphism of dual graphs induced by a composite is the composite of the induced
isomorphisms. -/
theorem toDualGraphIso_trans (e' : Iso I n d' d'') (hg' : ∀ i, g'' (e'.vertexEquiv i) = g' i)
    (hm' : ∀ l, e' (m'.point l) = m''.point l)
    (hg'' : ∀ i, g'' ((e.trans e').vertexEquiv i) = g i)
    (hm'' : ∀ l, e.trans e' (m.point l) = m''.point l) :
    (e.trans e').toDualGraphIso hg'' hm'' =
      (e.toDualGraphIso hg hm).trans (e'.toDualGraphIso hg' hm') := by
  ext <;> simp [DualGraph.Iso.trans_vertexEquiv, DualGraph.Iso.trans_edgeEquiv]

/-- The isomorphism of dual graphs induced by the inverse is the inverse of the induced
isomorphism. -/
theorem toDualGraphIso_symm (hg' : ∀ i, g (e.symm.vertexEquiv i) = g' i)
    (hm' : ∀ l, e.symm (m'.point l) = m.point l) :
    e.symm.toDualGraphIso hg' hm' = (e.toDualGraphIso hg hm).symm := by
  ext <;> simp [DualGraph.Iso.symm_vertexEquiv, DualGraph.Iso.symm_edgeEquiv]

end Iso

end NodalGluing

end TauCeti
