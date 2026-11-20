/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category

/-!
# The dual graph of a pointed prestable curve

Let `P` be an `n`-pointed prestable curve over `Spec K` for a separably closed field `K`. Its total
space `P.total` is a proper connected nodal curve over `K` and its `n` markings are sections landing
in the smooth locus of `P.toBase`. Specializing `AlgebraicGeometry.Scheme.dualGraph` to `P.total`
and `P.marking` yields the combinatorial dual graph `P.dualGraph : DualGraph (Fin n)`.

This file packages the dual graph API in the category of pointed prestable curves:

* **The dual graph and its components**: `PointedPrestableFamily.dualGraph`, the equivalences
  `PointedPrestableFamily.dualGraphVertexEquiv`, `PointedPrestableFamily.dualGraphEdgeEquiv`, and
  `PointedPrestableFamily.dualGraphIrreducibleComponentsEquiv`, the normalized component curves
  `PointedPrestableFamily.normalizedComponent`, geometric characterizations of incidence, valence,
  rational tails, and rational bridges, and compatibility with `PointedPrestableFamily.reindex`
  (`PointedPrestableFamily.dualGraph_reindex` and `PointedPrestableFamily.reindexDualGraphIso`).
* **Smooth validation**: when `P.toBase` is smooth, `P.dualGraph` has first Betti number zero
  (`PointedPrestableFamily.firstBetti_dualGraph_of_smooth`) and combinatorial arithmetic genus
  equal to `P.total.genus K`
  (`PointedPrestableFamily.arithmeticGenus_dualGraph_eq_genus_of_smooth`).
* **Functoriality under pointed isomorphisms**: any isomorphism `e : P ≅ Q` of pointed prestable
  curves induces an isomorphism `PointedPrestableFamily.dualGraphIsoOfIso e` of dual graphs,
  respecting `Iso.refl`, `Iso.trans`, and `Iso.symm`, and preserving `firstBetti`,
  `arithmeticGenus`, `IsStable`, and `IsSemistable`.
* **Invariance under extensions of separably closed fields**: for any extension `L / K` of separably
  closed fields, pulling `P` back along `Spec L ⟶ Spec K` induces a canonical isomorphism of dual
  graphs (`PointedPrestableFamily.pullbackDualGraphIso`).

## References

* [The Stacks Project, Tag 0E6S](https://stacks.math.columbia.edu/tag/0E6S): prestable curves.
* [The Stacks Project, Tag 0E6X](https://stacks.math.columbia.edu/tag/0E6X): semistable curves.
* [The Stacks Project, Tag 0E73](https://stacks.math.columbia.edu/tag/0E73): stable curves.
* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks `M_{g,n}`*,
  Math. Scand. 52 (1983), 161–199, Definition 1.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.PointedPrestableFamily

universe u

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] {m n : ℕ}
  (P Q R : PointedPrestableFamily (Spec (.of K)) n)

/-- **The dual graph of an `n`-pointed prestable curve over a separably closed field.** -/
def dualGraph : DualGraph (Fin n) :=
  P.total.dualGraph
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.marking P.range_marking_subset_smoothLocus_over

/-- Canonical identification of the vertices of `P.dualGraph` with the irreducible components of
the normalization `(P.total.singularLocus K).blowup`. -/
def dualGraphVertexEquiv :
    P.dualGraph.Vertex ≃ irreducibleComponents (P.total.singularLocus K).blowup :=
  P.total.dualGraphVertexEquiv
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.marking P.range_marking_subset_smoothLocus_over

/-- Canonical identification of the edges of `P.dualGraph` with the points of the singular
subscheme `(P.total.singularLocus K).subscheme`. -/
def dualGraphEdgeEquiv :
    P.dualGraph.Edge ≃ (P.total.singularLocus K).subscheme :=
  P.total.dualGraphEdgeEquiv
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.marking P.range_marking_subset_smoothLocus_over

/-- Equivalence between vertices of `P.dualGraph` and irreducible components of `P.total`. -/
def dualGraphIrreducibleComponentsEquiv :
    P.dualGraph.Vertex ≃ irreducibleComponents P.total :=
  P.total.dualGraphIrreducibleComponentsEquiv
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.marking P.range_marking_subset_smoothLocus_over

/-- The irreducible component of `P.total` attached to a vertex `v` is the image under the
normalization morphism of the corresponding component of `(P.total.singularLocus K).blowup`. -/
@[simp]
theorem coe_dualGraphIrreducibleComponentsEquiv (v : P.dualGraph.Vertex) :
    (P.dualGraphIrreducibleComponentsEquiv v : Set P.total) =
      (P.total.singularLocus K).blowupToBase ''
        (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup) :=
  P.total.coe_dualGraphIrreducibleComponentsEquiv _ P.marking
    P.range_marking_subset_smoothLocus_over v

/-- The normalized component scheme of `P.total` corresponding to a vertex `v` of `P.dualGraph`. -/
abbrev normalizedComponent (v : P.dualGraph.Vertex) : Scheme.{u} :=
  P.total.normalizedComponent
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    (P.dualGraphVertexEquiv v)

/-- The genus of a vertex `v` in `P.dualGraph` is the cohomological genus of `P.normalizedComponent`
at `v`. -/
@[simp]
theorem genus_dualGraph (v : P.dualGraph.Vertex) :
    P.dualGraph.genus v = (P.normalizedComponent v).genus K :=
  P.total.genus_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over v

/-- Under `P.dualGraphVertexEquiv`, the `i`-th marking of `P.dualGraph` is the component of the
normalization containing the lift of `P.marking i`. -/
@[simp]
theorem dualGraphVertexEquiv_marking (i : Fin n) :
    letI := P.total.isRegular_blowup_singularLocus
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.dualGraphVertexEquiv (P.dualGraph.marking i) =
      componentOf (P.total.singularLocus K).blowup
        (P.total.blowupSingularLocusLift (P.marking i)
          (P.range_marking_subset_smoothLocus_over i) default) :=
  P.total.dualGraphVertexEquiv_marking _ P.marking P.range_marking_subset_smoothLocus_over i

/-- The `i`-th marking of `P.dualGraph` is the unique irreducible component of `P.total` containing
the marked point `P.marking i default`. -/
theorem marking_dualGraph_eq_iff (i : Fin n) (v : P.dualGraph.Vertex) :
    P.dualGraph.marking i = v ↔
      P.marking i default ∈ (P.dualGraphIrreducibleComponentsEquiv v : Set P.total) :=
  P.total.marking_dualGraph_eq_iff _ P.marking P.range_marking_subset_smoothLocus_over i v

/-- Whenever `b₀ ≠ b₁` are the two branches of `P.total` over a node `e`, the unordered pair of
endpoints of `e` in `P.dualGraph` is the pair of components containing `b₀` and `b₁`. -/
theorem ends_dualGraph_eq_of_ne (e : P.dualGraph.Edge)
    {b₀ b₁ : P.total.branchScheme K}
    (hb₀ : P.total.branchSchemeToSingularLocus K b₀ = P.dualGraphEdgeEquiv e)
    (hb₁ : P.total.branchSchemeToSingularLocus K b₁ = P.dualGraphEdgeEquiv e)
    (hne : b₀ ≠ b₁) :
    letI := P.total.isRegular_blowup_singularLocus
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.dualGraph.ends e =
      s(P.dualGraphVertexEquiv.symm
          (componentOf (P.total.singularLocus K).blowup (P.total.branchSchemeToBlowup K b₀)),
        P.dualGraphVertexEquiv.symm
          (componentOf (P.total.singularLocus K).blowup (P.total.branchSchemeToBlowup K b₁))) :=
  P.total.ends_dualGraph_eq_of_ne _ P.marking P.range_marking_subset_smoothLocus_over e hb₀ hb₁ hne

/-- A vertex `v` lies on an edge `e` of `P.dualGraph` if and only if one of the branches over `e`
lies on `v`. -/
theorem mem_ends_dualGraph_iff (v : P.dualGraph.Vertex) (e : P.dualGraph.Edge) :
    v ∈ P.dualGraph.ends e ↔
      ∃ b : P.total.branchScheme K,
        P.total.branchSchemeToSingularLocus K b = P.dualGraphEdgeEquiv e ∧
          P.total.branchSchemeToBlowup K b ∈
            (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup) :=
  P.total.mem_ends_dualGraph_iff _ P.marking P.range_marking_subset_smoothLocus_over v e

/-- The number of vertices of `P.dualGraph` equals the number of irreducible components of
`P.total`. -/
theorem card_vertex_dualGraph :
    Fintype.card P.dualGraph.Vertex = Nat.card (irreducibleComponents P.total) :=
  P.total.card_vertex_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over

/-- The number of edges of `P.dualGraph` equals the number of singular points of `P.total`. -/
theorem card_edge_dualGraph :
    Fintype.card P.dualGraph.Edge = Nat.card (P.total.singularLocus K).support :=
  P.total.card_edge_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over

/-- The valence of a vertex `v` in `P.dualGraph` counts the branches of `P.total` lying on the
corresponding normalized component. -/
theorem valence_dualGraph (v : P.dualGraph.Vertex) :
    P.dualGraph.valence v =
      Nat.card {b : P.total.branchScheme K //
        P.total.branchSchemeToBlowup K b ∈
          (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup)} :=
  P.total.valence_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over v

/-- The valence of a vertex `v` in `P.dualGraph` counts the points of the corresponding normalized
component lying over nodes of `P.total`. -/
theorem valence_dualGraph_eq_natCard_preimage_singularLocus (v : P.dualGraph.Vertex) :
    P.dualGraph.valence v =
      Nat.card {y : (P.total.singularLocus K).blowup //
        y ∈ (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup) ∧
          (P.total.singularLocus K).blowupToBase y ∈ (P.total.singularLocus K).support} :=
  P.total.valence_dualGraph_eq_natCard_preimage_singularLocus _ P.marking
    P.range_marking_subset_smoothLocus_over v

/-- A vertex `v` carries no loop in `P.dualGraph` if and only if the normalization morphism is
injective on that component. -/
theorem forall_endpoint_dualGraph_one_ne_iff_injOn (v : P.dualGraph.Vertex) :
    (∀ e, P.dualGraph.endpoint e 0 = v → P.dualGraph.endpoint e 1 ≠ v) ↔
      Set.InjOn (P.total.singularLocus K).blowupToBase
        (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup) :=
  P.total.forall_endpoint_dualGraph_one_ne_iff_injOn _ P.marking
    P.range_marking_subset_smoothLocus_over v

/-- Geometric characterization of a rational tail in `P.dualGraph`. -/
theorem isRationalTail_dualGraph_iff (v : P.dualGraph.Vertex) :
    P.dualGraph.IsRationalTail v ↔
      (P.normalizedComponent v).genus K = 0 ∧
        Nat.card {b : P.total.branchScheme K //
          P.total.branchSchemeToBlowup K b ∈
            (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup)} = 1 :=
  P.total.isRationalTail_dualGraph_iff _ P.marking P.range_marking_subset_smoothLocus_over v

/-- Geometric characterization of a rational bridge in `P.dualGraph`. -/
theorem isRationalBridge_dualGraph_iff (v : P.dualGraph.Vertex) :
    P.dualGraph.IsRationalBridge v ↔
      (P.normalizedComponent v).genus K = 0 ∧
        Nat.card {b : P.total.branchScheme K //
          P.total.branchSchemeToBlowup K b ∈
            (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup)} = 2 ∧
        Set.InjOn (P.total.singularLocus K).blowupToBase
          (P.dualGraphVertexEquiv v : Set (P.total.singularLocus K).blowup) :=
  P.total.isRationalBridge_dualGraph_iff _ P.marking P.range_marking_subset_smoothLocus_over v

/-- Reindexing the markings of `P` along `e : Fin m ↪ Fin n` directly reindexes `P.dualGraph`. -/
@[simp]
theorem dualGraph_reindex (e : Fin m ↪ Fin n) :
    (P.reindex e).dualGraph = P.dualGraph.reindex e :=
  (P.total.reindex_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over e).symm

/-- Reindexing the markings of `P` along `e : Fin m ↪ Fin n` reindexes `P.dualGraph` up to canonical
isomorphism. -/
def reindexDualGraphIso (e : Fin m ↪ Fin n) :
    (P.reindex e).dualGraph.Iso (P.dualGraph.reindex e) :=
  (P.dualGraph_reindex e) ▸ DualGraph.Iso.refl (P.reindex e).dualGraph

/-- `reindexDualGraphIso` identifies normalized-component vertices of `(P.reindex e).dualGraph` and
`P.dualGraph`. -/
@[simp]
theorem dualGraphVertexEquiv_reindexDualGraphIso_vertexEquiv
    (e : Fin m ↪ Fin n) (v : (P.reindex e).dualGraph.Vertex) :
    P.dualGraphVertexEquiv ((P.reindexDualGraphIso e).vertexEquiv v) =
      (P.reindex e).dualGraphVertexEquiv v := by
  have hheq : ∀ {G H : DualGraph.{u} (Fin m)} (h : G = H) (v : G.Vertex),
      HEq ((h ▸ DualGraph.Iso.refl G : G.Iso H).vertexEquiv v) v := by
    rintro _ _ rfl v
    simp
  exact P.total.dualGraphVertexEquiv_eq_of_heq _ _ _ (hheq (P.dualGraph_reindex e) v)

/-- `reindexDualGraphIso` identifies singular-point edges of `(P.reindex e).dualGraph` and
`P.dualGraph`. -/
@[simp]
theorem dualGraphEdgeEquiv_reindexDualGraphIso_edgeEquiv
    (e : Fin m ↪ Fin n) (x : (P.reindex e).dualGraph.Edge) :
    P.dualGraphEdgeEquiv ((P.reindexDualGraphIso e).edgeEquiv x) =
      (P.reindex e).dualGraphEdgeEquiv x := by
  have hheq : ∀ {G H : DualGraph.{u} (Fin m)} (h : G = H) (x : G.Edge),
      HEq ((h ▸ DualGraph.Iso.refl G : G.Iso H).edgeEquiv x) x := by
    rintro _ _ rfl x
    simp
  exact P.total.dualGraphEdgeEquiv_eq_of_heq _ _ _ (hheq (P.dualGraph_reindex e) x)

/-- On edges, `reindexDualGraphIso` preserves the underlying singular point of `P.total`. -/
theorem subschemeι_reindexDualGraphIso_edgeEquiv
    (e : Fin m ↪ Fin n) (x : (P.reindex e).dualGraph.Edge) :
    (P.total.singularLocus K).subschemeι
        (P.dualGraphEdgeEquiv ((P.reindexDualGraphIso e).edgeEquiv x)) =
      ((P.reindex e).total.singularLocus K).subschemeι
        ((P.reindex e).dualGraphEdgeEquiv x) := by
  rw [P.dualGraphEdgeEquiv_reindexDualGraphIso_edgeEquiv]
  exact rfl

/-- On vertices, `reindexDualGraphIso` sends a component `v` of `(P.reindex e).dualGraph` to the
unique component `w` of `P.dualGraph` with the same underlying irreducible component of
`P.total`. -/
theorem vertexEquiv_reindexDualGraphIso_eq_iff
    (e : Fin m ↪ Fin n) (v : (P.reindex e).dualGraph.Vertex) (w : P.dualGraph.Vertex) :
    (P.reindexDualGraphIso e).vertexEquiv v = w ↔
      ((P.reindex e).dualGraphIrreducibleComponentsEquiv v).1 ⊆
        (P.dualGraphIrreducibleComponentsEquiv w : Set P.total) := by
  have heq : (((P.reindex e).dualGraphIrreducibleComponentsEquiv v).1 : Set P.total) =
      (P.dualGraphIrreducibleComponentsEquiv ((P.reindexDualGraphIso e).vertexEquiv v) :
        Set P.total) :=
    ((P.reindex e).coe_dualGraphIrreducibleComponentsEquiv v).trans <|
      (congrArg ((P.total.singularLocus K).blowupToBase '' ·)
        (congrArg Subtype.val
          (P.dualGraphVertexEquiv_reindexDualGraphIso_vertexEquiv e v)).symm).trans
        (P.coe_dualGraphIrreducibleComponentsEquiv _).symm
  rw [heq]
  refine ⟨fun h ↦ h ▸ Set.Subset.rfl, fun hsub ↦ ?_⟩
  let Z₁ := P.dualGraphIrreducibleComponentsEquiv ((P.reindexDualGraphIso e).vertexEquiv v)
  let Z₂ := P.dualGraphIrreducibleComponentsEquiv w
  exact P.dualGraphIrreducibleComponentsEquiv.injective
    (Subtype.ext (hsub.antisymm (Z₁.2.2 Z₂.2.1 hsub)))

/-- When `P.toBase` is smooth, `P.dualGraph` has first Betti number zero. -/
theorem firstBetti_dualGraph_of_smooth [Smooth P.toBase] :
    P.dualGraph.firstBetti = 0 := by
  have : Smooth (P.total ↘ Spec (.of K)) := P.over_eq_toBase.symm ▸ ‹Smooth P.toBase›
  exact P.total.firstBetti_dualGraph_of_smooth _ _ _

/-- When `P.toBase` is smooth, the combinatorial arithmetic genus of `P.dualGraph` coincides with
the cohomological genus `P.total.genus K`. -/
theorem arithmeticGenus_dualGraph_eq_genus_of_smooth [Smooth P.toBase] :
    haveI : Smooth (P.total ↘ Spec (.of K)) := P.over_eq_toBase.symm ▸ ‹Smooth P.toBase›
    letI : SmoothOfRelativeDimension 1 (P.total ↘ Spec (.of K)) :=
      (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension _).mpr ⟨‹_›, inferInstance⟩
    letI := finiteDimensional_cohomology_one_trivial_of_smooth K P.total
    P.dualGraph.arithmeticGenus = P.total.genus K := by
  have : Smooth (P.total ↘ Spec (.of K)) := P.over_eq_toBase.symm ▸ ‹Smooth P.toBase›
  exact P.total.arithmeticGenus_dualGraph_eq_genus_of_smooth _ _ _

/-! ### Functoriality under isomorphisms of pointed prestable curves -/

section Iso

variable {P Q R}

/-- An isomorphism `e : P ≅ Q` of `n`-pointed prestable curves over `Spec K` induces a canonical
isomorphism `P.dualGraph.Iso Q.dualGraph` of dual graphs. -/
def dualGraphIsoOfIso (e : P ≅ Q) : P.dualGraph.Iso Q.dualGraph :=
  TauCeti.AlgebraicGeometry.dualGraphIsoOfIso
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := Q.total ↘ Spec (.of K)))
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    ((Over.forget _).mapIso (toOver.mapIso e) : P.total ≅ Q.total)
    (forget_mapIso_toOver_hom_comp_over e)
    Q.marking P.marking
    Q.range_marking_subset_smoothLocus_over P.range_marking_subset_smoothLocus_over
    (fun i ↦ e.hom.marking_comp_hom i)

/-- On edges, `dualGraphIsoOfIso e` sends a singular point `x` of `P.total` to the singular point of
`Q.total` mapped onto `e.hom.hom x`. -/
theorem subschemeι_dualGraphIsoOfIso_edgeEquiv (e : P ≅ Q) (x : P.dualGraph.Edge) :
    (Q.total.singularLocus K).subschemeι
        (Q.dualGraphEdgeEquiv ((dualGraphIsoOfIso e).edgeEquiv x)) =
      e.hom.hom ((P.total.singularLocus K).subschemeι (P.dualGraphEdgeEquiv x)) :=
  TauCeti.AlgebraicGeometry.subschemeι_dualGraphIsoOfIso_edgeEquiv (X := Q.total) (X' := P.total)
    _ _ ((Over.forget _).mapIso (toOver.mapIso e) : P.total ≅ Q.total)
    (forget_mapIso_toOver_hom_comp_over e)
    Q.marking P.marking
    Q.range_marking_subset_smoothLocus_over P.range_marking_subset_smoothLocus_over
    (fun i ↦ e.hom.marking_comp_hom i) x

/-- On vertices, `dualGraphIsoOfIso e` sends a component `v` of `P.total` to the unique component
`w` of `Q.total` containing the image under `e.hom.hom` of the irreducible component corresponding
to `v`. -/
theorem vertexEquiv_dualGraphIsoOfIso_eq_iff (e : P ≅ Q)
    (v : P.dualGraph.Vertex) (w : Q.dualGraph.Vertex) :
    (dualGraphIsoOfIso e).vertexEquiv v = w ↔
      e.hom.hom '' (P.dualGraphIrreducibleComponentsEquiv v : Set P.total) ⊆
        (Q.dualGraphIrreducibleComponentsEquiv w : Set Q.total) :=
  TauCeti.AlgebraicGeometry.vertexEquiv_dualGraphIsoOfIso_eq_iff (X := Q.total) (X' := P.total)
    _ _ ((Over.forget _).mapIso (toOver.mapIso e) : P.total ≅ Q.total)
    (forget_mapIso_toOver_hom_comp_over e)
    Q.marking P.marking
    Q.range_marking_subset_smoothLocus_over P.range_marking_subset_smoothLocus_over
    (fun i ↦ e.hom.marking_comp_hom i) v w

/-- The identity isomorphism of a pointed prestable curve induces the identity isomorphism of its
dual graph. -/
@[simp]
theorem dualGraphIsoOfIso_refl (P : PointedPrestableFamily (Spec (.of K)) n) :
    dualGraphIsoOfIso (Iso.refl P) = DualGraph.Iso.refl P.dualGraph := by
  have aux : ∀ (e₀ : P.total ≅ P.total) (he₀ : e₀.hom ≫ (P.total ↘ Spec (.of K)) = _)
      (hm₀ : ∀ i, P.marking i ≫ e₀.hom = P.marking i),
      e₀ = Iso.refl P.total →
        TauCeti.AlgebraicGeometry.dualGraphIsoOfIso _ _ e₀ he₀
            P.marking P.marking P.range_marking_subset_smoothLocus_over
            P.range_marking_subset_smoothLocus_over hm₀ =
          DualGraph.Iso.refl P.dualGraph := by
    rintro _ _ _ rfl
    exact TauCeti.AlgebraicGeometry.dualGraphIsoOfIso_refl _ P.marking
      P.range_marking_subset_smoothLocus_over
  exact aux _ _ _ (Iso.ext rfl)

/-- `dualGraphIsoOfIso` respects composition of pointed prestable curve isomorphisms. -/
theorem dualGraphIsoOfIso_trans (e₁ : P ≅ Q) (e₂ : Q ≅ R) :
    dualGraphIsoOfIso (e₁ ≪≫ e₂) = (dualGraphIsoOfIso e₁).trans (dualGraphIsoOfIso e₂) := by
  let e₁_tot : P.total ≅ Q.total := (Over.forget _).mapIso (toOver.mapIso e₁)
  let e₂_tot : Q.total ≅ R.total := (Over.forget _).mapIso (toOver.mapIso e₂)
  have aux : ∀ (e₁₂ : P.total ≅ R.total) (he₁₂ : e₁₂.hom ≫ (R.total ↘ Spec (.of K)) = _)
      (hm₁₂ : ∀ i, P.marking i ≫ e₁₂.hom = R.marking i),
      e₁₂ = e₁_tot ≪≫ e₂_tot →
        TauCeti.AlgebraicGeometry.dualGraphIsoOfIso _ _ e₁₂ he₁₂
            R.marking P.marking R.range_marking_subset_smoothLocus_over
            P.range_marking_subset_smoothLocus_over hm₁₂ =
          (dualGraphIsoOfIso e₁).trans (dualGraphIsoOfIso e₂) := by
    rintro _ _ _ rfl
    exact TauCeti.AlgebraicGeometry.dualGraphIsoOfIso_trans _ _ _
      e₁_tot (forget_mapIso_toOver_hom_comp_over e₁)
      e₂_tot (forget_mapIso_toOver_hom_comp_over e₂)
      R.marking Q.marking P.marking
      R.range_marking_subset_smoothLocus_over Q.range_marking_subset_smoothLocus_over
      P.range_marking_subset_smoothLocus_over
      (fun i ↦ e₁.hom.marking_comp_hom i) (fun i ↦ e₂.hom.marking_comp_hom i)
  exact aux _ _ _ (Iso.ext rfl)

/-- `dualGraphIsoOfIso` commutes with symmetry of pointed prestable curve isomorphisms. -/
@[simp]
theorem dualGraphIsoOfIso_symm (e : P ≅ Q) :
    dualGraphIsoOfIso e.symm = (dualGraphIsoOfIso e).symm := by
  let e_tot : P.total ≅ Q.total := (Over.forget _).mapIso (toOver.mapIso e)
  have aux : ∀ (e' : Q.total ≅ P.total) (he' : e'.hom ≫ (P.total ↘ Spec (.of K)) = _)
      (hm' : ∀ i, Q.marking i ≫ e'.hom = P.marking i),
      e' = e_tot.symm →
        TauCeti.AlgebraicGeometry.dualGraphIsoOfIso _ _ e' he'
            P.marking Q.marking P.range_marking_subset_smoothLocus_over
            Q.range_marking_subset_smoothLocus_over hm' =
          (dualGraphIsoOfIso e).symm := by
    rintro _ _ _ rfl
    exact TauCeti.AlgebraicGeometry.dualGraphIsoOfIso_symm _ _
      e_tot (forget_mapIso_toOver_hom_comp_over e) Q.marking P.marking
      Q.range_marking_subset_smoothLocus_over P.range_marking_subset_smoothLocus_over
      (fun i ↦ e.hom.marking_comp_hom i)
  exact aux _ _ _ (Iso.ext rfl)

/-- Isomorphic pointed prestable curves have dual graphs with the same first Betti number. -/
theorem firstBetti_dualGraph_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.firstBetti = Q.dualGraph.firstBetti :=
  (dualGraphIsoOfIso e).firstBetti_eq

/-- Isomorphic pointed prestable curves have dual graphs with the same arithmetic genus. -/
theorem arithmeticGenus_dualGraph_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.arithmeticGenus = Q.dualGraph.arithmeticGenus :=
  (dualGraphIsoOfIso e).arithmeticGenus_eq

/-- Isomorphic pointed prestable curves have simultaneously stable dual graphs. -/
theorem isStable_dualGraph_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsStable ↔ Q.dualGraph.IsStable :=
  (dualGraphIsoOfIso e).isStable_iff

/-- Isomorphic pointed prestable curves have simultaneously semistable dual graphs. -/
theorem isSemistable_dualGraph_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsSemistable ↔ Q.dualGraph.IsSemistable :=
  (dualGraphIsoOfIso e).isSemistable_iff

end Iso

/-! ### Base change along extensions of separably closed fields -/

section BaseChange

variable (L : Type u) [Field L] [IsSepClosed L] [Algebra K L]

/-- **Invariance of the dual graph of a pointed prestable curve under extensions of separably
closed fields.** Pulling `P` back along `Spec L ⟶ Spec K` induces a canonical isomorphism of dual
graphs. -/
def pullbackDualGraphIso :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.Iso P.dualGraph :=
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  TauCeti.AlgebraicGeometry.dualGraphIsoOfIsPullback
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne
      (f := (P.pullback g).total ↘ Spec (.of L)))
    (g := Limits.pullback.fst P.toBase g)
    (by
      rw [over_eq_toBase, over_eq_toBase]
      exact IsPullback.of_hasPullback P.toBase g)
    P.marking (P.pullback g).marking
    P.range_marking_subset_smoothLocus_over
    (P.pullback g).range_marking_subset_smoothLocus_over
    (P.pullback_marking_fst g)

/-- `pullbackDualGraphIso` acts on vertices via `irreducibleComponentsEquivOfIsPullback` on the
irreducible components of the normalizations. -/
@[simp]
theorem dualGraphVertexEquiv_pullbackDualGraphIso_vertexEquiv
    (v' : (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.Vertex) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
    P.dualGraphVertexEquiv ((P.pullbackDualGraphIso L).vertexEquiv v') =
      irreducibleComponentsEquivOfIsPullback
        (isPullback_blowupSingularLocusMap_over
          (R := K) (R' := L) (X := P.total) (X' := (P.pullback g).total)
          (g := Limits.pullback.fst P.toBase g)
          (by
            rw [over_eq_toBase, over_eq_toBase]
            exact IsPullback.of_hasPullback P.toBase g))
        ((P.pullback g).dualGraphVertexEquiv v') :=
  TauCeti.AlgebraicGeometry.dualGraphVertexEquiv_dualGraphIsoOfIsPullback_vertexEquiv
    _ _ _ P.marking _ P.range_marking_subset_smoothLocus_over _
    (P.pullback_marking_fst _) v'

/-- On edges, `pullbackDualGraphIso` sends a singular point `x'` of the base-changed curve to the
unique singular point of `P.total` lying beneath `x'` under the first projection. -/
theorem subschemeι_pullbackDualGraphIso_edgeEquiv
    (x' : (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.Edge) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
    (P.total.singularLocus K).subschemeι
        (P.dualGraphEdgeEquiv ((P.pullbackDualGraphIso L).edgeEquiv x')) =
      Limits.pullback.fst P.toBase g
        (((P.pullback g).total.singularLocus L).subschemeι
          ((P.pullback g).dualGraphEdgeEquiv x')) :=
  TauCeti.AlgebraicGeometry.subschemeι_dualGraphIsoOfIsPullback_edgeEquiv
    _ _ _ P.marking _ P.range_marking_subset_smoothLocus_over _
    (P.pullback_marking_fst _) x'

/-- On vertices, `pullbackDualGraphIso` sends a component `v'` of the base-changed curve to the
unique component `w` of `P.total` containing its image under the first projection. -/
theorem vertexEquiv_pullbackDualGraphIso_eq_iff
    (v' : (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.Vertex)
    (w : P.dualGraph.Vertex) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
    (P.pullbackDualGraphIso L).vertexEquiv v' = w ↔
      Limits.pullback.fst P.toBase g ''
          ((P.pullback g).dualGraphIrreducibleComponentsEquiv v' : Set (P.pullback g).total) ⊆
        (P.dualGraphIrreducibleComponentsEquiv w : Set P.total) :=
  TauCeti.AlgebraicGeometry.vertexEquiv_dualGraphIsoOfIsPullback_eq_iff
    _ _ _ P.marking _ P.range_marking_subset_smoothLocus_over _
    (P.pullback_marking_fst _) v' w

/-- Pulling back along an extension of separably closed fields preserves the first Betti number of
the dual graph. -/
@[simp]
theorem firstBetti_dualGraph_pullback :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.firstBetti =
      P.dualGraph.firstBetti :=
  (P.pullbackDualGraphIso L).firstBetti_eq

/-- Pulling back along an extension of separably closed fields preserves the combinatorial
arithmetic genus of the dual graph. -/
@[simp]
theorem arithmeticGenus_dualGraph_pullback :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.arithmeticGenus =
      P.dualGraph.arithmeticGenus :=
  (P.pullbackDualGraphIso L).arithmeticGenus_eq

/-- Pulling back along an extension of separably closed fields preserves stability of the dual
graph. -/
@[simp]
theorem isStable_dualGraph_pullback_iff :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.IsStable ↔
      P.dualGraph.IsStable :=
  (P.pullbackDualGraphIso L).isStable_iff

/-- Pulling back along an extension of separably closed fields preserves semistability of the dual
graph. -/
@[simp]
theorem isSemistable_dualGraph_pullback_iff :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.IsSemistable ↔
      P.dualGraph.IsSemistable :=
  (P.pullbackDualGraphIso L).isSemistable_iff

end BaseChange

end SepClosed

end TauCeti.AlgebraicGeometry.PointedPrestableFamily
