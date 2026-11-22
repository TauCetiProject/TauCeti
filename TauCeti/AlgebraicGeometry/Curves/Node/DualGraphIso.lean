/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.Curves.Genus.BaseChange
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale

/-!
# Transporting the dual graph of a prestable curve along an isomorphism

Let `e : X ≅ Y` be an isomorphism of prestable curves over a field `K`, compatible with the
structure morphisms to `Spec K`. An isomorphism is étale, so it carries the singular locus of `Y`
back to that of `X` (`AlgebraicGeometry.Scheme.singularLocus_eq_comap_of_etale`), and blowing up
commutes with flat base change, so `e` lifts to an isomorphism `e^ν : X^ν ≅ Y^ν` of the blowups
along the singular subschemes, lying over `e`
(`AlgebraicGeometry.Scheme.singularLocusBlowupIso`).

Over a separably closed field, `e^ν` and `e` then induce an isomorphism of the dual graphs
`AlgebraicGeometry.Scheme.dualGraph` of `X` and `Y`, for markings at smooth points that `e`
carries to each other (`AlgebraicGeometry.Scheme.dualGraphIsoOfIso`):

* a component `v` of `X^ν` goes to its image `e^ν(v)`, a component of `Y^ν`;
* a node `x` of `X` goes to the node `e(x)` of `Y`, and the two points of `X^ν` over `x` go to
  the two points of `Y^ν` over `e(x)`, possibly in the opposite order;
* `e^ν` restricts to an isomorphism over `K` of a component of `X^ν` onto its image, so the genera
  agree, by flat base change of cohomology along the identity of `K`;
* the point of `X^ν` over a marking goes to the point of `Y^ν` over the corresponding marking.

Since the components of `Y^ν` correspond to those of `X^ν` through `e^ν` and `e^ν` lies over `e`,
a morphism `f` out of `Y` is constant on the image in `Y` of the component `e^ν(v)` exactly when
`e ≫ f` is constant on the image in `X` of `v`
(`AlgebraicGeometry.Scheme.image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv`). This is what
the invariance of the stability of a prestable map under isomorphisms needs.

## Main definitions

* `AlgebraicGeometry.Scheme.singularLocusBlowupIso`: the isomorphism of the blowups of two
  isomorphic relative curves along their singular subschemes.
* `AlgebraicGeometry.Scheme.dualGraphIsoOfIso`: the isomorphism of dual graphs induced by an
  isomorphism of prestable curves over a separably closed field matching the markings.

## Main results

* `AlgebraicGeometry.Scheme.singularLocusBlowupIso_hom_blowupToBase`: the isomorphism of blowups
  lies over the isomorphism of curves.
* `AlgebraicGeometry.Scheme.coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv` and
  `AlgebraicGeometry.Scheme.dualGraphEdgeEquiv_dualGraphIsoOfIso_edgeEquiv`: the isomorphism of
  dual graphs maps a component to its image and a node to its image.
* `AlgebraicGeometry.Scheme.image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv`: the image of a
  component under a morphism out of `Y` is the image of the corresponding component of `X` under
  its composite with `e`.

## References

* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, Section 2, for the dual graph of a pointed nodal curve and its isomorphisms.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [PrestableFamily (X ↘ Spec (.of K))] [PrestableFamily (Y ↘ Spec (.of K))]
  (e : X ≅ Y) (he : e.hom ≫ Y ↘ Spec (.of K) = X ↘ Spec (.of K))

/-! ### The singular loci and their blowups -/

include he in
/-- An isomorphism of prestable curves over `K` carries the singular locus of the target back to
that of the source: an isomorphism is étale. -/
private theorem singularLocus_eq_comap_of_iso :
    X.singularLocus K = (Y.singularLocus K).comap e.hom :=
  have : e.hom.IsOver (Spec (.of K)) := ⟨he⟩
  singularLocus_eq_comap_of_etale e.hom

/-- Blowing up equal ideal sheaves gives the same scheme over the base. -/
private theorem eqToHom_blowupToBase {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg IdealSheafData.blowup h) ≫ J.blowupToBase = I.blowupToBase := by
  subst h
  simp

/-- An isomorphism `e : X ≅ Y` of prestable curves over `K` lifts to an isomorphism of the blowups
of `X` and `Y` along their singular subschemes: the singular locus of `X` is the inverse image of
that of `Y`, as `e` is étale, and blowing up commutes with flat base change. It lies over `e`
(`singularLocusBlowupIso_hom_blowupToBase`). -/
def singularLocusBlowupIso : (X.singularLocus K).blowup ≅ (Y.singularLocus K).blowup :=
  have : IsIso ((Y.singularLocus K).blowupMap e.hom) :=
    ((Y.singularLocus K).isPullback_blowupMap_of_flat e.hom).isIso_snd_of_isIso
  eqToIso (congrArg IdealSheafData.blowup (singularLocus_eq_comap_of_iso e he)) ≪≫
    asIso ((Y.singularLocus K).blowupMap e.hom)

/-- The isomorphism of blowups lies over the isomorphism of curves. -/
@[reassoc (attr := simp)]
theorem singularLocusBlowupIso_hom_blowupToBase :
    (singularLocusBlowupIso e he).hom ≫ (Y.singularLocus K).blowupToBase =
      (X.singularLocus K).blowupToBase ≫ e.hom := by
  simp only [singularLocusBlowupIso, Iso.trans_hom, eqToIso.hom, asIso_hom, Category.assoc,
    IdealSheafData.blowupMap_blowupToBase]
  rw [← Category.assoc, eqToHom_blowupToBase (singularLocus_eq_comap_of_iso e he)]

/-- The isomorphism of blowups lies over the isomorphism of curves, on points. -/
theorem blowupToBase_singularLocusBlowupIso_hom_apply (b : (X.singularLocus K).blowup) :
    (Y.singularLocus K).blowupToBase ((singularLocusBlowupIso e he).hom b) =
      e.hom ((X.singularLocus K).blowupToBase b) := by
  rw [← Scheme.Hom.comp_apply, singularLocusBlowupIso_hom_blowupToBase, Scheme.Hom.comp_apply]

/-! ### Components and nodes -/

/-- The blowup of a prestable curve along its singular subscheme is regular. -/
private instance isRegular_blowup_singularLocus_of_prestableFamily (Z : Scheme.{u})
    [Z.Over (Spec (.of K))] [PrestableFamily (Z ↘ Spec (.of K))] :
    IsRegular (Z.singularLocus K).blowup :=
  Z.isRegular_blowup_singularLocus PrestableFamily.atWorstNodalOfRelativeDimensionOne

/-- The bijection of irreducible components of the blowups induced by
`singularLocusBlowupIso`: a component goes to its image. -/
private def blowupComponentsEquiv :
    irreducibleComponents (X.singularLocus K).blowup ≃
      irreducibleComponents (Y.singularLocus K).blowup :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber (singularLocusBlowupIso e he).hom
    (singularLocusBlowupIso e he).hom.continuous
    (Scheme.homeoOfIso (singularLocusBlowupIso e he)).isOpenMap
    (fun _ ↦ (Set.subsingleton_singleton.preimage
      (Scheme.homeoOfIso (singularLocusBlowupIso e he)).injective).isPreirreducible)
    (Scheme.homeoOfIso (singularLocusBlowupIso e he)).surjective).symm.toEquiv

/-- A component goes to its image under `singularLocusBlowupIso`. -/
private theorem coe_blowupComponentsEquiv (v : irreducibleComponents (X.singularLocus K).blowup) :
    (blowupComponentsEquiv e he v : Set (Y.singularLocus K).blowup) =
      (singularLocusBlowupIso e he).hom '' v :=
  (rfl)

/-- The component through a point goes to the component through its image. -/
private theorem blowupComponentsEquiv_irreducibleComponentOf (b : (X.singularLocus K).blowup) :
    blowupComponentsEquiv e he (irreducibleComponentOf b) =
      irreducibleComponentOf ((singularLocusBlowupIso e he).hom b) :=
  (irreducibleComponentOf_eq_iff.mpr (by
    rw [coe_blowupComponentsEquiv]
    exact ⟨b, mem_irreducibleComponentOf b, rfl⟩)).symm

include he in
/-- An isomorphism of prestable curves over `K` matches their smooth loci. -/
private theorem iso_hom_mem_smoothLocus_iff (x : X) :
    e.hom x ∈ (Y ↘ Spec (.of K)).smoothLocus ↔ x ∈ (X ↘ Spec (.of K)).smoothLocus := by
  rw [← not_iff_not, ← mem_support_singularLocus_iff_notMem_smoothLocus,
    ← mem_support_singularLocus_iff_notMem_smoothLocus, singularLocus_eq_comap_of_iso e he,
    IdealSheafData.support_comap]
  rfl

/-- The bijection of nodes induced by an isomorphism of prestable curves. -/
private def nodeEquiv :
    ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ) ≃ ↥(((Y ↘ Spec (.of K)).smoothLocus : Set Y)ᶜ) :=
  (Scheme.homeoOfIso e).toEquiv.subtypeEquiv fun x ↦
    not_congr (iso_hom_mem_smoothLocus_iff e he x).symm

/-- Corresponding components of the blowups have the same genus: `singularLocusBlowupIso`
restricts to an isomorphism between them over `K`. -/
private theorem genus_blowupComponent_blowupComponentsEquiv
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    (Y.blowupComponent (blowupComponentsEquiv e he v)).toScheme.genus K =
      (X.blowupComponent v).toScheme.genus K := by
  set f := singularLocusBlowupIso e he
  have hpre : f.hom ⁻¹ᵁ Y.blowupComponent (blowupComponentsEquiv e he v) = X.blowupComponent v := by
    ext1
    rw [Scheme.Hom.coe_preimage, coe_blowupComponent, coe_blowupComponent,
      coe_blowupComponentsEquiv]
    exact Set.preimage_image_eq _ (Scheme.homeoOfIso f).injective
  let g := ((X.singularLocus K).blowup.isoOfEq hpre.symm).hom ≫ f.hom ∣_ _
  have hg : g ≫ (Y.blowupComponent (blowupComponentsEquiv e he v)).toScheme ↘ Spec (.of K) =
      (X.blowupComponent v).toScheme ↘ Spec (.of K) := by
    simp [g, f, he]
  have H : IsPullback g ((X.blowupComponent v).toScheme ↘ Spec (.of K))
      ((Y.blowupComponent (blowupComponentsEquiv e he v)).toScheme ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ by simp]
    exact IsPullback.of_horiz_isIso ⟨by rw [hg, Category.comp_id]⟩
  exact (genus_eq_of_isPullback_of_isProper H).symm

/-! ### The isomorphism of dual graphs -/

variable [IsSepClosed K]

/-- The point of the blowup of `X` over a node, on a given branch, goes to a point of the blowup
of `Y` over the image node. -/
private theorem exists_singularLocusBlowupIso_hom_branchPointEquiv
    (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)) (i : Fin 2) :
    ∃ j, (singularLocusBlowupIso e he).hom (X.branchPointEquiv x i) =
      Y.branchPointEquiv (nodeEquiv e he x) j := by
  refine ⟨(Y.branchPointEquiv (nodeEquiv e he x)).symm ⟨_, ?_⟩, by rw [Equiv.apply_symm_apply]⟩
  rw [Set.mem_preimage, blowupToBase_singularLocusBlowupIso_hom_apply,
    blowupToBase_branchPointEquiv]
  rfl

variable {ι : Type v} (p : ι → (X ↘ Spec (.of K)).smoothLocus)
  (q : ι → (Y ↘ Spec (.of K)).smoothLocus)

/-- The bijection of vertices of the dual graphs induced by an isomorphism of prestable curves:
a component of the blowup of `X` goes to its image in the blowup of `Y`. -/
private def vertexEquivOfIso : (X.dualGraph p).Vertex ≃ (Y.dualGraph q).Vertex :=
  (X.dualGraphVertexEquiv p).trans ((blowupComponentsEquiv e he).trans
    (Y.dualGraphVertexEquiv q).symm)

/-- The bijection of edges of the dual graphs induced by an isomorphism of prestable curves: a
node of `X` goes to its image in `Y`. -/
private def edgeEquivOfIso : (X.dualGraph p).Edge ≃ (Y.dualGraph q).Edge :=
  (X.dualGraphEdgeEquiv p).trans ((nodeEquiv e he).trans (Y.dualGraphEdgeEquiv q).symm)

/-- The bijection of edges carries the ends of an edge to those of its image. -/
private theorem ends_edgeEquivOfIso (x : (X.dualGraph p).Edge) :
    (Y.dualGraph q).ends (edgeEquivOfIso e he p q x) =
      ((X.dualGraph p).ends x).map (vertexEquivOfIso e he p q) := by
  set x' := X.dualGraphEdgeEquiv p x
  have hx : Y.dualGraphEdgeEquiv q (edgeEquivOfIso e he p q x) = nodeEquiv e he x' := by
    simp [edgeEquivOfIso, x']
  have hv (i : Fin 2) : vertexEquivOfIso e he p q ((X.dualGraph p).endpoint x i) =
      (Y.dualGraphVertexEquiv q).symm (irreducibleComponentOf
        ((singularLocusBlowupIso e he).hom (X.branchPointEquiv x' i))) := by
    simp [vertexEquivOfIso, x', blowupComponentsEquiv_irreducibleComponentOf]
  have hw (j : Fin 2) : (Y.dualGraph q).endpoint (edgeEquivOfIso e he p q x) j =
      (Y.dualGraphVertexEquiv q).symm (irreducibleComponentOf
        (Y.branchPointEquiv (nodeEquiv e he x') j : (Y.singularLocus K).blowup)) := by
    rw [Equiv.eq_symm_apply, dualGraphVertexEquiv_endpoint, hx]
  obtain ⟨j₀, hj₀⟩ := exists_singularLocusBlowupIso_hom_branchPointEquiv e he x' 0
  obtain ⟨j₁, hj₁⟩ := exists_singularLocusBlowupIso_hom_branchPointEquiv e he x' 1
  have hne : j₀ ≠ j₁ := by
    rintro rfl
    have := (X.branchPointEquiv x').injective (Subtype.ext
      ((Scheme.homeoOfIso (singularLocusBlowupIso e he)).injective (hj₀.trans hj₁.symm)))
    exact zero_ne_one this
  rw [DualGraph.ends_def, DualGraph.ends_def, Sym2.map_mk, hv, hv, hw, hw, hj₀, hj₁]
  fin_cases j₀ <;> fin_cases j₁
  · exact (hne rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (hne rfl).elim

/-- The bijection of vertices preserves the genera. -/
private theorem genus_vertexEquivOfIso (v : (X.dualGraph p).Vertex) :
    (Y.dualGraph q).genus (vertexEquivOfIso e he p q v) = (X.dualGraph p).genus v := by
  rw [dualGraph_genus, dualGraph_genus]
  rw [vertexEquivOfIso, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact genus_blowupComponent_blowupComponentsEquiv e he _

/-- The bijection of vertices matches the components carrying the markings, when `e` carries
each marking of `X` to the corresponding marking of `Y`. -/
private theorem vertexEquivOfIso_marking (hpq : ∀ i, e.hom (p i : X) = q i) (i : ι) :
    vertexEquivOfIso e he p q ((X.dualGraph p).marking i) = (Y.dualGraph q).marking i := by
  obtain ⟨b, hb⟩ := X.surjective_blowupToBase_singularLocus (K := K)
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := X ↘ Spec (.of K))) |>.surj (p i : X)
  rw [vertexEquivOfIso, Equiv.trans_apply, Equiv.trans_apply,
    X.dualGraphVertexEquiv_marking p i hb, blowupComponentsEquiv_irreducibleComponentOf,
    Equiv.symm_apply_eq, Y.dualGraphVertexEquiv_marking q i
      (by rw [blowupToBase_singularLocusBlowupIso_hom_apply e he, hb, hpq])]

/-- **The dual graph is invariant under isomorphism.** An isomorphism `e : X ≅ Y` of prestable
curves over a separably closed field `K`, compatible with the structure morphisms and carrying the
markings `p` of `X` to the markings `q` of `Y`, induces an isomorphism of their dual graphs. A
component of the blowup of `X` goes to its image under `singularLocusBlowupIso`
(`coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv`) and a node of `X` goes to its image
under `e` (`dualGraphEdgeEquiv_dualGraphIsoOfIso_edgeEquiv`). -/
def dualGraphIsoOfIso (hpq : ∀ i, e.hom (p i : X) = q i) :
    (X.dualGraph p).Iso (Y.dualGraph q) where
  vertexEquiv := vertexEquivOfIso e he p q
  edgeEquiv := edgeEquivOfIso e he p q
  ends_edgeEquiv := ends_edgeEquivOfIso e he p q
  genus_vertexEquiv := genus_vertexEquivOfIso e he p q
  vertexEquiv_marking := vertexEquivOfIso_marking e he p q hpq

variable (hpq : ∀ i, e.hom (p i : X) = q i)

/-- The isomorphism of dual graphs carries a component of the blowup of `X` to its image under
`singularLocusBlowupIso`. -/
theorem coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv (v : (X.dualGraph p).Vertex) :
    (Y.dualGraphVertexEquiv q ((dualGraphIsoOfIso e he p q hpq).vertexEquiv v) :
        Set (Y.singularLocus K).blowup) =
      (singularLocusBlowupIso e he).hom '' (X.dualGraphVertexEquiv p v) := by
  simp [dualGraphIsoOfIso, vertexEquivOfIso, coe_blowupComponentsEquiv]

/-- The isomorphism of dual graphs carries a node of `X` to its image under `e`. -/
theorem dualGraphEdgeEquiv_dualGraphIsoOfIso_edgeEquiv (x : (X.dualGraph p).Edge) :
    (Y.dualGraphEdgeEquiv q ((dualGraphIsoOfIso e he p q hpq).edgeEquiv x) : Y) =
      e.hom (X.dualGraphEdgeEquiv p x) := by
  simp [dualGraphIsoOfIso, edgeEquivOfIso, nodeEquiv]

/-- The image of the component of the blowup of `Y` corresponding to a vertex `v`, under the
blowup morphism followed by a morphism `f` out of `Y`, is the image of the component `v` of the
blowup of `X` under the blowup morphism followed by `e ≫ f`. In particular `f` is constant on the
image in `Y` of the component corresponding to `v` exactly when `e ≫ f` is constant on the image
in `X` of `v`. -/
theorem image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv {Z : Scheme.{u}} (f : Y ⟶ Z)
    (v : (X.dualGraph p).Vertex) :
    ((Y.singularLocus K).blowupToBase ≫ f) ''
        (Y.dualGraphVertexEquiv q ((dualGraphIsoOfIso e he p q hpq).vertexEquiv v) :
          Set (Y.singularLocus K).blowup) =
      ((X.singularLocus K).blowupToBase ≫ e.hom ≫ f) ''
        (X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup) := by
  rw [coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv, Set.image_image]
  refine Set.image_congr fun b _ ↦ ?_
  rw [← Scheme.Hom.comp_apply, singularLocusBlowupIso_hom_blowupToBase_assoc]

end AlgebraicGeometry.Scheme
