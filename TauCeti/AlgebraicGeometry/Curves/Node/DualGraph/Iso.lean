/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph.Basic

/-!
# Transporting the dual graph of a prestable curve along isomorphisms and field extensions

Let `e : X ≅ Y` be an isomorphism of prestable curves over a field `K`, compatible with the
structure morphisms to `Spec K`. Then `e` lifts to an isomorphism `e^ν : X^ν ≅ Y^ν` of the blowups
along the singular subschemes, lying over `e` (`AlgebraicGeometry.Scheme.singularLocusBlowupIso`).

Over a separably closed field, `e^ν` and `e` then induce an isomorphism of the dual graphs
`AlgebraicGeometry.Scheme.dualGraph` of `X` and `Y`, for markings at smooth points that `e`
carries to each other (`AlgebraicGeometry.Scheme.dualGraphIsoOfIso`):

* a component `v` of `X^ν` goes to its image `e^ν(v)`, a component of `Y^ν`;
* a node `x` of `X` goes to the node `e(x)` of `Y`, and the two points of `X^ν` over `x` go to
  the two points of `Y^ν` over `e(x)`, possibly in the opposite order;
* `e^ν` restricts to an isomorphism over `K` of a component of `X^ν` onto its image, so the genera
  agree (`TauCeti.AlgebraicGeometry.genus_eq_of_isIso`);
* the point of `X^ν` over a marking goes to the point of `Y^ν` over the corresponding marking.

Since the components of `Y^ν` correspond to those of `X^ν` through `e^ν` and `e^ν` lies over `e`,
a morphism `f` out of `Y` is constant on the image in `Y` of the component `e^ν(v)` exactly when
`e ≫ f` is constant on the image in `X` of `v`
(`AlgebraicGeometry.Scheme.image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv`). This is what
the invariance of the stability of a prestable map under isomorphisms needs.

Similarly, if `X'` is the base change of `X` along an extension `L / K` of separably closed fields,
`singularLocusBlowupMap` bijects the irreducible components of `X'^ν` with those of `X^ν`, the
finite étale singular subscheme and branch scheme biject on points, and flat base change of
cohomology preserves the component genera, yielding a canonical isomorphism of dual graphs
`AlgebraicGeometry.Scheme.dualGraphBaseChangeIso`.

## Main definitions

* `AlgebraicGeometry.Scheme.dualGraphIsoOfIso`: the isomorphism of dual graphs induced by an
  isomorphism of prestable curves over a separably closed field matching the markings.
* `AlgebraicGeometry.Scheme.dualGraphBaseChangeIso`: the isomorphism of dual graphs under base
  change along an extension `L / K` of separably closed fields.

## Main results

* `AlgebraicGeometry.Scheme.coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv` and
  `AlgebraicGeometry.Scheme.dualGraphEdgeEquiv_dualGraphIsoOfIso_edgeEquiv`: the isomorphism of
  dual graphs maps a component to its image and a node to its image.
* `AlgebraicGeometry.Scheme.image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv`: the image of a
  component under a morphism out of `Y` is the image of the corresponding component of `X` under
  its composite with `e`.
* `AlgebraicGeometry.Scheme.dualGraphIsoOfIso_refl`,
  `AlgebraicGeometry.Scheme.dualGraphIsoOfIso_symm` and
  `AlgebraicGeometry.Scheme.dualGraphIsoOfIso_trans`: the construction is compatible with
  identities, inverses and composites.
* `AlgebraicGeometry.Scheme.coe_dualGraphVertexEquiv_dualGraphBaseChangeIso_vertexEquiv` and
  `AlgebraicGeometry.Scheme.dualGraphEdgeEquiv_dualGraphBaseChangeIso_edgeEquiv`: base change maps
  a component to its preimage in `X'^ν` and identifies nodes along `g : X' ⟶ X`.
* `AlgebraicGeometry.Scheme.isRationalTail_preimageSingularLocusBlowupEquiv_iff` and
  `AlgebraicGeometry.Scheme.isRationalBridge_preimageSingularLocusBlowupEquiv_iff`: geometric
  rational tails and bridges are invariant under extensions of separably closed fields.

## References

* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, Section 2, for the dual graph of a pointed nodal curve and its isomorphisms.
* The constructions and arguments follow mo271's
  https://github.com/TauCetiProject/TauCeti/pull/42297 and
  https://github.com/TauCetiProject/TauCeti/pull/42356, which transport a different dual graph of
  a nodal curve along isomorphisms (`dualGraphIsoOfIso`, `blowupSingularLocusMap`, and the genus
  comparison).
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [PrestableFamily (X ↘ Spec (.of K))] [PrestableFamily (Y ↘ Spec (.of K))]
  (e : X ≅ Y) (he : e.hom ≫ Y ↘ Spec (.of K) = X ↘ Spec (.of K))

/-! ### Components and nodes -/

/-- The bijection of irreducible components of the blowups induced by
`singularLocusBlowupIso`: a component goes to its image. -/
private def blowupComponentsEquiv :
    irreducibleComponents (X.singularLocus K).blowup ≃
      irreducibleComponents (Y.singularLocus K).blowup :=
  (Scheme.homeoOfIso (singularLocusBlowupIso e he)).irreducibleComponentsEquiv

/-- The component through a point goes to the component through its image. -/
private theorem blowupComponentsEquiv_irreducibleComponentOf (b : (X.singularLocus K).blowup) :
    blowupComponentsEquiv e he (irreducibleComponentOf b) =
      irreducibleComponentOf ((singularLocusBlowupIso e he).hom b) := by
  rw [blowupComponentsEquiv]
  simpa only [Scheme.coe_homeoOfIso] using
    (Scheme.homeoOfIso _).irreducibleComponentsEquiv_irreducibleComponentOf
      (existsUnique_mem_irreducibleComponents_of_unique_minimalPrime_stalk _)

include he in
/-- An isomorphism of prestable curves over `K` matches their smooth loci. -/
private theorem iso_hom_mem_smoothLocus_iff (x : X) :
    e.hom x ∈ (Y ↘ Spec (.of K)).smoothLocus ↔ x ∈ (X ↘ Spec (.of K)).smoothLocus := by
  rw [← Scheme.Hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq]
  simp only [he]

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
    rw [Scheme.Hom.coe_preimage, coe_blowupComponent, coe_blowupComponent, blowupComponentsEquiv,
      Homeomorph.coe_irreducibleComponentsEquiv_apply, ← Scheme.coe_homeoOfIso,
      Homeomorph.preimage_image]
  let g := ((X.singularLocus K).blowup.isoOfEq hpre.symm).hom ≫ f.hom ∣_ _
  have : g.IsOver (Spec (.of K)) := ⟨by simp [g, f, he]⟩
  exact (TauCeti.AlgebraicGeometry.genus_eq_of_isIso K g).symm

/-! ### The isomorphism of dual graphs -/

variable [IsSepClosed K]

/-- The point of the blowup of `X` over a node, on a given branch, goes to a point of the blowup
of `Y` over the image node. -/
private theorem exists_singularLocusBlowupIso_hom_branchPointEquiv
    (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)) (i : Fin 2) :
    ∃ j, (singularLocusBlowupIso e he).hom (X.branchPointEquiv x i) =
      Y.branchPointEquiv (nodeEquiv e he x) j := by
  refine ⟨(Y.branchPointEquiv (nodeEquiv e he x)).symm ⟨_, ?_⟩, by rw [Equiv.apply_symm_apply]⟩
  simp [nodeEquiv, blowupToBase_branchPointEquiv]

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
    have hinj : Function.Injective (singularLocusBlowupIso e he).hom := by
      simpa only [Scheme.coe_homeoOfIso] using
        (Scheme.homeoOfIso (singularLocusBlowupIso e he)).injective
    have := (X.branchPointEquiv x').injective (Subtype.ext (hinj (hj₀.trans hj₁.symm)))
    exact zero_ne_one this
  -- The branch indices `j₀ ≠ j₁` are `0` and `1` in some order.
  have hj : s((0 : Fin 2), 1) = s(j₀, j₁) :=
    (Sym2.mem_and_mem_iff hne).1 ⟨by fin_cases j₀ <;> simp, by fin_cases j₁ <;> simp⟩
  simp only [DualGraph.ends_def, Sym2.map_mk, hv, hj₀, hj₁, hw]
  simpa only [Sym2.map_mk] using congrArg (Sym2.map fun j ↦ (Y.dualGraphVertexEquiv q).symm
    (irreducibleComponentOf (Y.branchPointEquiv (nodeEquiv e he x') j :
      (Y.singularLocus K).blowup))) hj

/-- The bijection of vertices preserves the genera. -/
private theorem genus_vertexEquivOfIso (v : (X.dualGraph p).Vertex) :
    (Y.dualGraph q).genus (vertexEquivOfIso e he p q v) = (X.dualGraph p).genus v := by
  simp only [dualGraph_genus, vertexEquivOfIso, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply]
  exact genus_blowupComponent_blowupComponentsEquiv e he _

/-- The bijection of vertices matches the components carrying the markings, when `e` carries
each marking of `X` to the corresponding marking of `Y`. -/
private theorem vertexEquivOfIso_marking (hpq : ∀ i, e.hom (p i : X) = q i) (i : ι) :
    vertexEquivOfIso e he p q ((X.dualGraph p).marking i) = (Y.dualGraph q).marking i := by
  obtain ⟨b, hb⟩ := X.surjective_blowupToBase_singularLocus (K := K)
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := X ↘ Spec (.of K))) |>.surj (p i : X)
  simp only [vertexEquivOfIso, Equiv.trans_apply]
  rw [X.dualGraphVertexEquiv_marking p i hb, blowupComponentsEquiv_irreducibleComponentOf,
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
@[simp]
theorem coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv (v : (X.dualGraph p).Vertex) :
    (Y.dualGraphVertexEquiv q ((dualGraphIsoOfIso e he p q hpq).vertexEquiv v) :
        Set (Y.singularLocus K).blowup) =
      (singularLocusBlowupIso e he).hom '' (X.dualGraphVertexEquiv p v) := by
  simp [dualGraphIsoOfIso, vertexEquivOfIso, blowupComponentsEquiv]

/-- The isomorphism of dual graphs carries a node of `X` to its image under `e`. -/
@[simp]
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

/-- The isomorphism of dual graphs induced by the identity is the identity. -/
@[simp]
theorem dualGraphIsoOfIso_refl :
    dualGraphIsoOfIso (CategoryTheory.Iso.refl X) (Category.id_comp _) p p (fun _ ↦ by simp) =
      DualGraph.Iso.refl _ := by
  ext v
  · refine (X.dualGraphVertexEquiv p).injective (Subtype.ext ?_)
    rw [coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv, singularLocusBlowupIso_refl]
    simp
  · refine (X.dualGraphEdgeEquiv p).injective (Subtype.ext ?_)
    rw [dualGraphEdgeEquiv_dualGraphIsoOfIso_edgeEquiv]
    simp

/-- The isomorphism of dual graphs induced by the inverse isomorphism is the inverse. The
compatibility of `e.symm` with the structure morphisms and the markings is derived from `he` and
`hpq`. -/
theorem dualGraphIsoOfIso_symm :
    dualGraphIsoOfIso e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq, he]) q p
        (fun i ↦ by rw [Iso.symm_hom, ← hpq, Scheme.hom_inv_apply]) =
      (dualGraphIsoOfIso e he p q hpq).symm := by
  ext w
  · rw [DualGraph.Iso.symm_vertexEquiv, Equiv.eq_symm_apply]
    refine (Y.dualGraphVertexEquiv q).injective (Subtype.ext ?_)
    simp only [coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv,
      singularLocusBlowupIso_symm e he]
    rw [Iso.symm_hom, Set.image_image]
    simp only [Scheme.inv_hom_apply, Set.image_id']
  · rw [DualGraph.Iso.symm_edgeEquiv, Equiv.eq_symm_apply]
    refine (Y.dualGraphEdgeEquiv q).injective (Subtype.ext ?_)
    simp only [dualGraphEdgeEquiv_dualGraphIsoOfIso_edgeEquiv]
    rw [Iso.symm_hom, Scheme.inv_hom_apply]

/-- The isomorphism of dual graphs induced by a composite of isomorphisms is the composite. The
compatibility of `e ≪≫ e'` with the structure morphisms and the markings is derived from those of
`e` and `e'`. -/
theorem dualGraphIsoOfIso_trans {Z : Scheme.{u}} [Z.Over (Spec (.of K))]
    [PrestableFamily (Z ↘ Spec (.of K))] (e' : Y ≅ Z)
    (he' : e'.hom ≫ Z ↘ Spec (.of K) = Y ↘ Spec (.of K))
    (r : ι → (Z ↘ Spec (.of K)).smoothLocus) (hqr : ∀ i, e'.hom (q i : Y) = r i) :
    dualGraphIsoOfIso (e ≪≫ e') (by rw [Iso.trans_hom, Category.assoc, he', he]) p r
        (fun i ↦ by rw [Iso.trans_hom, Scheme.Hom.comp_apply, hpq, hqr]) =
      (dualGraphIsoOfIso e he p q hpq).trans (dualGraphIsoOfIso e' he' q r hqr) := by
  ext v
  · refine (Z.dualGraphVertexEquiv r).injective (Subtype.ext ?_)
    simp only [DualGraph.Iso.trans_vertexEquiv, Equiv.trans_apply,
      coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv,
      singularLocusBlowupIso_trans e he e' he', Set.image_image]
    exact Set.image_congr fun b _ ↦ by rw [Iso.trans_hom, Scheme.Hom.comp_apply]
  · refine (Z.dualGraphEdgeEquiv r).injective (Subtype.ext ?_)
    simp only [DualGraph.Iso.trans_edgeEquiv, Equiv.trans_apply,
      dualGraphEdgeEquiv_dualGraphIsoOfIso_edgeEquiv]
    rw [Iso.trans_hom, Scheme.Hom.comp_apply]

/-! ### Base change along extensions of separably closed fields -/

section BaseChange

variable {K L : Type u} [Field K] [IsSepClosed K] [Field L] [Algebra K L]
  {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
  [PrestableFamily (X ↘ Spec (.of K))] [PrestableFamily (X' ↘ Spec (.of L))]
  {g : X' ⟶ X} (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K)) (Spec.algebraMap K L))

/-- The bijection of nodes induced by base change of a prestable curve from a separably closed
field `K` to any field extension `L / K`. -/
private def nodeBaseChangeEquiv :
    ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ) ≃
      ↥(((X' ↘ Spec (.of L)).smoothLocus : Set X')ᶜ) :=
  (X.singularLocusSubschemeEquiv K).symm.trans <|
    (Equiv.ofBijective _
      (bijective_singularLocus_subschemeMap PrestableFamily.atWorstNodalOfRelativeDimensionOne
        H)).symm.trans
      (X'.singularLocusSubschemeEquiv L)

/-- `subschemeMap` sends the singular-subscheme point of `nodeBaseChangeEquiv H x` to that of
`x`. -/
@[simp]
private theorem subschemeMap_singularLocusSubschemeEquiv_symm_nodeBaseChangeEquiv
    (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)) :
    (X'.singularLocus L).subschemeMap (X.singularLocus K) g
        (IdealSheafData.le_map_iff_comap_le.mpr (singularLocus_eq_comap_of_isPullback H).ge)
        ((X'.singularLocusSubschemeEquiv L).symm (nodeBaseChangeEquiv H x)) =
      (X.singularLocusSubschemeEquiv K).symm x := by
  simp [nodeBaseChangeEquiv, Equiv.ofBijective_apply_symm_apply]

/-- `g` maps the base-changed node `nodeBaseChangeEquiv H x` back to `x`. -/
private theorem apply_nodeBaseChangeEquiv
    (x : ↥(((X ↘ Spec (.of K)).smoothLocus : Set X)ᶜ)) :
    g (nodeBaseChangeEquiv H x : X') = (x : X) := by
  let hle := IdealSheafData.le_map_iff_comap_le.mpr (singularLocus_eq_comap_of_isPullback H).ge
  rw [← X'.subschemeι_singularLocusSubschemeEquiv_symm (nodeBaseChangeEquiv H x),
    ← Scheme.Hom.comp_apply, ← (X'.singularLocus L).subschemeMap_subschemeι _ g hle,
    Scheme.Hom.comp_apply]
  simp

variable [IsSepClosed L] {ι : Type v} (p : ι → (X ↘ Spec (.of K)).smoothLocus)
  (p' : ι → (X' ↘ Spec (.of L)).smoothLocus)

/-- Vertex bijection of dual graphs under base change: preimage of blowup components. -/
private def vertexEquivOfBaseChange : (X.dualGraph p).Vertex ≃ (X'.dualGraph p').Vertex :=
  (X.dualGraphVertexEquiv p).trans <|
    (preimageSingularLocusBlowupEquiv PrestableFamily.atWorstNodalOfRelativeDimensionOne H).trans
      (X'.dualGraphVertexEquiv p').symm

/-- Edge bijection of dual graphs under base change: lifting nodes along `g`. -/
private def edgeEquivOfBaseChange : (X.dualGraph p).Edge ≃ (X'.dualGraph p').Edge :=
  (X.dualGraphEdgeEquiv p).trans <|
    (nodeBaseChangeEquiv H).trans (X'.dualGraphEdgeEquiv p').symm

/-- Base change transports edge endpoints: pushing a blowup point forward along
`singularLocusBlowupMap H` and lifting branches along `branchSchemeBaseChangeMap H` match the
incidence characterizations of `X.dualGraph p` and `X'.dualGraph p'`. -/
private theorem ends_edgeEquivOfBaseChange (x : (X.dualGraph p).Edge) :
    (X'.dualGraph p').ends (edgeEquivOfBaseChange H p p' x) =
      ((X.dualGraph p).ends x).map (vertexEquivOfBaseChange H p p') := by
  let fBl := singularLocusBlowupMap H
  let σ := vertexEquivOfBaseChange H p p'
  let x' := edgeEquivOfBaseChange H p p' x
  have hgx' : g (X'.dualGraphEdgeEquiv p' x' : X') = (X.dualGraphEdgeEquiv p x : X) := by
    simpa [x', edgeEquivOfBaseChange] using
      apply_nodeBaseChangeEquiv H (X.dualGraphEdgeEquiv p x)
  refine Sym2.ext fun w' ↦ ?_
  rw [Sym2.mem_map]
  refine ⟨fun hw' ↦ ⟨σ.symm w', ?_, σ.apply_symm_apply w'⟩, ?_⟩
  · -- Push a point of `w'` over `x'` down to `Bl X` via `fBl`.
    obtain ⟨b', hb'w, hb'x⟩ := (X'.mem_ends_dualGraph_iff p' w' x').mp hw'
    rw [X.mem_ends_dualGraph_iff p]
    have hpre : fBl ⁻¹' (X.dualGraphVertexEquiv p (σ.symm w')).val =
        (X'.dualGraphVertexEquiv p' w').val := by
      have h := congrArg (fun u ↦ (X'.dualGraphVertexEquiv p' u).val) (σ.apply_symm_apply w')
      dsimp only [σ, vertexEquivOfBaseChange, Equiv.trans_apply] at h
      rwa [Equiv.apply_symm_apply, coe_preimageSingularLocusBlowupEquiv] at h
    exact ⟨fBl b', Set.mem_preimage.mp (hpre.symm ▸ hb'w), by
      rw [blowupToBase_singularLocusBlowupMap_apply, hb'x, hgx']⟩
  · -- Lift a branch over `x` in `v` along the bijective map `branchSchemeBaseChangeMap H`.
    rintro ⟨v, hv, rfl⟩
    obtain ⟨b, hbv, hbx⟩ := (X.mem_ends_dualGraph_iff p v x).mp hv
    obtain ⟨br, hbrs, rfl⟩ := exists_preimage_of_isPullback (X.isPullback_branchScheme K)
      ((X.singularLocusSubschemeEquiv K).symm (X.dualGraphEdgeEquiv p x)) b
      ((X.subschemeι_singularLocusSubschemeEquiv_symm _).trans hbx.symm)
    obtain ⟨br', rfl⟩ :=
      (bijective_branchSchemeBaseChangeMap PrestableFamily.atWorstNodalOfRelativeDimensionOne
        H).surjective br
    rw [X'.mem_ends_dualGraph_iff p']
    refine ⟨X'.branchSchemeToBlowup L br', ?_, ?_⟩
    · simp only [vertexEquivOfBaseChange, Equiv.trans_apply, Equiv.apply_symm_apply,
        coe_preimageSingularLocusBlowupEquiv, Set.mem_preimage]
      rwa [← Scheme.Hom.comp_apply, ← branchSchemeBaseChangeMap_toBlowup H]
    · have hbr' : X'.branchSchemeToSingularLocus L br' =
          (X'.singularLocusSubschemeEquiv L).symm
            (nodeBaseChangeEquiv H (X.dualGraphEdgeEquiv p x)) :=
        (bijective_singularLocus_subschemeMap PrestableFamily.atWorstNodalOfRelativeDimensionOne
          H).injective <| by
          rw [subschemeMap_singularLocusSubschemeEquiv_symm_nodeBaseChangeEquiv,
            ← Scheme.Hom.comp_apply, ← branchSchemeBaseChangeMap_toSingularLocus H,
            Scheme.Hom.comp_apply, hbrs]
      rw [← Scheme.Hom.comp_apply, ← X'.branchSchemeToSingularLocus_subschemeι L,
        Scheme.Hom.comp_apply, hbr']
      simp [edgeEquivOfBaseChange]

/-- Base change preserves the component genera of vertices. -/
private theorem genus_vertexEquivOfBaseChange (v : (X.dualGraph p).Vertex) :
    (X'.dualGraph p').genus (vertexEquivOfBaseChange H p p' v) = (X.dualGraph p).genus v := by
  simp only [dualGraph_genus, vertexEquivOfBaseChange, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply]
  exact genus_blowupComponent_preimageSingularLocusBlowupEquiv
    PrestableFamily.atWorstNodalOfRelativeDimensionOne H (X.dualGraphVertexEquiv p v)

/-- Base change matches the marked vertices when `g` sends `p' i` to `p i`. -/
private theorem vertexEquivOfBaseChange_marking (hp : ∀ i, g (p' i : X') = p i) (i : ι) :
    vertexEquivOfBaseChange H p p' ((X.dualGraph p).marking i) = (X'.dualGraph p').marking i := by
  obtain ⟨b', hb'⟩ := (X'.surjective_blowupToBase_singularLocus
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := X' ↘ Spec (.of L)))).surj (p' i : X')
  have hb : (X.singularLocus K).blowupToBase (singularLocusBlowupMap H b') = p i := by
    rw [blowupToBase_singularLocusBlowupMap_apply, hb', hp i]
  simp only [vertexEquivOfBaseChange, Equiv.trans_apply]
  rw [X.dualGraphVertexEquiv_marking p i hb,
    preimageSingularLocusBlowupEquiv_irreducibleComponentOf,
    Equiv.symm_apply_eq, X'.dualGraphVertexEquiv_marking p' i hb']

/-- **The dual graph is invariant under extension of a separably closed base field.** If `X'` is the
base change of `X` along `Spec L ⟶ Spec K` for separably closed fields `L / K` and `g : X' ⟶ X`
carries the smooth markings `p'` of `X'` to `p` of `X`, then `X.dualGraph p` and `X'.dualGraph p'`
are canonically isomorphic. -/
def dualGraphBaseChangeIso (hp : ∀ i, g (p' i : X') = p i) :
    (X.dualGraph p).Iso (X'.dualGraph p') where
  vertexEquiv := vertexEquivOfBaseChange H p p'
  edgeEquiv := edgeEquivOfBaseChange H p p'
  ends_edgeEquiv := ends_edgeEquivOfBaseChange H p p'
  genus_vertexEquiv := genus_vertexEquivOfBaseChange H p p'
  vertexEquiv_marking := vertexEquivOfBaseChange_marking H p p' hp

/-- `dualGraphBaseChangeIso` maps each vertex to its preimage under `singularLocusBlowupMap H`. -/
@[simp]
theorem coe_dualGraphVertexEquiv_dualGraphBaseChangeIso_vertexEquiv
    (hp : ∀ i, g (p' i : X') = p i) (v : (X.dualGraph p).Vertex) :
    (X'.dualGraphVertexEquiv p' ((dualGraphBaseChangeIso H p p' hp).vertexEquiv v) :
        Set (X'.singularLocus L).blowup) =
      singularLocusBlowupMap H ⁻¹'
        (X.dualGraphVertexEquiv p v : Set (X.singularLocus K).blowup) := by
  simp [dualGraphBaseChangeIso, vertexEquivOfBaseChange]

/-- `g` sends the base-changed edge `(dualGraphBaseChangeIso H p p' hp).edgeEquiv x` back to `x`. -/
@[simp]
theorem dualGraphEdgeEquiv_dualGraphBaseChangeIso_edgeEquiv
    (hp : ∀ i, g (p' i : X') = p i) (x : (X.dualGraph p).Edge) :
    g (X'.dualGraphEdgeEquiv p' ((dualGraphBaseChangeIso H p p' hp).edgeEquiv x) : X') =
      (X.dualGraphEdgeEquiv p x : X) := by
  simpa [dualGraphBaseChangeIso, edgeEquivOfBaseChange] using
    apply_nodeBaseChangeEquiv H (X.dualGraphEdgeEquiv p x)

/-- `dualGraphBaseChangeIso` sends `(X.dualGraphVertexEquiv p).symm v` to the component
`preimageSingularLocusBlowupEquiv _ H v`. -/
private theorem dualGraphVertexEquiv_dualGraphBaseChangeIso_symm
    (hp : ∀ i, g (p' i : X') = p i)
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    X'.dualGraphVertexEquiv p'
        ((dualGraphBaseChangeIso H p p' hp).vertexEquiv ((X.dualGraphVertexEquiv p).symm v)) =
      preimageSingularLocusBlowupEquiv PrestableFamily.atWorstNodalOfRelativeDimensionOne H v :=
  Subtype.ext (by simp)

/-- Geometric rational tails are invariant under extensions of separably closed base fields. -/
theorem isRationalTail_preimageSingularLocusBlowupEquiv_iff
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    X'.IsRationalTail L PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (preimageSingularLocusBlowupEquiv PrestableFamily.atWorstNodalOfRelativeDimensionOne H v) ↔
      X.IsRationalTail K PrestableFamily.atWorstNodalOfRelativeDimensionOne v := by
  rw [← dualGraphVertexEquiv_dualGraphBaseChangeIso_symm H Empty.elim Empty.elim (fun i ↦ i.elim) v,
    ← X'.dualGraph_isRationalTail_iff, DualGraph.Iso.isRationalTail_vertexEquiv_iff,
    X.dualGraph_isRationalTail_iff, Equiv.apply_symm_apply]

/-- Geometric rational bridges are invariant under extensions of separably closed base fields. -/
theorem isRationalBridge_preimageSingularLocusBlowupEquiv_iff
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    X'.IsRationalBridge L PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (preimageSingularLocusBlowupEquiv PrestableFamily.atWorstNodalOfRelativeDimensionOne H v) ↔
      X.IsRationalBridge K PrestableFamily.atWorstNodalOfRelativeDimensionOne v := by
  rw [← dualGraphVertexEquiv_dualGraphBaseChangeIso_symm H Empty.elim Empty.elim (fun i ↦ i.elim) v,
    ← X'.dualGraph_isRationalBridge_iff, DualGraph.Iso.isRationalBridge_vertexEquiv_iff,
    X.dualGraph_isRationalBridge_iff, Equiv.apply_symm_apply]

end BaseChange

end AlgebraicGeometry.Scheme
