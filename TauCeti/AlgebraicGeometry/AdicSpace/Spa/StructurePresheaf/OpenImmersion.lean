/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.OpenEmbedding
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Localization
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.KanExtension

/-!
# The structure presheaf on a rational subset is the structure presheaf of `A⟨T/s⟩`

Let `U = R(T/s)` be a rational subset of `X = Spa(A, A⁺)`, let `B = A⟨T/s⟩` with plus ring
`A_U⁺`, and let `j : Spa(B, A_U⁺) → X` be the open embedding induced by the structure map
`A → B`. Wedhorn's Remark 8.4 identifies `𝒪_X(V)` with `𝒪_U(j⁻¹(V))` for every open `V ⊆ U`,
compatibly with restriction; equivalently, the presheaf `𝒪_X` restricted along `j` is `𝒪_U`. This
file proves that statement for the presentation-limit presheaves: `j''ᵒᵖ ⋙ 𝒪_X ≅ 𝒪_U`, where `j''`
is the image functor on opens, when `A⁺` consists of power-bounded elements and contains the ring of
definition. It is the presheaf half of Wedhorn's Remark 8.8, that `j` is an open immersion of
pre-adic spaces with image `U`; the compatibility of the stalk valuations is not treated here.

## The isomorphism on arbitrary opens

For an open `W` of `Spa(B, A_U⁺)`, the component of `presentationLimitPresheafLocIso` at `W` is an
isomorphism `𝒪_X(j(W)) ≅ 𝒪_U(W)` of complete separated topological rings, natural in `W`. On a
rational open `W` it is the identification `presentationLimitLocIso` of
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Localization`, indexed by `W` through
`j(W)` (`presentationLimitLocImageIso`, `presentationLimitPresheafLocIso_hom_app`); on a general
`W` it is determined by its restrictions to the rational opens `W' ⊆ W`
(`presentationLimitPresheafLocIso_hom_app_comp_map`), since both presheaves are the limits of their
values on rational opens (`presentationLimitPresheafIsPointwiseRightKanExtension`). The
restricted presheaf `j''ᵒᵖ ⋙ 𝒪_X` is the structure presheaf of the presheafed space `X` restricted
along `j` (Mathlib's `PresheafedSpace.restrict`), so `presentationLimitPresheafLocIso` is the
isomorphism of presheafed spaces underlying the open immersion; together with the compatibility of
the stalk valuations, it makes the rational subset `U` an open affinoid subspace of `X`.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitLocImageIso` : the identification
  `𝒪_X(j(W)) ≅ 𝒪_U(W)` for a rational open `W` of `Spa(B, A_U⁺)`.
* `TauCeti.ValuationSpectrum.presentationLimitPresheafLocIso` : **Wedhorn's Remark 8.4** for the
  presentation-limit presheaves, `j''ᵒᵖ ⋙ 𝒪_X ≅ 𝒪_U` as presheaves on `Spa(B, A_U⁺)`.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitMap_comp_presentationLimitLocImageIso_hom` : the
  rational-level identification commutes with restriction.
* `TauCeti.ValuationSpectrum.presentationLimitLocImageIso_hom` : the rational-level identification
  is `presentationLimitLocIso` at `j(W)`, up to transport along `j⁻¹(j(W)) = W`.
* `TauCeti.ValuationSpectrum.presentationLimitPresheafLocIso_hom_app_comp_map` and
  `TauCeti.ValuationSpectrum.presentationLimitPresheafLocIso_hom_app` : the presheaf isomorphism,
  followed by restriction to a rational open, is the rational-level identification; on a rational
  open it is that identification.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remarks 8.4 and 8.8.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

namespace TauCeti.ValuationSpectrum

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
  (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus) (hT : IsOpen (Ideal.span (T : Set A) : Set A))

/-! ### The identification on rational opens, indexed by the opens of `Spa(B, A_U⁺)` -/

/-- **Wedhorn's Remark 8.4 on a rational open of `Spa(B, A_U⁺)`.** For a rational open `W` of
`Spa(B, A_U⁺)`, the presentation limit of `Spa(A, A⁺)` on the image `j(W)` is isomorphic to the
presentation limit of `Spa(B, A_U⁺)` on `W`. This is `presentationLimitLocIso` at the rational open
`j(W) ⊆ R(T/s)`, whose pullback `j⁻¹(j(W))` is `W`. -/
noncomputable def presentationLimitLocImageIso :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden),
      presentationLimit (P := P) Aplus
          ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W) ≅
        presentationLimit (P := completionLocalization P T s S hden)
          (completedPlusSubring P Aplus T s S hden) W :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  fun W hW ↦
    presentationLimitLocIso P Aplus T s S hden hAplus hT _
      (spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT W hW)
      (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W) ≪≫
    eqToIso (congrArg _ (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W))

/-- On a rational open `W` of `Spa(B, A_U⁺)`, the identification `presentationLimitLocImageIso` is
`presentationLimitLocIso` at the rational open `j(W)`, followed by the transport along
`j⁻¹(j(W)) = W`. -/
theorem presentationLimitLocImageIso_hom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
      (hW : W ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden)),
      (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W hW).hom =
        (presentationLimitLocIso P Aplus T s S hden hAplus hT _
            (spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT W hW)
            (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W)).hom ≫
          eqToHom (congrArg _ (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W)) := by
  intro W hW
  rw [presentationLimitLocImageIso, Iso.trans_hom, eqToIso.hom]

/-- **The identification on rational opens is natural**: for rational opens `W' ⊆ W` of
`Spa(B, A_U⁺)`, the isomorphisms at `W` and `W'` carry the restriction map from `j(W)` to `j(W')`
over `A` to the restriction map from `W` to `W'` over `B`. -/
theorem presentationLimitMap_comp_presentationLimitLocImageIso_hom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W W' : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
      (hW : W ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden))
      (hW' : W' ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden)) (h : W' ≤ W),
      presentationLimitMap (P := P)
          (spaComapLoc_functor_obj_mono P Aplus hP T s S hden h) ≫
        (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W' hW').hom =
      (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W hW).hom ≫
        presentationLimitMap (P := completionLocalization P T s S hden) h := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W W' hW hW' h
  simp only [presentationLimitLocImageIso, Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, presentationLimitMap_comp_presentationLimitLocIso_hom P Aplus T s S hden
    hAplus hT (spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT W hW)
    (spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT W' hW')
    (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W)
    (spaComapLoc_functor_obj_mono P Aplus hP T s S hden h), Category.assoc, Category.assoc,
    eqToHom_presentationLimit (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W'),
    eqToHom_presentationLimit (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W),
    presentationLimitMap_comp, presentationLimitMap_comp]

/-! ### The comparison maps -/

section Comparison

/-- **The cone over the rational opens of `W` with vertex `𝒪_X(j(W))`**: its leg at a rational
`W' ⊆ W` restricts from `j(W)` to `j(W')` and applies the identification
`presentationLimitLocImageIso`. Its limit-induced morphism `𝒪_X(j(W)) ⟶ 𝒪_U(W)` is the component
of `presentationLimitPresheafLocIso`. -/
private noncomputable def toLocCone :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      Cone (StructuredArrow.proj (op W)
          (rationalOpensFunctor (completedPlusSubring P Aplus T s S hden)).op ⋙
        (rationalOpensFunctor (completedPlusSubring P Aplus T s S hden)).op ⋙
          presentationLimitPresheaf (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden)) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  fun W ↦
  { pt := (presentationLimitPresheaf P Aplus).obj
      (op ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W))
    π :=
      { app := fun g ↦ eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
          presentationLimitMap (P := P)
            (spaComapLoc_functor_obj_mono P Aplus hP T s S hden (leOfHom g.hom.unop)) ≫
          (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT
            ((rationalOpensFunctor _).obj g.right.unop) g.right.unop.2).hom ≫
          eqToHom (presentationLimitPresheaf_obj (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden)
            (op ((rationalOpensFunctor _).obj g.right.unop))).symm
        naturality := fun g₁ g₂ φ ↦ by
          have hφ : (rationalOpensFunctor _).obj g₂.right.unop ≤
              (rationalOpensFunctor _).obj g₁.right.unop :=
            leOfHom ((rationalOpensFunctor _).op.map φ.right).unop
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
            StructuredArrow.proj_map, Functor.comp_obj, StructuredArrow.proj_obj,
            presentationLimitPresheaf_map, Category.id_comp, Category.assoc, eqToHom_trans_assoc,
            eqToHom_refl]
          rw [← reassoc_of% presentationLimitMap_comp_presentationLimitLocImageIso_hom P Aplus T s S
            hden hAplus hP hT ((rationalOpensFunctor _).obj g₁.right.unop)
            ((rationalOpensFunctor _).obj g₂.right.unop) g₁.right.unop.2 g₂.right.unop.2 hφ,
            reassoc_of% presentationLimitMap_comp] } }

/-- **The cone over the rational opens of `j(W)` with vertex `𝒪_U(W)`**: its leg at a rational
`V ⊆ j(W)` restricts from `W` to `j⁻¹(V)` and applies the inverse of the identification
`presentationLimitLocIso`. Its limit-induced morphism `𝒪_U(W) ⟶ 𝒪_X(j(W))` is the inverse component
of `presentationLimitPresheafLocIso`. -/
private noncomputable def ofLocCone :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      Cone (StructuredArrow.proj
          (op ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W))
          (rationalOpensFunctor Aplus).op ⋙
        (rationalOpensFunctor Aplus).op ⋙ presentationLimitPresheaf P Aplus) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  fun W ↦
  { pt := (presentationLimitPresheaf (completionLocalization P T s S hden)
      (completedPlusSubring P Aplus T s S hden)).obj (op W)
    π :=
      { app := fun g ↦ eqToHom (presentationLimitPresheaf_obj _ _ _) ≫
          presentationLimitMap (P := completionLocalization P T s S hden)
            ((locOpensComap_mono P Aplus T s S hden (leOfHom g.hom.unop)).trans
              (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W).le) ≫
          (presentationLimitLocIso P Aplus T s S hden hAplus hT
            ((rationalOpensFunctor Aplus).obj g.right.unop) g.right.unop.2
            ((leOfHom g.hom.unop).trans
              (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W))).inv ≫
          eqToHom (presentationLimitPresheaf_obj P Aplus
            (op ((rationalOpensFunctor Aplus).obj g.right.unop))).symm
        naturality := fun g₁ g₂ φ ↦ by
          have hφ : (rationalOpensFunctor Aplus).obj g₂.right.unop ≤
              (rationalOpensFunctor Aplus).obj g₁.right.unop :=
            leOfHom ((rationalOpensFunctor Aplus).op.map φ.right).unop
          have h₁ := (leOfHom g₁.hom.unop).trans
            (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W)
          -- the inverse identifications commute with restriction
          have key :
              (presentationLimitLocIso P Aplus T s S hden hAplus hT
                ((rationalOpensFunctor Aplus).obj g₁.right.unop) g₁.right.unop.2 h₁).inv ≫
                presentationLimitMap (P := P) hφ =
              presentationLimitMap (P := completionLocalization P T s S hden)
                (locOpensComap_mono P Aplus T s S hden hφ) ≫
              (presentationLimitLocIso P Aplus T s S hden hAplus hT
                ((rationalOpensFunctor Aplus).obj g₂.right.unop) g₂.right.unop.2
                (hφ.trans h₁)).inv := by
            rw [Iso.inv_comp_eq, ← Category.assoc,
              ← presentationLimitMap_comp_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT
                (V := (rationalOpensFunctor Aplus).obj g₁.right.unop)
                (V' := (rationalOpensFunctor Aplus).obj g₂.right.unop)
                g₁.right.unop.2 g₂.right.unop.2 h₁ hφ,
              Category.assoc, Iso.hom_inv_id, Category.comp_id]
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
            StructuredArrow.proj_map, Functor.comp_obj, StructuredArrow.proj_obj,
            presentationLimitPresheaf_map, Category.id_comp, Category.assoc, eqToHom_trans_assoc,
            eqToHom_refl]
          rw [reassoc_of% key, reassoc_of% presentationLimitMap_comp] } }

/-- The leg of `toLocCone W` at a rational `W' ⊆ W`. -/
private theorem toLocCone_π_app :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
      (g : StructuredArrow (op W)
        (rationalOpensFunctor (completedPlusSubring P Aplus T s S hden)).op),
      (toLocCone P Aplus T s S hden hAplus hP hT W).π.app g =
        eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
          presentationLimitMap (P := P)
            (spaComapLoc_functor_obj_mono P Aplus hP T s S hden (leOfHom g.hom.unop)) ≫
          (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT
            ((rationalOpensFunctor _).obj g.right.unop) g.right.unop.2).hom ≫
          eqToHom (presentationLimitPresheaf_obj (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden)
            (op ((rationalOpensFunctor _).obj g.right.unop))).symm :=
  fun _ _ ↦ rfl

/-- The leg of `ofLocCone W` at a rational `V ⊆ j(W)`. -/
private theorem ofLocCone_π_app :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
      (g : StructuredArrow
        (op ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W))
        (rationalOpensFunctor Aplus).op),
      (ofLocCone P Aplus T s S hden hAplus hP hT W).π.app g =
        eqToHom (presentationLimitPresheaf_obj _ _ _) ≫
          presentationLimitMap (P := completionLocalization P T s S hden)
            ((locOpensComap_mono P Aplus T s S hden (leOfHom g.hom.unop)).trans
              (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W).le) ≫
          (presentationLimitLocIso P Aplus T s S hden hAplus hT
            ((rationalOpensFunctor Aplus).obj g.right.unop) g.right.unop.2
            ((leOfHom g.hom.unop).trans
              (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W))).inv ≫
          eqToHom (presentationLimitPresheaf_obj P Aplus
            (op ((rationalOpensFunctor Aplus).obj g.right.unop))).symm :=
  fun _ _ ↦ rfl

/-- The morphism `𝒪_X(j(W)) ⟶ 𝒪_U(W)` induced by `toLocCone`. -/
private noncomputable def toLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.op ⋙
        presentationLimitPresheaf P Aplus).obj (op W) ⟶
      (presentationLimitPresheaf (completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden)).obj (op W) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  fun W ↦ (presentationLimitPresheafIsPointwiseRightKanExtension (op W)).lift
    (toLocCone P Aplus T s S hden hAplus hP hT W)

/-- The morphism `𝒪_U(W) ⟶ 𝒪_X(j(W))` induced by `ofLocCone`. -/
private noncomputable def ofLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      (presentationLimitPresheaf (completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden)).obj (op W) ⟶
      ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.op ⋙
        presentationLimitPresheaf P Aplus).obj (op W) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  fun W ↦ (presentationLimitPresheafIsPointwiseRightKanExtension (op _)).lift
    (ofLocCone P Aplus T s S hden hAplus hP hT W)

/-- **`toLoc` restricts to the identification on rational opens**: for a rational `W' ⊆ W`,
`toLoc W` followed by restriction to `W'` is restriction from `j(W)` to `j(W')` followed by
`presentationLimitLocImageIso`. -/
private theorem toLoc_comp_map :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W W' : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
      (hW' : W' ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden)) (h : W' ≤ W),
      toLoc P Aplus T s S hden hAplus hP hT W ≫
          eqToHom (presentationLimitPresheaf_obj (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden) (op W)) ≫
          presentationLimitMap (P := completionLocalization P T s S hden) h =
        eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
          presentationLimitMap (P := P) (spaComapLoc_functor_obj_mono P Aplus hP T s S hden h) ≫
          (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W' hW').hom := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W W' hW' h
  -- the factorization of `toLoc W` through the leg at `W'` of the Kan-extension cone
  have key := (presentationLimitPresheafIsPointwiseRightKanExtension (op W)).fac
    (toLocCone P Aplus T s S hden hAplus hP hT W)
    (StructuredArrow.mk (C := (InducedCategory _ (Subtype.val :
      spaRationalOpens (completedPlusSubring P Aplus T s S hden) → _))ᵒᵖ) (Y := op ⟨W', hW'⟩)
      (homOfLE h).op)
  rw [presentationLimitPresheaf_coneAt_π_app, toLocCone_π_app, presentationLimitPresheaf_map]
    at key
  simp only [StructuredArrow.mk_right, unop_op, inducedFunctor_obj] at key
  -- cancel the final transport, which both sides end with
  rw [← cancel_mono (eqToHom (presentationLimitPresheaf_obj (completionLocalization P T s S hden)
    (completedPlusSubring P Aplus T s S hden) (op W')).symm)]
  simp only [toLoc, Category.assoc]
  exact key

/-- **`ofLoc` restricts to the inverse identification on rational opens**: for a rational
`V ⊆ j(W)`, `ofLoc W` followed by restriction to `V` is restriction from `W` to `j⁻¹(V)` followed by
the inverse of `presentationLimitLocIso`. -/
private theorem ofLoc_comp_map :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden))) (V : Opens ↥(spa Aplus))
      (hV : V ∈ spaRationalOpens Aplus)
      (h : V ≤ (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W),
      ofLoc P Aplus T s S hden hAplus hP hT W ≫
          eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫ presentationLimitMap (P := P) h =
        eqToHom (presentationLimitPresheaf_obj (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden) (op W)) ≫
          presentationLimitMap (P := completionLocalization P T s S hden)
            ((locOpensComap_mono P Aplus T s S hden h).trans
              (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W).le) ≫
          (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV
            (h.trans (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W))).inv := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W V hV h
  -- the factorization of `ofLoc W` through the leg at `V` of the Kan-extension cone
  have key := (presentationLimitPresheafIsPointwiseRightKanExtension (op _)).fac
    (ofLocCone P Aplus T s S hden hAplus hP hT W)
    (StructuredArrow.mk (C := (InducedCategory _ (Subtype.val : spaRationalOpens Aplus → _))ᵒᵖ)
      (Y := op ⟨V, hV⟩) (homOfLE h).op)
  rw [presentationLimitPresheaf_coneAt_π_app, ofLocCone_π_app, presentationLimitPresheaf_map]
    at key
  simp only [StructuredArrow.mk_right, unop_op, inducedFunctor_obj] at key
  -- cancel the final transport, which both sides end with
  rw [← cancel_mono (eqToHom (presentationLimitPresheaf_obj P Aplus (op V)).symm)]
  simp only [ofLoc, Category.assoc]
  exact key

/-- `toLoc` followed by `ofLoc` is the identity. -/
private theorem toLoc_comp_ofLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      toLoc P Aplus T s S hden hAplus hP hT W ≫ ofLoc P Aplus T s S hden hAplus hP hT W = 𝟙 _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W
  refine (presentationLimitPresheafIsPointwiseRightKanExtension (op _)).hom_ext fun g ↦ ?_
  -- the leg of the Kan-extension cone at `g` is restriction to the rational open `V = R(g)`
  have hV : (rationalOpensFunctor Aplus).obj g.right.unop ∈ spaRationalOpens Aplus :=
    g.right.unop.2
  have hVW : (rationalOpensFunctor Aplus).obj g.right.unop ≤
      (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W :=
    leOfHom g.hom.unop
  have hVT := hVW.trans (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W)
  rw [presentationLimitPresheaf_coneAt_π_app, presentationLimitPresheaf_map]
  simp only [Category.assoc, Category.id_comp]
  -- `ofLoc W` followed by restriction to `V`, then `toLoc W` followed by restriction to `j⁻¹(V)`
  rw [reassoc_of% ofLoc_comp_map P Aplus T s S hden hAplus hP hT W _ hV hVW,
    reassoc_of% toLoc_comp_map P Aplus T s S hden hAplus hP hT W _
      (locOpensComap_mem_spaRationalOpens P Aplus T s S hden hV)
      ((locOpensComap_mono P Aplus T s S hden hVW).trans
        (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W).le),
    presentationLimitLocImageIso, Iso.trans_hom, eqToIso.hom,
    presentationLimitLocIso_hom_congr P Aplus T s S hden hAplus hT
      (spaComapLoc_functor_obj_locOpensComap P Aplus hP T s S hden hVT) _ hV _ hVT]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.hom_inv_id_assoc]
  rw [eqToHom_presentationLimit (spaComapLoc_functor_obj_locOpensComap P Aplus hP T s S hden hVT),
    reassoc_of% presentationLimitMap_comp]

/-- `ofLoc` followed by `toLoc` is the identity. -/
private theorem ofLoc_comp_toLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      ofLoc P Aplus T s S hden hAplus hP hT W ≫ toLoc P Aplus T s S hden hAplus hP hT W = 𝟙 _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W
  refine (presentationLimitPresheafIsPointwiseRightKanExtension (op W)).hom_ext fun g ↦ ?_
  -- the leg of the Kan-extension cone at `g` is restriction to the rational open `W' = R(g)`
  have hW' : (rationalOpensFunctor _).obj g.right.unop ∈
      spaRationalOpens (completedPlusSubring P Aplus T s S hden) :=
    g.right.unop.2
  have h : (rationalOpensFunctor _).obj g.right.unop ≤ W := leOfHom g.hom.unop
  rw [presentationLimitPresheaf_coneAt_π_app, presentationLimitPresheaf_map]
  simp only [Category.assoc, Category.id_comp]
  -- `toLoc W` followed by restriction to `W'`, then `ofLoc W` followed by restriction to `j(W')`
  rw [reassoc_of% toLoc_comp_map P Aplus T s S hden hAplus hP hT W _ hW' h,
    reassoc_of% ofLoc_comp_map P Aplus T s S hden hAplus hP hT W _
      (spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT _ hW')
      (spaComapLoc_functor_obj_mono P Aplus hP T s S hden h),
    presentationLimitLocImageIso, Iso.trans_hom, eqToIso.hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [eqToHom_presentationLimit (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden _),
    reassoc_of% presentationLimitMap_comp]

/-- `toLoc` is natural in `W`. -/
private theorem map_comp_toLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {X Y : (Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))ᵒᵖ} (f : X ⟶ Y),
      ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.op ⋙
          presentationLimitPresheaf P Aplus).map f ≫
        toLoc P Aplus T s S hden hAplus hP hT Y.unop =
      toLoc P Aplus T s S hden hAplus hP hT X.unop ≫
        (presentationLimitPresheaf (completionLocalization P T s S hden)
          (completedPlusSubring P Aplus T s S hden)).map f := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro X Y f
  refine (presentationLimitPresheafIsPointwiseRightKanExtension (op Y.unop)).hom_ext fun g ↦ ?_
  have hW' : (rationalOpensFunctor _).obj g.right.unop ∈
      spaRationalOpens (completedPlusSubring P Aplus T s S hden) :=
    g.right.unop.2
  have h₂ : (rationalOpensFunctor _).obj g.right.unop ≤ Y.unop := leOfHom g.hom.unop
  -- the leg of the Kan-extension cone at `g` is restriction to the rational open `W' = R(g)`;
  -- on the right, the two restrictions compose to the restriction from `X` to `W'`
  rw [presentationLimitPresheaf_coneAt_π_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp, presentationLimitPresheaf_map, presentationLimitPresheaf_map,
    reassoc_of% toLoc_comp_map P Aplus T s S hden hAplus hP hT Y.unop _ hW' h₂,
    reassoc_of% toLoc_comp_map P Aplus T s S hden hAplus hP hT X.unop _ hW'
      (h₂.trans (leOfHom f.unop))]
  simp only [Functor.comp_map, Functor.op_map, Functor.op_obj, unop_op,
    presentationLimitPresheaf_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [reassoc_of% presentationLimitMap_comp]

end Comparison

/-! ### Wedhorn's Remark 8.4 as an isomorphism of presheaves -/

/-- **Wedhorn's Remark 8.4 for the presentation-limit presheaves.** Let `U = R(T/s)` be a rational
subset of `X = Spa(A, A⁺)`, where `T` spans an open ideal and `A⁺` consists of power-bounded
elements and contains the ring of definition, and let `j : Spa(A⟨T/s⟩, A_U⁺) → X` be the open
embedding induced by the structure map. The presheaf `𝒪_X` restricted along `j` — the presheaf
`W ↦ 𝒪_X(j(W))` on `Spa(A⟨T/s⟩, A_U⁺)`, which is the structure presheaf of the restriction of the
presheafed space `X` along `j` — is isomorphic to the presentation-limit presheaf of
`Spa(A⟨T/s⟩, A_U⁺)`. On a rational open the isomorphism is `presentationLimitLocImageIso`
(`presentationLimitPresheafLocIso_hom_app`). -/
noncomputable def presentationLimitPresheafLocIso :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.op ⋙
        presentationLimitPresheaf P Aplus ≅
      presentationLimitPresheaf (completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  NatIso.ofComponents
    (fun W ↦
      { hom := toLoc P Aplus T s S hden hAplus hP hT W.unop
        inv := ofLoc P Aplus T s S hden hAplus hP hT W.unop
        hom_inv_id := toLoc_comp_ofLoc P Aplus T s S hden hAplus hP hT W.unop
        inv_hom_id := ofLoc_comp_toLoc P Aplus T s S hden hAplus hP hT W.unop })
    (fun f ↦ map_comp_toLoc P Aplus T s S hden hAplus hP hT f)

/-- **The presheaf isomorphism restricts to the identification on rational opens**: for an open
`W` of `Spa(A⟨T/s⟩, A_U⁺)` and a rational open `W' ⊆ W`, the component of
`presentationLimitPresheafLocIso` at `W` followed by restriction to `W'` is restriction from
`j(W)` to `j(W')` followed by `presentationLimitLocImageIso`. -/
theorem presentationLimitPresheafLocIso_hom_app_comp_map :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W W' : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
      (hW' : W' ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden)) (h : W' ≤ W),
      (presentationLimitPresheafLocIso P Aplus T s S hden hAplus hP hT).hom.app (op W) ≫
          (presentationLimitPresheaf (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden)).map (homOfLE h).op =
        eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
          presentationLimitMap (P := P) (spaComapLoc_functor_obj_mono P Aplus hP T s S hden h) ≫
          (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W' hW').hom ≫
          eqToHom (presentationLimitPresheaf_obj _ _ _).symm := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W W' hW' h
  simp only [presentationLimitPresheafLocIso, NatIso.ofComponents_hom_app]
  rw [presentationLimitPresheaf_map,
    reassoc_of% toLoc_comp_map P Aplus T s S hden hAplus hP hT W W' hW' h]

/-- **On a rational open, the presheaf isomorphism is the identification
`presentationLimitLocImageIso`.** -/
theorem presentationLimitPresheafLocIso_hom_app :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
      (hW : W ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden)),
      (presentationLimitPresheafLocIso P Aplus T s S hden hAplus hP hT).hom.app (op W) =
        eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
          (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W hW).hom ≫
          eqToHom (presentationLimitPresheaf_obj _ _ _).symm := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W hW
  have := toLoc_comp_map P Aplus T s S hden hAplus hP hT W W hW le_rfl
  rw [presentationLimitMap_refl, presentationLimitMap_refl] at this
  simp only [Category.comp_id, Category.id_comp] at this
  rw [comp_eqToHom_iff] at this
  simp only [presentationLimitPresheafLocIso, NatIso.ofComponents_hom_app]
  rw [this, Category.assoc]

end TauCeti.ValuationSpectrum

end
