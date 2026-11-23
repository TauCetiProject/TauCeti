/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor
public import TauCeti.AlgebraicGeometry.RelativeSpec.MorphismProperties

/-!
# Quotient algebras give closed subschemes of relative spectra

Let `f : A ⟶ B` be a morphism of quasi-coherent commutative `𝒪_X`-algebras. Over an affine open
`U` of `X`, the relative spectra of `A` and `B` are `Spec Γ(A, U)` and `Spec Γ(B, U)`, and the
induced morphism `Spec_X(B) ⟶ Spec_X(A)` is `Spec` of the ring map `Γ(A, U) ⟶ Γ(B, U)`; the chart
of `Spec_X(B)` over `U` is the base change of `Spec_X(B) ⟶ Spec_X(A)` along the chart of
`Spec_X(A)` over `U`. If `f` is an epimorphism of module sheaves, these ring maps are surjective,
since the kernel of `f` is quasi-coherent, so `Spec_X(B)` is a closed subscheme of `Spec_X(A)`.

This is how a surjection of graded algebras, such as `Sym(I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` for an ideal sheaf
`I`, becomes a closed embedding of the corresponding cones.

## Main results

* `CategoryTheory.CommMon.isPullback_relativeSpecCover_f_relativeSpecMap`: over an affine open
  `U`, the chart `Spec Γ(B, U)` of `Spec_X(B)` is the pullback of `Spec_X(B) ⟶ Spec_X(A)` along
  the chart `Spec Γ(A, U)` of `Spec_X(A)`.
* `CategoryTheory.CommMon.isClosedImmersion_relativeSpecMap_of_epi`: a morphism `A ⟶ B` of
  quasi-coherent algebras that is an epimorphism of module sheaves induces a closed immersion
  `Spec_X(B) ⟶ Spec_X(A)`.

## References

* The Stacks Project, [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ) (relative spectrum as
  a functor).
* The Stacks Project, [Tag 01QO](https://stacks.math.columbia.edu/tag/01QO) (closed immersions).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

variable {X : Scheme.{u}} {A B : CommMon X.Modules} [A.X.IsQuasicoherent] [B.X.IsQuasicoherent]

/-- Over an affine open `U` of `X`, the chart `Spec Γ(B, U) ⟶ Spec_X(B)` is the base change of
`Spec_X(B) ⟶ Spec_X(A)` along the chart `Spec Γ(A, U) ⟶ Spec_X(A)`, with projection to
`Spec Γ(A, U)` the spectrum of the ring map `Γ(A, U) ⟶ Γ(B, U)`. -/
theorem isPullback_relativeSpecCover_f_relativeSpecMap (f : A ⟶ B) (U : X.AffineZariskiSite) :
    IsPullback (B.relativeSpecCover.f U)
      (Spec.map (CommRingCat.ofHom (CommMon.sectionsAlgHom f U.val).toRingHom))
      (CommMon.relativeSpecMap f) (A.relativeSpecCover.f U) := by
  -- Both charts are base changes of `U ⟶ X`, along the structure morphisms of `Spec_X(A)` and
  -- `Spec_X(B) ⟶ Spec_X(A) ⟶ X`; the left square of the pasting is then a pullback.
  refine IsPullback.of_bot ?_ (CommMon.relativeSpecCover_f_relativeSpecMap f U)
    (A.isPullback_relativeSpecCover U).flip
  have hab : A.toSectionsPresheaf.app (op U.val) ≫
      CommRingCat.ofHom (CommMon.sectionsAlgHom f U.val).toRingHom =
        B.toSectionsPresheaf.app (op U.val) := by
    have h := NatTrans.congr_app (CommMon.toSectionsPresheaf_comp_sectionsPresheafMap f) (op U.val)
    rw [NatTrans.comp_app, CommMon.sectionsPresheafMap_app] at h
    exact h
  have e : Spec.map (CommRingCat.ofHom (CommMon.sectionsAlgHom f U.val).toRingHom) ≫
      Spec.map (A.toSectionsPresheaf.app (op U.val)) ≫ U.property.isoSpec.inv =
        Spec.map (B.toSectionsPresheaf.app (op U.val)) ≫ U.property.isoSpec.inv :=
    (Spec.map_comp_assoc _ _ _).symm.trans (congrArg (Spec.map · ≫ _) hab)
  rw [CommMon.relativeSpecMap_relativeSpecToBase]
  exact e ▸ (B.isPullback_relativeSpecCover U).flip

/-- **A quotient algebra gives a closed subscheme.** If `f : A ⟶ B` is a morphism of
quasi-coherent commutative `𝒪_X`-algebras whose underlying morphism of module sheaves is an
epimorphism (i.e. `f` is surjective), then `Spec_X(B) ⟶ Spec_X(A)` is a closed immersion. -/
theorem isClosedImmersion_relativeSpecMap_of_epi (f : A ⟶ B) [Epi f.hom.hom] :
    IsClosedImmersion (CommMon.relativeSpecMap f) := by
  refine IsZariskiLocalAtTarget.of_openCover A.relativeSpecCover fun U ↦ ?_
  have h := CommMon.isPullback_relativeSpecCover_f_relativeSpecMap f U
  -- Over the chart of `U`, the morphism is `Spec` of `Γ(A, U) ⟶ Γ(B, U)`, which is surjective
  -- because `U` is affine and `A` is quasi-coherent.
  -- The quasi-coherence instances are stated for `A.X`; the surjectivity lemma is stated for the
  -- carrier `A.toMon.X`, where typeclass search does not find them.
  have : A.toMon.X.IsQuasicoherent := inferInstanceAs A.X.IsQuasicoherent
  have : B.toMon.X.IsQuasicoherent := inferInstanceAs B.X.IsQuasicoherent
  have hs := Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen f.hom.hom U.val U.property
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (CommMon.sectionsAlgHom f U.val).toRingHom) fun y ↦
      (hs y).imp fun x hx ↦ (CommMon.sectionsAlgHom_apply f U.val x).trans hx
  have h' : IsClosedImmersion (h.isoPullback.inv ≫
      Spec.map (CommRingCat.ofHom (CommMon.sectionsAlgHom f U.val).toRingHom)) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mpr this
  rw [h.isoPullback_inv_snd] at h'
  exact h'

end CategoryTheory.CommMon
