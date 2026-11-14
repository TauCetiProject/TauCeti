/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Algebra
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward

/-!
# Full faithfulness of finite étale pullback from formal completion

Let `X` be a scheme, `I` an ideal sheaf on `X`, and `i : Z ⟶ X` a closed immersion with
`i.ker = I` (for instance `I.subschemeι : V(I) ⟶ X` or level `0` of `X.formalCompletion I`).
This file proves **Stacks Project, Lemma 58.17.1 (Tag 0EL8)**:

* if the formal completion functor `Scheme.formalCompletion.completionFunctor X I` is faithful on
  finite locally free `𝒪_X`-modules, then base change `FiniteEtaleScheme.pullback i` is faithful
  (`faithful_pullback_of_faithful_completion_finiteLocallyFree`);
* if `Scheme.formalCompletion.completionFunctor X I` is fully faithful on finite locally free
  `𝒪_X`-modules, then `FiniteEtaleScheme.pullback i` is fully faithful
  (`fullyFaithfulPullbackOfCompletionFiniteLocallyFree`);
* in particular, both conclusions hold whenever `Scheme.formalCompletion.completionFunctor X I` is
  faithful (respectively fully faithful) on all finitely presented `𝒪_X`-modules
  (`faithful_pullback_of_faithful_completion`, `fullyFaithfulPullbackOfCompletion`).

Stating the primary results under faithfulness or full faithfulness on `FiniteLocallyFreeSheaf X`
and without any Noetherian assumption allows them to apply directly in situations such as local
purity (Stacks Tags `0EKP` and `0EKS`), where formal completion along a hypersurface in the
punctured spectrum of a regular local ring is fully faithful on finite locally free sheaves even
though it need not be faithful on arbitrary coherent sheaves.

## Proof overview

Every finite étale morphism `p : Y ⟶ X` is affine (`IsFinite`), and its coordinate algebra
`p_* 𝒪_Y` has finite locally free underlying `𝒪_X`-module
(`Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra`). Embedding `FiniteEtaleScheme S`
fully faithfully into `AffineSchemeOver S` via `toAffineSchemeOver S` and composing with the
coordinate-algebra equivalence `affineFunctions S` translates base change of finite étale schemes
along `toScheme X I 0` into `QuasicoherentAlgebra.pullback (toScheme X I 0)` on opposite
categories. Moreover, the counit of `relativeSpecEquiv X` identifies `Y` over `X` with the
relative spectrum of `p_* 𝒪_Y`, so `Spec_X (p_* 𝒪_Y) ⟶ X` inherits étaleness (and hence formal
unramifiedness) from `p`. Injectivity and surjectivity on algebra morphisms then follow from
`Scheme.formalCompletion.pullback_toScheme_zero_map_injective` and
`Scheme.formalCompletion.pullback_toScheme_zero_map_surjective`. Finally, any closed immersion
`i : Z ⟶ X` with `i.ker = I` factors through `toScheme X I 0` by an isomorphism
(`IsClosedImmersion.isIso_lift`), transporting faithfulness and fullness from `toScheme X I 0` to
`i`.

## Main declarations

* `TauCeti.FiniteEtaleScheme.isEquivalence_pullback_of_isIso`: base change of finite étale schemes
  along an isomorphism is an equivalence of categories;
* `TauCeti.FiniteEtaleScheme.toAffineSchemeOver` and
  `TauCeti.FiniteEtaleScheme.pullbackCompToAffineSchemeOverIso`: the fully faithful forgetful
  functor to affine schemes over the base and its compatibility with base change;
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_faithful_completion_finiteLocallyFree`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_fullyFaithful_completion_finiteLocallyFree`, and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletionFiniteLocallyFree`: faithfulness,
  fullness, and full faithfulness of `FiniteEtaleScheme.pullback i` from `completionFunctor` on
  finite locally free sheaves;
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_faithful_completion`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_fullyFaithful_completion`,
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletion`, and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackSubschemeιOfCompletion`: specializations to
  finitely presented sheaves and to `I.subschemeι`.

## References

* [The Stacks Project, Lemma 58.17.1 (Tag 0EL8)](https://stacks.math.columbia.edu/tag/0EL8)
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section General

variable {S T : Scheme.{u}}

/-- Base change of finite étale schemes along an isomorphism of base schemes is an equivalence of
categories. -/
instance isEquivalence_pullback_of_isIso (f : T ⟶ S) [IsIso f] :
    (pullback f).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (pullback f) (pullback (inv f))
    (pullbackId.symm ≪≫ eqToIso (congrArg pullback (IsIso.inv_hom_id f).symm) ≪≫
      pullbackComp (inv f) f)
    ((pullbackComp f (inv f)).symm ≪≫ eqToIso (congrArg pullback (IsIso.hom_inv_id f)) ≪≫
      pullbackId)).isEquivalence_functor

-- Exposed so that `.left` and `.hom` of `(toAffineSchemeOver S).obj Y` compute definitionally to
-- `Y.obj.left` and `Y.obj.hom`, allowing `toAffineSchemeOver_obj_hom` and
-- `toAffineSchemeOver_map_left` to state homogeneous equalities.
/-- Every finite étale scheme over `S` is finite, hence affine, over `S`. This defines the
forgetful functor `FiniteEtaleScheme S ⥤ AffineSchemeOver S`. -/
@[expose]
noncomputable def toAffineSchemeOver (S : Scheme.{u}) :
    FiniteEtaleScheme S ⥤ AffineSchemeOver S where
  obj Y := MorphismProperty.Over.mk ⊤ Y.obj.hom inferInstance
  map g := MorphismProperty.Over.homMk g.hom.left (Over.w g.hom)

/-- The underlying scheme of `(toAffineSchemeOver S).obj Y` is that of `Y`. -/
@[simp]
theorem toAffineSchemeOver_obj_left (Y : FiniteEtaleScheme S) :
    ((toAffineSchemeOver S).obj Y).left = Y.obj.left :=
  (rfl)

/-- The structure morphism of `(toAffineSchemeOver S).obj Y` is that of `Y`. -/
@[simp]
theorem toAffineSchemeOver_obj_hom (Y : FiniteEtaleScheme S) :
    ((toAffineSchemeOver S).obj Y).hom = Y.obj.hom :=
  (rfl)

/-- On underlying morphisms of schemes, `toAffineSchemeOver S` is the identity. -/
@[simp]
theorem toAffineSchemeOver_map_left {Y₁ Y₂ : FiniteEtaleScheme S} (g : Y₁ ⟶ Y₂) :
    ((toAffineSchemeOver S).map g).left = g.hom.left :=
  (rfl)

/-- Finite étale schemes over `S` embed faithfully into affine schemes over `S`. -/
instance faithful_toAffineSchemeOver (S : Scheme.{u}) : (toAffineSchemeOver S).Faithful where
  map_injective h :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (congrArg (·.left) h))

/-- Finite étale schemes over `S` form a full subcategory of affine schemes over `S`. -/
instance full_toAffineSchemeOver (S : Scheme.{u}) : (toAffineSchemeOver S).Full where
  map_surjective φ :=
    ⟨ObjectProperty.homMk (Over.homMk φ.left (MorphismProperty.Over.w φ)),
      MorphismProperty.Over.Hom.ext rfl⟩

/-- The forgetful functor `toAffineSchemeOver` commutes with base change along any morphism
`f : T ⟶ S`: both functors send `Y` to `Limits.pullback Y.obj.hom f` with second projection to
`T`. -/
noncomputable def pullbackCompToAffineSchemeOverIso (f : T ⟶ S) :
    pullback f ⋙ toAffineSchemeOver T ≅
      toAffineSchemeOver S ⋙ baseChangeAffineSchemeOver f :=
  NatIso.ofComponents
    (fun Y ↦ MorphismProperty.Over.isoMk (Iso.refl (Limits.pullback Y.obj.hom f))
      (Category.id_comp _))
    fun {Y₁ Y₂} g ↦ by
      apply MorphismProperty.Over.Hom.ext
      -- Unfold composition in `AffineSchemeOver T`, where `@IsAffineHom` is a semireducible
      -- morphism property, to compare the underlying morphisms of pullback schemes.
      change ((Over.pullback f).map g.hom).left ≫ 𝟙 (Limits.pullback Y₂.obj.hom f) =
        𝟙 (Limits.pullback Y₁.obj.hom f) ≫
          ((baseChangeAffineSchemeOver f).map ((toAffineSchemeOver S).map g)).left
      refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
      refine Limits.pullback.hom_ext ?_ ?_
      · simp only [Over.pullback_map_left, Limits.pullback.lift_fst]
        exact (baseChangeAffineSchemeOver_map_left_fst f ((toAffineSchemeOver S).map g)).symm
      · simp only [Over.pullback_map_left, Limits.pullback.lift_snd]
        exact (baseChangeAffineSchemeOver_map_left_snd f ((toAffineSchemeOver S).map g)).symm

private noncomputable def baseChangeAffineSchemeOverCompAffineFunctionsIso (f : T ⟶ S) :
    baseChangeAffineSchemeOver f ⋙ affineFunctions T ≅
      affineFunctions S ⋙ (QuasicoherentAlgebra.pullback f).op :=
  Functor.fullyFaithfulCancelRight (relativeSpec T) <|
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (baseChangeAffineSchemeOver f) (relativeSpecCounit T) ≪≫
      Functor.rightUnitor (baseChangeAffineSchemeOver f) ≪≫
      (Functor.leftUnitor (baseChangeAffineSchemeOver f)).symm ≪≫
      Functor.isoWhiskerRight (relativeSpecCounit S).symm (baseChangeAffineSchemeOver f) ≪≫
      Functor.associator (affineFunctions S) (relativeSpec S) (baseChangeAffineSchemeOver f) ≪≫
      Functor.isoWhiskerLeft (affineFunctions S) (relativeSpecBaseChangeIso f).symm ≪≫
      (Functor.associator (affineFunctions S) (QuasicoherentAlgebra.pullback f).op
        (relativeSpec T)).symm

private noncomputable def pullbackCompCoordAlgebraOpIso (f : T ⟶ S) :
    pullback f ⋙ (toAffineSchemeOver T ⋙ affineFunctions T) ≅
      (toAffineSchemeOver S ⋙ affineFunctions S) ⋙ (QuasicoherentAlgebra.pullback f).op :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackCompToAffineSchemeOverIso f) (affineFunctions T) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toAffineSchemeOver S)
      (baseChangeAffineSchemeOverCompAffineFunctionsIso f) ≪≫
    (Functor.associator _ _ _).symm

end General

section FormalCompletion

variable {X Z : Scheme.{u}} {I : X.IdealSheafData}

private lemma isFiniteLocallyFree_coordAlgebra (Y : FiniteEtaleScheme X) :
    Scheme.Modules.isFiniteLocallyFree X
      (((affineFunctions X).obj ((toAffineSchemeOver X).obj Y)).unop).obj.X := by
  rw [affineFunctions_obj_unop_obj, toAffineSchemeOver_obj_hom]
  exact Y.obj.hom.isFiniteLocallyFree_pushforwardStructureAlgebra

private lemma etale_relativeSpecToBase_coordAlgebra (Y : FiniteEtaleScheme X) :
    Etale
      (((affineFunctions X).obj ((toAffineSchemeOver X).obj Y)).unop).obj.relativeSpecToBase := by
  let V := (toAffineSchemeOver X).obj Y
  let c := (relativeSpecCounit X).app V
  let u : (((affineFunctions X).obj V).unop).obj.relativeSpec ⟶ Y.obj.left := c.hom.left
  have hu_iso : IsIso u :=
    ⟨⟨c.inv.left, congrArg (·.left) c.hom_inv_id, congrArg (·.left) c.inv_hom_id⟩⟩
  have hw : u ≫ Y.obj.hom =
      (((affineFunctions X).obj V).unop).obj.relativeSpecToBase :=
    MorphismProperty.Over.w c.hom
  rw [← hw]
  infer_instance

private lemma completion_injective_of_faithful_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    ∀ ⦃M N : FinitelyPresentedSheaf X⦄,
      Scheme.Modules.isFiniteLocallyFree X M.obj →
      Scheme.Modules.isFiniteLocallyFree X N.obj →
      Function.Injective
        (fun f : M ⟶ N ↦ (Scheme.formalCompletion.completionFunctor X I).map f) := by
  intro M N hM hN f₁ f₂ hf
  let M' : FiniteLocallyFreeSheaf X := ⟨M.obj, hM⟩
  let N' : FiniteLocallyFreeSheaf X := ⟨N.obj, hN⟩
  have h := (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).map_injective
    (X := M') (Y := N') (a₁ := ObjectProperty.homMk f₁.hom) (a₂ := ObjectProperty.homMk f₂.hom) hf
  exact ObjectProperty.hom_ext _ (congrArg (·.hom) h)

private lemma completion_surjective_of_full_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full] :
    ∀ ⦃M N : FinitelyPresentedSheaf X⦄,
      Scheme.Modules.isFiniteLocallyFree X M.obj →
      Scheme.Modules.isFiniteLocallyFree X N.obj →
      Function.Surjective
        (fun f : M ⟶ N ↦ (Scheme.formalCompletion.completionFunctor X I).map f) := by
  intro M N hM hN Φ
  let M' : FiniteLocallyFreeSheaf X := ⟨M.obj, hM⟩
  let N' : FiniteLocallyFreeSheaf X := ⟨N.obj, hN⟩
  obtain ⟨f', hf'⟩ := (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).map_surjective (X := M') (Y := N') Φ
  exact ⟨(FiniteLocallyFreeSheaf.toFinitelyPresented X).map f', hf'⟩

/-- Base change of finite étale schemes to level `0` of `X.formalCompletion I` is faithful when
`completionFunctor X I` is faithful on finite locally free sheaves. -/
@[stacks 0EL8]
instance faithful_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful := by
  have : ((toAffineSchemeOver X ⋙ affineFunctions X) ⋙
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I 0)).op).Faithful :=
    ⟨fun {Y₁ Y₂} {_ _} hφ ↦ (toAffineSchemeOver X ⋙ affineFunctions X).map_injective <| by
      have : Etale
          (((affineFunctions X).obj ((toAffineSchemeOver X).obj Y₂)).unop).obj.relativeSpecToBase :=
        etale_relativeSpecToBase_coordAlgebra Y₂
      exact Quiver.Hom.unop_inj (Scheme.formalCompletion.pullback_toScheme_zero_map_injective
        (P := Scheme.Modules.isFiniteLocallyFree X) (fun _ h ↦ h.2)
        completion_injective_of_faithful_finiteLocallyFree
        (isFiniteLocallyFree_coordAlgebra Y₁) (isFiniteLocallyFree_coordAlgebra Y₂)
        (congrArg Quiver.Hom.unop hφ))⟩
  exact Functor.Faithful.of_comp_iso
    (pullbackCompCoordAlgebraOpIso (Scheme.formalCompletion.toScheme X I 0))

/-- Base change of finite étale schemes to level `0` of `X.formalCompletion I` is full when
`completionFunctor X I` is fully faithful on finite locally free sheaves. -/
@[stacks 0EL8]
instance full_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full := by
  have : ((toAffineSchemeOver X ⋙ affineFunctions X) ⋙
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I 0)).op).Full :=
    ⟨fun {Y₁ Y₂} ψ₀ ↦ by
      have : Etale
          (((affineFunctions X).obj ((toAffineSchemeOver X).obj Y₂)).unop).obj.relativeSpecToBase :=
        etale_relativeSpecToBase_coordAlgebra Y₂
      obtain ⟨ψ, hψ⟩ := Scheme.formalCompletion.pullback_toScheme_zero_map_surjective
        (P := Scheme.Modules.isFiniteLocallyFree X) (fun _ h ↦ h.2)
        completion_surjective_of_full_finiteLocallyFree
        completion_injective_of_faithful_finiteLocallyFree
        (isFiniteLocallyFree_coordAlgebra Y₁) (isFiniteLocallyFree_coordAlgebra Y₂) ψ₀.unop
      exact ⟨(toAffineSchemeOver X ⋙ affineFunctions X).preimage ψ.op,
        (congrArg (QuasicoherentAlgebra.pullback
          (Scheme.formalCompletion.toScheme X I 0)).op.map
          ((toAffineSchemeOver X ⋙ affineFunctions X).map_preimage ψ.op)).trans
          (Quiver.Hom.unop_inj hψ)⟩⟩
  exact Functor.Full.of_comp_faithful_iso
    (pullbackCompCoordAlgebraOpIso (Scheme.formalCompletion.toScheme X I 0))

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), faithfulness.** Let `i : Z ⟶ X` be a closed
immersion with ideal sheaf `i.ker = I`. If `Scheme.formalCompletion.completionFunctor X I` is
faithful on finite locally free `𝒪_X`-modules, then base change of finite étale schemes along `i`
is faithful. -/
@[stacks 0EL8]
theorem faithful_pullback_of_faithful_completion_finiteLocallyFree
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Faithful := by
  let t₀ := Scheme.formalCompletion.toScheme X I 0
  have hker : t₀.ker = i.ker :=
    ((Scheme.formalCompletion.ker_toScheme X I 0).trans (pow_one I)).trans hi.symm
  let l : Z ⟶ (X.formalCompletion I).X 0 := IsClosedImmersion.lift t₀ i hker.le
  have : IsIso l := IsClosedImmersion.isIso_lift t₀ i hker
  have hl : l ≫ t₀ = i := IsClosedImmersion.lift_fac t₀ i hker.le
  exact Functor.Faithful.of_iso
    (eqToIso (congrArg pullback hl.symm) ≪≫ pullbackComp l t₀).symm

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), fullness.** Let `i : Z ⟶ X` be a closed immersion
with ideal sheaf `i.ker = I`. If `Scheme.formalCompletion.completionFunctor X I` is fully faithful
on finite locally free `𝒪_X`-modules, then base change of finite étale schemes along `i` is
full. -/
@[stacks 0EL8]
theorem full_pullback_of_fullyFaithful_completion_finiteLocallyFree
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Full := by
  let t₀ := Scheme.formalCompletion.toScheme X I 0
  have hker : t₀.ker = i.ker :=
    ((Scheme.formalCompletion.ker_toScheme X I 0).trans (pow_one I)).trans hi.symm
  let l : Z ⟶ (X.formalCompletion I).X 0 := IsClosedImmersion.lift t₀ i hker.le
  have : IsIso l := IsClosedImmersion.isIso_lift t₀ i hker
  have hl : l ≫ t₀ = i := IsClosedImmersion.lift_fac t₀ i hker.le
  have : (pullback t₀ ⋙ pullback l).Full := Functor.Full.comp (pullback t₀) (pullback l)
  exact Functor.Full.of_iso
    (eqToIso (congrArg pullback hl.symm) ≪≫ pullbackComp l t₀).symm

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8).** Let `i : Z ⟶ X` be a closed immersion with ideal
sheaf `i.ker = I`. If `Scheme.formalCompletion.completionFunctor X I` is fully faithful on finite
locally free `𝒪_X`-modules, then `FiniteEtaleScheme.pullback i` is fully faithful. -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfCompletionFiniteLocallyFree
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).FullyFaithful :=
  have := faithful_pullback_of_faithful_completion_finiteLocallyFree i hi
  have := full_pullback_of_fullyFaithful_completion_finiteLocallyFree i hi
  .ofFullyFaithful (pullback i)

/-- Base change of finite étale schemes along `I.subschemeι : V(I) ⟶ X` is faithful when
`completionFunctor X I` is faithful on finite locally free sheaves. -/
@[stacks 0EL8]
instance faithful_pullback_subschemeι_of_faithful_completion_finiteLocallyFree
    (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_of_faithful_completion_finiteLocallyFree I.subschemeι I.ker_subschemeι

/-- Base change of finite étale schemes along `I.subschemeι : V(I) ⟶ X` is full when
`completionFunctor X I` is fully faithful on finite locally free sheaves. -/
@[stacks 0EL8]
instance full_pullback_subschemeι_of_fullyFaithful_completion_finiteLocallyFree
    (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_of_fullyFaithful_completion_finiteLocallyFree I.subschemeι I.ker_subschemeι

/-- Specialization of `fullyFaithfulPullbackOfCompletionFiniteLocallyFree` to the canonical closed
immersion `I.subschemeι : V(I) ⟶ X`. -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackSubschemeιOfCompletionFiniteLocallyFree
    (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  .ofFullyFaithful (pullback I.subschemeι)

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), faithfulness for finitely presented completion.**
Let `i : Z ⟶ X` be a closed immersion with `i.ker = I`. If
`Scheme.formalCompletion.completionFunctor X I` is faithful on finitely presented `𝒪_X`-modules,
then `FiniteEtaleScheme.pullback i` is faithful. -/
@[stacks 0EL8]
theorem faithful_pullback_of_faithful_completion
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Faithful :=
  faithful_pullback_of_faithful_completion_finiteLocallyFree i hi

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), fullness for finitely presented completion.**
Let `i : Z ⟶ X` be a closed immersion with `i.ker = I`. If
`Scheme.formalCompletion.completionFunctor X I` is fully faithful on finitely presented
`𝒪_X`-modules, then `FiniteEtaleScheme.pullback i` is full. -/
@[stacks 0EL8]
theorem full_pullback_of_fullyFaithful_completion
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Full :=
  full_pullback_of_fullyFaithful_completion_finiteLocallyFree i hi

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8).** Let `i : Z ⟶ X` be a closed immersion with
`i.ker = I`. If `Scheme.formalCompletion.completionFunctor X I` is fully faithful on finitely
presented `𝒪_X`-modules (hence on coherent sheaves when `X` is locally Noetherian), then
`FiniteEtaleScheme.pullback i` is fully faithful. -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfCompletion
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).FullyFaithful :=
  fullyFaithfulPullbackOfCompletionFiniteLocallyFree i hi

/-- Specialization of `fullyFaithfulPullbackOfCompletion` to `I.subschemeι : V(I) ⟶ X`. -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackSubschemeιOfCompletion
    (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  .ofFullyFaithful (pullback I.subschemeι)

end FormalCompletion

end TauCeti.FiniteEtaleScheme
