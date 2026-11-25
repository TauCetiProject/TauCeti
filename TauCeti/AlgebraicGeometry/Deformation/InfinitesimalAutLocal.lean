/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import TauCeti.AlgebraicGeometry.Deformation.InfinitesimalAut

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Infinitesimal automorphisms are local

Let `X` be a scheme over `Spec R` and `X[ε] = X ×_{Spec R} Spec R[ε]` its trivial first-order
deformation. This file shows that the infinitesimal automorphisms of `X`
(`TauCeti.AlgebraicGeometry.infinitesimalAut`) are local on `X`.

The inclusion `X ⟶ X[ε]` over `ε ↦ 0` is the base change of `Spec R ⟶ Spec R[ε]`, a homeomorphism
because its kernel `ε R` is nilpotent, so it is surjective
(`TauCeti.AlgebraicGeometry.surjective_dualNumberDeformationι`). An infinitesimal automorphism
restricts to the identity of `X` along this inclusion, so it is the identity on the points of
`X[ε]` (`TauCeti.AlgebraicGeometry.infinitesimalAut_base_apply`). For an open immersion
`j : U ⟶ X`, the deformation `U[ε]` is the open subscheme of `X[ε]` over `U`
(`TauCeti.AlgebraicGeometry.isPullback_dualNumberDeformationMap`), so every infinitesimal
automorphism of `X` restricts to one of `U` (`TauCeti.AlgebraicGeometry.infinitesimalAutRestrict`),
and an infinitesimal automorphism is determined by its restrictions to the members of an open
cover (`TauCeti.AlgebraicGeometry.infinitesimalAut_ext_of_openCover`).

Together with the affine case `TauCeti.AlgebraicGeometry.derivationMulEquivInfinitesimalAut`, this
is the first step in identifying the infinitesimal automorphisms of `X` with the global
`R`-derivations of `𝒪_X`.

## Main definitions

* `TauCeti.AlgebraicGeometry.dualNumberDeformationMap f j`: for `j : U ⟶ X`, the morphism
  `U[ε] ⟶ X[ε]` over `Spec R[ε]`.
* `TauCeti.AlgebraicGeometry.infinitesimalAutRestrict f j`: for an open immersion `j : U ⟶ X`, the
  restriction of infinitesimal automorphisms of `X` to `U`.

## Main results

* `TauCeti.AlgebraicGeometry.isPullback_dualNumberDeformationι`: the inclusion `X ⟶ X[ε]` is the
  base change of `Spec R ⟶ Spec R[ε]`.
* `TauCeti.AlgebraicGeometry.infinitesimalAut_base_apply`: an infinitesimal automorphism is the
  identity on points.
* `TauCeti.AlgebraicGeometry.infinitesimalAutRestrict_comp_dualNumberDeformationMap`: the
  restriction is characterized by `e|_U ∘ (U[ε] ⟶ X[ε]) = (U[ε] ⟶ X[ε]) ∘ e`.
* `TauCeti.AlgebraicGeometry.infinitesimalAut_ext_of_openCover`: infinitesimal automorphisms with
  the same restrictions to the members of an open cover are equal.

## References

* R. Hartshorne, *Deformation Theory*, Graduate Texts in Mathematics 257, Springer, 2010,
  Chapter 1, for infinitesimal automorphisms as derivations.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry DualNumber TrivSqZeroExt

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The inclusion `X ⟶ X[ε]` over `ε ↦ 0` is the base change of the section
`Spec R ⟶ Spec R[ε]` along the projection `X[ε] ⟶ Spec R[ε]`. -/
theorem isPullback_dualNumberDeformationι :
    IsPullback (dualNumberDeformationι f) f
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))))
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R : R[ε] →+* R))) := by
  refine IsPullback.of_right ?_ (dualNumberDeformationι_snd f)
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))))
  rw [dualNumberDeformationι_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert IsPullback.id_horiz f
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp

/-- The section `Spec R ⟶ Spec R[ε]` over `ε ↦ 0` is surjective, since `ε` is nilpotent. -/
instance surjective_spec_map_fstHom :
    Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R : R[ε] →+* R))) :=
  ⟨(PrimeSpectrum.isHomeomorph_comap _ (fun x ↦ ⟨1, one_pos, inl x, by simp⟩) fun x hx ↦
    ⟨2, by
      have hx : x.fst = 0 := hx
      ext <;> simp [pow_two, hx]⟩).surjective⟩

/-- The inclusion `X ⟶ X[ε]` over `ε ↦ 0` is surjective. -/
instance surjective_dualNumberDeformationι : Surjective (dualNumberDeformationι f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_dualNumberDeformationι f).flip inferInstance

/-- An infinitesimal automorphism of `X` is the identity on the points of `X[ε]`. -/
theorem infinitesimalAut_base_apply (e : infinitesimalAut f) (x : (dualNumberDeformation f).left) :
    e.val.asIso.hom.left x = x := by
  obtain ⟨y, rfl⟩ := (dualNumberDeformationι f).surjective x
  rw [← Scheme.Hom.comp_apply, (mem_infinitesimalAut_iff f e.val).1 e.property]

/-! ### Restriction to open subschemes -/

section Restrict

variable {U : Scheme.{u}} (j : U ⟶ X)

/-- For a morphism `j : U ⟶ X`, the morphism `U[ε] ⟶ X[ε]` of trivial first-order deformations,
the base change of `j` along `Spec R[ε] ⟶ Spec R`. -/
def dualNumberDeformationMap :
    (dualNumberDeformation (j ≫ f)).left ⟶ (dualNumberDeformation f).left :=
  pullback.map (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) f
    (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) j (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem dualNumberDeformationMap_fst :
    dualNumberDeformationMap f j ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) =
      pullback.fst (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem dualNumberDeformationMap_snd :
    dualNumberDeformationMap f j ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) =
      pullback.snd (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The morphism `U[ε] ⟶ X[ε]` is the base change of `j : U ⟶ X` along `X[ε] ⟶ X`. -/
theorem isPullback_dualNumberDeformationMap :
    IsPullback (dualNumberDeformationMap f j)
      (pullback.fst (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε])))) j := by
  refine IsPullback.of_right ?_ (dualNumberDeformationMap_fst f j)
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε])))).flip
  rw [dualNumberDeformationMap_snd]
  exact (IsPullback.of_hasPullback (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R[ε])))).flip

/-- The base change `U[ε] ⟶ X[ε]` of an open immersion is an open immersion. -/
instance isOpenImmersion_dualNumberDeformationMap [IsOpenImmersion j] :
    IsOpenImmersion (dualNumberDeformationMap f j) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_dualNumberDeformationMap f j).flip inferInstance

/-- The inclusions over `ε ↦ 0` commute with `U[ε] ⟶ X[ε]`. -/
@[reassoc (attr := simp)]
theorem dualNumberDeformationι_dualNumberDeformationMap :
    dualNumberDeformationι (j ≫ f) ≫ dualNumberDeformationMap f j = j ≫ dualNumberDeformationι f :=
  pullback.hom_ext (by simp) (by simp)

/-- An infinitesimal automorphism `e` of `X` maps the image of `U[ε] ⟶ X[ε]` onto itself, since it
is the identity on points. -/
theorem range_dualNumberDeformationMap_comp (e : infinitesimalAut f) :
    Set.range (dualNumberDeformationMap f j ≫ e.val.asIso.hom.left) =
      Set.range (dualNumberDeformationMap f j) := by
  refine Set.ext fun x ↦ ⟨?_, ?_⟩ <;> rintro ⟨y, rfl⟩ <;> refine ⟨y, ?_⟩
  · rw [Scheme.Hom.comp_apply, infinitesimalAut_base_apply]
  · rw [Scheme.Hom.comp_apply, infinitesimalAut_base_apply]

variable [IsOpenImmersion j]

/-- The restriction of an infinitesimal automorphism `e` of `X` to the open subscheme `U[ε]`, as an
automorphism of the scheme `U[ε]`. -/
private def restrictIso (e : infinitesimalAut f) :
    (dualNumberDeformation (j ≫ f)).left ≅ (dualNumberDeformation (j ≫ f)).left :=
  IsOpenImmersion.isoOfRangeEq (dualNumberDeformationMap f j ≫ e.val.asIso.hom.left)
    (dualNumberDeformationMap f j) (range_dualNumberDeformationMap_comp f j e)

@[reassoc]
private theorem restrictIso_hom_comp (e : infinitesimalAut f) :
    (restrictIso f j e).hom ≫ dualNumberDeformationMap f j =
      dualNumberDeformationMap f j ≫ e.val.asIso.hom.left :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The restriction of an infinitesimal automorphism to the open subscheme `U[ε]`, as an
automorphism over `Spec R[ε]`. -/
private def restrictAut (e : infinitesimalAut f) : Aut (dualNumberDeformation (j ≫ f)) :=
  .of <| Over.isoMk (restrictIso f j e) <| by
    change (restrictIso f j e).hom ≫ pullback.snd (j ≫ f) _ = pullback.snd (j ≫ f) _
    rw [← dualNumberDeformationMap_snd, restrictIso_hom_comp_assoc]
    exact congrArg (dualNumberDeformationMap f j ≫ ·) (Over.w e.val.asIso.hom)

private theorem restrictAut_asIso_hom_left (e : infinitesimalAut f) :
    (restrictAut f j e).asIso.hom.left = (restrictIso f j e).hom :=
  rfl

/-- Automorphisms of `U[ε]` over `Spec R[ε]` agree once they agree after `U[ε] ⟶ X[ε]`. -/
private theorem aut_ext {a b : Aut (dualNumberDeformation (j ≫ f))}
    (h : a.asIso.hom.left ≫ dualNumberDeformationMap f j =
      b.asIso.hom.left ≫ dualNumberDeformationMap f j) : a = b :=
  Aut.ext (Iso.ext (Over.OverMorphism.ext ((cancel_mono _).1 h)))

/-- **Restriction of infinitesimal automorphisms to an open subscheme.** For an open immersion
`j : U ⟶ X`, an infinitesimal automorphism `e` of `X` restricts to the infinitesimal automorphism
of `U` characterized by `e|_U ∘ (U[ε] ⟶ X[ε]) = (U[ε] ⟶ X[ε]) ∘ e`
(`infinitesimalAutRestrict_comp_dualNumberDeformationMap`). -/
def infinitesimalAutRestrict : infinitesimalAut f →* infinitesimalAut (j ≫ f) where
  toFun e := ⟨restrictAut f j e, by
    rw [mem_infinitesimalAut_iff, restrictAut_asIso_hom_left,
      ← cancel_mono (dualNumberDeformationMap f j), Category.assoc, restrictIso_hom_comp,
      dualNumberDeformationι_dualNumberDeformationMap_assoc,
      (mem_infinitesimalAut_iff f e.val).1 e.property,
      dualNumberDeformationι_dualNumberDeformationMap]⟩
  map_one' := Subtype.ext <| aut_ext f j <| by
    rw [restrictAut_asIso_hom_left, restrictIso_hom_comp]
    simp
  map_mul' e e' := Subtype.ext <| aut_ext f j <| by
    simp only [Subgroup.coe_mul, Aut.mul_asIso, Iso.trans_hom, Over.comp_left, Category.assoc,
      restrictAut_asIso_hom_left, restrictIso_hom_comp, restrictIso_hom_comp_assoc]

/-- The restriction `e|_U` of an infinitesimal automorphism `e` to an open subscheme satisfies
`e|_U ∘ (U[ε] ⟶ X[ε]) = (U[ε] ⟶ X[ε]) ∘ e`. -/
@[reassoc]
theorem infinitesimalAutRestrict_comp_dualNumberDeformationMap (e : infinitesimalAut f) :
    (infinitesimalAutRestrict f j e).val.asIso.hom.left ≫ dualNumberDeformationMap f j =
      dualNumberDeformationMap f j ≫ e.val.asIso.hom.left :=
  restrictIso_hom_comp f j e

end Restrict

/-- **Infinitesimal automorphisms are local.** Two infinitesimal automorphisms of `X` whose
restrictions to the members of an open cover of `X` agree are equal. -/
theorem infinitesimalAut_ext_of_openCover (𝒰 : X.OpenCover) {e e' : infinitesimalAut f}
    (h : ∀ i, infinitesimalAutRestrict f (𝒰.f i) e = infinitesimalAutRestrict f (𝒰.f i) e') :
    e = e' := by
  let 𝒱 : (dualNumberDeformation f).left.OpenCover :=
    Scheme.Cover.mkOfCovers 𝒰.I₀ _ (fun i ↦ dualNumberDeformationMap f (𝒰.f i)) fun x ↦ by
      obtain ⟨y, rfl⟩ := (dualNumberDeformationι f).surjective x
      obtain ⟨i, z, rfl⟩ := 𝒰.exists_eq y
      exact ⟨i, dualNumberDeformationι (𝒰.f i ≫ f) z, by
        rw [← Scheme.Hom.comp_apply, dualNumberDeformationι_dualNumberDeformationMap,
          Scheme.Hom.comp_apply]⟩
  refine Subtype.ext (Aut.ext (Iso.ext (Over.OverMorphism.ext (𝒱.hom_ext _ _ fun (i : 𝒰.I₀) ↦ ?_))))
  exact (infinitesimalAutRestrict_comp_dualNumberDeformationMap f (𝒰.f i) e).symm.trans
    ((congrArg (fun a ↦ a.val.asIso.hom.left ≫ dualNumberDeformationMap f (𝒰.f i)) (h i)).trans
      (infinitesimalAutRestrict_comp_dualNumberDeformationMap f (𝒰.f i) e'))

end TauCeti.AlgebraicGeometry
