/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import TauCeti.AlgebraicGeometry.Deformation.InfinitesimalAut.Basic

import Mathlib.AlgebraicGeometry.PullbackCarrier
import TauCeti.AlgebraicGeometry.Morphisms.Thickening
import TauCeti.CategoryTheory.Comma.Over

/-!
# Infinitesimal automorphisms are determined by their restrictions to an open cover

Let `X` be a scheme over `Spec R` and `X[ε] = X ×_{Spec R} Spec R[ε]` its trivial first-order
deformation. This file restricts the infinitesimal automorphisms of `X`
(`TauCeti.AlgebraicGeometry.infinitesimalAut`) to open subschemes of `X` and shows that an
infinitesimal automorphism is determined by its restrictions to the members of an open cover of
`X`. This is the uniqueness half of locality; gluing compatible local infinitesimal automorphisms
is not proved here.

The inclusion `X ⟶ X[ε]` over `ε ↦ 0` is the base change of `Spec R ⟶ Spec R[ε]`, a homeomorphism
because its kernel `ε R` is nilpotent
(`TauCeti.AlgebraicGeometry.IsFirstOrderThickening.SpecMap_fstHom`), so it is surjective
(`TauCeti.AlgebraicGeometry.surjective_dualNumberDeformationι`). An infinitesimal automorphism
restricts to the identity of `X` along this inclusion, so it is the identity on the points of
`X[ε]` (`TauCeti.AlgebraicGeometry.infinitesimalAut_base_apply`). For an open immersion
`j : U ⟶ X`, the deformation `U[ε]` is the open subscheme of `X[ε]` over `U`
(`TauCeti.AlgebraicGeometry.isPullback_dualNumberDeformationMap`), so every infinitesimal
automorphism of `X` restricts to one of `U` (`TauCeti.AlgebraicGeometry.infinitesimalAutRestrict`),
and an infinitesimal automorphism is determined by its restrictions to the members of an open
cover (`TauCeti.AlgebraicGeometry.infinitesimalAut_ext_of_openCover`), using the induced open
cover of `X[ε]` (`TauCeti.AlgebraicGeometry.dualNumberDeformationOpenCover`).

Together with the affine case `TauCeti.AlgebraicGeometry.derivationMulEquivInfinitesimalAut`, this
is the first step in identifying the infinitesimal automorphisms of `X` with the global
`R`-derivations of `𝒪_X`.

## Main definitions

* `TauCeti.AlgebraicGeometry.dualNumberDeformationMap f j`: for `j : U ⟶ X`, the morphism
  `U[ε] ⟶ X[ε]` over `Spec R[ε]`.
* `TauCeti.AlgebraicGeometry.infinitesimalAutRestrict f j`: for an open immersion `j : U ⟶ X`, the
  restriction of infinitesimal automorphisms of `X` to `U`.
* `TauCeti.AlgebraicGeometry.dualNumberDeformationOpenCover f 𝒰`: the open cover of `X[ε]` by the
  deformations `U_i[ε]` of the members of an open cover `𝒰` of `X`.

## Main results

* `TauCeti.AlgebraicGeometry.isPullback_dualNumberDeformationι`: the inclusion `X ⟶ X[ε]` is the
  base change of `Spec R ⟶ Spec R[ε]`.
* `TauCeti.AlgebraicGeometry.infinitesimalAut_base_apply`: an infinitesimal automorphism is the
  identity on points.
* `TauCeti.AlgebraicGeometry.infinitesimalAutRestrict_comp_dualNumberDeformationMap`: the
  restriction satisfies `e|_U ≫ (U[ε] ⟶ X[ε]) = (U[ε] ⟶ X[ε]) ≫ e`, and
  `TauCeti.AlgebraicGeometry.eq_infinitesimalAutRestrict_iff` says this characterizes it.
* `TauCeti.AlgebraicGeometry.dualNumberDeformationMap_comp`: compatibility of `U[ε] ⟶ X[ε]` with
  composition of open immersions.
* `TauCeti.AlgebraicGeometry.infinitesimalAutRestrict_infinitesimalAutRestrict`: restricting to
  `U` and then to `V` is restricting along the composite `V ⟶ U ⟶ X`.
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
  have hfst : (TrivSqZeroExt.fstHom R R R : R[ε] →+* R).comp (algebraMap R R[ε]) =
      RingHom.id R := by
    ext r
    simp
  rw [dualNumberDeformationι_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfst,
    CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.id_horiz f

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
the base change of `j` along `Spec R[ε] ⟶ Spec R`: the action of the pullback functor defining
`dualNumberDeformation` on `j`, viewed as a morphism over `Spec R`. -/
def dualNumberDeformationMap :
    (dualNumberDeformation (j ≫ f)).left ⟶ (dualNumberDeformation f).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R[ε])))).map
    (Over.homMk j rfl : Over.mk (j ≫ f) ⟶ Over.mk f)).left

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
  pullback.lift_snd _ _ _

/-- The morphism `U[ε] ⟶ X[ε]` as a `pullback.map`. -/
theorem dualNumberDeformationMap_eq_pullbackMap :
    dualNumberDeformationMap f j =
      pullback.map (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) f
        (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))) j (𝟙 _) (𝟙 _) (by simp) (by simp) :=
  pullback.hom_ext (by simp) (by simp)

/-- The morphism `U[ε] ⟶ X[ε]` is the base change of `j : U ⟶ X` along `X[ε] ⟶ X`. -/
theorem isPullback_dualNumberDeformationMap :
    IsPullback (dualNumberDeformationMap f j)
      (pullback.fst (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε])))) j :=
  Over.isPullback_pullback_map_left _ _

/-- The base change `U[ε] ⟶ X[ε]` of an open immersion is an open immersion. -/
instance isOpenImmersion_dualNumberDeformationMap [IsOpenImmersion j] :
    IsOpenImmersion (dualNumberDeformationMap f j) := by
  rw [dualNumberDeformationMap_eq_pullbackMap]
  infer_instance

/-- The inclusions over `ε ↦ 0` commute with `U[ε] ⟶ X[ε]`. -/
@[reassoc (attr := simp)]
theorem dualNumberDeformationι_dualNumberDeformationMap :
    dualNumberDeformationι (j ≫ f) ≫ dualNumberDeformationMap f j = j ≫ dualNumberDeformationι f :=
  pullback.hom_ext (by simp) (by simp)

/-- For `j = 𝟙 X`, the morphism `X[ε] ⟶ X[ε]` is the identity, up to reindexing along
`𝟙 X ≫ f = f`. -/
theorem dualNumberDeformationMap_id :
    dualNumberDeformationMap f (𝟙 X) = (pullback.congrHom (Category.id_comp f) rfl).hom :=
  pullback.hom_ext (by simp) (by simp)

/-- For `k : V ⟶ U`, the composite `V[ε] ⟶ U[ε] ⟶ X[ε]` is the morphism `V[ε] ⟶ X[ε]` for
`k ≫ j`, up to reindexing along `k ≫ j ≫ f = (k ≫ j) ≫ f`. -/
@[reassoc]
theorem dualNumberDeformationMap_comp {V : Scheme.{u}} (k : V ⟶ U) :
    dualNumberDeformationMap (j ≫ f) k ≫ dualNumberDeformationMap f j =
      (pullback.congrHom (Category.assoc k j f).symm rfl).hom ≫
        dualNumberDeformationMap f (k ≫ j) :=
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
    simpa [← dualNumberDeformationMap_snd, restrictIso_hom_comp_assoc] using
      congrArg (dualNumberDeformationMap f j ≫ ·) (Over.w e.val.asIso.hom)

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
of `U` characterized by `e|_U ≫ (U[ε] ⟶ X[ε]) = (U[ε] ⟶ X[ε]) ≫ e`
(`infinitesimalAutRestrict_comp_dualNumberDeformationMap`, `eq_infinitesimalAutRestrict_iff`). -/
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
`e|_U ≫ (U[ε] ⟶ X[ε]) = (U[ε] ⟶ X[ε]) ≫ e`. -/
@[reassoc (attr := simp)]
theorem infinitesimalAutRestrict_comp_dualNumberDeformationMap (e : infinitesimalAut f) :
    (infinitesimalAutRestrict f j e).val.asIso.hom.left ≫ dualNumberDeformationMap f j =
      dualNumberDeformationMap f j ≫ e.val.asIso.hom.left :=
  restrictIso_hom_comp f j e

/-- The restriction `e|_U` is the unique infinitesimal automorphism `g` of `U` with
`g ≫ (U[ε] ⟶ X[ε]) = (U[ε] ⟶ X[ε]) ≫ e`, since `U[ε] ⟶ X[ε]` is a monomorphism. -/
theorem eq_infinitesimalAutRestrict_iff {e : infinitesimalAut f} {g : infinitesimalAut (j ≫ f)} :
    g = infinitesimalAutRestrict f j e ↔
      g.val.asIso.hom.left ≫ dualNumberDeformationMap f j =
        dualNumberDeformationMap f j ≫ e.val.asIso.hom.left :=
  ⟨by rintro rfl; exact infinitesimalAutRestrict_comp_dualNumberDeformationMap f j e,
    fun h ↦ Subtype.ext <| aut_ext f j <|
      h.trans (infinitesimalAutRestrict_comp_dualNumberDeformationMap f j e).symm⟩

/-- **Transitivity of restriction.** For open immersions `k : V ⟶ U` and `j : U ⟶ X`, restricting
an infinitesimal automorphism `e` of `X` to `U` and then to `V` gives its restriction along
`k ≫ j`, up to reindexing along `k ≫ j ≫ f = (k ≫ j) ≫ f`. -/
theorem infinitesimalAutRestrict_infinitesimalAutRestrict {V : Scheme.{u}} (k : V ⟶ U)
    [IsOpenImmersion k] (e : infinitesimalAut f) :
    (infinitesimalAutRestrict (j ≫ f) k (infinitesimalAutRestrict f j e)).val.asIso.hom.left =
      (pullback.congrHom (Category.assoc k j f).symm rfl).hom ≫
        (infinitesimalAutRestrict f (k ≫ j) e).val.asIso.hom.left ≫
          (pullback.congrHom (Category.assoc k j f).symm rfl).inv := by
  rw [← cancel_mono (dualNumberDeformationMap (j ≫ f) k ≫ dualNumberDeformationMap f j),
    infinitesimalAutRestrict_comp_dualNumberDeformationMap_assoc,
    infinitesimalAutRestrict_comp_dualNumberDeformationMap, dualNumberDeformationMap_comp_assoc,
    dualNumberDeformationMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    infinitesimalAutRestrict_comp_dualNumberDeformationMap]

end Restrict

/-- The open cover of `X[ε]` by the deformations `U_i[ε] ⟶ X[ε]` of the members `U_i ⟶ X` of an
open cover `𝒰` of `X`: the pullback of `𝒰` along `X[ε] ⟶ X`, with its members identified with the
`U_i[ε]` by `isPullback_dualNumberDeformationMap`. -/
@[expose]
def dualNumberDeformationOpenCover (𝒰 : X.OpenCover) : (dualNumberDeformation f).left.OpenCover :=
  Scheme.Cover.copy
    (𝒰.pullback₁ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R[ε]))))) 𝒰.I₀ _
    (fun i ↦ dualNumberDeformationMap f (𝒰.f i)) (Equiv.refl _)
    (fun i ↦ (isPullback_dualNumberDeformationMap f (𝒰.f i)).isoPullback)
    fun i ↦ ((isPullback_dualNumberDeformationMap f (𝒰.f i)).isoPullback_hom_fst).symm

@[simp]
theorem dualNumberDeformationOpenCover_f (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    (dualNumberDeformationOpenCover f 𝒰).f i = dualNumberDeformationMap f (𝒰.f i) :=
  rfl

/-- **Infinitesimal automorphisms are determined by their restrictions to an open cover.** Two
infinitesimal automorphisms of `X` whose restrictions to the members of an open cover of `X` agree
are equal. -/
theorem infinitesimalAut_ext_of_openCover (𝒰 : X.OpenCover) {e e' : infinitesimalAut f}
    (h : ∀ i, infinitesimalAutRestrict f (𝒰.f i) e = infinitesimalAutRestrict f (𝒰.f i) e') :
    e = e' := by
  refine Subtype.ext (Aut.ext (Iso.ext (Over.OverMorphism.ext
    ((dualNumberDeformationOpenCover f 𝒰).hom_ext _ _ fun (i : 𝒰.I₀) ↦ ?_))))
  have := congrArg (fun a ↦ a.val.asIso.hom.left ≫ dualNumberDeformationMap f (𝒰.f i)) (h i)
  simp only [infinitesimalAutRestrict_comp_dualNumberDeformationMap] at this
  exact this

end TauCeti.AlgebraicGeometry
