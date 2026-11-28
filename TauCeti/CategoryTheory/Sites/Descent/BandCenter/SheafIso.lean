/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.FromBanding
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Glue

/-!
# The coefficient sheaf of a banding is the sheaf of intrinsic central sections

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a gerbe for a Grothendieck topology `J` and `b` an
`A`-banding of `F` by a sheaf of abelian groups `A`. The coefficient maps
`c_b(U) : A(U) →* ZF(U)` (`AbelianBanding.centerFromBanding`) are group isomorphisms
(`AbelianBanding.centerFromBandingEquiv`, `BandCenter/FromBanding.lean`). This file packages
them as an isomorphism of presheaves `A ≅ (U ↦ Additive ZF(U))` and then of sheaves `A ≅ S` for
any sheaf `S` whose underlying presheaf is `U ↦ Additive ZF(U)`, in particular the sheaf of
intrinsic central sections `IntrinsicBandSections.sheaf F J`. The sheaf isomorphism is the unique
one whose value at a coefficient `a ∈ A(U)` evaluates at every `f : V ⟶ U` and every object `x`
over `V` to the band automorphism `b(V, x)(a|_V)`.

The banding `b` is kept as data: two bandings by the same sheaf `A` give different isomorphisms
whenever they differ at one coefficient and one object. No terminal object, global object,
neutrality or fibre products are assumed.

This is the fixed-band comparison in the varying-base step of the Stacks Project, Lemma 8.11.8
(0CJY).

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `centerFromBandingPresheaf`: the natural transformation `A ⟶ (U ↦ Additive ZF(U))` with
  components `c_b(U)`.
* `centerFromBandingPresheafIso`: the natural isomorphism extending it.
* `centerFromBandingSheafIso S h`: for a sheaf `S` with `h : S.obj = (U ↦ Additive ZF(U))`, the
  isomorphism of sheaves `A ≅ S` lifting it.
* `bandCenterIso`: the isomorphism `A ≅ IntrinsicBandSections.sheaf F J`, with uniqueness
  `bandCenterIso_unique`.

## Main results

* `centerFromBandingSheafIso_hom`, `centerFromBandingSheafIso_inv`: the underlying maps of
  presheaves.
* `centerFromBandingSheafIso_hom_transport`, `centerFromBandingSheafIso_inv_transport`: after
  transporting the target back to `U ↦ Additive ZF(U)`, the maps are
  `centerFromBandingPresheaf` and the inverse of `centerFromBandingPresheafIso`.
* `centerFromBandingSheafIso_unique`: a sheaf isomorphism `A ≅ S` whose value at every
  coefficient `a ∈ A(U)` evaluates to `b(V, x)(a|_V)` at every `f : V ⟶ U` and `x` over `V` is
  `centerFromBandingSheafIso S h`.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

open IntrinsicBandSections

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{max u v u' v'}}
  (b : F.AbelianBanding J A)

/-! ### The presheaf map -/

section Presheaf

variable [∀ U : C, IsGroupoid (F.obj (.mk (op U)))]

/-- The **coefficient transformation** of a banding: the natural transformation from the
coefficient presheaf `A` to `U ↦ Additive ZF(U)` whose component at `U` is `c_b(U)`. -/
noncomputable def centerFromBandingPresheaf : A.obj ⟶ IntrinsicBandSections.presheaf F where
  app U := AddCommGrpCat.ofHom (b.centerFromBanding U.unop).toAdditiveRight
  naturality _ _ f := AddCommGrpCat.ext fun a ↦
    congrArg Additive.ofMul (b.restrict_centerFromBanding f.unop (.ofAdd a)).symm

/-- The component of `centerFromBandingPresheaf` at `U` sends `a` to `c_b(U)(a)`. -/
@[simp]
theorem centerFromBandingPresheaf_app_apply (U : Cᵒᵖ) (a : A.obj.obj U) :
    b.centerFromBandingPresheaf.app U a =
      Additive.ofMul (b.centerFromBanding U.unop (Multiplicative.ofAdd a)) :=
  (rfl)

end Presheaf

variable [F.IsGerbe J]

/-! ### The presheaf isomorphism -/

/-- The component of `centerFromBandingPresheaf` at `U` is the forward map of
`centerFromBandingEquiv U`, viewed as an isomorphism of additive groups. -/
private theorem toAddCommGrpIso_centerFromBandingEquiv_hom (U : Cᵒᵖ) :
    (MulEquiv.toAdditiveRight (b.centerFromBandingEquiv U.unop)).toAddCommGrpIso.hom =
      b.centerFromBandingPresheaf.app U :=
  AddCommGrpCat.ext fun _ ↦ congrArg Additive.ofMul (b.centerFromBandingEquiv_apply _ _)

/-- The **presheaf comparison** of a banding: the natural isomorphism from the coefficient presheaf
`A` to `U ↦ Additive ZF(U)` whose component at `U` is `centerFromBandingEquiv U`, so whose forward
map is `centerFromBandingPresheaf`. -/
noncomputable def centerFromBandingPresheafIso : A.obj ≅ IntrinsicBandSections.presheaf F :=
  NatIso.ofComponents
    (fun U ↦ (MulEquiv.toAdditiveRight (b.centerFromBandingEquiv U.unop)).toAddCommGrpIso)
    (fun f ↦ by
      simpa only [toAddCommGrpIso_centerFromBandingEquiv_hom] using
        b.centerFromBandingPresheaf.naturality f)

/-- The forward map of `centerFromBandingPresheafIso` is `centerFromBandingPresheaf`. -/
@[simp]
theorem centerFromBandingPresheafIso_hom :
    b.centerFromBandingPresheafIso.hom = b.centerFromBandingPresheaf :=
  NatTrans.ext (funext b.toAddCommGrpIso_centerFromBandingEquiv_hom)

/-- The inverse component of `centerFromBandingPresheafIso` at `U` sends `z` to the coefficient
`(centerFromBandingEquiv U)⁻¹ z`. -/
@[simp]
theorem centerFromBandingPresheafIso_inv_app_apply (U : Cᵒᵖ)
    (z : (IntrinsicBandSections.presheaf F).obj U) :
    b.centerFromBandingPresheafIso.inv.app U z =
      Multiplicative.toAdd ((b.centerFromBandingEquiv U.unop).symm (Additive.toMul z)) :=
  (rfl)

/-! ### The sheaf isomorphism -/

/-- The **sheaf comparison** of a banding: for a sheaf `S` whose underlying presheaf is
`U ↦ Additive ZF(U)`, the isomorphism of sheaves `A ≅ S` lifting `centerFromBandingPresheafIso`
through the fully faithful inclusion of sheaves. The equality `h` only identifies carriers. -/
noncomputable def centerFromBandingSheafIso (S : Sheaf J AddCommGrpCat.{max u v u' v'})
    (h : S.obj = IntrinsicBandSections.presheaf F) : A ≅ S :=
  (fullyFaithfulSheafToPresheaf J _).preimageIso
    (b.centerFromBandingPresheafIso ≪≫ eqToIso h.symm)

variable (S : Sheaf J AddCommGrpCat.{max u v u' v'}) (h : S.obj = IntrinsicBandSections.presheaf F)

/-- The underlying presheaf map of `centerFromBandingSheafIso S h` is `centerFromBandingPresheaf`
followed by the carrier identification. -/
theorem centerFromBandingSheafIso_hom :
    (b.centerFromBandingSheafIso S h).hom.hom = b.centerFromBandingPresheaf ≫ eqToHom h.symm := by
  rw [← centerFromBandingPresheafIso_hom]
  exact (fullyFaithfulSheafToPresheaf J _).map_preimage _

/-- The underlying presheaf map of the inverse of `centerFromBandingSheafIso S h` is the carrier
identification followed by the inverse of `centerFromBandingPresheafIso`. -/
theorem centerFromBandingSheafIso_inv :
    (b.centerFromBandingSheafIso S h).inv.hom =
      eqToHom h ≫ b.centerFromBandingPresheafIso.inv := by
  rw [centerFromBandingSheafIso, Functor.FullyFaithful.preimageIso_inv]
  exact (fullyFaithfulSheafToPresheaf J _).map_preimage _

/-- **Transport of the forward map**: transporting the target of `centerFromBandingSheafIso S h`
back to `U ↦ Additive ZF(U)` gives `centerFromBandingPresheaf`. -/
@[simp]
theorem centerFromBandingSheafIso_hom_transport :
    (b.centerFromBandingSheafIso S h).hom.hom ≫ eqToHom h = b.centerFromBandingPresheaf := by
  simp [centerFromBandingSheafIso_hom]

/-- **Transport of the inverse**: transporting the source of the inverse of
`centerFromBandingSheafIso S h` to `U ↦ Additive ZF(U)` gives the inverse of
`centerFromBandingPresheafIso`. -/
@[simp]
theorem centerFromBandingSheafIso_inv_transport :
    eqToHom h.symm ≫ (b.centerFromBandingSheafIso S h).inv.hom =
      b.centerFromBandingPresheafIso.inv := by
  simp [centerFromBandingSheafIso_inv]

/-- **Uniqueness of the sheaf comparison.** A sheaf isomorphism `e : A ≅ S` whose value at every
coefficient `a ∈ A(U)`, read in `U ↦ Additive ZF(U)` through `h`, evaluates at every `f : V ⟶ U`
and every object `x` over `V` to the band automorphism `b(V, x)(a|_V)` is
`centerFromBandingSheafIso S h`. No object over `U` is chosen. -/
theorem centerFromBandingSheafIso_unique (e : A ≅ S)
    (he : ∀ (U V : C) (f : V ⟶ U) (x : F.obj (.mk (op V))) (a : A.obj.obj (op U)),
      IntrinsicBandSections.evaluation f x (Additive.toMul ((e.hom.hom ≫ eqToHom h).app (op U) a)) =
        b.mulEquiv V x (.ofAdd (A.obj.map f.op a))) :
    e = b.centerFromBandingSheafIso S h := by
  refine Iso.ext (Sheaf.hom_ext ?_)
  rw [← cancel_mono (eqToHom h), centerFromBandingSheafIso_hom_transport]
  refine NatTrans.ext (funext fun U ↦ AddCommGrpCat.ext fun a ↦ ?_)
  rw [centerFromBandingPresheaf_app_apply]
  exact congrArg Additive.ofMul (b.eq_centerFromBanding (.ofAdd a) _ fun V f x ↦ he U.unop V f x a)

/-! ### The intrinsic central-section sheaf -/

/-- **The coefficient sheaf of a banding is the intrinsic band**: the isomorphism of sheaves
`A ≅ IntrinsicBandSections.sheaf F J` whose component at `U` is `c_b(U)`. -/
noncomputable def bandCenterIso : A ≅ IntrinsicBandSections.sheaf F J :=
  b.centerFromBandingSheafIso _ (sheaf_obj F J)

/-- The underlying presheaf map of `bandCenterIso` is `centerFromBandingPresheaf`. -/
@[simp]
theorem bandCenterIso_hom : b.bandCenterIso.hom.hom = b.centerFromBandingPresheaf :=
  (b.centerFromBandingSheafIso_hom _ (sheaf_obj F J)).trans (Category.comp_id _)

/-- The underlying presheaf map of the inverse of `bandCenterIso` is the inverse of
`centerFromBandingPresheafIso`. -/
@[simp]
theorem bandCenterIso_inv : b.bandCenterIso.inv.hom = b.centerFromBandingPresheafIso.inv :=
  (b.centerFromBandingSheafIso_inv _ (sheaf_obj F J)).trans (Category.id_comp _)

/-- **Uniqueness of the intrinsic-band comparison.** An isomorphism of sheaves
`e : A ≅ IntrinsicBandSections.sheaf F J` whose value at every coefficient `a ∈ A(U)` evaluates at
every `f : V ⟶ U` and every object `x` over `V` to `b(V, x)(a|_V)` is `bandCenterIso`. -/
theorem bandCenterIso_unique (e : A ≅ IntrinsicBandSections.sheaf F J)
    (he : ∀ (U V : C) (f : V ⟶ U) (x : F.obj (.mk (op V))) (a : A.obj.obj (op U)),
      IntrinsicBandSections.evaluation f x (Additive.toMul (e.hom.hom.app (op U) a)) =
        b.mulEquiv V x (.ofAdd (A.obj.map f.op a))) :
    e = b.bandCenterIso :=
  b.centerFromBandingSheafIso_unique _ (sheaf_obj F J) e he

end CategoryTheory.Pseudofunctor.AbelianBanding
