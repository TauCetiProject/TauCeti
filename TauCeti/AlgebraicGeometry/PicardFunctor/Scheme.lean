/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The Picard scheme

For a morphism of schemes `f : X ⟶ S`, the relative Picard functor is the fppf sheaf
`relativePicardFppfSheaf f` of abelian groups on schemes over `S`. Its representability is a
property with a canonical representing object: `HasPicardScheme f` says that the underlying
presheaf of sets is representable (Mathlib's `Functor.IsRepresentable`), and the **Picard scheme**
`picardScheme f : Over S` is the representing object chosen by Mathlib's `Functor.reprX`, with
the representing isomorphism `picardSchemeIso f` of functors of points.

Any other representing object is canonically isomorphic to `picardScheme f`, compatibly with the
representations (`picardSchemeIsoOfRepresentableBy`), so a construction of a representing scheme
proves `HasPicardScheme f` and is transported along that isomorphism.

The group law of `picardScheme f` is the tensor product of line-bundle classes, transported by
Yoneda: the sheaf written multiplicatively makes `picardScheme f` a commutative group object
in `Over S` (Mathlib's `GrpObj.ofRepresentableBy` and `IsCommMonObj.ofRepresentableBy`). The
representing isomorphism sends the unit section to the trivial class and the product of two
sections to the sum of their classes (`picardSchemeIso_hom_app_one`,
`picardSchemeIso_hom_app_mul`).

For a morphism of bases `g : S' ⟶ S`, the relative Picard fppf sheaf of the base change
`S' ×_S X ⟶ S'` is the relative Picard fppf sheaf of `f` restricted along `Over.map g`
(`relativePicardFppfSheafBaseChangeIso`, in `PicardFunctor/BaseChange.lean`). As `Over.map g` is
left adjoint to `Over.pullback g`, the base change of a Picard scheme is the Picard scheme of the
base change (`picardSchemeBaseChangeIso`).

## Main declarations

* `TauCeti.AlgebraicGeometry.HasPicardScheme`: the relative Picard fppf sheaf of `f` is
  representable;
* `TauCeti.AlgebraicGeometry.picardScheme`: its representing object;
* `TauCeti.AlgebraicGeometry.picardSchemeIso`: the representing isomorphism of functors of points;
* `TauCeti.AlgebraicGeometry.picardSchemeIsoOfRepresentableBy`: uniqueness of the Picard scheme;
* `TauCeti.AlgebraicGeometry.instGrpObjPicardScheme`,
  `TauCeti.AlgebraicGeometry.instIsCommMonObjPicardScheme`: the commutative group law;
* `TauCeti.AlgebraicGeometry.instHasPicardSchemeFstPullback`,
  `TauCeti.AlgebraicGeometry.picardSchemeBaseChangeIso`: base change of the Picard scheme.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.2 and 9.4; base change is Exercise 4.4 and its answer in the arXiv
  version, arXiv:math/0504020, p. 27 and pp. 65–66.
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- A morphism `f : X ⟶ S` **has a Picard scheme** when the presheaf of sets underlying the
relative Picard fppf sheaf `relativePicardFppfSheaf f` is representable on schemes over `S`.
The sheaf takes values in `Type (u + 1)` while morphisms of `Over S` lie in `Type u`;
`Functor.RepresentableBy` allows this, so no universe is shrunk. -/
abbrev HasPicardScheme : Prop :=
  ((relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat).IsRepresentable

/-- The **Picard scheme** of `f : X ⟶ S`: the representing object of the relative Picard fppf
sheaf, as a scheme over `S`. Its group law is tensor product of line-bundle classes, transported
by Yoneda (`instGrpObjPicardScheme`). -/
def picardScheme [HasPicardScheme f] : Over S :=
  ((relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat).reprX

/-- The representation of the relative Picard fppf sheaf by the Picard scheme: morphisms
`T ⟶ picardScheme f` of schemes over `S` are the sections of the sheaf over `T`. -/
-- The lemmas below about `(picardSchemeRepresentableBy f).homEquiv` are not `@[simp]`: `simp`
-- rewrites the codomain `(_ ⋙ forget AddCommGrpCat).obj (op T)` inside the type of the coercion
-- by `Functor.comp_obj`, after which their left-hand sides no longer match.
def picardSchemeRepresentableBy [HasPicardScheme f] :
    ((relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat).RepresentableBy (picardScheme f) :=
  Functor.representableBy _

/-- The **representing isomorphism** between the lifted functor of points of `picardScheme f`
and the relative Picard fppf sheaf. -/
def picardSchemeIso [HasPicardScheme f] :
    uliftYoneda.{u + 1}.obj (picardScheme f) ≅
      (relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat :=
  Functor.uliftYonedaReprXIso _

/-- The representing isomorphism sends a morphism `φ : T ⟶ picardScheme f` to the section it
corresponds to under `picardSchemeRepresentableBy f`. -/
theorem picardSchemeIso_hom_app [HasPicardScheme f] (T : (Over S)ᵒᵖ)
    (φ : ULift.{u + 1} (T.unop ⟶ picardScheme f)) :
    (picardSchemeIso f).hom.app T φ = (picardSchemeRepresentableBy f).homEquiv φ.down :=
  (Functor.uliftYonedaReprXIso_hom_app _ T φ).trans
    ((picardSchemeRepresentableBy f).homEquiv_eq φ.down).symm

/-! ### Uniqueness -/

/-- **Uniqueness of the Picard scheme.** Any scheme `P` over `S` representing the relative
Picard fppf sheaf is canonically isomorphic to `picardScheme f`. -/
def picardSchemeIsoOfRepresentableBy [HasPicardScheme f] {P : Over S}
    (e : ((relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat).RepresentableBy P) :
    P ≅ picardScheme f :=
  e.isoReprX

/-- The isomorphism `picardSchemeIsoOfRepresentableBy f e` is compatible with the
representations: composing with it turns the representation `e` into
`picardSchemeRepresentableBy f`. -/
theorem picardSchemeRepresentableBy_homEquiv_comp_isoOfRepresentableBy_hom [HasPicardScheme f]
    {P : Over S} (e : ((relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat).RepresentableBy P)
    {T : Over S} (φ : T ⟶ P) :
    (picardSchemeRepresentableBy f).homEquiv (φ ≫ (picardSchemeIsoOfRepresentableBy f e).hom) =
      e.homEquiv φ := by
  have h : (picardSchemeIsoOfRepresentableBy f e).hom =
      (picardSchemeRepresentableBy f).homEquiv.symm (e.homEquiv (𝟙 P)) := rfl
  rw [h, Functor.RepresentableBy.comp_homEquiv_symm, Equiv.apply_symm_apply,
    ← e.homEquiv_comp, Category.comp_id]

/-! ### The group law -/

/-- The representation of the relative Picard fppf sheaf by `picardScheme f`, for the sheaf
written multiplicatively. -/
def picardSchemeMulRepresentableBy [HasPicardScheme f] :
    (((relativePicardFppfSheaf f).obj ⋙ AddCommGrpCat.toCommGrp) ⋙
      forget CommGrpCat).RepresentableBy (picardScheme f) :=
  (picardSchemeRepresentableBy f).ofIso
    (NatIso.ofComponents (fun _ ↦ Equiv.toIso Multiplicative.ofAdd) fun _ ↦ rfl)

/-- The commutative group object structure on `picardScheme f` transported from the relative
Picard fppf sheaf written multiplicatively. -/
abbrev picardSchemeCommGrpObj [HasPicardScheme f] : CommGrpObj (picardScheme f) :=
  CommGrpObj.ofRepresentableBy (picardScheme f) _ (picardSchemeMulRepresentableBy f)

/-- The **group law of the Picard scheme**: tensor product of line-bundle classes, transported
by Yoneda from the relative Picard fppf sheaf written multiplicatively. -/
instance instGrpObjPicardScheme [HasPicardScheme f] : GrpObj (picardScheme f) :=
  (picardSchemeCommGrpObj f).toGrpObj

/-- The group law of the Picard scheme is commutative. -/
instance instIsCommMonObjPicardScheme [HasPicardScheme f] : IsCommMonObj (picardScheme f) :=
  (picardSchemeCommGrpObj f).toIsCommMonObj

/-- The representation `picardSchemeMulRepresentableBy f` is `picardSchemeRepresentableBy f`
followed by `Multiplicative.ofAdd`. -/
theorem picardSchemeMulRepresentableBy_homEquiv' [HasPicardScheme f] {T : Over S}
    (φ : T ⟶ picardScheme f) :
    (picardSchemeMulRepresentableBy f).homEquiv' φ =
      Multiplicative.ofAdd ((picardSchemeRepresentableBy f).homEquiv φ) :=
  (rfl)

/-- The unit section of the Picard scheme is the morphism representing the unit of the sheaf,
as defined by Mathlib's `MonObj.ofRepresentableBy`. -/
theorem picardScheme_one_eq [HasPicardScheme f] (T : Over S) :
    (1 : T ⟶ picardScheme f) = toUnit T ≫ (picardSchemeMulRepresentableBy f).homEquiv'.symm 1 :=
  (rfl)

/-- The product of two sections of the Picard scheme is their pairing composed with the morphism
representing the product of the two projections, as defined by Mathlib's
`MonObj.ofRepresentableBy`. -/
theorem picardScheme_mul_eq [HasPicardScheme f] {T : Over S} (φ ψ : T ⟶ picardScheme f) :
    φ * ψ = lift φ ψ ≫ (picardSchemeMulRepresentableBy f).homEquiv'.symm
      ((picardSchemeMulRepresentableBy f).homEquiv' (fst (picardScheme f) (picardScheme f)) *
        (picardSchemeMulRepresentableBy f).homEquiv' (snd (picardScheme f) (picardScheme f))) :=
  (rfl)

/-- The unit section of the Picard scheme corresponds to the trivial class. -/
theorem picardSchemeRepresentableBy_homEquiv_one [HasPicardScheme f] (T : Over S) :
    (picardSchemeRepresentableBy f).homEquiv (1 : T ⟶ picardScheme f) = 0 := by
  apply Multiplicative.ofAdd.injective
  rw [ofAdd_zero, ← picardSchemeMulRepresentableBy_homEquiv', picardScheme_one_eq,
    Functor.RepresentableBy.homEquiv'_comp, Equiv.apply_symm_apply, map_one]
  -- Both sides are `1` of `Multiplicative` of the sections over `T`, its carrier written once
  -- through `AddCommGrpCat.toCommGrp` and once directly.
  rfl

/-- The product of two sections of the Picard scheme corresponds to the sum of their classes,
that is, to the tensor product of line-bundle classes. -/
theorem picardSchemeRepresentableBy_homEquiv_mul [HasPicardScheme f] {T : Over S}
    (φ ψ : T ⟶ picardScheme f) :
    (picardSchemeRepresentableBy f).homEquiv (φ * ψ) =
      (picardSchemeRepresentableBy f).homEquiv φ + (picardSchemeRepresentableBy f).homEquiv ψ := by
  apply Multiplicative.ofAdd.injective
  rw [ofAdd_add, ← picardSchemeMulRepresentableBy_homEquiv',
    ← picardSchemeMulRepresentableBy_homEquiv', ← picardSchemeMulRepresentableBy_homEquiv',
    picardScheme_mul_eq, Functor.RepresentableBy.homEquiv'_comp, Equiv.apply_symm_apply, map_mul,
    ← Functor.RepresentableBy.homEquiv'_comp, ← Functor.RepresentableBy.homEquiv'_comp, lift_fst,
    lift_snd]
  -- As in `picardSchemeRepresentableBy_homEquiv_one`, the two products differ only in how the
  -- carrier of `Multiplicative` of the sections over `T` is written.
  rfl

/-- Morphisms to the Picard scheme form a group isomorphic to the group of sections of the
relative Picard fppf sheaf, written multiplicatively. -/
def picardSchemeHomMulEquiv [HasPicardScheme f] (T : Over S) :
    (T ⟶ picardScheme f) ≃*
      Multiplicative (((relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat).obj (op T)) where
  toEquiv := (picardSchemeRepresentableBy f).homEquiv.trans Multiplicative.ofAdd
  map_mul' φ ψ := congrArg Multiplicative.ofAdd (picardSchemeRepresentableBy_homEquiv_mul f φ ψ)

/-- The inverse of a section of the Picard scheme corresponds to the negative of its class. -/
theorem picardSchemeRepresentableBy_homEquiv_inv [HasPicardScheme f] {T : Over S}
    (φ : T ⟶ picardScheme f) :
    (picardSchemeRepresentableBy f).homEquiv φ⁻¹ = -(picardSchemeRepresentableBy f).homEquiv φ :=
  congrArg Multiplicative.toAdd (map_inv (picardSchemeHomMulEquiv f T) φ)

/-- The representing isomorphism sends the unit section to the trivial class. -/
theorem picardSchemeIso_hom_app_one [HasPicardScheme f] (T : Over S) :
    (picardSchemeIso f).hom.app (op T) ⟨(1 : T ⟶ picardScheme f)⟩ = 0 := by
  rw [picardSchemeIso_hom_app, picardSchemeRepresentableBy_homEquiv_one]

/-- The representing isomorphism sends the group law to tensor product of line-bundle
classes. -/
theorem picardSchemeIso_hom_app_mul [HasPicardScheme f] {T : Over S}
    (φ ψ : T ⟶ picardScheme f) :
    (picardSchemeIso f).hom.app (op T) ⟨φ * ψ⟩ =
      (picardSchemeIso f).hom.app (op T) ⟨φ⟩ + (picardSchemeIso f).hom.app (op T) ⟨ψ⟩ := by
  simp only [picardSchemeIso_hom_app, picardSchemeRepresentableBy_homEquiv_mul]

/-! ### Base change -/

variable {S' : Scheme.{u}} (g : S' ⟶ S)

/-- If `f` has a Picard scheme `P`, its base change `P ×_S S'` along `g : S' ⟶ S` represents the
relative Picard fppf sheaf of the base change `S' ×_S X ⟶ S'`: a morphism `T ⟶ P ×_S S'` over
`S'` is a morphism `T ⟶ P` over `S`, by the adjunction `Over.map g ⊣ Over.pullback g`. -/
def picardSchemeBaseChangeRepresentableBy [HasPicardScheme f] :
    ((relativePicardFppfSheaf (pullback.fst g f)).obj ⋙ forget AddCommGrpCat).RepresentableBy
      ((Over.pullback g).obj (picardScheme f)) :=
  ((Over.mapPullbackAdj g).representableByComp (picardSchemeRepresentableBy f)).ofIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((sheafToPresheaf _ _).mapIso (relativePicardFppfSheafBaseChangeIso f g)).symm _)

/-- **Base change of the Picard scheme.** If `f` has a Picard scheme, so does its base change
`S' ×_S X ⟶ S'` along any `g : S' ⟶ S`. -/
instance instHasPicardSchemeFstPullback [HasPicardScheme f] :
    HasPicardScheme (pullback.fst g f) :=
  (picardSchemeBaseChangeRepresentableBy f g).isRepresentable

/-- **The Picard scheme of a base change is the base change of the Picard scheme.** For
`g : S' ⟶ S`, the Picard scheme of `S' ×_S X ⟶ S'` is `picardScheme f ×_S S'`. -/
def picardSchemeBaseChangeIso [HasPicardScheme f] :
    picardScheme (pullback.fst g f) ≅ (Over.pullback g).obj (picardScheme f) :=
  (picardSchemeIsoOfRepresentableBy _ (picardSchemeBaseChangeRepresentableBy f g)).symm

/-- The isomorphism `picardSchemeBaseChangeIso f g` is compatible with the representations of
the relative Picard fppf sheaf of the base change. -/
theorem picardSchemeRepresentableBy_homEquiv_comp_baseChangeIso_inv [HasPicardScheme f]
    {T : Over S'} (ψ : T ⟶ (Over.pullback g).obj (picardScheme f)) :
    (picardSchemeRepresentableBy (pullback.fst g f)).homEquiv
        (ψ ≫ (picardSchemeBaseChangeIso f g).inv) =
      (picardSchemeBaseChangeRepresentableBy f g).homEquiv ψ :=
  picardSchemeRepresentableBy_homEquiv_comp_isoOfRepresentableBy_hom _ _ ψ

end

end TauCeti.AlgebraicGeometry
