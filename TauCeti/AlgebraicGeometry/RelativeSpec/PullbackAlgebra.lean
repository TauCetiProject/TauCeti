/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Composition
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Identity
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor
public import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Pullback of quasicoherent algebras

A quasicoherent commutative algebra on a scheme can be viewed as a commutative monoid object in
the symmetric monoidal category of quasicoherent sheaves. This description makes pullback of
algebras functorial: the strong symmetric monoidal pullback of quasicoherent sheaves carries
commutative monoid objects to commutative monoid objects.

This is the algebraic side of base change for relative spectra. The characteristic equations in
this file identify the carrier, unit, multiplication, and morphisms of an algebra pullback with
the already established pullback of the underlying quasicoherent sheaves and its monoidal
comparisons.

The construction is Mathlib's `CategoryTheory.Functor.mapCommMon`, which carries commutative
monoid objects along a lax braided functor, applied to the strong symmetric monoidal structure
on `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullback`.

Pullback of algebras is left adjoint to pushforward of algebras: for `f : X ⟶ Y`, a
quasicoherent algebra `A` on `Y` and any commutative algebra `B` on `X`, algebra maps
`f^* A ⟶ B` correspond to algebra maps `A ⟶ f_* B`. The bijection is transposition along the
pullback–pushforward adjunction of modules. It preserves algebra maps because that adjunction is
monoidal (`CategoryTheory.Adjunction.isMonHom_homEquiv_iff`), and the multiplication of `f^* A` is
that of `A` transported along the tensor comparison of pullback, which is invertible as `A` is
quasicoherent. The algebra `B` need not be quasicoherent, so that `B` can be the structure sheaf
of an arbitrary scheme.

Pullback of algebras is pseudofunctorial: the identity and composition isomorphisms
`𝟙^* A ≅ A` and `f^* g^* A ≅ (f ≫ g)^* A` are those of the underlying modules, and the bijection
above is compatible with them and with the corresponding isomorphisms of pushforward. These are
the inputs for the compatibility of base change of relative spectra with composition.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.pullback`: pullback of quasicoherent algebras
  along a morphism of schemes;
* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.pullbackId` and
  `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.pullbackComp`: its identity and composition
  isomorphisms, given on underlying modules by Mathlib's `Scheme.Modules.pullbackId` and
  `Scheme.Modules.pullbackComp`;
* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.pullbackHomEquiv`: the bijection between
  algebra maps `f^* A ⟶ B` and `A ⟶ f_* B`, natural in `A` and `B`, and compatible with
  composition (`pullbackHomEquiv_comp`) and identities (`pullbackHomEquiv_id_hom_hom`).

## References

* The Stacks Project, Tag 01LQ (relative spectrum as a functor), where this adjunction for
  quasicoherent algebras gives the universal property of relative Spec in terms of pullbacks.
-/

public section

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

attribute [local instance] monoidalCategorySheafOfModules

/-- The symmetry of modules on a scheme, stated for the unfolded sheaf category used by the
quasicoherent full subcategory. -/
local instance pullbackAlgebraSymmetricCategorySheafOfModules :
    SymmetricCategory (_root_.SheafOfModules X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.instSymmetricCategory X

namespace QuasicoherentAlgebra

private def toCommMon : QuasicoherentAlgebra X ⥤ CommMon (QuasicoherentSheaf X) where
  obj A := by
    let E : QuasicoherentSheaf X := ⟨A.obj.X, A.property⟩
    letI : MonObj E := {
      one := ObjectProperty.homMk η[A.obj.X]
      mul := ObjectProperty.homMk μ[A.obj.X]
      one_mul := by
        apply ObjectProperty.hom_ext
        exact MonObj.one_mul A.obj.X
      mul_one := by
        apply ObjectProperty.hom_ext
        exact MonObj.mul_one A.obj.X
      mul_assoc := by
        apply ObjectProperty.hom_ext
        exact MonObj.mul_assoc A.obj.X
    }
    letI : IsCommMonObj E := {
      mul_comm := by
        apply ObjectProperty.hom_ext
        exact IsCommMonObj.mul_comm (X := A.obj.X)
    }
    exact CommMon.mk E
  map {A B} f := by
    refine CommMon.homMk (Mon.Hom.mk' (ObjectProperty.homMk f.hom.hom.hom) ?_ ?_)
    · apply ObjectProperty.hom_ext
      exact IsMonHom.one_hom f.hom.hom.hom
    · apply ObjectProperty.hom_ext
      exact IsMonHom.mul_hom f.hom.hom.hom
  map_id A := by
    apply CommMon.hom_ext
    apply ObjectProperty.hom_ext
    exact CategoryTheory.CommMon.id_hom A.obj
  map_comp f g := by
    apply CommMon.hom_ext
    apply ObjectProperty.hom_ext
    exact CategoryTheory.CommMon.comp_hom f.hom g.hom

private def ofCommMon : CommMon (QuasicoherentSheaf X) ⥤ QuasicoherentAlgebra X where
  obj A := by
    let E : X.Modules := A.X.obj
    letI : MonObj E := {
      one := η[A.X].hom
      mul := μ[A.X].hom
      one_mul := congrArg (fun f ↦ f.hom) (MonObj.one_mul A.X)
      mul_one := congrArg (fun f ↦ f.hom) (MonObj.mul_one A.X)
      mul_assoc := congrArg (fun f ↦ f.hom) (MonObj.mul_assoc A.X)
    }
    letI : IsCommMonObj E := {
      mul_comm := congrArg (fun f ↦ f.hom) (IsCommMonObj.mul_comm (X := A.X))
    }
    exact ⟨CommMon.mk E, A.X.property⟩
  map f := by
    refine ObjectProperty.homMk (CommMon.homMk (Mon.Hom.mk' f.hom.hom.hom ?_ ?_))
    · exact congrArg (fun g ↦ g.hom) (IsMonHom.one_hom f.hom.hom)
    · exact congrArg (fun g ↦ g.hom) (IsMonHom.mul_hom f.hom.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact congrArg (fun f ↦ f.hom) (CommMon.id_hom A)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact congrArg (fun h ↦ h.hom) (CommMon.comp_hom f g)

end QuasicoherentAlgebra

namespace QuasicoherentAlgebra

variable {X}

/-- Pullback of quasicoherent commutative algebras along a morphism of schemes. -/
def pullback {Y : Scheme.{u}} (f : Y ⟶ X) :
    QuasicoherentAlgebra X ⥤ QuasicoherentAlgebra Y :=
  toCommMon X ⋙
    (QuasicoherentSheaf.pullback f).mapCommMon ⋙
      ofCommMon Y

/-- The carrier of a pulled-back algebra is the pullback of its underlying module. -/
@[simp]
theorem pullback_obj_X {Y : Scheme.{u}} (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    ((pullback f).obj A).obj.X = (Scheme.Modules.pullback f).obj A.obj.X :=
  by
    unfold pullback ofCommMon toCommMon
    exact QuasicoherentSheaf.pullback_obj_obj f _

/-- The unit of a pulled-back algebra is the pullback of its unit, preceded by the
identification of the pulled-back structure sheaf. -/
@[simp]
theorem pullback_obj_one {Y : Scheme.{u}} (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    η[((pullback f).obj A).obj.X] =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map η[A.obj.X] ≫
        eqToHom (pullback_obj_X f A).symm := by
  unfold pullback ofCommMon toCommMon
  -- Definitional unfolding through the conversions: `ofCommMon` takes the unit to the
  -- underlying sheaf morphism `.hom` of the `CommMon` unit, `mapCommMon` defines that unit as
  -- `ε ≫ F.map η` (compare Mathlib's `rfl` lemma `comp_mapCommMon_one`), `toCommMon` wraps `η`
  -- by `ObjectProperty.homMk`, and composition in the full subcategory is that of sheaves.
  change (Functor.LaxMonoidal.ε (QuasicoherentSheaf.pullback f)).hom ≫
    ((QuasicoherentSheaf.pullback f).map _).hom = _
  rw [QuasicoherentSheaf.pullback_ε_hom, QuasicoherentSheaf.pullback_map_hom]
  -- `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf instances.
  refine (Category.assoc (obj := Y.Modules) _ _ _).trans ?_
  refine congrArg ((Scheme.Modules.pullbackObjUnitIso f).inv ≫ ·) ?_
  refine (eqToHom_trans_assoc (C := Y.Modules) _ _ _).trans ?_
  exact Category.id_comp (obj := Y.Modules) _

/-- The multiplication of a pulled-back algebra is the pullback of its multiplication,
preceded by the inverse tensor comparison of module pullback. -/
@[simp]
theorem pullback_obj_mul {Y : Scheme.{u}} (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    μ[((pullback f).obj A).obj.X] =
      (eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫
          (Scheme.Modules.pullback f).map μ[A.obj.X] ≫ eqToHom (pullback_obj_X f A).symm := by
  unfold pullback ofCommMon toCommMon
  -- As in `pullback_obj_one`: `ofCommMon` takes `.hom` of the `CommMon` multiplication, which
  -- `mapCommMon` defines as `μ ≫ F.map μ` (compare Mathlib's `rfl` lemma `comp_mapCommMon_mul`),
  -- and `toCommMon` wraps `μ` by `ObjectProperty.homMk`.
  change (Functor.LaxMonoidal.μ (QuasicoherentSheaf.pullback f) _ _).hom ≫
    ((QuasicoherentSheaf.pullback f).map _).hom = _
  rw [QuasicoherentSheaf.pullback_μ_hom, QuasicoherentSheaf.pullback_map_hom]
  simp only [Scheme.Modules.pullbackToModules_δ]
  -- `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf instances.
  refine (Category.assoc (obj := Y.Modules) _ _ _).trans ?_
  refine congrArg ((eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫ ·) ?_
  refine (Category.assoc (obj := Y.Modules) _ _ _).trans ?_
  refine congrArg
    (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫ ·) ?_
  refine (eqToHom_trans_assoc (C := Y.Modules) _ _ _).trans ?_
  exact Category.id_comp (obj := Y.Modules) _

/-- Pullback of algebra morphisms has the underlying map given by pullback of module
morphisms, transported along the canonical carrier identifications. -/
@[simp]
theorem pullback_map_hom_hom_hom {Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} (g : A ⟶ B) :
    ((pullback f).map g).hom.hom.hom =
      eqToHom (pullback_obj_X f A) ≫ (Scheme.Modules.pullback f).map g.hom.hom.hom ≫
        eqToHom (pullback_obj_X f B).symm := by
  unfold pullback ofCommMon toCommMon
  exact QuasicoherentSheaf.pullback_map_hom f _

end QuasicoherentAlgebra

namespace QuasicoherentAlgebra

/-- Converting a commutative monoid in quasicoherent sheaves to a quasicoherent algebra and back
is the identity. -/
private def ofCommMonCompToCommMonIso :
    ofCommMon X ⋙ toCommMon X ≅ 𝟭 (CommMon (QuasicoherentSheaf X)) :=
  NatIso.ofComponents (fun A ↦ CommMon.mkIso (Iso.refl _) (Category.comp_id _)
    ((Category.comp_id _).trans ((congrArg (· ≫ μ[A.X]) (id_tensorHom_id _ _)).trans
      (Category.id_comp _)).symm)) (by
    intro A B f
    apply CommMon.hom_ext
    rfl)

/-- Converting a quasicoherent algebra to a commutative monoid in quasicoherent sheaves and back
is the identity. -/
private def toCommMonCompOfCommMonIso :
    toCommMon X ⋙ ofCommMon X ≅ 𝟭 (QuasicoherentAlgebra X) :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (CommMon.mkIso (Iso.refl _)
    (Category.comp_id _) ((Category.comp_id _).trans ((congrArg (· ≫ μ[A.obj.X])
      (id_tensorHom_id _ _)).trans (Category.id_comp _)).symm))) (by
    intro A B f
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    rfl)

variable {X} {Y Z : Scheme.{u}}

variable (X) in
/-- Pullback of quasicoherent algebras along the identity is naturally the identity. -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 (QuasicoherentAlgebra X) :=
  Functor.isoWhiskerLeft (toCommMon X) (Functor.isoWhiskerRight
    (Functor.mapCommMonNatIso (QuasicoherentSheaf.pullbackId X) ≪≫ Functor.mapCommMonIdIso)
      (ofCommMon X)) ≪≫ toCommMonCompOfCommMonIso X

/-- Pullback of quasicoherent algebras respects composition. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Functor.isoWhiskerLeft (toCommMon Z ⋙ (QuasicoherentSheaf.pullback g).mapCommMon)
      (Functor.isoWhiskerRight (ofCommMonCompToCommMonIso Y)
        ((QuasicoherentSheaf.pullback f).mapCommMon ⋙ ofCommMon X)) ≪≫
    Functor.isoWhiskerLeft (toCommMon Z) (Functor.isoWhiskerRight
      (Functor.mapCommMonCompIso.symm ≪≫
        Functor.mapCommMonNatIso (QuasicoherentSheaf.pullbackComp f g)) (ofCommMon X))

/-- The identity comparison of algebra pullback is Mathlib's identity comparison of module
pullback on underlying modules. -/
@[simp]
theorem pullbackId_hom_app_hom_hom_hom (A : QuasicoherentAlgebra X) :
    ((pullbackId X).hom.app A).hom.hom.hom =
      eqToHom (pullback_obj_X (𝟙 X) A) ≫ (Scheme.Modules.pullbackId X).hom.app A.obj.X := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackId_hom_app_hom X ⟨A.obj.X, A.property⟩)
  -- Composites with the identity components of the conversions reduce definitionally.
  rfl

/-- The inverse identity comparison of algebra pullback is Mathlib's inverse identity comparison
of module pullback on underlying modules. -/
@[simp]
theorem pullbackId_inv_app_hom_hom_hom (A : QuasicoherentAlgebra X) :
    ((pullbackId X).inv.app A).hom.hom.hom =
      (Scheme.Modules.pullbackId X).inv.app A.obj.X ≫ eqToHom (pullback_obj_X (𝟙 X) A).symm := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackId_inv_app_hom X ⟨A.obj.X, A.property⟩)
  -- Composites with the identity components of the conversions reduce definitionally.
  rfl

/-- The composition comparison of algebra pullback is Mathlib's composition comparison of module
pullback on underlying modules. -/
@[simp]
theorem pullbackComp_hom_app_hom_hom_hom (f : X ⟶ Y) (g : Y ⟶ Z) (A : QuasicoherentAlgebra Z) :
    ((pullbackComp f g).hom.app A).hom.hom.hom =
      eqToHom ((pullback_obj_X f _).trans (congrArg _ (pullback_obj_X g A))) ≫
        (Scheme.Modules.pullbackComp f g).hom.app A.obj.X ≫
          eqToHom (pullback_obj_X (f ≫ g) A).symm := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackComp_hom_app_hom f g ⟨A.obj.X, A.property⟩)
  have h : (ofCommMonCompToCommMonIso Y).hom.app
      ((QuasicoherentSheaf.pullback g).mapCommMon.obj ((toCommMon Z).obj A)) = 𝟙 _ :=
    CommMon.hom_ext _ _ rfl
  dsimp only [pullbackComp]
  -- The intermediate functors of `pullbackComp` agree with those of `Iso.trans` only up to
  -- unfolding `Functor.comp`, so the composite is split with `erw`.
  erw [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, h, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

/-- The inverse composition comparison of algebra pullback is Mathlib's inverse composition
comparison of module pullback on underlying modules. -/
@[simp]
theorem pullbackComp_inv_app_hom_hom_hom (f : X ⟶ Y) (g : Y ⟶ Z) (A : QuasicoherentAlgebra Z) :
    ((pullbackComp f g).inv.app A).hom.hom.hom =
      eqToHom (pullback_obj_X (f ≫ g) A) ≫ (Scheme.Modules.pullbackComp f g).inv.app A.obj.X ≫
        eqToHom ((pullback_obj_X f _).trans (congrArg _ (pullback_obj_X g A))).symm := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackComp_inv_app_hom f g ⟨A.obj.X, A.property⟩)
  have h : (ofCommMonCompToCommMonIso Y).inv.app
      ((QuasicoherentSheaf.pullback g).mapCommMon.obj ((toCommMon Z).obj A)) = 𝟙 _ :=
    CommMon.hom_ext _ _ rfl
  dsimp only [pullbackComp]
  -- As in `pullbackComp_hom_app_hom_hom_hom`.
  erw [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, h,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end QuasicoherentAlgebra

namespace QuasicoherentAlgebra

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism out of the pullback of the underlying module of `A`, transported to the pulled-back
algebra, is an algebra map exactly when it carries the pulled-back unit and multiplication of `A`
to those of `B`, through the oplax comparisons of module pullback. -/
private lemma isMonHom_eqToHom_comp_iff (A : QuasicoherentAlgebra Y) (B : CommMon X.Modules)
    (φ : (Scheme.Modules.pullback f).obj A.obj.X ⟶ B.X) :
    IsMonHom (eqToHom (pullback_obj_X f A) ≫ φ) ↔
      (Scheme.Modules.pullback f).map η[A.obj.X] ≫ φ =
          Functor.OplaxMonoidal.η (Scheme.Modules.pullback f) ≫ η[B.X] ∧
        (Scheme.Modules.pullback f).map μ[A.obj.X] ≫ φ =
          Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X ≫
            (φ ⊗ₘ φ) ≫ μ[B.X] := by
  have hone : η[((pullback f).obj A).obj.X] ≫ eqToHom (pullback_obj_X f A) ≫ φ = η[B.X] ↔
      (Scheme.Modules.pullback f).map η[A.obj.X] ≫ φ =
        Functor.OplaxMonoidal.η (Scheme.Modules.pullback f) ≫ η[B.X] := by
    rw [pullback_obj_one]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [Scheme.Modules.pullback_η, Iso.inv_comp_eq]
  have hmul : μ[((pullback f).obj A).obj.X] ≫ eqToHom (pullback_obj_X f A) ≫ φ =
        ((eqToHom (pullback_obj_X f A) ≫ φ) ⊗ₘ (eqToHom (pullback_obj_X f A) ≫ φ)) ≫ μ[B.X] ↔
      (Scheme.Modules.pullback f).map μ[A.obj.X] ≫ φ =
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X ≫
          (φ ⊗ₘ φ) ≫ μ[B.X] := by
    rw [pullback_obj_mul, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [cancel_epi, IsIso.inv_comp_eq]
  rw [← hone, ← hmul]
  exact ⟨fun h ↦ ⟨h.one_hom, h.mul_hom⟩, fun h ↦ ⟨h.1, h.2⟩⟩

open scoped Obj in
private lemma isMonHom_homEquiv_iff_isMonHom_eqToHom_comp (A : QuasicoherentAlgebra Y)
    (B : CommMon X.Modules) (φ : (Scheme.Modules.pullback f).obj A.obj.X ⟶ B.X) :
    IsMonHom ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ φ) ↔
      IsMonHom (eqToHom (pullback_obj_X f A) ≫ φ) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).isMonHom_homEquiv_iff φ).trans
    (isMonHom_eqToHom_comp_iff f A B φ).symm

open scoped Obj in
private lemma isMonHom_iff_isMonHom_eqToHom_comp_homEquiv_symm (A : QuasicoherentAlgebra Y)
    (B : CommMon X.Modules) (ψ : A.obj.X ⟶ (Scheme.Modules.pushforward f).obj B.X) :
    IsMonHom ψ ↔ IsMonHom (eqToHom (pullback_obj_X f A) ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ψ) := by
  obtain ⟨φ, rfl⟩ := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).surjective ψ
  rw [Equiv.symm_apply_apply]
  exact isMonHom_homEquiv_iff_isMonHom_eqToHom_comp f A B φ

-- The two cancellations below are stated with their types explicit: inside the proofs of
-- `pullbackHomEquiv`, `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf
-- instances on the carrier of the pulled-back algebra.
private lemma eqToHom_comp_eqToHom_symm_comp (A : QuasicoherentAlgebra Y) {B : X.Modules}
    (g : ((pullback f).obj A).obj.X ⟶ B) :
    eqToHom (pullback_obj_X f A) ≫ eqToHom (pullback_obj_X f A).symm ≫ g = g := by
  simp

private lemma eqToHom_symm_comp_eqToHom_comp (A : QuasicoherentAlgebra Y) {B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A.obj.X ⟶ B) :
    eqToHom (pullback_obj_X f A).symm ≫ eqToHom (pullback_obj_X f A) ≫ φ = φ := by
  simp

/-- **Pullback of quasicoherent algebras is left adjoint to pushforward of algebras.** For a
morphism of schemes `f : X ⟶ Y`, a quasicoherent algebra `A` on `Y` and a commutative algebra `B`
on `X`, algebra maps `f^* A ⟶ B` correspond to algebra maps `A ⟶ f_* B`. On underlying modules
this is transposition along the pullback–pushforward adjunction
(`pullbackHomEquiv_apply_hom_hom`). -/
def pullbackHomEquiv (A : QuasicoherentAlgebra Y) (B : CommMon X.Modules) :
    (((pullback f).obj A).obj ⟶ B) ≃
      (A.obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj B) where
  toFun g :=
    CommMon.homMk (@Mon.Hom.mk _ _ _ _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (eqToHom (pullback_obj_X f A).symm ≫ g.hom.hom))
      ((isMonHom_homEquiv_iff_isMonHom_eqToHom_comp f A B _).mpr
        ((eqToHom_comp_eqToHom_symm_comp f A g.hom.hom).symm ▸ g.hom.isMonHom_hom)))
  invFun ψ :=
    CommMon.homMk (@Mon.Hom.mk _ _ _ _ _ (eqToHom (pullback_obj_X f A) ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ψ.hom.hom)
      ((isMonHom_iff_isMonHom_eqToHom_comp_homEquiv_symm f A B ψ.hom.hom).mp
        ψ.hom.isMonHom_hom))
  left_inv g := CommMon.hom_ext _ _
    ((congrArg (eqToHom (pullback_obj_X f A) ≫ ·) (Equiv.symm_apply_apply _ _)).trans
      (eqToHom_comp_eqToHom_symm_comp f A g.hom.hom))
  right_inv _ := CommMon.hom_ext _ _
    ((congrArg ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (eqToHom_symm_comp_eqToHom_comp f A _)).trans (Equiv.apply_symm_apply _ _))

/-- On underlying modules, the algebra map `A ⟶ f_* B` corresponding to `g : f^* A ⟶ B` is the
transpose of `g` along the pullback–pushforward adjunction. -/
@[simp]
lemma pullbackHomEquiv_apply_hom_hom (A : QuasicoherentAlgebra Y) (B : CommMon X.Modules)
    (g : ((pullback f).obj A).obj ⟶ B) :
    (pullbackHomEquiv f A B g).hom.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (eqToHom (pullback_obj_X f A).symm ≫ g.hom.hom) :=
  (rfl)

/-- On underlying modules, the algebra map `f^* A ⟶ B` corresponding to `ψ : A ⟶ f_* B` is the
inverse transpose of `ψ` along the pullback–pushforward adjunction. -/
@[simp]
lemma pullbackHomEquiv_symm_apply_hom_hom (A : QuasicoherentAlgebra Y) (B : CommMon X.Modules)
    (ψ : A.obj ⟶ (Scheme.Modules.pushforward f).mapCommMon.obj B) :
    ((pullbackHomEquiv f A B).symm ψ).hom.hom =
      eqToHom (pullback_obj_X f A) ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ψ.hom.hom :=
  (rfl)

/-- The bijection `pullbackHomEquiv` is natural in the algebra on the base: precomposing with
the pullback of `a : A' ⟶ A` corresponds to precomposing with `a`. -/
lemma pullbackHomEquiv_naturality_left {A' A : QuasicoherentAlgebra Y} (a : A' ⟶ A)
    (B : CommMon X.Modules) (g : ((pullback f).obj A).obj ⟶ B) :
    pullbackHomEquiv f A' B (((pullback f).map a).hom ≫ g) = a.hom ≫ pullbackHomEquiv f A B g := by
  have h : eqToHom (pullback_obj_X f A').symm ≫ ((pullback f).map a).hom.hom.hom ≫ g.hom.hom =
      (Scheme.Modules.pullback f).map a.hom.hom.hom ≫
        eqToHom (pullback_obj_X f A).symm ≫ g.hom.hom := by
    rw [pullback_map_hom_hom_hom]
    -- `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf instances.
    refine (congrArg (_ ≫ ·) (Category.assoc (obj := X.Modules) _ _ _)).trans ?_
    refine (eqToHom_trans_assoc (C := X.Modules) _ _ _).trans ?_
    exact (Category.id_comp (obj := X.Modules) _).trans (Category.assoc (obj := X.Modules) _ _ _)
  exact CommMon.hom_ext _ _ ((congrArg ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    _ _) h).trans (Adjunction.homEquiv_naturality_left _ _ _))

/-- The bijection `pullbackHomEquiv` is natural in the algebra on the source: postcomposing with
`b : B ⟶ B'` corresponds to postcomposing with its pushforward. -/
lemma pullbackHomEquiv_naturality_right (A : QuasicoherentAlgebra Y) {B B' : CommMon X.Modules}
    (g : ((pullback f).obj A).obj ⟶ B) (b : B ⟶ B') :
    pullbackHomEquiv f A B' (g ≫ b) =
      pullbackHomEquiv f A B g ≫ (Scheme.Modules.pushforward f).mapCommMon.map b :=
  CommMon.hom_ext _ _ ((congrArg ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
    (Category.assoc _ _ _).symm).trans (Adjunction.homEquiv_naturality_right _ _ _))

/-- Transposition along pullback of algebras is compatible with composition of scheme morphisms:
transposing along `f ≫ g`, after the composition isomorphism `(f ≫ g)^* A ≅ f^* g^* A`, is
transposing along `f` and then along `g`, followed by the composition isomorphism
`g_* f_* B ≅ (f ≫ g)_* B` of pushforward. -/
lemma pullbackHomEquiv_comp {Z : Scheme.{u}} (g : Y ⟶ Z) (A : QuasicoherentAlgebra Z)
    (B : CommMon X.Modules) (φ : ((pullback f).obj ((pullback g).obj A)).obj ⟶ B) :
    pullbackHomEquiv (f ≫ g) A B (((pullbackComp f g).inv.app A).hom ≫ φ) =
      pullbackHomEquiv g A _ (pullbackHomEquiv f _ B φ) ≫
        Functor.mapCommMonCompIso.inv.app B ≫
          (Functor.mapCommMonNatIso (Scheme.Modules.pushforwardComp f g)).hom.app B := by
  apply CommMon.hom_ext
  simp only [CommMon.comp_hom, pullbackHomEquiv_apply_hom_hom,
    Functor.mapCommMonCompIso_inv_app_hom_hom, Functor.mapCommMonNatIso_hom_app_hom_hom,
    pullbackComp_inv_app_hom_hom_hom]
  have h : eqToHom (pullback_obj_X (f ≫ g) A).symm ≫ (eqToHom (pullback_obj_X (f ≫ g) A) ≫
      (Scheme.Modules.pullbackComp f g).inv.app A.obj.X ≫ eqToHom ((pullback_obj_X f _).trans
        (congrArg (Scheme.Modules.pullback f).obj (pullback_obj_X g A))).symm) ≫ φ.hom.hom =
      (Scheme.Modules.pullbackComp f g).inv.app A.obj.X ≫
        (Scheme.Modules.pullback f).map (eqToHom (pullback_obj_X g A).symm) ≫
          eqToHom (pullback_obj_X f ((pullback g).obj A)).symm ≫ φ.hom.hom := by
    rw [eqToHom_map]
    -- As in `pullbackHomEquiv_naturality_left`, these composites mix the `X.Modules` and
    -- underlying sheaf category instances, which `rw` and `simp` do not identify.
    erw [Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg (_ ≫ ·) (eqToHom_trans_assoc _ _ _).symm
  -- The same instance mixing: the identity comes from `Functor.mapCommMonCompIso`.
  erw [Category.id_comp, h]
  rw [← Adjunction.homEquiv_conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left]
  rfl

/-- Transposition along pullback of algebras by the identity is the identity, through the
identity isomorphisms `𝟙^* A ≅ A` and `B ≅ 𝟙_* B` of pullback and pushforward. -/
lemma pullbackHomEquiv_id_hom_hom (A : QuasicoherentAlgebra X) (B : CommMon X.Modules)
    (φ : A.obj ⟶ B) :
    (pullbackHomEquiv (𝟙 X) A B (((pullbackId X).hom.app A).hom ≫ φ)).hom.hom =
      φ.hom.hom ≫ (Scheme.Modules.pushforwardId X).inv.app B.X := by
  have h : eqToHom (pullback_obj_X (𝟙 X) A).symm ≫ (eqToHom (pullback_obj_X (𝟙 X) A) ≫
      (Scheme.Modules.pullbackId X).hom.app A.obj.X) ≫ φ.hom.hom =
        (Scheme.Modules.pullbackId X).hom.app A.obj.X ≫ φ.hom.hom := by
    -- As in `pullbackHomEquiv_comp`, the composites mix two category instances.
    erw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [pullbackHomEquiv_apply_hom_hom, CommMon.comp_hom, pullbackId_hom_app_hom_hom_hom]
  erw [h]
  refine (Adjunction.homEquiv_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)) (Scheme.Modules.pullbackId X).hom
      φ.hom.hom).symm.trans ?_
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom]
  rfl

end QuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
