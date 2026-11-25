/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Composition
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Identity
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor
public import TauCeti.CategoryTheory.Monoidal.Subcategory

/-!
# Quasi-coherent sheaves of algebras

A quasi-coherent sheaf of algebras on a scheme `X` is a sheaf of associative unital rings `A`
with a structure map `𝒪_X ⟶ A` landing in the centre, whose underlying `𝒪_X`-module is
quasi-coherent. We model it as a monoid object in the symmetric monoidal category `X.Modules`
whose underlying module is quasi-coherent: the monoid structure on a module is the same as a
multiplication that is `𝒪_X`-bilinear, so the structure map `𝒪_X ⟶ A` (the unit) is automatically
central. Commutativity is not assumed, so matrix algebras and Azumaya algebras are included. The
commutative case is `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra`, which embeds by
`TauCeti.AlgebraicGeometry.SheafAlgebra.ofQuasicoherentAlgebra`.

The sections API does not use quasi-coherence and is stated for all monoid objects in
`X.Modules` (`CategoryTheory.Mon.ringSections`, `CategoryTheory.Mon.algebraSections`,
`CategoryTheory.Mon.restrictSections`, `CategoryTheory.Mon.sectionsPresheaf`,
`CategoryTheory.Mon.sectionsAlgHom`): on each open `U` the sections `Γ(A, U)` form a
`Γ(X, U)`-algebra, restriction is a ring homomorphism, so the sections form a sheaf of rings,
and a morphism of sheaves of algebras is an algebra homomorphism on sections. Morphisms of
sheaves of algebras are determined by their values on sections
(`TauCeti.AlgebraicGeometry.SheafAlgebra.hom_ext`).

Pullback along a morphism of schemes `f : Y ⟶ X` is Mathlib's `Functor.mapMon` applied to the
strong monoidal pullback of quasi-coherent sheaves; the characteristic equations identify the
carrier, unit and multiplication of `f^* A` with the pullback of those of `A`, through the
monoidal comparisons of module pullback.

## Main declarations

* `TauCeti.AlgebraicGeometry.SheafAlgebra X`: quasi-coherent, not necessarily commutative
  `𝒪_X`-algebras.
* `TauCeti.AlgebraicGeometry.SheafAlgebra.hom_ext`: morphisms agreeing on all sections are equal.
* `TauCeti.AlgebraicGeometry.SheafAlgebra.pullback`: pullback along a morphism of schemes, with
  `pullbackId` and `pullbackComp`, given on underlying modules by Mathlib's
  `Scheme.Modules.pullbackId` and `Scheme.Modules.pullbackComp`.
* `TauCeti.AlgebraicGeometry.SheafAlgebra.unit`: the scalar algebra `𝒪_X`.

## References

* The Stacks Project, Section 59.62 (Tag 0A2J), for sheaves of algebras on a scheme.
-/

public section

open CategoryTheory MonoidalCategory Opposite
open scoped MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

/-- Quasi-coherent, not necessarily commutative `𝒪_X`-algebras on a scheme `X`: monoid objects in
`X.Modules` whose underlying module is quasi-coherent, with monoid morphisms. -/
abbrev SheafAlgebra (X : Scheme.{u}) :=
  (show ObjectProperty (Mon X.Modules) from fun A ↦ A.X.IsQuasicoherent).FullSubcategory

namespace SheafAlgebra

variable {X : Scheme.{u}}

instance isQuasicoherent_X (A : SheafAlgebra X) : A.obj.X.IsQuasicoherent := A.property

variable {A B : SheafAlgebra X}

/-- Morphisms of sheaves of algebras are determined by their values on sections, where they are
the `Γ(X, U)`-algebra homomorphisms `CategoryTheory.Mon.sectionsAlgHom`. -/
@[ext]
lemma hom_ext {f g : A ⟶ B}
    (h : ∀ (U : X.Opens) (x : Γ(A.obj.X, U)),
      Mon.sectionsAlgHom f.hom U x = Mon.sectionsAlgHom g.hom U x) :
    f = g :=
  ObjectProperty.hom_ext _ (Mon.hom_ext_of_sectionsAlgHom fun U ↦ AlgHom.ext (h U))

/-- Two morphisms of sheaves of algebras are equal if their underlying morphisms of modules
are. -/
lemma hom_ext_of_hom {f g : A ⟶ B} (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (Mon.Hom.ext h)

variable (X) in
/-- The scalar algebra `𝒪_X`: the tensor unit of `X.Modules` with its trivial monoid
structure. -/
def unit : SheafAlgebra X := ⟨Mon.trivial X.Modules, isQuasicoherent_unit X⟩

@[simp]
lemma unit_obj_X : (unit X).obj.X = 𝟙_ X.Modules :=
  (rfl)

/-- The unit of the scalar algebra `𝒪_X` is the identity, transported along `unit_obj_X`. -/
@[simp]
lemma unit_obj_one : η[(unit X).obj.X] = eqToHom (unit_obj_X (X := X)).symm :=
  (rfl)

/-- The multiplication of the scalar algebra `𝒪_X` is the left unitor, transported along
`unit_obj_X`. -/
@[simp]
lemma unit_obj_mul : μ[(unit X).obj.X] =
    (eqToHom unit_obj_X ⊗ₘ eqToHom unit_obj_X) ≫ (λ_ (𝟙_ X.Modules)).hom ≫
      eqToHom (unit_obj_X (X := X)).symm :=
  -- The transports are identities here, where `unit` unfolds.
  (by simp : (𝟙 (𝟙_ X.Modules) ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (λ_ (𝟙_ X.Modules)).hom ≫ 𝟙 _ =
    (λ_ (𝟙_ X.Modules)).hom).symm

variable (X) in
/-- Commutative quasi-coherent algebras are quasi-coherent sheaves of algebras. -/
def ofQuasicoherentAlgebra : QuasicoherentAlgebra X ⥤ SheafAlgebra X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ CommMon.forget₂Mon X.Modules) fun A ↦ A.property

@[simp]
lemma ofQuasicoherentAlgebra_obj_obj_X (A : QuasicoherentAlgebra X) :
    ((ofQuasicoherentAlgebra X).obj A).obj.X = A.obj.X :=
  (rfl)

/-- The unit of the image of a commutative algebra is its unit, transported along
`ofQuasicoherentAlgebra_obj_obj_X`. -/
@[simp]
lemma ofQuasicoherentAlgebra_obj_obj_one (A : QuasicoherentAlgebra X) :
    η[((ofQuasicoherentAlgebra X).obj A).obj.X] =
      η[A.obj.X] ≫ eqToHom (ofQuasicoherentAlgebra_obj_obj_X A).symm :=
  (Category.comp_id (obj := X.Modules) _).symm

/-- The multiplication of the image of a commutative algebra is its multiplication, transported
along `ofQuasicoherentAlgebra_obj_obj_X`. -/
@[simp]
lemma ofQuasicoherentAlgebra_obj_obj_mul (A : QuasicoherentAlgebra X) :
    μ[((ofQuasicoherentAlgebra X).obj A).obj.X] =
      (eqToHom (ofQuasicoherentAlgebra_obj_obj_X A) ⊗ₘ eqToHom (ofQuasicoherentAlgebra_obj_obj_X A))
        ≫ μ[A.obj.X] ≫ eqToHom (ofQuasicoherentAlgebra_obj_obj_X A).symm :=
  -- The transports are identities here, where `ofQuasicoherentAlgebra` unfolds.
  (by simp : (𝟙 A.obj.X ⊗ₘ 𝟙 A.obj.X) ≫ μ[A.obj.X] ≫ 𝟙 _ = μ[A.obj.X]).symm

/-- The underlying morphism of modules of the image of a morphism of commutative algebras is
the original one, transported along `ofQuasicoherentAlgebra_obj_obj_X`. -/
@[simp]
lemma ofQuasicoherentAlgebra_map_hom_hom {A B : QuasicoherentAlgebra X} (f : A ⟶ B) :
    ((ofQuasicoherentAlgebra X).map f).hom.hom =
      eqToHom (ofQuasicoherentAlgebra_obj_obj_X A) ≫ f.hom.hom.hom ≫
        eqToHom (ofQuasicoherentAlgebra_obj_obj_X B).symm :=
  ((Category.id_comp (obj := X.Modules) _).trans (Category.comp_id (obj := X.Modules) _)).symm

/-- The functor from commutative quasi-coherent algebras is fully faithful: a morphism of sheaves
of algebras between commutative ones is a morphism of commutative algebras. -/
def fullyFaithfulOfQuasicoherentAlgebra : (ofQuasicoherentAlgebra X).FullyFaithful :=
  .ofCompFaithful (G := ObjectProperty.ι _)
    (((ObjectProperty.fullyFaithfulι _).comp (CommMon.fullyFaithfulForget₂Mon X.Modules)).ofIso
      (ObjectProperty.liftCompιIso _ _ _).symm)

end SheafAlgebra

/-! ### Pullback -/

namespace SheafAlgebra

variable (X : Scheme.{u})

attribute [local instance] monoidalCategorySheafOfModules

/-- Sheaves of algebras are the monoid objects in quasi-coherent sheaves. -/
private abbrev monEquivalence : Mon (QuasicoherentSheaf X) ≌ SheafAlgebra X :=
  ObjectProperty.monFullSubcategoryEquivalence _

variable {X} {Y Z : Scheme.{u}}

/-- Pullback of quasi-coherent sheaves of algebras along a morphism of schemes. -/
def pullback (f : Y ⟶ X) : SheafAlgebra X ⥤ SheafAlgebra Y :=
  (monEquivalence X).inverse ⋙ (QuasicoherentSheaf.pullback f).mapMon ⋙
    (monEquivalence Y).functor

/-- The carrier of a pulled-back algebra is the pullback of its underlying module. -/
@[simp]
theorem pullback_obj_X (f : Y ⟶ X) (A : SheafAlgebra X) :
    ((pullback f).obj A).obj.X = (Scheme.Modules.pullback f).obj A.obj.X := by
  unfold pullback
  exact QuasicoherentSheaf.pullback_obj_obj f _

/-- The unit of a pulled-back algebra is the pullback of its unit, preceded by the
identification of the pulled-back structure sheaf. -/
@[simp]
theorem pullback_obj_one (f : Y ⟶ X) (A : SheafAlgebra X) :
    η[((pullback f).obj A).obj.X] =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map η[A.obj.X] ≫
        eqToHom (pullback_obj_X f A).symm := by
  unfold pullback
  -- The functor of `monEquivalence` takes the unit to the underlying sheaf morphism of the
  -- `Mon` unit, which `mapMon` defines as `ε ≫ F.map η` (Mathlib's `comp_mapMon_one`), and its
  -- inverse wraps `η` by `ObjectProperty.homMk`; composition in the full subcategory is that of
  -- sheaves.
  change (Functor.LaxMonoidal.ε (QuasicoherentSheaf.pullback f)).hom ≫
    ((QuasicoherentSheaf.pullback f).map _).hom = _
  rw [QuasicoherentSheaf.pullback_ε_hom, QuasicoherentSheaf.pullback_map_hom]
  -- `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf instances.
  refine (Category.assoc (obj := Y.Modules) _ _ _).trans ?_
  refine congrArg ((Scheme.Modules.pullbackObjUnitIso f).inv ≫ ·) ?_
  refine (eqToHom_trans_assoc (C := Y.Modules) _ _ _).trans ?_
  exact Category.id_comp (obj := Y.Modules) _

/-- The multiplication of a pulled-back algebra is the pullback of its multiplication, preceded
by the inverse tensor comparison of module pullback. -/
@[simp]
theorem pullback_obj_mul (f : Y ⟶ X) (A : SheafAlgebra X) :
    μ[((pullback f).obj A).obj.X] =
      (eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫
          (Scheme.Modules.pullback f).map μ[A.obj.X] ≫ eqToHom (pullback_obj_X f A).symm := by
  unfold pullback
  -- As in `pullback_obj_one`, with `comp_mapMon_mul` in place of `comp_mapMon_one`.
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

/-- Pullback of algebra morphisms has the underlying map given by pullback of module morphisms,
transported along the canonical carrier identifications. -/
@[simp]
theorem pullback_map_hom_hom (f : Y ⟶ X) {A B : SheafAlgebra X} (g : A ⟶ B) :
    ((pullback f).map g).hom.hom =
      eqToHom (pullback_obj_X f A) ≫ (Scheme.Modules.pullback f).map g.hom.hom ≫
        eqToHom (pullback_obj_X f B).symm := by
  unfold pullback
  exact QuasicoherentSheaf.pullback_map_hom f _

variable (X) in
/-- Pullback of sheaves of algebras along the identity is naturally the identity. -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 (SheafAlgebra X) :=
  Functor.isoWhiskerLeft (monEquivalence X).inverse (Functor.isoWhiskerRight
    (Functor.mapMonNatIso (QuasicoherentSheaf.pullbackId X) ≪≫ Functor.mapMonIdIso)
      (monEquivalence X).functor) ≪≫ (monEquivalence X).counitIso

/-- Pullback of sheaves of algebras respects composition. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Functor.isoWhiskerLeft ((monEquivalence Z).inverse ⋙ (QuasicoherentSheaf.pullback g).mapMon)
      (Functor.isoWhiskerRight (monEquivalence Y).unitIso.symm
        ((QuasicoherentSheaf.pullback f).mapMon ⋙ (monEquivalence X).functor)) ≪≫
    Functor.isoWhiskerLeft (monEquivalence Z).inverse (Functor.isoWhiskerRight
      (Functor.mapMonCompIso.symm ≪≫
        Functor.mapMonNatIso (QuasicoherentSheaf.pullbackComp f g)) (monEquivalence X).functor)

/-- The identity comparison of algebra pullback is Mathlib's identity comparison of module
pullback on underlying modules. -/
@[simp]
theorem pullbackId_hom_app_hom_hom (A : SheafAlgebra X) :
    ((pullbackId X).hom.app A).hom.hom =
      eqToHom (pullback_obj_X (𝟙 X) A) ≫ (Scheme.Modules.pullbackId X).hom.app A.obj.X := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackId_hom_app_hom X ⟨A.obj.X, A.property⟩)
  -- Composites with the identity components of `monEquivalence` reduce definitionally.
  rfl

/-- The inverse identity comparison of algebra pullback is Mathlib's inverse identity comparison
of module pullback on underlying modules. -/
@[simp]
theorem pullbackId_inv_app_hom_hom (A : SheafAlgebra X) :
    ((pullbackId X).inv.app A).hom.hom =
      (Scheme.Modules.pullbackId X).inv.app A.obj.X ≫ eqToHom (pullback_obj_X (𝟙 X) A).symm := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackId_inv_app_hom X ⟨A.obj.X, A.property⟩)
  -- Composites with the identity components of `monEquivalence` reduce definitionally.
  rfl

/-- The composition comparison of algebra pullback is Mathlib's composition comparison of module
pullback on underlying modules. -/
@[simp]
theorem pullbackComp_hom_app_hom_hom (f : X ⟶ Y) (g : Y ⟶ Z) (A : SheafAlgebra Z) :
    ((pullbackComp f g).hom.app A).hom.hom =
      eqToHom ((pullback_obj_X f _).trans (congrArg _ (pullback_obj_X g A))) ≫
        (Scheme.Modules.pullbackComp f g).hom.app A.obj.X ≫
          eqToHom (pullback_obj_X (f ≫ g) A).symm := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackComp_hom_app_hom f g ⟨A.obj.X, A.property⟩)
  dsimp only [pullbackComp]
  -- The intermediate functors of `pullbackComp` agree with those of `Iso.trans` only up to
  -- unfolding `Functor.comp`, so the composite is split with `erw`. After the identity component
  -- of the unit of `monEquivalence` is removed, the composite with the identity components of
  -- `monEquivalence` reduces definitionally.
  erw [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    ObjectProperty.monFullSubcategoryEquivalence_unitIso_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The inverse composition comparison of algebra pullback is Mathlib's inverse composition
comparison of module pullback on underlying modules. -/
@[simp]
theorem pullbackComp_inv_app_hom_hom (f : X ⟶ Y) (g : Y ⟶ Z) (A : SheafAlgebra Z) :
    ((pullbackComp f g).inv.app A).hom.hom =
      eqToHom (pullback_obj_X (f ≫ g) A) ≫ (Scheme.Modules.pullbackComp f g).inv.app A.obj.X ≫
        eqToHom ((pullback_obj_X f _).trans (congrArg _ (pullback_obj_X g A))).symm := by
  -- The inverse of the underlying module isomorphism, computed from the forward component.
  refine Iso.inv_ext (f := (ObjectProperty.ι _ ⋙ Mon.forget X.Modules).mapIso
    ((pullbackComp f g).app A)) ?_
  -- The image of a morphism under `ObjectProperty.ι _ ⋙ Mon.forget X.Modules` is its underlying
  -- module morphism by definition; `change` states the goal with it, in `X.Modules`. Rewriting
  -- with `Functor.mapIso_hom`, `Functor.comp_map`, `Mon.forget_map`, `ObjectProperty.ι_map` and
  -- `Iso.app_hom` instead leaves a cancellation of `eqToHom` composites that `simp` does not close.
  change ((pullbackComp f g).hom.app A).hom.hom ≫ _ = 𝟙 _
  rw [pullbackComp_hom_app_hom_hom]
  simp

end SheafAlgebra

end

end TauCeti.AlgebraicGeometry
