/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra

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

On each open `U` the sections `Γ(A, U)` form a `Γ(X, U)`-algebra
(`TauCeti.AlgebraicGeometry.SheafAlgebra.sections`), restriction is a ring homomorphism, and a
morphism of sheaves of algebras is an algebra homomorphism on sections. Morphisms are determined
by their values on sections (`TauCeti.AlgebraicGeometry.SheafAlgebra.hom_ext`).

Pullback along a morphism of schemes `f : Y ⟶ X` is Mathlib's `Functor.mapMon` applied to the
strong monoidal pullback of quasi-coherent sheaves; the characteristic equations identify the
carrier, unit and multiplication of `f^* A` with the pullback of those of `A`, through the
monoidal comparisons of module pullback.

## Main declarations

* `TauCeti.AlgebraicGeometry.SheafAlgebra X`: quasi-coherent, not necessarily commutative
  `𝒪_X`-algebras.
* `TauCeti.AlgebraicGeometry.SheafAlgebra.sections`: the `Γ(X, U)`-algebra of sections over `U`,
  with restriction `SheafAlgebra.restrict` and the induced algebra homomorphisms
  `SheafAlgebra.sectionsAlgHom`.
* `TauCeti.AlgebraicGeometry.SheafAlgebra.hom_ext`: morphisms agreeing on all sections are equal.
* `TauCeti.AlgebraicGeometry.SheafAlgebra.pullback`: pullback along a morphism of schemes, with
  `pullbackId` and `pullbackComp`.
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

variable (A : SheafAlgebra X)

/-- The sections over `U` of a sheaf of algebras, as a monoid object in `Γ(X, U)`-modules: the
image of `A` under the lax monoidal sections functor. -/
abbrev sectionsMon (U : X.Opens) : Mon (ModuleCat.{u} Γ(X, U)) :=
  (Scheme.Modules.sectionsFunctor U).mapMon.obj A.obj

/-- The sections of a sheaf of algebras over an open `U`: the sections of its underlying module,
carrying the ring and `Γ(X, U)`-algebra structures `SheafAlgebra.instRingSections` and
`SheafAlgebra.instAlgebraSections`. -/
@[expose]
def sections (U : X.Opens) : Type u := Γ(A.obj.X, U)

/-- The sections of a sheaf of algebras over an open form a ring, whose multiplication is that of
`A` applied to the image of `x ⊗ₜ y` in the sections of the tensor product. -/
instance instRingSections (U : X.Opens) : Ring (A.sections U) :=
  ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing (A.sectionsMon U).X

/-- The sections of a sheaf of algebras over an open `U` form a `Γ(X, U)`-algebra, whose scalar
multiplication is that of the sections of the underlying `𝒪_X`-module. -/
instance instAlgebraSections (U : X.Opens) : Algebra Γ(X, U) (A.sections U) :=
  ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ (A.sectionsMon U).X

/-- A section of the underlying module, viewed as a section of the sheaf of algebras. -/
def ofModule {U : X.Opens} : Γ(A.obj.X, U) ≃ A.sections U := Equiv.refl _

/-- A section of the sheaf of algebras, viewed as a section of the underlying module. -/
def toModule {U : X.Opens} : A.sections U ≃ Γ(A.obj.X, U) := Equiv.refl _

@[simp]
lemma toModule_ofModule {U : X.Opens} (x : Γ(A.obj.X, U)) : A.toModule (A.ofModule x) = x :=
  (rfl)

@[simp]
lemma ofModule_toModule {U : X.Opens} (x : A.sections U) : A.ofModule (A.toModule x) = x :=
  (rfl)

/-- The product of two sections is the multiplication of `A` applied to the image of their
tensor product under the tensor map of the sections functor. -/
lemma toModule_mul (U : X.Opens) (x y : A.sections U) :
    A.toModule (x * y) = (MonObj.mul (X := A.obj.X)).app U
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) A.obj.X A.obj.X
        (A.toModule x ⊗ₜ A.toModule y)) :=
  (rfl)

/-- The structure map `Γ(X, U) → Γ(A, U)` is the unit of `A` on sections over `U`. -/
lemma toModule_algebraMap (U : X.Opens) (r : Γ(X, U)) :
    A.toModule (algebraMap Γ(X, U) (A.sections U) r) = (MonObj.one (X := A.obj.X)).app U
      (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r) :=
  (rfl)

/-- Restriction of sections of a sheaf of algebras along an inclusion of opens `V ≤ U`, as a
ring homomorphism. -/
def restrict {U V : X.Opens} (i : V ⟶ U) : A.sections U →+* A.sections V where
  toFun x := A.ofModule (A.obj.X.presheaf.map i.op (A.toModule x))
  map_one' := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    -- The unit of sections is `η[A]` applied to `1`; both maps commute with restriction.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.one (X := A.obj.X)).val i.op
      ((Functor.LaxMonoidal.ε F).app' (op U) (1 : Γ(X, U)))
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) i.op (1 : Γ(X, U))
    exact h₁.symm.trans (congrArg _ (h₂.symm.trans
      (congrArg _ (map_one (X.presheaf.map i.op).hom))))
  map_mul' x y := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    -- The product is `μ[A]` applied to the tensor map of `F`; both commute with restriction,
    -- and restriction of the sectionwise tensor product sends `x ⊗ₜ y` to the pure tensor of
    -- the restrictions.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.mul (X := A.obj.X)).val i.op
      ((Functor.LaxMonoidal.μ F A.obj.X A.obj.X).app' (op U) (x ⊗ₜ y))
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.μ F A.obj.X A.obj.X) i.op
      (x ⊗ₜ y)
    exact h₁.symm.trans (congrArg _ h₂.symm)
  map_zero' := map_zero (A.obj.X.presheaf.map i.op).hom
  map_add' := map_add (A.obj.X.presheaf.map i.op).hom

@[simp]
lemma toModule_restrict {U V : X.Opens} (i : V ⟶ U) (x : A.sections U) :
    A.toModule (A.restrict i x) = A.obj.X.presheaf.map i.op (A.toModule x) :=
  (rfl)

/-- Restriction of sections commutes with the structure maps from regular functions. -/
lemma restrict_algebraMap {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    A.restrict i (algebraMap Γ(X, U) (A.sections U) r) =
      algebraMap Γ(X, V) (A.sections V) (X.presheaf.map i.op r) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
  -- The algebra map is `η[A]` after the unit map of `F`; both commute with restriction.
  have h₁ := PresheafOfModules.naturality_apply (MonObj.one (X := A.obj.X)).val i.op
    ((Functor.LaxMonoidal.ε F).app' (op U) r)
  have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) i.op r
  exact h₁.symm.trans (congrArg _ h₂.symm)

variable {A} {B C : SheafAlgebra X}

/-- A morphism of sheaves of algebras is a `Γ(X, U)`-algebra homomorphism on sections over
every open `U`. -/
def sectionsAlgHom (f : A ⟶ B) (U : X.Opens) : A.sections U →ₐ[Γ(X, U)] B.sections U :=
  ModuleCat.MonModuleEquivalenceAlgebra.functor.map
    ((Scheme.Modules.sectionsFunctor U).mapMon.map f.hom) |>.hom

@[simp]
lemma toModule_sectionsAlgHom (f : A ⟶ B) (U : X.Opens) (x : A.sections U) :
    B.toModule (sectionsAlgHom f U x) = f.hom.hom.app U (A.toModule x) :=
  (rfl)

@[simp]
lemma sectionsAlgHom_id (U : X.Opens) : sectionsAlgHom (𝟙 A) U = AlgHom.id _ _ :=
  (rfl)

@[simp]
lemma sectionsAlgHom_comp (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens) :
    sectionsAlgHom (f ≫ g) U = (sectionsAlgHom g U).comp (sectionsAlgHom f U) :=
  (rfl)

/-- Morphisms of sheaves of algebras are determined by their values on sections. -/
@[ext]
lemma hom_ext {f g : A ⟶ B}
    (h : ∀ (U : X.Opens) (x : A.sections U), sectionsAlgHom f U x = sectionsAlgHom g U x) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply Mon.Hom.ext
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext x
  exact h U (A.ofModule x)

/-- Two morphisms of sheaves of algebras are equal if their underlying morphisms of modules
are. -/
lemma hom_ext_of_hom {f g : A ⟶ B} (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (Mon.Hom.ext h)

/-- An isomorphism of sheaves of algebras is a `Γ(X, U)`-algebra isomorphism on sections over
every open `U`. -/
def sectionsAlgEquiv (e : A ≅ B) (U : X.Opens) : A.sections U ≃ₐ[Γ(X, U)] B.sections U :=
  AlgEquiv.ofAlgHom (sectionsAlgHom e.hom U) (sectionsAlgHom e.inv U)
    (by rw [← sectionsAlgHom_comp, e.inv_hom_id, sectionsAlgHom_id])
    (by rw [← sectionsAlgHom_comp, e.hom_inv_id, sectionsAlgHom_id])

@[simp]
lemma sectionsAlgEquiv_apply (e : A ≅ B) (U : X.Opens) (x : A.sections U) :
    sectionsAlgEquiv e U x = sectionsAlgHom e.hom U x :=
  (rfl)

variable (X) in
/-- The scalar algebra `𝒪_X`: the tensor unit of `X.Modules` with its trivial monoid
structure. -/
def unit : SheafAlgebra X := ⟨Mon.trivial X.Modules, isQuasicoherent_unit X⟩

@[simp]
lemma unit_obj_X : (unit X).obj.X = 𝟙_ X.Modules :=
  (rfl)

variable (X) in
/-- Commutative quasi-coherent algebras are quasi-coherent sheaves of algebras. -/
def ofQuasicoherentAlgebra : QuasicoherentAlgebra X ⥤ SheafAlgebra X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ CommMon.forget₂Mon X.Modules) fun A ↦ A.property

@[simp]
lemma ofQuasicoherentAlgebra_obj_obj_X (A : QuasicoherentAlgebra X) :
    ((ofQuasicoherentAlgebra X).obj A).obj.X = A.obj.X :=
  (rfl)

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

private def toMon : SheafAlgebra X ⥤ Mon (QuasicoherentSheaf X) where
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
    exact Mon.mk E
  map {A B} f := by
    refine Mon.Hom.mk' (ObjectProperty.homMk f.hom.hom) ?_ ?_
    · apply ObjectProperty.hom_ext
      exact IsMonHom.one_hom f.hom.hom
    · apply ObjectProperty.hom_ext
      exact IsMonHom.mul_hom f.hom.hom
  map_id A := by
    apply Mon.Hom.ext
    apply ObjectProperty.hom_ext
    exact Mon.id_hom A.obj
  map_comp f g := by
    apply Mon.Hom.ext
    apply ObjectProperty.hom_ext
    exact Mon.comp_hom f.hom g.hom

private def ofMon : Mon (QuasicoherentSheaf X) ⥤ SheafAlgebra X where
  obj A := by
    let E : X.Modules := A.X.obj
    letI : MonObj E := {
      one := η[A.X].hom
      mul := μ[A.X].hom
      one_mul := congrArg (fun f ↦ f.hom) (MonObj.one_mul A.X)
      mul_one := congrArg (fun f ↦ f.hom) (MonObj.mul_one A.X)
      mul_assoc := congrArg (fun f ↦ f.hom) (MonObj.mul_assoc A.X)
    }
    exact ⟨Mon.mk E, A.X.property⟩
  map f := by
    refine ObjectProperty.homMk (Mon.Hom.mk' f.hom.hom ?_ ?_)
    · exact congrArg (fun g ↦ g.hom) (IsMonHom.one_hom f.hom)
    · exact congrArg (fun g ↦ g.hom) (IsMonHom.mul_hom f.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Mon.Hom.ext
    exact congrArg (fun f ↦ f.hom) (Mon.id_hom A)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Mon.Hom.ext
    exact congrArg (fun h ↦ h.hom) (Mon.comp_hom f g)

/-- Converting a monoid in quasi-coherent sheaves to a sheaf of algebras and back is the
identity. -/
private def ofMonCompToMonIso : ofMon X ⋙ toMon X ≅ 𝟭 (Mon (QuasicoherentSheaf X)) :=
  NatIso.ofComponents (fun A ↦ Mon.mkIso (Iso.refl _) (Category.comp_id _)
    ((Category.comp_id _).trans ((congrArg (· ≫ μ[A.X]) (id_tensorHom_id _ _)).trans
      (Category.id_comp _)).symm)) (by
    intro A B f
    apply Mon.Hom.ext
    rfl)

/-- Converting a sheaf of algebras to a monoid in quasi-coherent sheaves and back is the
identity. -/
private def toMonCompOfMonIso : toMon X ⋙ ofMon X ≅ 𝟭 (SheafAlgebra X) :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (Mon.mkIso (Iso.refl _)
    (Category.comp_id _) ((Category.comp_id _).trans ((congrArg (· ≫ μ[A.obj.X])
      (id_tensorHom_id _ _)).trans (Category.id_comp _)).symm))) (by
    intro A B f
    apply ObjectProperty.hom_ext
    apply Mon.Hom.ext
    rfl)

variable {X} {Y Z : Scheme.{u}}

/-- Pullback of quasi-coherent sheaves of algebras along a morphism of schemes. -/
def pullback (f : Y ⟶ X) : SheafAlgebra X ⥤ SheafAlgebra Y :=
  toMon X ⋙ (QuasicoherentSheaf.pullback f).mapMon ⋙ ofMon Y

/-- The carrier of a pulled-back algebra is the pullback of its underlying module. -/
@[simp]
theorem pullback_obj_X (f : Y ⟶ X) (A : SheafAlgebra X) :
    ((pullback f).obj A).obj.X = (Scheme.Modules.pullback f).obj A.obj.X := by
  unfold pullback ofMon toMon
  exact QuasicoherentSheaf.pullback_obj_obj f _

/-- The unit of a pulled-back algebra is the pullback of its unit, preceded by the
identification of the pulled-back structure sheaf. -/
@[simp]
theorem pullback_obj_one (f : Y ⟶ X) (A : SheafAlgebra X) :
    η[((pullback f).obj A).obj.X] =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map η[A.obj.X] ≫
        eqToHom (pullback_obj_X f A).symm := by
  unfold pullback ofMon toMon
  -- `ofMon` takes the unit to the underlying sheaf morphism of the `Mon` unit, which
  -- `mapMon` defines as `ε ≫ F.map η` (Mathlib's `comp_mapMon_one`), and `toMon` wraps `η`
  -- by `ObjectProperty.homMk`; composition in the full subcategory is that of sheaves.
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
  unfold pullback ofMon toMon
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
  unfold pullback ofMon toMon
  exact QuasicoherentSheaf.pullback_map_hom f _

variable (X) in
/-- Pullback of sheaves of algebras along the identity is naturally the identity. -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 (SheafAlgebra X) :=
  Functor.isoWhiskerLeft (toMon X) (Functor.isoWhiskerRight
    (Functor.mapMonNatIso (QuasicoherentSheaf.pullbackId X) ≪≫ Functor.mapMonIdIso)
      (ofMon X)) ≪≫ toMonCompOfMonIso X

/-- Pullback of sheaves of algebras respects composition. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Functor.isoWhiskerLeft (toMon Z ⋙ (QuasicoherentSheaf.pullback g).mapMon)
      (Functor.isoWhiskerRight (ofMonCompToMonIso Y)
        ((QuasicoherentSheaf.pullback f).mapMon ⋙ ofMon X)) ≪≫
    Functor.isoWhiskerLeft (toMon Z) (Functor.isoWhiskerRight
      (Functor.mapMonCompIso.symm ≪≫
        Functor.mapMonNatIso (QuasicoherentSheaf.pullbackComp f g)) (ofMon X))

/-- The identity comparison of algebra pullback is Mathlib's identity comparison of module
pullback on underlying modules. -/
@[simp]
theorem pullbackId_hom_app_hom_hom (A : SheafAlgebra X) :
    ((pullbackId X).hom.app A).hom.hom =
      eqToHom (pullback_obj_X (𝟙 X) A) ≫ (Scheme.Modules.pullbackId X).hom.app A.obj.X := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackId_hom_app_hom X ⟨A.obj.X, A.property⟩)
  -- Composites with the identity components of the conversions reduce definitionally.
  rfl

/-- The inverse identity comparison of algebra pullback is Mathlib's inverse identity comparison
of module pullback on underlying modules. -/
@[simp]
theorem pullbackId_inv_app_hom_hom (A : SheafAlgebra X) :
    ((pullbackId X).inv.app A).hom.hom =
      (Scheme.Modules.pullbackId X).inv.app A.obj.X ≫ eqToHom (pullback_obj_X (𝟙 X) A).symm := by
  refine Eq.trans ?_ (QuasicoherentSheaf.pullbackId_inv_app_hom X ⟨A.obj.X, A.property⟩)
  -- Composites with the identity components of the conversions reduce definitionally.
  rfl

end SheafAlgebra

end

end TauCeti.AlgebraicGeometry
