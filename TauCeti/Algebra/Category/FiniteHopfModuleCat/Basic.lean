/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Finite-dimensional modules over an algebra

`FiniteHopfModuleCat k H` is the category of left `H`-modules finite-dimensional over `k`.
Its objects are native `ModuleCat H` objects, with finiteness tested after native restriction
of scalars along `algebraMap k H`. Their carriers lie in the universe of `k`, so tensor products
over `k`, the scalar field itself, and finite duals can all have the same carrier universe.

The underlying category and its faithful forgetful functors require only a `k`-algebra.
The type synonym keeps additional Hopf-module tensor structures separate from tensor products
over a commutative `H`. In particular, no monoidal structure is installed here.

`ofShrink` places any finite-dimensional module, even one in a larger universe, in this category.
`ofShrinkEquiv` is an `H`-linear comparison with the original module; `ofShrinkLinearEquiv` is
its scalar-field-linear version. Morphisms transport by conjugation through these comparisons.

The full-subcategory construction follows Mathlib's `FGModuleCat`. The universe reduction uses
Mathlib's `Module.Finite.small` and `Shrink.linearEquiv`, as in Tau Ceti's `FDRep.ofShrink`.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti

universe u v w

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H]

/-- Left modules over `H` whose restriction to `k` is finite-dimensional, with carriers in the
universe of `k`. Only the algebra structure is needed for the underlying category. -/
-- Expose the type synonym to retain the native full-subcategory projections and constructors.
-- Implicit reducibility lets tactics typecheck those projections, without allowing instance
-- search to inherit tensor products over `H`.
@[expose, implicit_reducible]
def FiniteHopfModuleCat :=
  ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} H =>
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k H)).obj M))

namespace FiniteHopfModuleCat

instance : Category (FiniteHopfModuleCat k H) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

instance : Preadditive (FiniteHopfModuleCat k H) :=
  inferInstanceAs (Preadditive (ObjectProperty.FullSubcategory _))

instance : Linear k (FiniteHopfModuleCat k H) :=
  inferInstanceAs (Linear k (ObjectProperty.FullSubcategory _))

/-- The carrier of a finite-dimensional algebra module. -/
@[expose, reducible]
def carrier (M : FiniteHopfModuleCat k H) : Type u := M.obj

instance : CoeSort (FiniteHopfModuleCat k H) (Type u) := ⟨carrier k H⟩

attribute [coe] carrier

instance (M : FiniteHopfModuleCat k H) : AddCommGroup M :=
  inferInstanceAs (AddCommGroup M.obj)

instance (M : FiniteHopfModuleCat k H) : Module H M :=
  inferInstanceAs (Module H M.obj)

-- Prefer the scalar-field action when `H = k`, so dimension lemmas use this canonical action.
instance (priority := 1100) (M : FiniteHopfModuleCat k H) : Module k M :=
  ((ModuleCat.restrictScalars (algebraMap k H)).obj M.obj).isModule

instance (M : FiniteHopfModuleCat k H) : IsScalarTower k H M :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance (M : FiniteHopfModuleCat k H) : Module.Finite k M := M.property

/-- Inclusion into all native left `H`-modules. -/
abbrev incl : FiniteHopfModuleCat k H ⥤ ModuleCat.{u} H :=
  ObjectProperty.ι _

instance : (incl k H).Faithful := ObjectProperty.faithful_ι _

instance : (incl k H).Full := ObjectProperty.full_ι _

/-- Inclusion forgets the finiteness property of a morphism. -/
@[simp]
theorem incl_map {M N : FiniteHopfModuleCat k H} (f : M ⟶ N) :
    (incl k H).map f = f.hom := (rfl)

instance : (incl k H).Additive where

instance : (incl k H).Linear k where

/-- Forget the `H`-action by native restriction of scalars to `k`. -/
abbrev forgetToModule : FiniteHopfModuleCat k H ⥤ ModuleCat.{u} k :=
  incl k H ⋙ ModuleCat.restrictScalars (algebraMap k H)

instance : (forgetToModule k H).Faithful :=
  inferInstanceAs (incl k H ⋙ ModuleCat.restrictScalars (algebraMap k H)).Faithful

instance : (forgetToModule k H).Additive := inferInstance

instance : (forgetToModule k H).Linear k where

/-- Forget to the native category of finite-dimensional `k`-vector spaces. -/
def forgetToFiniteModule : FiniteHopfModuleCat k H ⥤ FGModuleCat.{u} k :=
  (ModuleCat.isFG k).lift (forgetToModule k H) fun M => M.property

/-- The two scalar-field forgetful functors agree after inclusion. -/
def forgetToFiniteModuleCompIso :
    forgetToFiniteModule k H ⋙ forget₂ (FGModuleCat k) (ModuleCat k) ≅ forgetToModule k H :=
  (ModuleCat.isFG k).liftCompιIso _ _

instance : (forgetToFiniteModule k H).Faithful :=
  Functor.Faithful.of_comp_iso (forgetToFiniteModuleCompIso k H)

instance : (forgetToFiniteModule k H).Additive where

instance : (forgetToFiniteModule k H).Linear k where

/-- Intertwiner spaces between finite-dimensional modules are finite-dimensional over `k`. -/
instance (M N : FiniteHopfModuleCat k H) : Module.Finite k (M ⟶ N) := by
  let : Module.Finite k ((forgetToModule k H).obj M) := M.property
  let : Module.Finite k ((forgetToModule k H).obj N) := N.property
  let e := ModuleCat.homLinearEquiv (R := k) (S := k)
    (M := (forgetToModule k H).obj M) (N := (forgetToModule k H).obj N)
  exact FiniteDimensional.of_injective
    (e.toLinearMap ∘ₗ (forgetToModule k H).mapLinearMap k)
    (e.injective.comp (Functor.map_injective (forgetToModule k H)))

variable {k H}

/-- Bundle a native module that is finite-dimensional over the scalar field. -/
abbrev of (V : Type u) [AddCommGroup V] [Module k V] [Module H V]
    [IsScalarTower k H V] [Module.Finite k V] : FiniteHopfModuleCat k H :=
  ⟨ModuleCat.of H V, by
    let e : ((ModuleCat.restrictScalars (algebraMap k H)).obj (ModuleCat.of H V)) ≃ₗ[k] V :=
      { AddEquiv.refl V with
        map_smul' := fun r x => IsScalarTower.algebraMap_smul (M := V) H r x }
    exact Module.Finite.equiv e.symm⟩

/-- Interpret an `H`-linear map as a morphism of finite-dimensional modules. -/
abbrev ofHom {V W : Type u} [AddCommGroup V] [Module k V] [Module H V]
    [IsScalarTower k H V] [Module.Finite k V] [AddCommGroup W] [Module k W] [Module H W]
    [IsScalarTower k H W] [Module.Finite k W] (f : V →ₗ[H] W) :
    of (k := k) (H := H) V ⟶ of (k := k) (H := H) W :=
  ObjectProperty.homMk (ModuleCat.ofHom f)

/-- An `H`-linear equivalence gives an isomorphism of bundled finite-dimensional modules. -/
def isoOfLinearEquiv {M N : FiniteHopfModuleCat k H} (e : M ≃ₗ[H] N) : M ≅ N :=
  ObjectProperty.isoMk _ (LinearEquiv.toModuleIso e)

/-- The forward map of the bundled isomorphism is the original linear equivalence. -/
@[simp]
theorem isoOfLinearEquiv_hom_hom {M N : FiniteHopfModuleCat k H} (e : M ≃ₗ[H] N) :
    (isoOfLinearEquiv e).hom.hom.hom = e.toLinearMap := (rfl)

/-- The inverse map of the bundled isomorphism is the inverse linear equivalence. -/
@[simp]
theorem isoOfLinearEquiv_inv_hom {M N : FiniteHopfModuleCat k H} (e : M ≃ₗ[H] N) :
    (isoOfLinearEquiv e).inv.hom.hom = e.symm.toLinearMap := (rfl)

/-- Morphisms of finite-dimensional modules are determined by their native linear maps. -/
@[ext]
theorem hom_ext {M N : FiniteHopfModuleCat k H} {f g : M ⟶ N}
    (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)

/-- The native linear map underlying the categorical identity is the identity. -/
@[simp]
theorem hom_hom_id (M : FiniteHopfModuleCat k H) :
    (𝟙 M : M ⟶ M).hom.hom = LinearMap.id := (rfl)

/-- Categorical composition agrees with composition of native linear maps. -/
@[simp]
theorem hom_hom_comp {M N P : FiniteHopfModuleCat k H} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom.hom = g.hom.hom ∘ₗ f.hom.hom := (rfl)

section Shrink

variable (k H) (V : Type w) [AddCommGroup V] [Module k V] [Module H V]
  [IsScalarTower k H V] [Module.Finite k V]

/-- Bundle a finite-dimensional module in the universe of the scalar field, regardless of its
original carrier universe. The `H`-action is transported through `Shrink.linearEquiv H V`. -/
def ofShrink : FiniteHopfModuleCat k H :=
  have : Small.{u} V := Module.Finite.small k V
  ⟨ModuleCat.of H (Shrink.{u} V), by
    let e : ((ModuleCat.restrictScalars (algebraMap k H)).obj
        (ModuleCat.of H (Shrink.{u} V))) ≃ₗ[k] V :=
      { (Shrink.linearEquiv H V).toAddEquiv with
        map_smul' := fun r x =>
          ((Shrink.linearEquiv H V).map_smul (algebraMap k H r) x).trans
            (IsScalarTower.algebraMap_smul H r _) }
    exact Module.Finite.equiv e.symm⟩

/-- Shrinking a finite-dimensional module preserves its native `H`-action. -/
def ofShrinkEquiv : ofShrink k H V ≃ₗ[H] V :=
  have : Small.{u} V := Module.Finite.small k V
  Shrink.linearEquiv H V

/-- The shrink comparison is also linear over the scalar field. -/
def ofShrinkLinearEquiv : ofShrink k H V ≃ₗ[k] V :=
  (ofShrinkEquiv k H V).restrictScalars k

/-- The scalar-field comparison has the same underlying function as the `H`-linear comparison. -/
@[simp]
theorem ofShrinkLinearEquiv_apply (x : ofShrink k H V) :
    ofShrinkLinearEquiv k H V x = ofShrinkEquiv k H V x := (rfl)

/-- The inverse scalar-field comparison agrees with the inverse `H`-linear comparison. -/
@[simp]
theorem ofShrinkLinearEquiv_symm_apply (x : V) :
    (ofShrinkLinearEquiv k H V).symm x = (ofShrinkEquiv k H V).symm x := (rfl)

/-- Shrinking preserves dimension over the scalar field. -/
@[simp]
theorem finrank_ofShrink : Module.finrank k (ofShrink k H V) = Module.finrank k V :=
  (ofShrinkLinearEquiv k H V).finrank_eq

end Shrink

section ShrinkHom

variable (k H) {V : Type w} [AddCommGroup V] [Module k V] [Module H V]
  [IsScalarTower k H V] [Module.Finite k V]
  {W : Type*} [AddCommGroup W] [Module k W] [Module H W]
  [IsScalarTower k H W] [Module.Finite k W]

/-- Transport an intertwiner to the small models by conjugating through the shrink comparisons.
The original modules may have different carrier universes. -/
def shrinkHom (f : V →ₗ[H] W) : ofShrink k H V ⟶ ofShrink k H W :=
  ObjectProperty.homMk (ModuleCat.ofHom <|
    (ofShrinkEquiv k H W).symm.toLinearMap ∘ₗ f ∘ₗ (ofShrinkEquiv k H V).toLinearMap)

/-- The native linear map of a transported intertwiner is conjugation by the comparisons. -/
@[simp]
theorem shrinkHom_hom_hom (f : V →ₗ[H] W) :
    (shrinkHom k H f).hom.hom =
      (ofShrinkEquiv k H W).symm.toLinearMap ∘ₗ f ∘ₗ (ofShrinkEquiv k H V).toLinearMap := (rfl)

/-- Transport to the small models preserves identities. -/
@[simp]
theorem shrinkHom_id : shrinkHom k H (LinearMap.id (R := H) (M := V)) = 𝟙 _ := by
  ext x
  simp

variable {X : Type*} [AddCommGroup X] [Module k X] [Module H X]
  [IsScalarTower k H X] [Module.Finite k X]

/-- Transport to the small models preserves composition. -/
@[simp]
theorem shrinkHom_comp (f : V →ₗ[H] W) (g : W →ₗ[H] X) :
    shrinkHom k H (g ∘ₗ f) = shrinkHom k H f ≫ shrinkHom k H g := by
  ext x
  simp

end ShrinkHom

end FiniteHopfModuleCat

end TauCeti
