/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# All modules over an algebra, as a home for coproduct tensor products

`HopfModuleCat k H` is the category of all left `H`-modules with carriers in the universe of the
scalar field `k`. It is a type synonym of the native `ModuleCat.{u} H`, with the same category,
preadditive, `k`-linear and abelian structures. The synonym keeps the tensor product over `k`
through the coproduct of a bialgebra, installed in
`TauCeti.Algebra.Category.HopfModuleCat.Monoidal`, separate from Mathlib's tensor product over
`H`, which exists on `ModuleCat H` whenever `H` is commutative.

Its objects are not Hopf modules in the sense of Larson–Sweedler, which also carry a coaction;
the name records that this is the category of all modules containing Tau Ceti's
`FiniteHopfModuleCat k H` of finite-dimensional modules as a full subcategory.

The underlying category requires only a `k`-algebra. The scalar-field action on an object is
restriction of scalars along `algebraMap k H`.

## Main declarations

* `TauCeti.HopfModuleCat k H`: all left `H`-modules in the universe of `k`.
* `TauCeti.HopfModuleCat.forgetToModule`: the faithful forgetful functor to `k`-modules.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti

universe u v

/-- All left modules over `H`, with carriers in the universe of the scalar field `k`.

This is the native category `ModuleCat.{u} H`; the separate name keeps tensor products over the
scalar field, through a coproduct, apart from tensor products over a commutative `H`. -/
-- Expose the type synonym so that the native module-category constructors and projections apply.
-- Implicit reducibility lets tactics typecheck those projections, without allowing instance
-- search to inherit tensor products over `H`.
@[expose, implicit_reducible]
def HopfModuleCat (_k : Type u) (H : Type v) [Ring H] := ModuleCat.{u} H

namespace HopfModuleCat

section Ring

variable (k : Type u) (H : Type v) [Ring H]

instance : Category (HopfModuleCat k H) := inferInstanceAs (Category (ModuleCat.{u} H))

instance : Preadditive (HopfModuleCat k H) := inferInstanceAs (Preadditive (ModuleCat.{u} H))

instance : Abelian (HopfModuleCat k H) := inferInstanceAs (Abelian (ModuleCat.{u} H))

/-- The carrier of a module. -/
@[expose, reducible]
def carrier (M : HopfModuleCat k H) : Type u := ModuleCat.carrier (R := H) M

instance : CoeSort (HopfModuleCat k H) (Type u) := ⟨carrier k H⟩

attribute [coe] carrier

instance (M : HopfModuleCat k H) : AddCommGroup M :=
  inferInstanceAs (AddCommGroup (ModuleCat.carrier (R := H) M))

instance (M : HopfModuleCat k H) : Module H M :=
  inferInstanceAs (Module H (ModuleCat.carrier (R := H) M))

variable {k H}

/-- Bundle a native module in the universe of the scalar field. -/
abbrev of (V : Type u) [AddCommGroup V] [Module H V] : HopfModuleCat k H :=
  ModuleCat.of H V

/-- Interpret an `H`-linear map as a morphism of modules. -/
abbrev ofHom {V W : Type u} [AddCommGroup V] [Module H V] [AddCommGroup W] [Module H W]
    (f : V →ₗ[H] W) : of (k := k) (H := H) V ⟶ of (k := k) (H := H) W :=
  ModuleCat.ofHom f

/-- Morphisms of modules are determined by their native linear maps. -/
@[ext]
theorem hom_ext {M N : HopfModuleCat k H} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  ModuleCat.hom_ext h

/-- The native linear map underlying the categorical identity is the identity. -/
@[simp]
theorem hom_id (M : HopfModuleCat k H) : (𝟙 M : M ⟶ M).hom = LinearMap.id := (rfl)

/-- Categorical composition agrees with composition of native linear maps. -/
@[simp]
theorem hom_comp {M N P : HopfModuleCat k H} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom ∘ₗ f.hom := (rfl)

end Ring

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H]

instance : Linear k (HopfModuleCat k H) := inferInstanceAs (Linear k (ModuleCat.{u} H))

-- The carrier reduces to the native carrier, so this instance also matches carriers of plain
-- `ModuleCat` objects. Its low priority keeps their native action preferred there; on a
-- `ModuleCat k` object, the restriction along `algebraMap k k` is not reducibly the native one.
instance (priority := 900) (M : HopfModuleCat k H) : Module k M :=
  ((ModuleCat.restrictScalars (algebraMap k H)).obj (C := ModuleCat.{u} H) M).isModule

instance (M : HopfModuleCat k H) : IsScalarTower k H M :=
  IsScalarTower.of_algebraMap_smul fun r x =>
    (ModuleCat.restrictScalars.smul_def (algebraMap k H) (M := (M : ModuleCat.{u} H)) r x).symm

/-- Forget the `H`-action by native restriction of scalars to `k`. -/
abbrev forgetToModule : HopfModuleCat k H ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k H)

/-- The forgetful functor keeps the underlying function of a morphism. -/
@[simp]
theorem forgetToModule_map_hom_apply {M N : HopfModuleCat k H} (f : M ⟶ N) (x : M) :
    ((forgetToModule k H).map f).hom x = f.hom x := (rfl)

instance : (forgetToModule k H).Faithful :=
  inferInstanceAs (ModuleCat.restrictScalars (algebraMap k H)).Faithful

instance : (forgetToModule k H).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars (algebraMap k H)).Additive

instance : (forgetToModule k H).Linear k where
  map_smul f r := by
    ext x
    exact (ModuleCat.restrictScalars.smul_def (algebraMap k H) r (f.hom x)).symm

end HopfModuleCat

end TauCeti
