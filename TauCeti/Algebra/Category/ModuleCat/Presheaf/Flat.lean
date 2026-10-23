/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Sectionwise flat presheaves of modules

Let `R` be a presheaf of commutative rings. The tensor product of presheaves of `R`-modules is
computed sectionwise, so tensoring with a presheaf of modules `P` whose modules of sections
`P(X)` are all flat over `R(X)` preserves monomorphisms. Free presheaves of modules are
sectionwise free, hence sectionwise flat. Sheafifying such presheaves gives flat sheaves of
modules, in `TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Flat`.

## Main declarations

* `PresheafOfModulesOfCommRing.preservesMonomorphisms_tensorLeft_of_flat`: tensoring with a
  sectionwise flat presheaf of modules preserves monomorphisms;
* `PresheafOfModulesOfCommRing.flat_freeObj_obj`: free presheaves of modules are sectionwise
  flat.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace PresheafOfModulesOfCommRing

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Tensoring with a presheaf of modules whose modules of sections are all flat preserves
monomorphisms. -/
instance preservesMonomorphisms_tensorLeft_of_flat (P : PresheafOfModulesOfCommRing.{u} R)
    [∀ X, Module.Flat (R.obj X) (P.obj X)] : (tensorLeft P).PreservesMonomorphisms where
  preserves {_ _} f _ := by
    refine PresheafOfModules.mono_of_injective fun X ↦ ?_
    -- The component of `P ◁ f` at `X` is the tensor product with `P.obj X` of that of `f`.
    have : Mono (f.app' X) := inferInstanceAs (Mono (f.app X))
    exact (ModuleCat.mono_iff_injective _).1 ((tensorLeft (P.obj X)).map_mono (f.app' X))

/-- The modules of sections of a free presheaf of modules are free, hence flat. -/
instance flat_freeObj_obj (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) :
    Module.Flat (R.obj X)
      (PresheafOfModulesOfCommRing.obj (PresheafOfModules.freeObj (R := R ⋙ forget₂ _ _) F) X) :=
  inferInstanceAs (Module.Flat (R.obj X) (F.obj X →₀ R.obj X))

end PresheafOfModulesOfCommRing
