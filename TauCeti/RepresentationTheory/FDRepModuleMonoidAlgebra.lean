/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.RepresentationTheory.AsModule

/-!
# The dictionary between representations of a finite monoid and modules over its monoid algebra

Mathlib's `Rep.equivalenceModuleMonoidAlgebra` identifies the `k`-linear representations of a
monoid `G` with the modules over the monoid algebra `k[G]`, by sending a representation `V` to
`V.ρ.asModule`. This file restricts that equivalence to the finite objects on both sides,

`TauCeti.fdRepEquivalence : FDRep k G ≌ FGModuleCat k[G]`.

The comparison of finiteness conditions behind the restriction is
`Representation.finite_asModule_iff`: for a **finite** monoid `G` the `k[G]`-module `ρ.asModule` is
finitely generated exactly when its carrier is finitely generated over `k`, because `k[G]` is then
a finite free `k`-module. Only one direction of that comparison needs `G` to be finite — a
representation whose carrier is module-finite over `k` defines a finitely generated `k[G]`-module
for every monoid — so the functor `TauCeti.fdRepToFGModuleCat`, which is Mathlib's
`Rep.toModuleMonoidAlgebra` read on the finite objects, is defined, full, faithful and additive for
an arbitrary monoid, and it is its essential surjectivity, hence the equivalence, that asks for
`Finite G`.

A **group** algebra is the special case of a group `G`, which nothing here needs: `G` is an
arbitrary monoid throughout, finite where the equivalence is concerned, and `k` an arbitrary
commutative ring.

## Main definitions

* `TauCeti.fdRepToFGModuleCat`: the functor `FDRep k G ⥤ FGModuleCat k[G]`, `V ↦ V.ρ.asModule`,
  obtained by restricting `Rep.toModuleMonoidAlgebra` to the finite objects.
* `TauCeti.fdRepEquivalence`: that functor, for a finite monoid, as an equivalence of categories.

## Main statements

* `TauCeti.isFG_obj_toModuleMonoidAlgebra`: a module-finite representation of an arbitrary monoid
  defines a finitely generated module over the monoid algebra, the object condition behind the
  restriction.
* `TauCeti.fdRepEquivalence_functor_obj_obj`: the dictionary sends `V` to `V.ρ.asModule`.
* `TauCeti.fdRepEquivalence_functor_map_hom`: on a morphism of representations it is the
  `k[G]`-linear map that `Rep.toModuleMonoidAlgebra` attaches to it.
* `TauCeti.fdRepEquivalence_functor_comp_ι`: composed with the inclusion of the finitely generated
  modules it *is* Mathlib's `Rep.toModuleMonoidAlgebra`, precomposed with the forgetful functor
  `FDRep k G ⥤ Rep k G`.
* `TauCeti.exists_fdRep_linearEquiv`: every finitely generated `k[G]`-module over a finite monoid
  comes from a representation.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u v

variable (k : Type u) (G : Type v) [CommRing k] [Monoid G]

/-- **A module-finite representation defines a finitely generated module over the monoid algebra.**
Finitely many `k`-generators of the carrier generate the attached `k[G]`-module as well, so this
direction of `Representation.finite_asModule_iff` needs no hypothesis on `G`. It is the object
condition that lets `Rep.toModuleMonoidAlgebra` be restricted to the finite objects. -/
theorem isFG_obj_toModuleMonoidAlgebra (A : FDRep k G) :
    ModuleCat.isFG.{u} k[G]
      ((forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra).obj A) :=
  Module.Finite.of_restrictScalars_finite k k[G]
    ((forget₂ (FDRep k G) (Rep k G)).obj A).ρ.asModule

-- The dictionary and the functor beneath it are exposed, so that an importing module reads the
-- module and the map off them as the ones `Rep.toModuleMonoidAlgebra` produces, definitionally.
/-- **The dictionary functor.** A module-finite representation of a monoid `G`, viewed as a
finitely generated module over the monoid algebra `k[G]`: Mathlib's `Rep.toModuleMonoidAlgebra`
restricted to the finite objects on both sides. -/
@[expose] noncomputable def fdRepToFGModuleCat : FDRep k G ⥤ FGModuleCat.{u} k[G] :=
  (ModuleCat.isFG.{u} k[G]).lift
    (forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra)
    (isFG_obj_toModuleMonoidAlgebra k G)

instance : (fdRepToFGModuleCat k G).Full := by
  unfold fdRepToFGModuleCat; infer_instance

instance : (fdRepToFGModuleCat k G).Faithful := by
  unfold fdRepToFGModuleCat; infer_instance

-- The morphisms of a full subcategory are the morphisms of the ambient category, so the
-- dictionary adds morphisms exactly as `Rep.toModuleMonoidAlgebra` does, definitionally.
instance : (fdRepToFGModuleCat k G).Additive where
  map_add := (rfl)

variable [Finite G]

instance : (fdRepToFGModuleCat k G).EssSurj where
  mem_essImage M := by
    have hM : Module.Finite k[G] M.obj := M.property
    have : Module.Finite k (Rep.ofModuleMonoidAlgebra.obj M.obj) :=
      (Representation.finite_asModule_iff _).mp
        (Module.Finite.equiv (Rep.counitIso M.obj).toLinearEquiv.symm)
    exact ⟨FDRep.of (Rep.ofModuleMonoidAlgebra.obj M.obj).ρ,
      ⟨(ModuleCat.isFG.{u} k[G]).isoMk (Rep.counitIso M.obj)⟩⟩

instance : (fdRepToFGModuleCat k G).IsEquivalence where

/-- **The dictionary.** For a finite monoid `G`, the module-finite `k`-linear representations of
`G` are the finitely generated modules over the monoid algebra `k[G]`, by `V ↦ V.ρ.asModule`. -/
@[expose] noncomputable def fdRepEquivalence : FDRep k G ≌ FGModuleCat.{u} k[G] :=
  (fdRepToFGModuleCat k G).asEquivalence

/-- The functor underlying the dictionary is `TauCeti.fdRepToFGModuleCat`, which carries the
fullness, faithfulness and additivity the dictionary inherits. -/
theorem fdRepEquivalence_functor :
    (fdRepEquivalence k G).functor = fdRepToFGModuleCat k G := (rfl)

/-- Composed with the inclusion of the finitely generated modules, the dictionary is Mathlib's
`Rep.toModuleMonoidAlgebra` on the underlying representation: the dictionary changes neither the
module nor the maps, only the ambient category. -/
theorem fdRepEquivalence_functor_comp_ι :
    (fdRepEquivalence k G).functor ⋙ (ModuleCat.isFG.{u} k[G]).ι =
      forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra := (rfl)

/-- **The object formula**: the dictionary sends a representation to the module it defines over
the monoid algebra. -/
@[simp]
theorem fdRepEquivalence_functor_obj_obj (V : FDRep k G) :
    ((fdRepEquivalence k G).functor.obj V).obj =
      ModuleCat.of k[G] (Representation.asModule V.ρ) := (rfl)

/-- **The morphism formula**: on a morphism of representations the dictionary is the `k[G]`-linear
map that `Rep.toModuleMonoidAlgebra` attaches to it, the underlying map of the intertwining map
itself. -/
@[simp]
theorem fdRepEquivalence_functor_map_hom {V W : FDRep k G} (f : V ⟶ W) :
    ((fdRepEquivalence k G).functor.map f).hom =
      Rep.toModuleMonoidAlgebra.map ((forget₂ (FDRep k G) (Rep k G)).map f) := (rfl)

/-- **Every finitely generated module over the monoid algebra of a finite monoid comes from a
representation**, the concrete form of the essential surjectivity of the dictionary. -/
theorem exists_fdRep_linearEquiv (M : Type u) [AddCommGroup M] [Module k[G] M]
    [Module.Finite k[G] M] :
    ∃ V : FDRep k G, Nonempty (Representation.asModule V.ρ ≃ₗ[k[G]] M) :=
  ⟨(fdRepToFGModuleCat k G).objPreimage
      ⟨ModuleCat.of k[G] M, inferInstanceAs (Module.Finite k[G] M)⟩,
    ⟨((ModuleCat.isFG.{u} k[G]).ι.mapIso
      ((fdRepToFGModuleCat k G).objObjPreimageIso _)).toLinearEquiv⟩⟩

end TauCeti
