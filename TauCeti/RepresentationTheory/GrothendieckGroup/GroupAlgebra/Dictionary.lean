/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.RepresentationTheory.FDRep

/-!
# The dictionary between representations of a finite group and modules over its group algebra

Mathlib's `Rep.equivalenceModuleMonoidAlgebra` identifies the `k`-linear representations of a
monoid `G` with the modules over the monoid algebra `k[G]`, by sending a representation `V` to
`V.ρ.asModule`. When `G` is **finite** that equivalence restricts to the finite objects on both
sides, because `k[G]` is then a finite free `k`-module: a `k[G]`-module is finitely generated
exactly when the `k`-module underlying it is
(`Representation.finite_asModule_iff`). This file records the restriction,

`TauCeti.fdRepEquivalence : FDRep k G ≌ FGModuleCat k[G]`,

which `Mathlib/RepresentationTheory/FDRep.lean` lists as a TODO. It is the dictionary through
which the Grothendieck group of the finitely generated `k[G]`-modules is read as a Grothendieck
group of representations: the exact structure
`TauCeti.finiteModulesExactStructure (MonoidAlgebra k G)` is transported to the short exact
sequences of the abelian category `FDRep k G`, in both directions, by
`TauCeti.conflation_map_fdRepEquivalence_functor_iff`.

Beside the equivalence the file records that `k[G]` is an Artinian ring whenever `k` is and `G`
is finite. That instance is what puts the Jordan-Hölder theory of
`TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis` — the simple-class basis of an
exact `K₀` over an Artinian ring — at the disposal of a group algebra, and through
`IsArtinianRing`'s Hopkins-Levitzki consequence it also supplies the Noetherianness that makes
`FGModuleCat k[G]` abelian.

The equivalence itself needs no hypothesis on `k` beyond `CommRing`, and none on `G` beyond
`Finite`; only the comparison of exact structures, which reads short exactness in the abelian
categories `FDRep k G` and `FGModuleCat k[G]`, asks for Artinian coefficients.

## Main definitions

* `TauCeti.fdRepToFGModuleCat`: the functor `FDRep k G ⥤ FGModuleCat k[G]`, `V ↦ V.ρ.asModule`,
  obtained by restricting `Rep.toModuleMonoidAlgebra` to the finite objects.
* `TauCeti.fdRepEquivalence`: that functor as an equivalence of categories.

## Main statements

* `Representation.finite_asModule_iff`: for a finite monoid `G`, the `k[G]`-module attached to a
  representation is finitely generated if and only if its carrier is finitely generated over `k`.
* `TauCeti.isArtinianRing_monoidAlgebra`: the monoid algebra of a finite monoid over an Artinian
  commutative ring is Artinian.
* `TauCeti.fdRepEquivalence_functor_obj_obj`: the dictionary sends `V` to `V.ρ.asModule`.
* `TauCeti.fdRepEquivalence_functor_comp_ι`: composed with the inclusion of the finitely generated
  modules it *is* Mathlib's `Rep.toModuleMonoidAlgebra`, precomposed with the forgetful functor
  `FDRep k G ⥤ Rep k G`.
* `TauCeti.exists_fdRep_linearEquiv`: every finitely generated `k[G]`-module comes from a
  representation.
* `TauCeti.shortExact_map_fdRepEquivalence_functor_iff` and
  `TauCeti.conflation_map_fdRepEquivalence_functor_iff`: the dictionary matches short exact
  sequences of representations with the conflations of the finitely generated `k[G]`-modules.

## References

* [Modular-induction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ModularInduction/README.md),
  Layer 0, "the Grothendieck group of a group algebra".
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [Finite G] [AddCommMonoid V] [Module k V]

/-- **Finiteness passes through the group algebra.** For a finite monoid `G`, the `k[G]`-module
`ρ.asModule` attached to a representation `ρ` is finitely generated exactly when its carrier is
finitely generated over `k`. Both directions are transitivity of module-finiteness along
`k → k[G]`, which is a finite extension because `G` is finite. -/
theorem finite_asModule_iff (ρ : Representation k G V) :
    Module.Finite k[G] ρ.asModule ↔ Module.Finite k V := by
  constructor
  · intro h
    have : Module.Finite k ρ.asModule := Module.Finite.trans k[G] ρ.asModule
    exact Module.Finite.equiv ρ.asModuleEquiv
  · intro h
    have : Module.Finite k ρ.asModule := inferInstance
    exact Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule

end Representation

namespace TauCeti

universe u

/-- **The group algebra of a finite monoid is Artinian** over Artinian coefficients, being a
module-finite algebra over them. This is the hypothesis of `TauCeti.simpleClassBasis`, and by
Hopkins-Levitzki it also makes `k[G]` Noetherian, hence `FGModuleCat k[G]` abelian. -/
instance isArtinianRing_monoidAlgebra (k G : Type*) [CommRing k] [IsArtinianRing k] [Monoid G]
    [Finite G] : IsArtinianRing (MonoidAlgebra k G) :=
  IsArtinianRing.of_finite k (MonoidAlgebra k G)

section Dictionary

variable (k G : Type u) [CommRing k] [Monoid G] [Finite G]

/-- The module over the group algebra attached to a module-finite representation is finitely
generated. This is the object condition that lets `Rep.toModuleMonoidAlgebra` be restricted to
the finite objects; it is `Representation.finite_asModule_iff` read on `FDRep k G`. -/
private theorem isFG_obj_toModuleMonoidAlgebra (A : FDRep k G) :
    ModuleCat.isFG.{u} k[G]
      ((forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra).obj A) :=
  (Representation.finite_asModule_iff ((forget₂ (FDRep k G) (Rep k G)).obj A).ρ).mpr inferInstance

/-- **The dictionary functor.** A module-finite representation of a finite monoid `G`, viewed as
a finitely generated module over the monoid algebra `k[G]`: Mathlib's `Rep.toModuleMonoidAlgebra`
restricted to the finite objects on both sides. -/
noncomputable def fdRepToFGModuleCat : FDRep k G ⥤ FGModuleCat.{u} k[G] :=
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
noncomputable def fdRepEquivalence : FDRep k G ≌ FGModuleCat.{u} k[G] :=
  (fdRepToFGModuleCat k G).asEquivalence

/-- The functor underlying the dictionary is `TauCeti.fdRepToFGModuleCat`. The body of
`TauCeti.fdRepEquivalence` is not exposed, so this is how an importing module reaches the
instances carried by the functor. -/
theorem fdRepEquivalence_functor :
    (fdRepEquivalence k G).functor = fdRepToFGModuleCat k G := (rfl)

/-- Composed with the inclusion of the finitely generated modules, the dictionary is Mathlib's
`Rep.toModuleMonoidAlgebra` on the underlying representation: the dictionary changes neither the
module nor the maps, only the ambient category. -/
theorem fdRepEquivalence_functor_comp_ι :
    (fdRepEquivalence k G).functor ⋙ (ModuleCat.isFG.{u} k[G]).ι =
      forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra := (rfl)

/-- **The object formula**: the dictionary sends a representation to the module it defines over
the group algebra. -/
theorem fdRepEquivalence_functor_obj_obj (V : FDRep k G) :
    ((fdRepEquivalence k G).functor.obj V).obj =
      ModuleCat.of k[G] (Representation.asModule V.ρ) := (rfl)

/-- **Every finitely generated module over the group algebra of a finite monoid comes from a
representation**, the concrete form of the essential surjectivity of the dictionary. -/
theorem exists_fdRep_linearEquiv (M : Type u) [AddCommGroup M] [Module k[G] M]
    [Module.Finite k[G] M] :
    ∃ V : FDRep k G, Nonempty (Representation.asModule V.ρ ≃ₗ[k[G]] M) :=
  ⟨(fdRepToFGModuleCat k G).objPreimage
      ⟨ModuleCat.of k[G] M, inferInstanceAs (Module.Finite k[G] M)⟩,
    ⟨((ModuleCat.isFG.{u} k[G]).ι.mapIso
      ((fdRepToFGModuleCat k G).objObjPreimageIso _)).toLinearEquiv⟩⟩

end Dictionary

section Exactness

variable (k G : Type u) [CommRing k] [IsArtinianRing k] [Monoid G] [Finite G]

/-- The dictionary matches the short exact sequences of `FDRep k G` with those of
`FGModuleCat k[G]`: it is an equivalence between abelian categories, hence exact, and faithful,
hence exactness-reflecting. -/
theorem shortExact_map_fdRepEquivalence_functor_iff (S : ShortComplex (FDRep k G)) :
    (S.map (fdRepEquivalence k G).functor).ShortExact ↔ S.ShortExact :=
  ShortExact.shortExact_map_iff _

/-- **The dictionary is exact.** A short complex of representations is short exact exactly when
its image is a conflation of the exact structure on the finitely generated `k[G]`-modules — the
exact structure whose Grothendieck group is `G₀(k[G])`. -/
theorem conflation_map_fdRepEquivalence_functor_iff (S : ShortComplex (FDRep k G)) :
    (finiteModulesExactStructure k[G]).Conflation (S.map (fdRepEquivalence k G).functor) ↔
      S.ShortExact :=
  (finiteModulesExactStructure_conflation_iff _ _).trans
    ((ShortExact.shortExact_map_iff (forget₂ (FGModuleCat.{u} k[G]) (ModuleCat.{u} k[G]))).trans
      (shortExact_map_fdRepEquivalence_functor_iff k G S))

end Exactness

end TauCeti
