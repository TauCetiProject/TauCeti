/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.MonoidAlgebra.Artinian
public import TauCeti.RepresentationTheory.AsModule

/-!
# The dictionary between representations of a finite monoid and modules over its monoid algebra

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
`TauCeti.conflation_map_fdRepEquivalence_functor_iff`. A **group** algebra is the special case of
a group `G`, which nothing here needs: `G` is an arbitrary finite monoid throughout.

The equivalence itself needs no hypothesis on `k` beyond `CommRing`, and none on `G` beyond
`Finite`; only the comparison of exact structures, which reads short exactness in the abelian
categories `FDRep k G` and `FGModuleCat k[G]`, asks for Noetherian coefficients, the hypothesis
under which `FGModuleCat` is abelian. `FDRep k G` gets it from `k` directly, and `FGModuleCat k[G]`
from `TauCeti.isNoetherianRing_monoidAlgebra`. The monoid may live in any universe for the
dictionary,
but the exact structure `TauCeti.finiteModulesExactStructure R` is defined only on
`FGModuleCat.{u} R` for `R : Type u`, so the comparison of exact structures is stated for a monoid
in the universe of `k`.

## Main definitions

* `TauCeti.fdRepToFGModuleCat`: the functor `FDRep k G ⥤ FGModuleCat k[G]`, `V ↦ V.ρ.asModule`,
  obtained by restricting `Rep.toModuleMonoidAlgebra` to the finite objects.
* `TauCeti.fdRepEquivalence`: that functor as an equivalence of categories.

## Main statements

* `TauCeti.fdRepEquivalence_functor_obj_obj`: the dictionary sends `V` to `V.ρ.asModule`.
* `TauCeti.fdRepEquivalence_functor_comp_ι`: composed with the inclusion of the finitely generated
  modules it *is* Mathlib's `Rep.toModuleMonoidAlgebra`, precomposed with the forgetful functor
  `FDRep k G ⥤ Rep k G`.
* `TauCeti.exists_fdRep_linearEquiv`: every finitely generated `k[G]`-module comes from a
  representation.
* `TauCeti.conflation_map_fdRepEquivalence_functor_iff`: the dictionary matches short exact
  sequences of representations with the conflations of the finitely generated `k[G]`-modules.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

namespace TauCeti

universe u v

section Dictionary

variable (k : Type u) (G : Type v) [CommRing k] [Monoid G] [Finite G]

/-- The module over the monoid algebra attached to a module-finite representation is finitely
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
the monoid algebra. -/
@[simp]
theorem fdRepEquivalence_functor_obj_obj (V : FDRep k G) :
    ((fdRepEquivalence k G).functor.obj V).obj =
      ModuleCat.of k[G] (Representation.asModule V.ρ) := (rfl)

/-- **Every finitely generated module over the monoid algebra of a finite monoid comes from a
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

-- `TauCeti.finiteModulesExactStructure` pins the carrier universe of `FGModuleCat R` to the
-- universe of `R`, so the exact structure on `FGModuleCat.{u} k[G]` exists only when
-- `k[G] : Type u`, i.e. for `G` in the universe of `k`. The dictionary itself is universe
-- polymorphic in `G`.
variable (k G : Type u) [CommRing k] [IsNoetherianRing k] [Monoid G] [Finite G]

/-- **The dictionary is exact.** A short complex of representations is short exact exactly when
its image is a conflation of the exact structure on the finitely generated `k[G]`-modules — the
exact structure whose Grothendieck group is `G₀(k[G])`. The dictionary is an equivalence between
abelian categories, hence exact, and faithful, hence exactness-reflecting.

This is deliberately not a `simp` lemma: `TauCeti.finiteModulesExactStructure_conflation_iff` is
already one, so `simp` rewrites the left-hand side below before this lemma can fire, and tagging it
fails the `simpNF` linter. -/
theorem conflation_map_fdRepEquivalence_functor_iff (S : ShortComplex (FDRep k G)) :
    (finiteModulesExactStructure k[G]).Conflation (S.map (fdRepEquivalence k G).functor) ↔
      S.ShortExact :=
  (finiteModulesExactStructure_conflation_iff _ _).trans
    ((ShortExact.shortExact_map_iff (forget₂ (FGModuleCat.{u} k[G]) (ModuleCat.{u} k[G]))).trans
      (ShortExact.shortExact_map_iff (fdRepEquivalence k G).functor))

end Exactness

end TauCeti
