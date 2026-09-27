/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import TauCeti.CategoryTheory.Subobject.Equivalence
public import TauCeti.Order.CompactlyGenerated

/-!
# Finite generation and projectivity along an equivalence of module categories

Let `e : ModuleCat A ≌ ModuleCat B` be an equivalence of categories between the module categories
of two rings, for instance a Morita equivalence. Finite generation of a module is a property of its
submodule lattice: `M` is finitely generated exactly when `⊤` is a compact element of
`Submodule A M`. Since `e` induces an order isomorphism between subobject lattices, and the
subobjects of a module are its submodules, `e` preserves and reflects finite generation.
Projectivity is a categorical property, so it is preserved and reflected as well.

The results are stated for arbitrary equivalences of module categories, with the two rings and
the two module universes independent.

## Main definitions

* `CategoryTheory.Equivalence.submoduleOrderIso`: the order isomorphism
  `Submodule A M ≃o Submodule B (e.functor.obj M)` induced by `e`.

## Main results

* `CategoryTheory.Equivalence.submoduleOrderIso_apply`: it sends a submodule to the image of its
  inclusion under `e.functor`.
* `CategoryTheory.Equivalence.finite_functor_obj_iff`: `e.functor.obj M` is finitely generated
  if and only if `M` is.
* `CategoryTheory.Equivalence.isFG_inverseImage`: `e.functor` pulls the finitely generated
  `B`-modules back to the finitely generated `A`-modules.
* `CategoryTheory.Equivalence.projective_functor_obj_iff`: `e.functor.obj M` is projective if
  and only if `M` is.
-/

public section

namespace CategoryTheory.Equivalence

open CategoryTheory.ObjectProperty

universe v v' u u'

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B)

/-- **Submodules along an equivalence of module categories.** The order isomorphism from the
submodules of `M` to the submodules of `e.functor.obj M`, obtained by identifying submodules with
categorical subobjects on both sides. -/
noncomputable def submoduleOrderIso (M : ModuleCat.{v} A) :
    Submodule A M ≃o Submodule B (e.functor.obj M) :=
  (ModuleCat.subobjectModule M).symm.trans
    ((e.subobjectOrderIso M).trans (ModuleCat.subobjectModule (e.functor.obj M)))

/-- The induced order isomorphism of submodule lattices sends a submodule `N` of `M` to the
image of `e.functor.obj N` under the map induced by the inclusion `N ⟶ M`. -/
@[simp]
theorem submoduleOrderIso_apply (M : ModuleCat.{v} A) (N : Submodule A M) :
    e.submoduleOrderIso M N = LinearMap.range (e.functor.map (ModuleCat.ofHom N.subtype)).hom := by
  -- `ModuleCat.subobjectModule` has no evaluation lemmas; `h1` and `h2` record its two directions.
  have h1 : (ModuleCat.subobjectModule M).symm N = Subobject.mk (ModuleCat.ofHom N.subtype) := rfl
  have h2 : ∀ S : Subobject (e.functor.obj M),
      ModuleCat.subobjectModule (e.functor.obj M) S = LinearMap.range S.arrow.hom := fun _ ↦ rfl
  rw [submoduleOrderIso, OrderIso.trans_apply, OrderIso.trans_apply, h1, subobjectOrderIso_mk, h2,
    ← Subobject.underlyingIso_hom_comp_eq_mk, ModuleCat.hom_comp,
    LinearMap.range_comp_of_range_eq_top _ (ModuleCat.range_eq_top_of_epi _)]

/-- An equivalence of module categories preserves and reflects finite generation. -/
@[simp]
theorem finite_functor_obj_iff (M : ModuleCat.{v} A) :
    Module.Finite B (e.functor.obj M) ↔ Module.Finite A M := by
  rw [Module.finite_def, Module.finite_def, Submodule.fg_iff_compact, Submodule.fg_iff_compact,
    ← (e.submoduleOrderIso M).map_top, OrderIso.isCompactElement_iff]

/-- An equivalence of module categories pulls the finitely generated `B`-modules back to the
finitely generated `A`-modules. -/
@[simp]
theorem isFG_inverseImage : (ModuleCat.isFG.{v'} B).inverseImage e.functor = ModuleCat.isFG.{v} A :=
  funext fun M ↦ propext (e.finite_functor_obj_iff M)

/-- An equivalence of module categories preserves and reflects projectivity. -/
@[simp]
theorem projective_functor_obj_iff [Small.{v} A] [Small.{v'} B] (M : ModuleCat.{v} A) :
    Module.Projective B (e.functor.obj M) ↔ Module.Projective A M := by
  constructor
  · intro h
    have : Projective M := (e.map_projective_iff M).mp inferInstance
    exact M.projective_of_module_projective
  · intro h
    have : Projective (e.functor.obj M) := (e.map_projective_iff M).mpr inferInstance
    exact (e.functor.obj M).projective_of_module_projective

end CategoryTheory.Equivalence
