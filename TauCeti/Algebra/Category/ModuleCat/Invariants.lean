/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# Limits of actions on modules are submodules of invariants

A functor `J : SingleObj G ⥤ ModuleCat R` is an `R`-module `J.obj *` with an action of the monoid
`G` by the linear maps `J.map g`, and its limit is the module of invariants. This file reads a
given limit cone concretely: its leg `c.pt ⟶ J.obj *` is injective
(`ModuleCat.injective_π_app_star_of_isLimit`), and its range is the submodule
`ModuleCat.invariants J` of the elements fixed by every `J.map g`
(`ModuleCat.range_π_app_star_of_isLimit`). So the cone point is identified with the invariants,
whose inclusion is itself a limit cone (`ModuleCat.isLimitInvariantsCone`). In particular every
action of a monoid, of any universe, on modules has a limit
(`ModuleCat.hasLimitsOfShape_singleObj`), and so has every action on complexes of modules.

This is the form in which limit cones over an action, such as the one by which the transfer of a
finite quotient covering exhibits the homology of the base as the invariants of the homology of the
total space (`IsQuotientCoveringMap.isLimitHomologyMapConePairTransferCone`), are applied to
individual classes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u w

namespace ModuleCat

variable {G : Type w} [Monoid G] {R : Type u} [Ring R] {J : SingleObj G ⥤ ModuleCat.{v} R}
  {c : Cone J} (hc : IsLimit c)

variable (J) in
/-- The invariants of an action `J : SingleObj G ⥤ ModuleCat R`: the submodule of the elements of
`J.obj *` fixed by every `J.map g`. -/
def invariants : Submodule R (J.obj (SingleObj.star G)) where
  carrier := {y | ∀ g : G, (J.map g).hom y = y}
  add_mem' hx hy g := by simp [hx g, hy g]
  zero_mem' _ := map_zero _
  smul_mem' r _ hx g := by simp [hx g]

/-- An element lies in the invariants of `J` exactly when every `J.map g` fixes it. -/
@[simp]
theorem mem_invariants_iff {y : J.obj (SingleObj.star G)} :
    y ∈ invariants J ↔ ∀ g : G, (J.map g).hom y = y :=
  Iff.rfl

variable (J) in
/-- The cone over `J` given by the inclusion of its invariants. -/
@[simps pt π_app]
def invariantsCone : Cone J where
  pt := ModuleCat.of R (invariants J)
  π :=
    { app _ := ModuleCat.ofHom (invariants J).subtype
      naturality _ _ g := by
        ext y
        exact (y.property g).symm }

variable (J) in
/-- **The invariants are the limit of an action.** The inclusion of the invariants of
`J : SingleObj G ⥤ ModuleCat R` is a limit cone over `J`: a cone over `J` factors through it by
restricting its leg to the invariants, in which that leg lands. -/
def isLimitInvariantsCone : IsLimit (invariantsCone J) where
  lift s := ModuleCat.ofHom ((s.π.app (SingleObj.star G)).hom.codRestrict _
    fun x g ↦ congr($(s.w g).hom x))
  fac s j := by
    -- The shape `SingleObj G` has a single object.
    obtain rfl : j = SingleObj.star G := rfl
    rfl
  uniq s m hm := by
    ext x
    exact Subtype.ext congr($(hm (SingleObj.star G)).hom x)

/-- **Actions on modules have limits**, the submodules of invariants (`isLimitInvariantsCone`),
whatever the universe of the acting monoid. -/
instance hasLimitsOfShape_singleObj : HasLimitsOfShape (SingleObj G) (ModuleCat.{v} R) :=
  ⟨fun J ↦ ⟨⟨⟨_, isLimitInvariantsCone J⟩⟩⟩⟩

include hc in
/-- **The leg of a limit cone over an action is injective.** For a limit cone `c` over
`J : SingleObj G ⥤ ModuleCat R`, its leg `c.pt ⟶ J.obj *` is injective. -/
theorem injective_π_app_star_of_isLimit : Function.Injective (c.π.app (SingleObj.star G)).hom :=
  fun x y h ↦ Concrete.isLimit_ext J hc x y fun j ↦ by
    -- The shape `SingleObj G` has a single object.
    obtain rfl : j = SingleObj.star G := rfl
    exact h

include hc in
/-- **The range of the leg of a limit cone over an action is the invariants.** For a limit cone `c`
over `J : SingleObj G ⥤ ModuleCat R`, the range of the leg `c.pt ⟶ J.obj *` is the submodule
`ModuleCat.invariants J` of the elements fixed by every `J.map g`. -/
theorem range_π_app_star_of_isLimit :
    LinearMap.range (c.π.app (SingleObj.star G)).hom = invariants J := by
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, rfl⟩ g
    exact congr($(c.w g).hom x)
  · exact ⟨(hc.lift (invariantsCone J)).hom ⟨y, hy⟩,
      congr($(hc.fac (invariantsCone J) (SingleObj.star G)).hom (⟨y, hy⟩ : invariants J))⟩

end ModuleCat
