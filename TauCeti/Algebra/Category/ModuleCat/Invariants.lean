/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# Limits of actions on modules are submodules of invariants

A functor `J : SingleObj G ⥤ ModuleCat R` is an `R`-module `J.obj *` with an action of the monoid
`G` by the linear maps `J.map g`, and its limit is the module of invariants. This file reads a
given limit cone concretely: its leg `c.pt ⟶ J.obj *` is injective
(`ModuleCat.injective_π_app_star_of_isLimit`), and its range consists of the elements fixed by every
`J.map g` (`ModuleCat.mem_range_π_app_star_of_isLimit_iff`). So the cone point is identified with
the invariants.

This is the form in which limit cones over an action, such as the one by which the transfer of a
finite quotient covering exhibits the homology of the base as the invariants of the homology of the
total space (`IsQuotientCoveringMap.isLimitHomologyMapConePairTransferCone`), are applied to
individual classes.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u w

namespace ModuleCat

variable {G : Type w} [Monoid G] {R : Type u} [Ring R] {J : SingleObj G ⥤ ModuleCat.{v} R}
  {c : Cone J} (hc : IsLimit c)

/-- The submodule of the elements of `J.obj *` fixed by every `J.map g`. -/
private abbrev fixed : Submodule R (J.obj (SingleObj.star G)) :=
  ⨅ g : G, LinearMap.ker ((J.map g).hom - LinearMap.id)

private theorem map_apply_of_mem_fixed {y : J.obj (SingleObj.star G)} (hy : y ∈ fixed (J := J))
    (g : G) : (J.map g).hom y = y := by
  have := Submodule.mem_iInf _ |>.1 hy g
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this

/-- The cone over `J` given by the inclusion of the submodule of fixed elements. -/
private def fixedCone : Cone J where
  pt := ModuleCat.of R (fixed (J := J))
  π :=
    { app _ := ModuleCat.ofHom (fixed (J := J)).subtype
      naturality _ _ g := by
        ext y
        exact (map_apply_of_mem_fixed y.property g).symm }

include hc in
/-- **The leg of a limit cone over an action is injective.** For a limit cone `c` over
`J : SingleObj G ⥤ ModuleCat R`, its leg `c.pt ⟶ J.obj *` is injective. -/
theorem injective_π_app_star_of_isLimit : Function.Injective (c.π.app (SingleObj.star G)).hom := by
  refine LinearMap.ker_eq_bot.1 (eq_bot_iff.2 fun x hx ↦ ?_)
  let N := LinearMap.ker (c.π.app (SingleObj.star G)).hom
  have h : ModuleCat.ofHom N.subtype = (0 : ModuleCat.of R N ⟶ c.pt) := hc.hom_ext fun j ↦ by
    -- The shape `SingleObj G` has a single object.
    obtain rfl : j = SingleObj.star G := rfl
    ext y
    simp
  exact (Submodule.mem_bot R).2 congr($(h).hom ⟨x, hx⟩)

include hc in
/-- **The range of the leg of a limit cone over an action is the invariants.** For a limit cone `c`
over `J : SingleObj G ⥤ ModuleCat R`, an element of `J.obj *` lies in the range of the leg
`c.pt ⟶ J.obj *` exactly when every `J.map g` fixes it. -/
theorem mem_range_π_app_star_of_isLimit_iff (y : J.obj (SingleObj.star G)) :
    y ∈ LinearMap.range (c.π.app (SingleObj.star G)).hom ↔ ∀ g : G, (J.map g).hom y = y := by
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, rfl⟩ g
    exact congr($(c.w g).hom x)
  · have hy' : y ∈ fixed (J := J) := Submodule.mem_iInf _ |>.2 fun g ↦ by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hy g]
    exact ⟨(hc.lift fixedCone).hom (⟨y, hy'⟩ : fixed (J := J)),
      congr($(hc.fac fixedCone (SingleObj.star G)).hom (⟨y, hy'⟩ : fixed (J := J)))⟩

end ModuleCat
