/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.RingTheory.Idempotented.NondegMod

/-!
# Nondegenerate modules form a Grothendieck abelian category

Let `H` be an idempotented algebra over a commutative ring `A`. The category `NondegMod A H` of
nondegenerate modules is a full subcategory of the modules over the unitization `A ⊕ H`, closed
under colimits and finite limits. So filtered colimits of nondegenerate modules are computed on
underlying modules and are exact, as they are for modules.

A separator is the nondegenerate part `H • (A ⊕ H)` of the regular module: an element `m` of a
nondegenerate module has a local unit `e ∈ H`, and `r ↦ r • m` sends `e ∈ H • (A ⊕ H)` to
`e • m = m`.

## Main results

* `TauCeti.NondegMod.isSeparator_nondegeneratePartRegular`: the nondegenerate part of the regular
  module is a separator.
* the instances `HasExactColimitsOfShape` (for every shape for which modules have exact colimits)
  and `TauCeti.NondegMod.isGrothendieckAbelian`: when `A` and `H` are `v`-small, `NondegMod.{v} A H`
  is a Grothendieck abelian category.

## References

* J. N. Bernstein, *Le "centre" de Bernstein*, edited by P. Deligne, in *Représentations des groupes
  réductifs sur un corps local*, Hermann, Paris (1984), §1.1.
-/

public section

universe v u₁ u₂

open CategoryTheory Limits

namespace TauCeti.NondegMod

variable (A : Type u₁) (H : Type u₂) [CommRing A] [NonUnitalRing H] [Module A H]
  [IsScalarTower A H H] [SMulCommClass A H H] [IsIdempotented H]

/-- Colimits of nondegenerate modules are exact whenever colimits of the same shape are exact
for modules over the unitization: the inclusion preserves colimits and finite limits. -/
instance hasExactColimitsOfShape (J : Type*) [Category J]
    [HasColimitsOfShape J (ModuleCat.{v} (Unitization A H))]
    [HasExactColimitsOfShape J (ModuleCat.{v} (Unitization A H))] :
    HasExactColimitsOfShape J (NondegMod.{v} A H) :=
  HasExactColimitsOfShape.domain_of_functor J (nondegenerateModuleProperty.{v} A H).ι

/-- Nondegenerate modules satisfy AB5: filtered colimits are exact. -/
instance ab5OfSize : AB5OfSize.{v, v} (NondegMod.{v} A H) where
  ofShape _ _ _ := inferInstance

/-- The nondegenerate part `H • (A ⊕ H)` of the regular module over the unitization, as a
nondegenerate module (with the underlying type shrunk to the universe `v`). -/
noncomputable def nondegeneratePartRegular [Small.{v} A] [Small.{v} H] : NondegMod.{v} A H :=
  (nondegeneratePartFunctor.{v} A H).obj (ModuleCat.of _ (Shrink.{v} (Unitization A H)))

/-- The underlying module of `nondegeneratePartRegular A H` is the nondegenerate part of the
regular module `Shrink (A ⊕ H)`. -/
theorem nondegeneratePartRegular_obj [Small.{v} A] [Small.{v} H] :
    (nondegeneratePartRegular.{v} A H).obj =
      ModuleCat.of _ (nondegeneratePart A H (Shrink.{v} (Unitization A H))) :=
  (rfl)

/-- The nondegenerate part of the regular module over the unitization is a separator of the
category of nondegenerate modules. -/
theorem isSeparator_nondegeneratePartRegular [Small.{v} A] [Small.{v} H] :
    IsSeparator (nondegeneratePartRegular.{v} A H) := by
  rw [isSeparator_def]
  intro X Y f g hfg
  ext x
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 ((nondegenerateModuleProperty_iff _).1 X.property) x
  let R := Unitization A H
  -- The map `r ↦ r • x` out of the regular module, restricted to its nondegenerate part.
  let φ : Shrink.{v} R →ₗ[R] X.obj :=
    (LinearMap.toSpanSingleton R X.obj x).comp (Shrink.linearEquiv R R).toLinearMap
  let h : nondegeneratePartRegular.{v} A H ⟶ X :=
    ObjectProperty.homMk (ModuleCat.ofHom (φ.comp (nondegeneratePart A H _).subtype))
  let m : (nondegeneratePartRegular.{v} A H).obj :=
    (⟨(e : R) • equivShrink R 1, inr_smul_mem_nondegeneratePart e _⟩ :
      nondegeneratePart A H (Shrink.{v} R))
  have hm : (h.hom.hom m : X.obj) = x := by
    -- `h` applied to `m` is `φ m` by `ObjectProperty.homMk_hom` and `ModuleCat.hom_ofHom`, but
    -- `simp` cannot use them: the source of `h` is `nondegeneratePartRegular A H`, which is
    -- `ModuleCat.of _ (H • Shrink R)` only after unfolding (`nondegeneratePartRegular_obj`).
    change φ ((e : R) • equivShrink R 1) = x
    simp [φ, he]
  have := congrArg (fun k : nondegeneratePartRegular.{v} A H ⟶ Y ↦ k.hom.hom m) (hfg h)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, hm] using this

instance hasSeparator [Small.{v} A] [Small.{v} H] : HasSeparator (NondegMod.{v} A H) :=
  ⟨_, isSeparator_nondegeneratePartRegular A H⟩

/-- **Nondegenerate modules form a Grothendieck abelian category.** -/
instance isGrothendieckAbelian [Small.{v} A] [Small.{v} H] :
    IsGrothendieckAbelian.{v} (NondegMod.{v} A H) where

end TauCeti.NondegMod
