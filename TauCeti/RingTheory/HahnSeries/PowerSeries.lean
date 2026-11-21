/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.PowerSeries

/-!
# Power series as scalars on Hahn series

If `A⟦X⟧` is an `S`-algebra, the `S`-algebra structure on `A⟦Γ⟧` is inherited from `A⟦X⟧`
through `HahnSeries.ofPowerSeries`. This file records that the resulting algebra actions form a
scalar tower `S → A⟦X⟧ → A⟦Γ⟧`.

## Main results

* `HahnSeries.ofPowerSeries_comp_algebraMap`: composing `HahnSeries.ofPowerSeries` with
  `algebraMap S A⟦X⟧` recovers `algebraMap S A⟦Γ⟧`.
* `TauCeti.hahnSeries_isScalarTower_powerSeries`: the algebra actions of `S` on `A⟦X⟧` and on
  Hahn series `A⟦Γ⟧` form a scalar tower.
-/

public section

open scoped PowerSeries

namespace HahnSeries

/-- Composing `HahnSeries.ofPowerSeries` with `algebraMap S A⟦X⟧` recovers `algebraMap S A⟦Γ⟧`. -/
@[simp]
theorem ofPowerSeries_comp_algebraMap {Γ A S : Type*} [Semiring Γ] [PartialOrder Γ]
    [IsStrictOrderedRing Γ] [CommSemiring A] [CommSemiring S] [Algebra S A⟦X⟧] :
    (ofPowerSeries Γ A).comp (algebraMap S A⟦X⟧) = algebraMap S (HahnSeries Γ A) :=
  RingHom.ext fun s ↦ (algebraMap_apply' Γ s).symm

end HahnSeries

namespace TauCeti

/-- If `A⟦X⟧` is an `S`-algebra, the scalars of `S` on the Hahn series `A⟦Γ⟧` factor through
`A⟦X⟧`. The `S`-algebra structure on `A⟦Γ⟧` is the one inherited from `A⟦X⟧`. -/
instance hahnSeries_isScalarTower_powerSeries {Γ A S : Type*} [Semiring Γ] [PartialOrder Γ]
    [IsStrictOrderedRing Γ] [CommSemiring A] [CommSemiring S] [Algebra S A⟦X⟧] :
    IsScalarTower S A⟦X⟧ (HahnSeries Γ A) :=
  .of_algebraMap_eq fun s ↦ by
    rw [HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply', Algebra.algebraMap_self_apply]

end TauCeti
