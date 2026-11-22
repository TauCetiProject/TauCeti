/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Minimal periods along cyclic-subgroup orbits

For a group `G` acting on a type `α` and an element `g : G`, the minimal period of `g • ·` is
invariant along every `Subgroup.zpowers g`-orbit, and any point `a` is a `g ^ j`-translate of its
`Subgroup.zpowers g`-orbit representative `⟦a⟧.out`.

## Main results

* `MulAction.minimalPeriod_zpow_smul`: `Function.minimalPeriod (g • ·) (g ^ j • a) =
  Function.minimalPeriod (g • ·) a`.
* `MulAction.exists_zpow_smul_eq_out`: every `a` satisfies `g ^ j • a = ⟦a⟧.out` for some
  `j : ℤ`.
-/

public section

namespace MulAction

/-- The minimal period of `g • ·` is constant along every `Subgroup.zpowers g`-orbit. -/
@[to_additive /-- The minimal period of `g +ᵥ ·` is constant along every
`AddSubgroup.zmultiples g`-orbit. -/]
theorem minimalPeriod_zpow_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (j : ℤ)
    (a : α) :
    Function.minimalPeriod (g • ·) (g ^ j • a) = Function.minimalPeriod (g • ·) a :=
  Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ by
    simp only [isPeriodicPt_smul_iff, ← mul_smul]
    rw [← zpow_natCast, ← zpow_add, add_comm, zpow_add, zpow_natCast, mul_smul,
      smul_left_cancel_iff]

/-- Any point `a` is a `g ^ j`-translate of its `Subgroup.zpowers g`-orbit representative
`⟦a⟧.out`. -/
@[to_additive /-- Any point `a` is a `(j • g) +ᵥ ·`-translate of its
`AddSubgroup.zmultiples g`-orbit representative `⟦a⟧.out`. -/]
theorem exists_zpow_smul_eq_out {G α : Type*} [Group G] [MulAction G α] (g : G) (a : α) :
    ∃ j : ℤ, g ^ j • a = (⟦a⟧ : orbitRel.Quotient (Subgroup.zpowers g) α).out := by
  obtain ⟨h, hh⟩ := (orbitRel_apply (G := Subgroup.zpowers g)).mp
    (Quotient.eq.mp (Quotient.out_eq (⟦a⟧ : orbitRel.Quotient (Subgroup.zpowers g) α)))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h.property
  exact ⟨j, by rw [hj]; exact hh⟩

end MulAction

end
