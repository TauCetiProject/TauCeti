/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
public import TauCeti.RingTheory.LocalRing.UnitFiltration

/-!
# Interaction between the ramification filtration and the unit filtration of a local ring

Let a group `G` act by ring automorphisms on a commutative local ring `S`. This file records the
compatibility between the ramification filtration `TauCeti.IsLocalRing.ramificationGroup G S` and
the unit filtration `TauCeti.IsLocalRing.unitFiltration S`.

## Main results

* `TauCeti.IsLocalRing.unitsMap_div_mem_unitFiltration_succ`: an element of the `i`-th
  ramification group moves every unit of a local ring by a factor in `U_{i+1}`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

section Action

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- For an element `σ` in the `i`-th ramification group of a local ring `S` and any unit `u : Sˣ`,
the ratio `(σ • u) / u` lies one step deeper in the unit filtration, in `unitFiltration S (i + 1)`.
-/
theorem unitsMap_div_mem_unitFiltration_succ {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S (i : ℤ)) (u : Sˣ) :
    Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom u / u ∈
      unitFiltration S (i + 1) := by
  rw [div_eq_mul_inv, unitFiltration_def]
  exact Ideal.unitsMap_mul_inv_mem_principalUnitGroup
    (Ideal.mem_inertia.mpr (mem_ramificationGroup_natCast_iff.mp hσ)) u

end Action

end TauCeti.IsLocalRing
