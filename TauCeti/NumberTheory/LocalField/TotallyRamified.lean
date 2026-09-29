/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.InertiaDegree

/-!
# Total ramification in towers

The residue-degree characterization of total ramification and multiplicativity of residue degree
show that a tower is totally ramified exactly when each step is. The predicate and characterization
are defined in `RamificationIndex` and `InertiaDegree`, respectively.

## Main results

* `TauCeti.isTotallyRamified_tower_iff`: total ramification is equivalent to total ramification
  of both steps of a tower.

## References

* J.-P. Serre, *Corps Locaux*, Chapter I, §4.
-/

public section
noncomputable section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension K L]

section Tower

variable (K L) (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M]

/-- A tower is totally ramified exactly when both of its steps are totally ramified. -/
theorem isTotallyRamified_tower_iff :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    IsTotallyRamified K M ↔ IsTotallyRamified K L ∧ IsTotallyRamified L M := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  simp only [isTotallyRamified_iff_inertiaDegree_eq_one,
    inertiaDegree_tower (K := K) (L := L) M, mul_eq_one]

/-- Total ramification is transitive in a tower. -/
theorem IsTotallyRamified.trans (hKL : IsTotallyRamified K L)
    (hLM : IsTotallyRamified L M) :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    IsTotallyRamified K M :=
  (isTotallyRamified_tower_iff K L M).2 ⟨hKL, hLM⟩

/-- The first step of a totally ramified tower is totally ramified. -/
theorem IsTotallyRamified.tower_bot
    (hKM : letI : ValuativeExtension K M := ValuativeExtension.trans K L M
      IsTotallyRamified K M) :
    IsTotallyRamified K L :=
  ((isTotallyRamified_tower_iff K L M).1 hKM).1

/-- The second step of a totally ramified tower is totally ramified. -/
theorem IsTotallyRamified.tower_top
    (hKM : letI : ValuativeExtension K M := ValuativeExtension.trans K L M
      IsTotallyRamified K M) :
    IsTotallyRamified L M :=
  ((isTotallyRamified_tower_iff K L M).1 hKM).2

end Tower

end TauCeti
