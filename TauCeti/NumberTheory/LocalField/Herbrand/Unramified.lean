/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic
public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence

/-!
# Herbrand numbering for an unramified extension

The inertia group of an unramified Galois extension is trivial. Consequently every lower and
upper ramification group at a nonnegative index is trivial, and both Herbrand functions are the
identity. In particular the integral inverse Herbrand function leaves unit-filtration depths
unchanged; this identifies the unramified norm theorem with the corresponding Herbrand-indexed
statement.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §3.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing intervalIntegral

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L] [IsUnramified K L]

/-- The inertia group, which is the zeroth lower ramification group, is trivial in an
unramified extension. -/
theorem lowerRamificationGroup_zero_eq_bot_of_isUnramified :
    lowerRamificationGroup K L 0 = ⊥ := by
  rw [lowerRamificationGroup_zero]
  exact IsUnramified.inertia_eq_bot (K := K) (L := L)

/-- All nonnegative lower ramification groups of an unramified extension are trivial. -/
@[simp]
theorem lowerRamificationGroup_eq_bot_of_isUnramified {i : ℤ} (hi : 0 ≤ i) :
    lowerRamificationGroup K L i = ⊥ :=
  le_bot_iff.mp ((lowerRamificationGroup_antitone K L hi).trans
    (lowerRamificationGroup_zero_eq_bot_of_isUnramified K L).le)

/-- The real-indexed lower filtration is trivial at every nonnegative index in an unramified
extension. -/
@[simp]
theorem lowerRamificationGroupReal_eq_bot_of_isUnramified {u : ℝ} (hu : 0 ≤ u) :
    lowerRamificationGroupReal K L u = ⊥ := by
  rw [lowerRamificationGroupReal_def]
  exact lowerRamificationGroup_eq_bot_of_isUnramified K L
    (by exact_mod_cast hu.trans (Int.le_ceil u))

/-- The Herbrand function of an unramified extension is the identity. -/
@[simp]
theorem herbrand_of_isUnramified (u : RamificationIndexDomain) : herbrand K L u = u := by
  by_cases hu : (u : ℝ) ≤ 0
  · exact herbrand_of_coe_le_zero K L hu
  have hnonneg : 0 ≤ (u : ℝ) := le_of_not_ge hu
  apply herbrand_eq_self_of_forall_eq K L hnonneg
  intro t ht0 _
  rw [lowerRamificationGroupReal_eq_bot_of_isUnramified K L ht0.le,
    lowerRamificationGroup_zero_eq_bot_of_isUnramified K L]

/-- The inverse Herbrand function of an unramified extension is the identity. -/
@[simp]
theorem inverseHerbrand_of_isUnramified (u : RamificationIndexDomain) :
    inverseHerbrand K L u = u := by
  calc
    inverseHerbrand K L u = inverseHerbrand K L (herbrand K L u) := by
      rw [herbrand_of_isUnramified]
    _ = u := inverseHerbrand_herbrand K L u

/-- The integral inverse Herbrand function `ψℕ_{L/K}` of an unramified extension is the identity:
`ψℕ_{L/K}(n) = n`. -/
@[simp]
theorem psiNat_of_isUnramified (n : ℕ) : psiNat K L n = n := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, inverseHerbrand_of_isUnramified]

/-- The upper ramification group is trivial at every nonnegative index of an unramified
extension. -/
@[simp]
theorem upperRamificationGroup_eq_bot_of_isUnramified {u : RamificationIndexDomain}
    (hu : 0 ≤ (u : ℝ)) : upperRamificationGroup K L u = ⊥ := by
  rw [upperRamificationGroup_def, inverseHerbrand_of_isUnramified]
  exact lowerRamificationGroupReal_eq_bot_of_isUnramified K L hu

end TauCeti.LocalFieldsRamification
