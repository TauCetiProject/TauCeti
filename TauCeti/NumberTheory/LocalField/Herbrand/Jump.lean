/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic

/-!
# Jumps of the ramification filtrations

An upper jump is an index at which the upper ramification group is strictly larger than at every
later index, including the possible jump at `-1` from the full Galois group to inertia. The
Herbrand order isomorphism carries the lower jumps exactly to the upper jumps. The lower-jump
definition and its integer criterion are in `RamificationGroup`.

These statements identify the breaks used by the norm filtration and Hasse–Arf theory.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

/-- An upper break: the upper ramification group at `u` is strictly larger than the group at
every later index. -/
def UpperJump (u : RamificationIndexDomain) : Prop :=
  ∀ v : RamificationIndexDomain, u < v →
    upperRamificationGroup K L v < upperRamificationGroup K L u

/-- An upper break is a strict drop of the upper ramification group at every later index. -/
theorem upperJump_iff (u : RamificationIndexDomain) :
    UpperJump K L u ↔ ∀ v : RamificationIndexDomain, u < v →
      upperRamificationGroup K L v < upperRamificationGroup K L u := Iff.rfl

/-- The Herbrand function takes lower breaks precisely to upper breaks. -/
@[simp]
theorem upperJump_herbrand_iff (u : RamificationIndexDomain) :
    UpperJump K L (herbrand K L u) ↔ LowerJump K L u := by
  constructor
  · intro h
    apply (lowerJump_iff K L u).mpr
    intro v huv
    have h' := (upperJump_iff K L _).mp h (herbrand K L v)
      ((herbrand_strictMono K L) huv)
    simpa only [upperRamificationGroup_herbrand] using h'
  · intro h
    apply (upperJump_iff K L _).mpr
    intro v huv
    have h' : u < inverseHerbrand K L v := by
      have hv := (inverseHerbrand_strictMono K L) huv
      rwa [inverseHerbrand_herbrand] at hv
    simpa only [upperRamificationGroup_def, inverseHerbrand_herbrand] using
      (lowerJump_iff K L u).mp h (inverseHerbrand K L v) h'

/-- The inverse Herbrand function takes upper breaks precisely to lower breaks. -/
@[simp]
theorem lowerJump_inverseHerbrand_iff (u : RamificationIndexDomain) :
    LowerJump K L (inverseHerbrand K L u) ↔ UpperJump K L u := by
  simpa only [herbrand_inverseHerbrand] using
    (upperJump_herbrand_iff K L (inverseHerbrand K L u)).symm

end TauCeti.LocalFieldsRamification
