/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic

/-!
# Jumps of the ramification filtrations

A jump is an index at which the ramification group is strictly larger than at every later
index. This definition applies to both the lower and upper real-indexed filtrations, including
the possible jump at `-1` from the full Galois group to inertia. The Herbrand order isomorphism
carries the lower jumps exactly to the upper jumps. At an integer, the lower-jump condition is
equivalent to a strict decrease from `G_i` to `G_{i+1}`.

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

/-- A lower break: the ramification group at `u` is strictly larger than the group at every
later index. Since lower numbering uses ceilings, its breaks occur at integers. -/
def LowerJump (u : RamificationIndexDomain) : Prop :=
  ∀ v : RamificationIndexDomain, u < v →
    lowerRamificationGroupReal K L v < lowerRamificationGroupReal K L u

/-- An upper break: the upper ramification group at `u` is strictly larger than the group at
every later index. -/
def UpperJump (u : RamificationIndexDomain) : Prop :=
  ∀ v : RamificationIndexDomain, u < v →
    upperRamificationGroup K L v < upperRamificationGroup K L u

/-- The Herbrand function takes lower breaks precisely to upper breaks. -/
@[simp]
theorem upperJump_herbrand_iff (u : RamificationIndexDomain) :
    UpperJump K L (herbrand K L u) ↔ LowerJump K L u := by
  constructor
  · intro h v huv
    have h' := h (herbrand K L v) ((herbrand_strictMono K L) huv)
    simpa only [upperRamificationGroup_herbrand] using h'
  · intro h v huv
    have h' : u < inverseHerbrand K L v := by
      have hv := (inverseHerbrand_strictMono K L) huv
      rwa [inverseHerbrand_herbrand] at hv
    simpa only [upperRamificationGroup_def, inverseHerbrand_herbrand] using
      h (inverseHerbrand K L v) h'

omit [IsGalois K L] in
/-- At an integer `i ≥ -1`, a lower break is exactly a strict decrease from `G_i` to
`G_{i+1}`. -/
@[simp]
theorem lowerJump_intCast_iff {i : ℤ} (hi : (-1 : ℝ) ≤ (i : ℝ)) :
    LowerJump K L ⟨i, hi⟩ ↔
      lowerRamificationGroup K L (i + 1) < lowerRamificationGroup K L i := by
  constructor
  · intro h
    have hi' : (-1 : ℝ) ≤ ((i + 1 : ℤ) : ℝ) := by
      have h : (i : ℝ) ≤ ((i + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact hi.trans h
    have hsucc : (⟨(i : ℝ), hi⟩ : RamificationIndexDomain) < ⟨(i + 1 : ℤ), hi'⟩ := by
      apply Subtype.mk_lt_mk.mpr
      exact_mod_cast (by omega : i < i + 1)
    simpa only [LowerJump, lowerRamificationGroupReal_intCast] using
      h ⟨(i + 1 : ℤ), hi'⟩ hsucc
  · intro h v hiv
    have hreal : (i : ℝ) < (v : ℝ) := hiv
    have hceil : i + 1 ≤ ⌈(v : ℝ)⌉ := by
      have hlt : i < ⌈(v : ℝ)⌉ := (Int.lt_ceil).2 hreal
      omega
    have hle : lowerRamificationGroupReal K L v ≤
        lowerRamificationGroup K L (i + 1) := by
      rw [lowerRamificationGroupReal_def]
      exact lowerRamificationGroup_antitone K L hceil
    simpa only [Subtype.coe_mk, lowerRamificationGroupReal_intCast] using lt_of_le_of_lt hle h

end TauCeti.LocalFieldsRamification
