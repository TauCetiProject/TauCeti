/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.RingTheory.LocalRing.RamificationGroup

/-!
# Lower ramification groups of a local field extension

For a finite Galois extension `L/K` of nonarchimedean local fields, the canonical lower
ramification group consists of automorphisms acting trivially on the integer ring modulo
the `(i + 1)`-st power of its maximal ideal. The integer index is total: at `i ≤ -1` the
group is the full Galois group.

This is the local field specialization of `TauCeti.IsLocalRing.ramificationGroup`.

## Main definitions

* `TauCeti.LocalFieldsRamification.lowerRamificationGroup K L i`: the `i`-th lower-numbering
  ramification group of `L/K`.

## Main results

* `TauCeti.LocalFieldsRamification.mem_lowerRamificationGroup_iff`: the defining congruence
  `σ • x ≡ x mod 𝔪 ^ (i + 1)` on `𝒪[L]`.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroup_eq_top_of_le_neg_one`,
  `TauCeti.LocalFieldsRamification.lowerRamificationGroup_zero` and
  `TauCeti.LocalFieldsRamification.lowerRamificationGroup_antitone`: the filtration is `⊤` below
  `0`, starts with the inertia group of the maximal ideal, and decreases.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroup_natCast`: at a nonnegative index it is
  `Ideal.ramificationGroup` of the maximal ideal of `𝒪[L]`.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- The lower-numbering ramification group of a finite extension of local fields. -/
def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) :=
  TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i

/-- The local-field filtration is the ramification filtration of its integer ring. -/
theorem lowerRamificationGroup_def (i : ℤ) :
    lowerRamificationGroup K L i =
      TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i :=
  (rfl)

variable {K L} in
/-- The defining membership criterion of the lower ramification groups. -/
@[simp]
theorem mem_lowerRamificationGroup_iff {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x : 𝒪[L], σ • x - x ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ (i + 1).toNat := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.mem_ramificationGroup_iff]

/-- Below the index `0` the lower filtration is the whole Galois group. -/
theorem lowerRamificationGroup_eq_top_of_le_neg_one {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup K L i = ⊤ := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.ramificationGroup_eq_top_of_le_neg_one _ _ hi]

/-- The zeroth lower ramification group is the inertia group of the maximal ideal of `𝒪[L]`. -/
theorem lowerRamificationGroup_zero :
    lowerRamificationGroup K L 0 = Ideal.inertia (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal 𝒪[L]) := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertia]

/-- The lower ramification filtration is decreasing. -/
theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup K L) :=
  TauCeti.IsLocalRing.ramificationGroup_antitone _ _

/-- At nonnegative indices, the canonical lower group is the maximal-ideal ramification group. -/
@[simp]
theorem lowerRamificationGroup_natCast (i : ℕ) :
    lowerRamificationGroup K L i =
      (IsLocalRing.maximalIdeal 𝒪[L]).ramificationGroup (L ≃ₐ[K] L) i := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.ramificationGroup_natCast]

end TauCeti.LocalFieldsRamification
