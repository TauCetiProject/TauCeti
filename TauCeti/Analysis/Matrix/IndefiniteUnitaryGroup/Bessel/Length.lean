/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.CosetNorm
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Graded.BesselGroup

/-!
# Bessel length

The Bessel length measures the smallest operator norm obtainable by translating a point by
its Bessel subgroup, with `1` added. For a string of length `2ρ + 1`, the graded form at `N = 1`
has `ρ` hyperbolic planes and a negative unit line, in addition to the positive space indexed
by `X`. The graded Bessel group is the product of its unipotent subgroup and the copy of `U(X)`.
The length is continuous and its closed sublevel condition gives an actual norm-bounded
representative. The scaled length is used to measure decay on the Bessel quotient.

The lengths follow `New.besselLength` and `New.scaledBesselLength` in `grh-lean`
(revision `72fead1`, `src/New/Spanning/Bessel/Basic.lean`).
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TauCeti

variable {𝕜 X : Type*} [RCLike 𝕜] [Fintype X] [DecidableEq X] {s : ℕ}

/-- The Bessel length of `y` is `1` plus the infimum of `‖h * y‖` over Bessel translates. -/
noncomputable def besselLength (y : unitaryGroupOf (gradedGram X s (1 : 𝕜))) : ℝ :=
  (gradedBesselGroup X s (1 : 𝕜)).rightCosetOpNorm y + 1

/-- Read the Bessel length as a translated coset norm. -/
theorem besselLength_def (y : unitaryGroupOf (gradedGram X s (1 : 𝕜))) :
    besselLength y = (gradedBesselGroup X s (1 : 𝕜)).rightCosetOpNorm y + 1 := (rfl)

/-- Bessel length does not change under left translation by the Bessel subgroup. -/
@[simp] theorem besselLength_mul_left (y : unitaryGroupOf (gradedGram X s (1 : 𝕜)))
    (h : gradedBesselGroup X s (1 : 𝕜)) : besselLength (h.val * y) = besselLength y := by
  simp [besselLength_def]

/-- Bessel length is continuous on the normalized graded unitary group. -/
theorem continuous_besselLength :
    Continuous (besselLength : unitaryGroupOf (gradedGram X s (1 : 𝕜)) → ℝ) := by
  exact ((gradedBesselGroup X s (1 : 𝕜)).continuous_rightCosetOpNorm.add
    (continuous_const (y := (1 : ℝ)))).congr fun y ↦ (besselLength_def y).symm

/-- In positive matrix size, every Bessel length is at least two. -/
theorem two_le_besselLength [Nonempty (X ⊕ Fin s)]
    (y : unitaryGroupOf (gradedGram X s (1 : 𝕜))) : 2 ≤ besselLength y := by
  rw [besselLength_def]
  suffices 1 ≤ (gradedBesselGroup X s (1 : 𝕜)).rightCosetOpNorm y by linarith
  exact (Subgroup.le_rightCosetOpNorm_iff _).mpr fun h ↦
    one_le_norm_val_of_mem_unitaryGroupOf gradedGram_one_mem_unitary (h.val * y).property

/-- The Bessel length is at most `L` precisely when some translate has norm at most `L - 1`. -/
theorem besselLength_le_iff (y : unitaryGroupOf (gradedGram X s (1 : 𝕜))) {L : ℝ} :
    besselLength y ≤ L ↔ ∃ h : gradedBesselGroup X s (1 : 𝕜),
      ‖((h.val * y : GL (X ⊕ Fin s) 𝕜) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) 𝕜)‖ + 1 ≤ L := by
  rw [besselLength_def]
  constructor
  · intro hy
    obtain ⟨h, hh⟩ := (gradedBesselGroup X s (1 : 𝕜)).exists_norm_eq_rightCosetOpNorm
      (Unitary.isUnit_coe (U := ⟨_, gradedGram_one_mem_unitary⟩)) isClosed_gradedBesselGroup y
    exact ⟨h, hh ▸ hy⟩
  · rintro ⟨h, hh⟩
    exact (add_le_add_left ((gradedBesselGroup X s (1 : 𝕜)).rightCosetOpNorm_le y h) 1).trans hh

/-- The Bessel length at the identity is two in positive matrix size. -/
@[simp] theorem besselLength_one [Nonempty (X ⊕ Fin s)] :
    besselLength (1 : unitaryGroupOf (gradedGram X s (1 : 𝕜))) = 2 := by
  refine le_antisymm ((besselLength_le_iff _).mpr ⟨1, ?_⟩) (two_le_besselLength _)
  norm_num

/-- The Bessel length divided by `b^(6n)` and clipped below at `1`, where `n = (s + 1) / 2`
counts the string vectors of nonnegative grade. For `s = 2ρ + 1`, this is the frame size `ρ + 1`. -/
noncomputable def scaledBesselLength (y : unitaryGroupOf (gradedGram X s (1 : 𝕜)))
    (b : ℝ) : ℝ :=
  max 1 (besselLength y / b ^ (6 * ((s + 1) / 2)))

/-- The scaled length is the rescaled Bessel length clipped below at `1`. -/
theorem scaledBesselLength_def (y : unitaryGroupOf (gradedGram X s (1 : 𝕜))) (b : ℝ) :
    scaledBesselLength y b = max 1 (besselLength y / b ^ (6 * ((s + 1) / 2))) := (rfl)

/-- The scaled Bessel length is continuous in the group variable at every fixed scale. -/
theorem continuous_scaledBesselLength (b : ℝ) :
    Continuous fun y : unitaryGroupOf (gradedGram X s (1 : 𝕜)) ↦ scaledBesselLength y b := by
  simp only [scaledBesselLength_def, div_eq_mul_inv]
  exact continuous_const.max (continuous_besselLength.mul continuous_const)

/-- The scaled Bessel length is constant under left translation by the Bessel subgroup. -/
@[simp] theorem scaledBesselLength_mul_left (y : unitaryGroupOf (gradedGram X s (1 : 𝕜)))
    (h : gradedBesselGroup X s (1 : 𝕜)) (b : ℝ) :
    scaledBesselLength (h.val * y) b = scaledBesselLength y b := by
  simp [scaledBesselLength_def]

/-- The threshold for the scaled length gives a norm cutoff at the original scale. -/
theorem scaledBesselLength_le_iff (y : unitaryGroupOf (gradedGram X s (1 : 𝕜)))
    {b L : ℝ} (hb : 0 < b) : scaledBesselLength y b ≤ L ↔
    1 ≤ L ∧ besselLength y ≤ L * b ^ (6 * ((s + 1) / 2)) := by
  rw [scaledBesselLength_def, max_le_iff, div_le_iff₀ (pow_pos hb _)]

end TauCeti
