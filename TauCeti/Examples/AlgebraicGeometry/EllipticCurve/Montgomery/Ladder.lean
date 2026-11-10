/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of the odd Montgomery-ladder step

On `y² = x³ + x` over `𝔽₅`, the point `(2, 0)` is a non-distinguished point of order two.
The odd step is nonzero for every index at this base point, not just at points of odd order.
In contrast, at the distinguished point `(0, 0)` it is always zero; its multiples alternate
between that point and infinity. The alternation remains valid in characteristic two.
-/

namespace TauCeti.Montgomery

open WeierstrassCurve

variable [Fact (Nat.Prime 2)] [Fact (Nat.Prime 5)] [Fact (Nat.Prime 7)]

-- Use three independently scaled representatives of the non-distinguished point of order two.
example (k : ℕ) :
    let T : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 (by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide +revert)
    let R := diffAdd ((2 : ZMod 5) • coordinates (0 : ZMod 5) 1 ((k + 1) • T))
      ((3 : ZMod 5) • coordinates (0 : ZMod 5) 1 (k • T))
      ((4 : ZMod 5) • coordinates (0 : ZMod 5) 1 T)
    R.cross (coordinates (0 : ZMod 5) 1 ((2 * k + 1) • T)) = 0 ∧ R ≠ 0 := by
  dsimp only
  have hB : (1 : ZMod 5) ≠ 0 := one_ne_zero
  have h₂ : (2 : ZMod 5) ≠ 0 := by decide +revert
  have h₃ : (3 : ZMod 5) ≠ 0 := by decide +revert
  have h₄ : (4 : ZMod 5) ≠ 0 := by decide +revert
  have nonsingular_two_zero : (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff,
      model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
    decide +revert
  have hscale (a : ZMod 5) (ha : a ≠ 0) (Q : (model (0 : ZMod 5) 1).toAffine.Point) :
      a • coordinates 0 1 Q ≠ 0 := by
    rw [Ne, Pair.smul_eq_zero, not_or]
    exact ⟨ha, coordinates_ne_zero hB Q⟩
  refine ⟨diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero hB
    (.some 2 0 nonsingular_two_zero) k (by simp) (by simp) (by simp), ?_⟩
  have h := diffAdd_nsmul_ne_zero_iff_of_cross_eq_zero h₂ hB
    (A := 0) (.some 2 0 nonsingular_two_zero) k
    (SNext := (2 : ZMod 5) • coordinates 0 1 ((k + 1) • .some 2 0 nonsingular_two_zero))
    (SCurrent := (3 : ZMod 5) • coordinates 0 1 (k • .some 2 0 nonsingular_two_zero))
    (SBase := (4 : ZMod 5) • coordinates 0 1 (.some 2 0 nonsingular_two_zero))
    (hscale 2 h₂ _) (hscale 3 h₃ _) (hscale 4 h₄ _)
    (by simp) (by simp) (by simp)
  apply h.mpr ⟨Affine.Point.some_ne_zero _, ?_⟩
  exact (some_eq_twoTorsionPoint_iff hB nonsingular_two_zero).not.mpr h₂

-- The distinguished point alternates, while its odd differential-addition step degenerates.
example (k : ℕ) :
    coordinates (0 : ZMod 7) 1 ((2 * k) • twoTorsionPoint (0 : ZMod 7) (by decide +revert)) =
      ⟨1, 0⟩ := by
  simp [coordinates_nsmul_twoTorsionPoint]

example (k : ℕ) :
    coordinates (0 : ZMod 7) 1 ((2 * k + 1) • twoTorsionPoint (0 : ZMod 7) (by decide +revert)) =
      ⟨0, 1⟩ := by
  simp [coordinates_nsmul_twoTorsionPoint]

example (k : ℕ) :
    diffAdd
      (coordinates (0 : ZMod 7) 1 ((k + 1) • twoTorsionPoint (0 : ZMod 7) (by decide +revert)))
      (coordinates (0 : ZMod 7) 1 (k • twoTorsionPoint (0 : ZMod 7) (by decide +revert)))
      (coordinates (0 : ZMod 7) 1 (twoTorsionPoint (0 : ZMod 7) (by decide +revert))) = 0 := by
  simp

-- Characteristic two is not excluded from the alternation theorem.
example (k : ℕ) :
    coordinates (0 : ZMod 2) 1 ((2 * k + 1) • twoTorsionPoint (0 : ZMod 2) (by decide +revert)) =
      ⟨0, 1⟩ := by
  simp [coordinates_nsmul_twoTorsionPoint]

-- Infinity is also an exceptional fixed difference, even though the input pairs are nonzero.
example (k : ℕ) :
    diffAdd (coordinates (0 : ZMod 7) 1 ((k + 1) • (0 : (model (0 : ZMod 7) 1).toAffine.Point)))
      (coordinates (0 : ZMod 7) 1 (k • 0)) (coordinates (0 : ZMod 7) 1 0) = 0 := by
  ext <;> simp

end TauCeti.Montgomery
