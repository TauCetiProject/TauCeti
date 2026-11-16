/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder
public import Mathlib.Algebra.Field.ZMod

/-!
# Examples of the odd Montgomery-ladder step

On `y² = x³ + x` over `𝔽₅`, the point `(2, 0)` is a non-distinguished point of order two.
The odd step is nonzero for every index at this base point, not just at points of odd order.
In contrast, at the distinguished point `(0, 0)` it is always zero even though `[1]T₀ + [0]T₀ = T₀`;
its multiples alternate between that point and infinity, and the alternation remains valid in
characteristic two.

On `y² = x³ + x` over `𝔽₇` at `P = (3, 3)`, differential addition of the coordinate pairs of
`[2]P`, `P` and `P` gives `(2, 6)`, representing `x([3]P) = 5`. Modulo `35`, differential addition
of `(21, 25)`, `(22, 1)` and `(22, 1)` gives `(1, 8)` with `gcd(8, 35) = 1`, matching
`[3](2, 0) = (2, 0)` over `𝔽₅` and `[3](1, 3) = (1, 4)` over `𝔽₇`.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section

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
  refine ⟨diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero
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

end

section Concrete

local instance ladderPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance ladderPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

-- For `k = 0`, `[1]T₀ + [0]T₀ = T₀ ≠ 0` even though differential addition outputs `(0, 0)`.
example :
    let T₀ := twoTorsionPoint (0 : ZMod 7) one_ne_zero
    diffAdd (coordinates (0 : ZMod 7) 1 ((1 : ℕ) • T₀))
        (coordinates (0 : ZMod 7) 1 ((0 : ℕ) • T₀)) (coordinates (0 : ZMod 7) 1 T₀) = 0 ∧
      (1 : ℕ) • T₀ + (0 : ℕ) • T₀ = T₀ ∧ T₀ ≠ 0 :=
  ⟨diffAdd_coordinates_nsmul_twoTorsionPoint _ 0, by simp, twoTorsionPoint_ne_zero _ _⟩

-- On `y² = x³ + x` over `𝔽₇` at `P = (3, 3)`, `diffAdd` of the coordinate pairs of `[2]P`, `P`
-- and `P` is `(2, 6) ≠ 0`, representing both `5` and `[3]P`.
example :
    let P : (model (0 : ZMod 7) 1).toAffine.Point :=
      .some 3 3 (by
        simpa using (nonsingular_model_iff (A := (0 : ZMod 7)) one_ne_zero 3 3).mpr (by decide))
    let R := diffAdd (coordinates (0 : ZMod 7) 1 ((2 : ℕ) • P))
      (coordinates (0 : ZMod 7) 1 P) (coordinates (0 : ZMod 7) 1 P)
    R = ⟨2, 6⟩ ∧ R ≠ 0 ∧ R.cross ⟨5, 1⟩ = 0 ∧
      R.cross (coordinates (0 : ZMod 7) 1 ((3 : ℕ) • P)) = 0 := by
  set P : (model (0 : ZMod 7) 1).toAffine.Point :=
    .some 3 3 (by
      simpa using (nonsingular_model_iff (A := (0 : ZMod 7)) one_ne_zero 3 3).mpr (by decide))
  have hd : double (2 : ZMod 7) 4 (coordinates 0 1 P) = ⟨4, 4⟩ := by
    rw [coordinates_some]
    ext <;> simp only [double_x, double_z] <;> decide
  have h2cross := (double_coordinates (N := (2 : ZMod 7)) (D := 4) (by decide) (by decide) P).2
  rw [hd, ← two_nsmul] at h2cross
  have h2coords : coordinates (0 : ZMod 7) 1 ((2 : ℕ) • P) = ⟨1, 1⟩ := by
    rcases h : (2 : ℕ) • P with _ | ⟨x, y, hxy⟩
    · rw [h, ← Affine.Point.zero_def, coordinates_zero, Pair.cross_def] at h2cross
      exact absurd h2cross (by decide)
    · rw [h, coordinates_some, Pair.cross_def] at h2cross
      have hx : x = 1 := (by decide : ∀ a : ZMod 7, 4 * 1 - a * 4 = 0 → a = 1) x h2cross
      subst hx
      rw [coordinates_some]
  have hR : diffAdd (coordinates (0 : ZMod 7) 1 ((2 : ℕ) • P))
      (coordinates (0 : ZMod 7) 1 P) (coordinates (0 : ZMod 7) 1 P) = ⟨2, 6⟩ := by
    rw [h2coords, coordinates_some]
    ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  refine ⟨hR, ?_, ?_, ?_⟩
  · rw [hR, Ne, Pair.eq_zero_iff]
    decide
  · rw [hR, Pair.cross_def]
    decide
  · simpa only [one_nsmul] using
      diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P 1
        (Pair.cross_self _) (Pair.cross_self _) (Pair.cross_self _)

-- Modulo `35`, `diffAdd (21, 25) (22, 1) (22, 1) = (1, 8)` has `gcd(8, 35) = 1`.
private theorem diffAdd_mod35 :
    diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ := by
  ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

example :
    diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ ∧
      Nat.gcd (diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩).z.val 35 = 1 :=
  ⟨diffAdd_mod35, by rw [diffAdd_mod35]; decide⟩

-- Modulo `5`, `(1, 8)` represents `[3](2, 0) = (2, 0)` on `y² = x³ + x`.
example :
    let T : (model (0 : ZMod 5) 1).toAffine.Point :=
      .some 2 0 (by
        simpa using (nonsingular_model_iff (A := (0 : ZMod 5)) one_ne_zero 2 0).mpr (by decide))
    (3 : ℕ) • T = T ∧
      ((⟨1, 8⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
        (coordinates 0 1 ((3 : ℕ) • T)) = 0 := by
  set T : (model (0 : ZMod 5) 1).toAffine.Point :=
    .some 2 0 (by
      simpa using (nonsingular_model_iff (A := (0 : ZMod 5)) one_ne_zero 2 0).mpr (by decide))
  have h2T : (2 : ℕ) • T = 0 := by
    rw [two_nsmul]
    exact Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])
  refine ⟨by rw [succ_nsmul, h2T, zero_add], ?_⟩
  rw [← diffAdd_mod35, map_diffAdd]
  refine diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero T 1 ?_ ?_ ?_
  · rw [h2T, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [one_nsmul, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Modulo `7`, `(1, 8)` represents `[3](1, 3) = (1, 4)` on `y² = x³ + x`.
example :
    let P₇ : (model (0 : ZMod 7) 1).toAffine.Point :=
      .some 1 3 (by
        simpa using (nonsingular_model_iff (A := (0 : ZMod 7)) one_ne_zero 1 3).mpr (by decide))
    (3 : ℕ) • P₇ = .some 1 4 (by
        simpa using (nonsingular_model_iff (A := (0 : ZMod 7)) one_ne_zero 1 4).mpr (by decide)) ∧
      ((⟨1, 8⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 ((3 : ℕ) • P₇)) = 0 := by
  set P₇ : (model (0 : ZMod 7) 1).toAffine.Point :=
    .some 1 3 (by
      simpa using (nonsingular_model_iff (A := (0 : ZMod 7)) one_ne_zero 1 3).mpr (by decide))
  have h2P₇ : (2 : ℕ) • P₇ = twoTorsionPoint 0 one_ne_zero := by
    rw [two_nsmul]
    exact (add_self_eq_twoTorsionPoint_iff one_ne_zero _).mpr (by decide)
  have h4P₇ : (4 : ℕ) • P₇ = 0 := by
    have h4 : (4 : ℕ) = 2 + 2 := rfl
    rw [h4, add_nsmul, h2P₇, twoTorsionPoint_add_self]
  refine ⟨?_, ?_⟩
  · have hneg : (3 : ℕ) • P₇ = -P₇ :=
      eq_neg_of_add_eq_zero_left (by rw [← succ_nsmul]; exact h4P₇)
    rw [hneg, Affine.Point.neg_some]
    simp only [Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
    decide
  · rw [← diffAdd_mod35, map_diffAdd]
    refine diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P₇ 1 ?_ ?_ ?_
    · rw [h2P₇, coordinates_twoTorsionPoint, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [one_nsmul, coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide

end Concrete

end TauCeti.Montgomery
