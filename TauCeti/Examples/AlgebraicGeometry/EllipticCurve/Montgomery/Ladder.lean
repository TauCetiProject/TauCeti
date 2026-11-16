/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
public import Mathlib.Algebra.Field.ZMod

/-!
# Examples of the odd Montgomery-ladder step

On `y² = x³ + x` over `𝔽₅`, the point `(2, 0)` is a non-distinguished point of order two.
The odd step is nonzero for every index at this base point, not just at points of odd order.
In contrast, at the distinguished point `(0, 0)` it is always zero; its multiples alternate
between that point and infinity, and already at `k = 0` the sum `[1]T₀ + [0]T₀ = T₀` is nonzero
while `diffAdd` degenerates to `(0, 0)`. The alternation remains valid in characteristic two.

Over `𝔽₇`, the generator `P = (3, 3)` of order `8` on `y² = x³ + x` has multiples `[1..8]P` with
Montgomery `x`-coordinates `3, 1, 5, 0, 5, 1, 3, ∞`, computed directly from `double_coordinates`,
`diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero` and negation invariance without
Weierstrass `y`-coordinates, and the odd step from `[2]P`, `P`, `P` is a nonzero representative
of `5`. Modulo `35`, applying `diffAdd` to `(21, 25)`, `(22, 1)`, `(22, 1)` yields `(1, 8)` with
`gcd(8, 35) = 1`, whose reductions modulo `5` and `7` represent `[3](2, 0) = (2, 0)` over `𝔽₅`
and `[3](1, 3) = (1, 4)` over `𝔽₇`.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, p. 261: the binary ladder relations.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section Parametric

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

end Parametric

section Concrete

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- On `model 0 1` over `𝔽₇`, a pair `(r, 1)` with vanishing cross difference against
-- `coordinates 0 1 R` forces `coordinates 0 1 R = (r, 1)`.
private theorem coordinates_eq_of_cross_eq_zero {r : ZMod 7}
    {R : (model (0 : ZMod 7) 1).toAffine.Point}
    (h : (⟨r, 1⟩ : Pair (ZMod 7)).cross (coordinates 0 1 R) = 0) :
    coordinates 0 1 R = ⟨r, 1⟩ := by
  rcases R with _ | ⟨x, y, hns⟩
  · simp [← Affine.Point.zero_def, Pair.cross_def] at h
  · simp only [coordinates_some, Pair.cross_def, mul_one, sub_eq_zero] at h
    rw [coordinates_some, ← h]

private theorem nonsingular_three_three : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def baseSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 3 3 nonsingular_three_three

-- Over `𝔽₇` with `(A, B) = (0, 1)` and `P = (3, 3)` of order `8`, the multiples `[1..8]P` have
-- coordinate pairs representing `x = 3, 1, 5, 0, 5, 1, 3, ∞`, and `diffAdd` of the pairs of
-- `[2]P`, `P`, `P` is a nonzero representative of `5`.
example :
    coordinates 0 1 ((1 : ℕ) • baseSeven) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((2 : ℕ) • baseSeven) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((3 : ℕ) • baseSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((4 : ℕ) • baseSeven) = ⟨0, 1⟩ ∧
    coordinates 0 1 ((5 : ℕ) • baseSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((6 : ℕ) • baseSeven) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((7 : ℕ) • baseSeven) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((8 : ℕ) • baseSeven) = ⟨1, 0⟩ ∧
    diffAdd (coordinates 0 1 ((2 : ℕ) • baseSeven)) (coordinates 0 1 baseSeven)
      (coordinates 0 1 baseSeven) ≠ 0 ∧
    (diffAdd (coordinates 0 1 ((2 : ℕ) • baseSeven)) (coordinates 0 1 baseSeven)
      (coordinates 0 1 baseSeven)).cross ⟨5, 1⟩ = 0 := by
  have hD : (4 : ZMod 7) ≠ 0 := by decide
  have hND : 4 * (2 : ZMod 7) = ((0 : ZMod 7) + 2) * 4 := by decide
  have hc₁ : coordinates 0 1 baseSeven = ⟨3, 1⟩ := coordinates_some _ _ _
  have hc₂ : coordinates 0 1 ((2 : ℕ) • baseSeven) = ⟨1, 1⟩ := by
    obtain ⟨hne, hcr⟩ := double_coordinates hD hND baseSeven
    rw [hc₁] at hne
    rw [← two_nsmul, hc₁] at hcr
    exact coordinates_eq_of_cross_eq_zero
      (Pair.cross_eq_zero_trans hne (by rw [Pair.cross_def, double_x, double_z]; decide) hcr)
  have hdiff₃ := diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero baseSeven 1
    (Pair.cross_self _) (Pair.cross_self _) (Pair.cross_self _)
  rw [one_nsmul] at hdiff₃
  have hne₃ : diffAdd (coordinates 0 1 ((2 : ℕ) • baseSeven)) (coordinates 0 1 baseSeven)
      (coordinates 0 1 baseSeven) ≠ 0 := by
    have hiff := diffAdd_nsmul_ne_zero_iff_of_cross_eq_zero (by decide)
      (one_ne_zero : (1 : ZMod 7) ≠ 0) baseSeven 1
      (coordinates_ne_zero one_ne_zero ((2 : ℕ) • baseSeven))
      (coordinates_ne_zero one_ne_zero ((1 : ℕ) • baseSeven))
      (coordinates_ne_zero one_ne_zero baseSeven)
      (Pair.cross_self _) (Pair.cross_self _) (Pair.cross_self _)
    rw [one_nsmul] at hiff
    refine hiff.mpr ⟨Affine.Point.some_ne_zero _, ?_⟩
    exact (some_eq_twoTorsionPoint_iff one_ne_zero nonsingular_three_three).not.mpr (by decide)
  have hc₃ : coordinates 0 1 ((3 : ℕ) • baseSeven) = ⟨5, 1⟩ := by
    have hraw : (⟨5, 1⟩ : Pair (ZMod 7)).cross
        (diffAdd (coordinates 0 1 ((2 : ℕ) • baseSeven)) (coordinates 0 1 baseSeven)
          (coordinates 0 1 baseSeven)) = 0 := by
      rw [hc₂, hc₁, Pair.cross_def, diffAdd_x, diffAdd_z, Pair.cross_def]
      decide
    exact coordinates_eq_of_cross_eq_zero (Pair.cross_eq_zero_trans hne₃ hraw hdiff₃)
  have hc₄ : coordinates 0 1 ((4 : ℕ) • baseSeven) = ⟨0, 1⟩ := by
    obtain ⟨hne, hcr⟩ := double_coordinates hD hND ((2 : ℕ) • baseSeven)
    have h4 : (2 : ℕ) • baseSeven + (2 : ℕ) • baseSeven = (4 : ℕ) • baseSeven := by
      rw [← add_nsmul]
    rw [hc₂] at hne
    rw [h4, hc₂] at hcr
    exact coordinates_eq_of_cross_eq_zero
      (Pair.cross_eq_zero_trans hne (by rw [Pair.cross_def, double_x, double_z]; decide) hcr)
  have h₈ : (8 : ℕ) • baseSeven = 0 := by
    obtain ⟨-, hcr⟩ := double_coordinates hD hND ((4 : ℕ) • baseSeven)
    have h8 : (4 : ℕ) • baseSeven + (4 : ℕ) • baseSeven = (8 : ℕ) • baseSeven := by
      rw [← add_nsmul]
    have hdbl : double (2 : ZMod 7) 4 ⟨0, 1⟩ = ⟨4, 0⟩ := by
      ext <;> simp only [double_x, double_z] <;> decide
    rw [h8, hc₄, hdbl, Pair.cross_def] at hcr
    simp only [mul_zero, sub_zero, mul_eq_zero, hD, false_or] at hcr
    exact (coordinates_z_eq_zero_iff one_ne_zero).mp hcr
  have hc₅ : coordinates 0 1 ((5 : ℕ) • baseSeven) = ⟨5, 1⟩ := by
    have hsum : (5 : ℕ) • baseSeven + (3 : ℕ) • baseSeven = 0 := by
      rw [← add_nsmul]; exact h₈
    rw [eq_neg_of_add_eq_zero_left hsum, coordinates_neg, hc₃]
  have hc₆ : coordinates 0 1 ((6 : ℕ) • baseSeven) = ⟨1, 1⟩ := by
    have hsum : (6 : ℕ) • baseSeven + (2 : ℕ) • baseSeven = 0 := by
      rw [← add_nsmul]; exact h₈
    rw [eq_neg_of_add_eq_zero_left hsum, coordinates_neg, hc₂]
  have hc₇ : coordinates 0 1 ((7 : ℕ) • baseSeven) = ⟨3, 1⟩ := by
    have hsum : (7 : ℕ) • baseSeven + (1 : ℕ) • baseSeven = 0 := by
      rw [← add_nsmul]; exact h₈
    rw [eq_neg_of_add_eq_zero_left hsum, coordinates_neg, one_nsmul, hc₁]
  refine ⟨by rw [one_nsmul, hc₁], hc₂, hc₃, hc₄, hc₅, hc₆, hc₇,
    by rw [h₈, coordinates_zero], hne₃, ?_⟩
  rwa [← hc₃]

-- For `T₀ = (0, 0)` over `𝔽₇` at `k = 0`, `[1]T₀ + [0]T₀ = T₀ ≠ 0`, whereas `diffAdd` of the
-- coordinate pairs of `[1]T₀`, `[0]T₀` and `T₀` is `(0, 0)`.
example :
    let T₀ := twoTorsionPoint (0 : ZMod 7) one_ne_zero
    (1 : ℕ) • T₀ + (0 : ℕ) • T₀ = T₀ ∧
    T₀ ≠ 0 ∧
    diffAdd (coordinates 0 1 ((1 : ℕ) • T₀)) (coordinates 0 1 ((0 : ℕ) • T₀))
      (coordinates 0 1 T₀) = 0 := by
  refine ⟨by simp, twoTorsionPoint_ne_zero 0 one_ne_zero, ?_⟩
  simp

private theorem nonsingular_two_zero_five :
    (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private theorem nonsingular_one_three_seven :
    (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private theorem nonsingular_one_four_seven :
    (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 4 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

-- Modulo `35`, `diffAdd` of `(21, 25)`, `(22, 1)`, `(22, 1)` is `(1, 8)` with `gcd(8, 35) = 1`,
-- whose reductions modulo `5` and `7` represent `[3](2, 0) = (2, 0)` over `𝔽₅` and
-- `[3](1, 3) = (1, 4)` over `𝔽₇`.
example :
    let R₃₅ := diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩
    let T₅ : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 nonsingular_two_zero_five
    let P₇ : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 nonsingular_one_three_seven
    R₃₅ = ⟨1, 8⟩ ∧
    Nat.gcd R₃₅.z.val 35 = 1 ∧
    (3 : ℕ) • T₅ = T₅ ∧
    (3 : ℕ) • P₇ = .some 1 4 nonsingular_one_four_seven ∧
    (R₃₅.map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
      (coordinates 0 1 ((3 : ℕ) • T₅)) = 0 ∧
    (R₃₅.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
      (coordinates 0 1 ((3 : ℕ) • P₇)) = 0 := by
  dsimp only
  have hR : diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ := by
    ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have hT₅ : (3 : ℕ) • (.some 2 0 nonsingular_two_zero_five :
      (model (0 : ZMod 5) 1).toAffine.Point) = .some 2 0 nonsingular_two_zero_five := by
    have h₂ : (2 : ℕ) • (.some 2 0 nonsingular_two_zero_five :
        (model (0 : ZMod 5) 1).toAffine.Point) = 0 := by
      rw [two_nsmul]
      exact Affine.Point.add_of_Y_eq rfl (by simp only [Affine.negY, model_a₁, model_a₃]; decide)
    rw [succ_nsmul, h₂, zero_add]
  have hP₇ : (3 : ℕ) • (.some 1 3 nonsingular_one_three_seven :
      (model (0 : ZMod 7) 1).toAffine.Point) = .some 1 4 nonsingular_one_four_seven := by
    let P₇ : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 nonsingular_one_three_seven
    have h₂ : (2 : ℕ) • P₇ = twoTorsionPoint 0 one_ne_zero := by
      rw [two_nsmul]
      exact (add_self_eq_twoTorsionPoint_iff one_ne_zero nonsingular_one_three_seven).mpr
        (by decide)
    have hsum : (3 : ℕ) • P₇ + (1 : ℕ) • P₇ = 0 := by
      have h4 : 3 + 1 = 2 + 2 := rfl
      rw [← add_nsmul, h4, add_nsmul, h₂, twoTorsionPoint_add_self]
    rw [eq_neg_of_add_eq_zero_left hsum, one_nsmul]
    simp only [P₇, Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
    decide
  refine ⟨hR, by rw [hR]; decide, hT₅, hP₇, ?_, ?_⟩
  · rw [hR, hT₅, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]
    decide
  · rw [hR, hP₇, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]
    decide

end Concrete

end TauCeti.Montgomery
