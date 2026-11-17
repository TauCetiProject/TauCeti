/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates
import TauCeti.Examples.AlgebraicGeometry.EllipticCurve.Montgomery.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Set.Card

/-!
# Examples of coordinate pairs and of the image and fibres of the projective `x`-coordinate

On the curve `y² = x³ + x` over `𝔽₇`, the model with `(A, B) = (0, 1)`, the coordinate pair of
infinity is `(1, 0)`, that of the distinguished point of order two `(0, 0)` is `(0, 1)`, and the
points `(1, 3)` and `(1, 4) = -(1, 3)` both have coordinate pair `(1, 1)`. On `model 0 2`, the
monic model of `2 y² = x³ + x`, the point `(2, 4)` has coordinate pair `(2, B) = (2, 2)`, which
represents its Montgomery coordinate `x = 2 / 2 = 1`; the pair `(2, 1)` would represent the
Weierstrass coordinate `2` instead.

On the curve `y² = x³ + x` over `𝔽₇`, the model with `(A, B) = (0, 1)`, the point `(1 : 1)` of
the projective line is the projective `x`-coordinate of a native point, since `1³ + 1 = 2 = 3²`,
while `(2 : 1)` is not, since `2³ + 2 = 3` is not a square modulo `7`: the projective
`x`-coordinate is not surjective.

The image consists of `(1 : 0)`, `(0 : 1)`, `(1 : 1)`, `(3 : 1)` and `(5 : 1)`.
Only infinity and the distinguished point `(0, 0)` have singleton fibres. Each of the other
three fibres has two native points, exchanged by negation.

On the same curve, `Q = (3, 3)` has additive order `8`, with `[1..8]Q` having `x`-coordinates
`3, 1, 5, 0, 5, 1, 3, ∞`. Comparing `[5]Q` and `[3]Q` gives vanishing cross difference because
`[5 + 3]Q = [8]Q = 0`, whereas `[3]Q` and `[1]Q` have distinct `x`-coordinates `5` and `3` and
neither `[2]Q` nor `[4]Q` vanishes; the same equivalences hold on arbitrary nonzero scaled
representatives. With giant-step width `w = 6`, `q = 8 = 6 + 2` makes the cross difference of
`[6]Q = (1, 3)` and `[2]Q = (1, 4)` vanish while `q = 7 = 6 + 1` satisfies `[7]Q = -Q ≠ 0`, and
the nearest-multiple bound `2 j ≤ w` covers `13 = 2 · 6 + 1`, `17 = 3 · 6 - 1`, and the midpoint
`15 = 2 · 6 + 3` that a strict inequality `2 j < w` would miss.
-/

public section

namespace TauCeti.Montgomery

open TauCeti.Examples.Montgomery

section Seven

local instance fibresPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Coordinate pairs -/

-- Infinity, the distinguished point `(0, 0)` and the point `(1, 3)` have coordinate pairs
-- `(1, 0)`, `(0, 1)` and `(1, 1)`.
example : coordinates (0 : ZMod 7) 1 0 = ⟨1, 0⟩ ∧
    coordinates (0 : ZMod 7) 1 (twoTorsionPoint 0 one_ne_zero) = ⟨0, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 (.some 1 3 nonsingular_one_three_seven) = ⟨1, 1⟩ :=
  ⟨coordinates_zero .., coordinates_twoTorsionPoint _, coordinates_some ..⟩

-- The point `(1, 4)` is the negative of `(1, 3)` and has the same coordinate pair `(1, 1)`.
example : WeierstrassCurve.Affine.Point.some 1 4 nonsingular_one_four_seven =
      -.some 1 3 nonsingular_one_three_seven ∧
    coordinates (0 : ZMod 7) 1 (.some 1 4 nonsingular_one_four_seven) = ⟨1, 1⟩ := by
  refine ⟨?_, coordinates_some ..⟩
  simp only [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.negY, model_a₁,
    model_a₃, WeierstrassCurve.Affine.Point.some.injEq]
  decide

private theorem nonsingular_two_four : (model (0 : ZMod 7) 2).toAffine.Nonsingular 2 4 := by
  simp only [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
    model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
  decide

-- On `model 0 2`, the point `(2, 4)` has coordinate pair `(2, 2)`, representing the Montgomery
-- coordinate `1`; the pair `(2, 1)` does not represent `1`.
example : coordinates (0 : ZMod 7) 2 (.some 2 4 nonsingular_two_four) = ⟨2, 2⟩ ∧
    (coordinates (0 : ZMod 7) 2 (.some 2 4 nonsingular_two_four)).cross ⟨1, 1⟩ = 0 ∧
    (⟨2, 1⟩ : Pair (ZMod 7)).cross ⟨1, 1⟩ ≠ 0 := by
  simp only [coordinates_some, Pair.cross_def, true_and]
  decide

/-! ### The image of the projective `x`-coordinate -/

-- `(1 : 1)` lifts: `1³ + 0 · 1² + 1 = 2 = 3 · 3` in `𝔽₇`.
example : Pair.toProj ⟨(1 : ZMod 7), 1⟩ (Pair.ne_zero_iff.mpr (.inr one_ne_zero)) ∈
    Set.range (projectiveX 0 (one_ne_zero : (1 : ZMod 7) ≠ 0)) := by
  have : (model (0 : ZMod 7) 1).IsElliptic :=
    isElliptic_model_iff_ne_zero.mpr ⟨by decide, by decide, by decide⟩
  rw [toProj_mem_range_projectiveX_iff, div_one]
  exact ⟨3, by decide⟩

-- `(2 : 1)` does not lift: `2³ + 0 · 2² + 2 = 3` is not a square in `𝔽₇`.
example : Pair.toProj ⟨(2 : ZMod 7), 1⟩ (Pair.ne_zero_iff.mpr (.inr one_ne_zero)) ∉
    Set.range (projectiveX 0 (one_ne_zero : (1 : ZMod 7) ≠ 0)) := by
  have : (model (0 : ZMod 7) 1).IsElliptic :=
    isElliptic_model_iff_ne_zero.mpr ⟨by decide, by decide, by decide⟩
  rw [toProj_mem_range_projectiveX_iff, div_one]
  rintro ⟨t, ht⟩
  revert t
  decide

open WeierstrassCurve

private abbrev E := (model (0 : ZMod 7) 1).toAffine.Point

private noncomputable def affineX (x : ZMod 7) :=
  Pair.toProj ⟨x, 1⟩ (Pair.ne_zero_iff.mpr (.inr one_ne_zero))

private theorem equation_seven {x y : ZMod 7}
    (h : (model (0 : ZMod 7) 1).toAffine.Nonsingular x y) : y ^ 2 = x ^ 3 + x := by
  simpa [Affine.equation_iff] using h.1

private theorem range_projectiveX_seven :
    Set.range (projectiveX 0 (one_ne_zero : (1 : ZMod 7) ≠ 0)) =
      {projectiveX 0 one_ne_zero (0 : E), affineX 0, affineX 1, affineX 3, affineX 5} := by
  ext L
  constructor
  · rintro ⟨P, rfl⟩
    rcases P with _ | ⟨x, y, h⟩
    · simp [← Affine.Point.zero_def]
    · have hx : x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 5 := by
        have check : ∀ x y : ZMod 7, y ^ 2 = x ^ 3 + x →
            x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 5 := by decide
        exact check x y (equation_seven h)
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [projectiveX_def, coordinates_some, affineX]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    all_goals
      have : (model (0 : ZMod 7) 1).IsElliptic :=
        isElliptic_model_iff_ne_zero.mpr ⟨by decide, one_ne_zero, by decide⟩
      simp only [affineX, toProj_mem_range_projectiveX_iff, zero_mul, div_one]
    · exact ⟨0, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨2, by decide⟩

-- The native points of `y² = x³ + x` over `𝔽₇` have five projective `x`-coordinates.
example :
    (Set.range (projectiveX 0 (one_ne_zero : (1 : ZMod 7) ≠ 0))).ncard = 5 := by
  rw [range_projectiveX_seven]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
  all_goals norm_num [projectiveX_def, affineX, Pair.toProj_eq_toProj_iff, Pair.cross_def]
  all_goals decide

private theorem eq_neg_iff_seven (P : E) :
    P = -P ↔ P = 0 ∨ P = twoTorsionPoint 0 (one_ne_zero : (1 : ZMod 7) ≠ 0) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  · have check : ∀ x y : ZMod 7, y ^ 2 = x ^ 3 + x → (y = -y ↔ x = 0) := by
      decide
    simpa [Affine.Point.neg_some, Affine.negY, Affine.Point.some_ne_zero,
      some_eq_twoTorsionPoint_iff one_ne_zero h] using check x y (equation_seven h)

-- The singleton fibres are exactly infinity and the distinguished point of order two;
-- every other point belongs to a two-element fibre.
example (P : E) :
    {Q : E | projectiveX 0 (one_ne_zero : (1 : ZMod 7) ≠ 0) Q =
      projectiveX 0 one_ne_zero P}.ncard =
      if P = 0 ∨ P = twoTorsionPoint 0 one_ne_zero then 1 else 2 := by
  have hfibre : {Q : E | projectiveX 0 (one_ne_zero : (1 : ZMod 7) ≠ 0) Q =
      projectiveX 0 one_ne_zero P} = {P, -P} := by
    ext Q
    simp [projectiveX_eq_projectiveX_iff]
  rw [hfibre]
  by_cases h : P = -P
  · simp [← h, ← eq_neg_iff_seven]
  · simp [Set.ncard_pair h, ← eq_neg_iff_seven, h]

/-! ### Cross differences of scalar multiples and giant/baby steps -/

private theorem eight_genSeven : (8 : ℕ) • generatorSeven = 0 := by
  rw [← addOrderOf_generatorSeven, addOrderOf_nsmul_eq_zero]

private theorem five_genSeven :
    (5 : ℕ) • generatorSeven = -Affine.Point.some 5 5 nonsingular_five_five_seven := by
  apply eq_neg_of_add_eq_zero_left
  rw [← three_nsmul_generatorSeven, ← add_nsmul]
  exact eight_genSeven

private theorem six_genSeven :
    (6 : ℕ) • generatorSeven = .some 1 3 nonsingular_one_three_seven := by
  have hneg : -Affine.Point.some 1 4 nonsingular_one_four_seven =
      .some 1 3 nonsingular_one_three_seven := by
    simp only [Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
    decide
  rw [← hneg]
  apply eq_neg_of_add_eq_zero_left
  rw [← two_nsmul_generatorSeven, ← add_nsmul]
  exact eight_genSeven

private theorem seven_genSeven : (7 : ℕ) • generatorSeven = -generatorSeven := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [succ_nsmul] using eight_genSeven

-- The multiples `[1..8]Q` of `Q = (3, 3)` have coordinate pairs with `x`-coordinates
-- `3, 1, 5, 0, 5, 1, 3, ∞`, and `Q` has order `8`.
example : addOrderOf generatorSeven = 8 ∧
    coordinates 0 1 ((1 : ℕ) • generatorSeven) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((2 : ℕ) • generatorSeven) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((3 : ℕ) • generatorSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((4 : ℕ) • generatorSeven) = ⟨0, 1⟩ ∧
    coordinates 0 1 ((5 : ℕ) • generatorSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((6 : ℕ) • generatorSeven) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((7 : ℕ) • generatorSeven) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((8 : ℕ) • generatorSeven) = ⟨1, 0⟩ := by
  refine ⟨addOrderOf_generatorSeven, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [one_nsmul, generatorSeven_def, coordinates_some]
  · rw [two_nsmul_generatorSeven, coordinates_some]
  · rw [three_nsmul_generatorSeven, coordinates_some]
  · rw [four_nsmul_generatorSeven, coordinates_twoTorsionPoint]
  · rw [five_genSeven, coordinates_neg, coordinates_some]
  · rw [six_genSeven, coordinates_some]
  · rw [seven_genSeven, coordinates_neg, generatorSeven_def, coordinates_some]
  · rw [eight_genSeven, coordinates_zero]

-- `(m, n) = (5, 3)`: `[5]Q` and `[3]Q` share coordinate pair `(5, 1)` since `[5 + 3]Q = [8]Q = 0`.
example : (coordinates 0 1 ((5 : ℤ) • generatorSeven)).cross
    (coordinates 0 1 ((3 : ℤ) • generatorSeven)) = 0 := by
  have h8 : ((5 : ℤ) + 3) • generatorSeven = 0 := by
    have h8z : ((5 : ℤ) + 3) = (8 : ℕ) := rfl
    rw [h8z, natCast_zsmul, eight_genSeven]
  exact (cross_coordinates_zsmul_eq_zero_iff (one_ne_zero : (1 : ZMod 7) ≠ 0)).mpr (.inr h8)

-- `(m, n) = (3, 1)`: scaled representatives `(3, 2)` of `[3]Q` (`3 ≡ 2 · 5`) and `(2, 3)` of
-- `[1]Q` (`2 ≡ 3 · 3`) have nonvanishing cross difference, equivalent via
-- `cross_eq_zero_iff_zsmul_eq_zero_of_cross_coordinates_eq_zero` to `[2]Q ≠ 0 ∧ [4]Q ≠ 0`.
example : (⟨3, 2⟩ : Pair (ZMod 7)).cross ⟨2, 3⟩ ≠ 0 ∧
    (2 : ℤ) • generatorSeven ≠ 0 ∧ (4 : ℤ) • generatorSeven ≠ 0 := by
  have h3 : (⟨3, 2⟩ : Pair (ZMod 7)).cross (coordinates 0 1 ((3 : ℤ) • generatorSeven)) = 0 := by
    have h3z : (3 : ℤ) = (3 : ℕ) := rfl
    rw [h3z, natCast_zsmul, three_nsmul_generatorSeven, coordinates_some, Pair.cross_def]
    decide
  have h1 : (⟨2, 3⟩ : Pair (ZMod 7)).cross (coordinates 0 1 ((1 : ℤ) • generatorSeven)) = 0 := by
    rw [one_zsmul, generatorSeven_def, coordinates_some, Pair.cross_def]
    decide
  have h2ne : (2 : ℤ) • generatorSeven ≠ 0 := by
    have h2z : (2 : ℤ) = (2 : ℕ) := rfl
    rw [h2z, natCast_zsmul, two_nsmul_generatorSeven]
    exact Affine.Point.some_ne_zero _
  have h4ne : (4 : ℤ) • generatorSeven ≠ 0 := by
    have h4z : (4 : ℤ) = (4 : ℕ) := rfl
    rw [h4z, natCast_zsmul, four_nsmul_generatorSeven]
    exact twoTorsionPoint_ne_zero 0 one_ne_zero
  refine ⟨?_, h2ne, h4ne⟩
  rw [Ne, cross_eq_zero_iff_zsmul_eq_zero_of_cross_coordinates_eq_zero
    (one_ne_zero : (1 : ZMod 7) ≠ 0) (Pair.ne_zero_iff.mpr (.inl (by decide)))
    (Pair.ne_zero_iff.mpr (.inl (by decide))) h3 h1]
  have hsub : ((3 : ℤ) - 1) = 2 := rfl
  have hadd : ((3 : ℤ) + 1) = 4 := rfl
  rw [hsub, hadd]
  exact not_or.mpr ⟨h2ne, h4ne⟩

-- `m = n = 0`: both coordinate pairs are `(1, 0)` with cross difference `0`, matching `[0]Q = 0`.
example : (coordinates 0 1 ((0 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((0 : ℤ) • generatorSeven)) = 0 ∧
    ((0 : ℤ) - 0) • generatorSeven = 0 ∧ ((0 : ℤ) + 0) • generatorSeven = 0 := by
  simp

-- With step `w = 6`: `q = 7 = 6 + 1` leaves `[7]Q = -Q ≠ 0`, while `q = 8 = 6 + 2` annihilates `Q`
-- and gives vanishing cross difference between `[6]Q = (1, 3)` and `[2]Q = (1, 4)`.
example : (7 : ℤ) • generatorSeven ≠ 0 ∧ (8 : ℤ) • generatorSeven = 0 ∧
    (coordinates 0 1 ((6 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((2 : ℤ) • generatorSeven)) = 0 := by
  have h8z : (8 : ℤ) • generatorSeven = 0 := by
    have h8 : (8 : ℤ) = (8 : ℕ) := rfl
    rw [h8, natCast_zsmul, eight_genSeven]
  refine ⟨?_, h8z, cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero h8z (.inl (by norm_num))⟩
  have h7 : (7 : ℤ) = (7 : ℕ) := rfl
  rw [h7, natCast_zsmul, seven_genSeven, neg_ne_zero, generatorSeven_def]
  exact Affine.Point.some_ne_zero _

-- For `w = 6`, `13 = 2 · 6 + 1`, `17 = 3 · 6 - 1`, and the midpoint `15 = 2 · 6 + 3` has no
-- representation `i · 6 ± j` with `0 ≤ j` and `2 · j < 6`.
example : (13 : ℤ) = 2 * 6 + 1 ∧ (17 : ℤ) = 3 * 6 - 1 ∧ (15 : ℤ) = 2 * 6 + 3 ∧
    ¬ ∃ i j : ℤ, 0 ≤ j ∧ 2 * j < 6 ∧ ((15 : ℤ) = i * 6 + j ∨ (15 : ℤ) = i * 6 - j) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨i, j, hj0, hj6, h | h⟩ <;> omega

end Seven

end TauCeti.Montgomery
