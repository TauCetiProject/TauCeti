/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates
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

The point `Q = (3, 3)` on `y² = x³ + x` over `𝔽₇` has order `8`, with multiples `[1..8] Q` having
coordinate pairs `(3, 1)`, `(1, 1)`, `(5, 1)`, `(0, 1)`, `(5, 1)`, `(1, 1)`, `(3, 1)` and `(1, 0)`.
The cross-difference criterion matches `(m, n) = (5, 3)` (cross difference `0`, `[8] Q = 0`),
`(m, n) = (3, 1)` (cross difference `2 ≠ 0`, neither `[2] Q` nor `[4] Q` vanishes), and
`m = n = 0`; with step `w = 6`, `q = 7 = 6 + 1` does not annihilate `Q` (`[7] Q = -Q`), while
`q = 8 = 6 + 2` annihilates `Q` and `[6] Q = (1, 3)` and `[2] Q = (1, 4)` have vanishing cross
difference. The finite arithmetic is verified by kernel reduction.
-/

public section

namespace TauCeti.Montgomery

section Seven

local instance fibresPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Coordinate pairs -/

private theorem nonsingular_one_three : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
  simp only [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
    model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
  decide

private theorem nonsingular_one_four : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 4 := by
  simp only [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
    model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
  decide

-- Infinity, the distinguished point `(0, 0)` and the point `(1, 3)` have coordinate pairs
-- `(1, 0)`, `(0, 1)` and `(1, 1)`.
example : coordinates (0 : ZMod 7) 1 0 = ⟨1, 0⟩ ∧
    coordinates (0 : ZMod 7) 1 (twoTorsionPoint 0 one_ne_zero) = ⟨0, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 (.some 1 3 nonsingular_one_three) = ⟨1, 1⟩ :=
  ⟨coordinates_zero .., coordinates_twoTorsionPoint _, coordinates_some ..⟩

-- The point `(1, 4)` is the negative of `(1, 3)` and has the same coordinate pair `(1, 1)`.
example : WeierstrassCurve.Affine.Point.some 1 4 nonsingular_one_four =
      -.some 1 3 nonsingular_one_three ∧
    coordinates (0 : ZMod 7) 1 (.some 1 4 nonsingular_one_four) = ⟨1, 1⟩ := by
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

/-! ### Scalar multiples and the stage-2 cross-difference criterion -/

private noncomputable def ptSeven (x y : ZMod 7) (h : y ^ 2 = x ^ 3 + x := by decide) : E :=
  .some x y <| by
    have : (model (0 : ZMod 7) 1).IsElliptic :=
      isElliptic_model_iff_ne_zero.mpr ⟨by decide, one_ne_zero, by decide⟩
    exact (model (0 : ZMod 7) 1).toAffine.equation_iff_nonsingular.mp <| by
      simpa [Affine.equation_iff] using h

private noncomputable def genSeven : E := ptSeven 3 3

private theorem two_nsmul_genSeven : (2 : ℕ) • genSeven = ptSeven 1 4 := by
  have hy : (3 : ZMod 7) ≠ (model (0 : ZMod 7) 1).toAffine.negY 3 3 := by
    simp only [Affine.negY, model_a₁, model_a₃]
    decide
  have hs : (model (0 : ZMod 7) 1).toAffine.slope 3 3 3 3 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy]
    simp only [Affine.negY, model_a₁, model_a₂, model_a₃, model_a₄]
    rw [div_eq_iff (by decide)]
    decide
  rw [two_nsmul, genSeven, ptSeven, ptSeven, Affine.Point.add_self_of_Y_ne hy]
  simp only [Affine.Point.some.injEq, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY,
    hs, model_a₁, model_a₂, model_a₃]
  decide

private theorem three_nsmul_genSeven : (3 : ℕ) • genSeven = ptSeven 5 5 := by
  have hx : (1 : ZMod 7) ≠ 3 := by decide
  have hs : (model (0 : ZMod 7) 1).toAffine.slope 1 3 4 3 = 3 := by
    rw [Affine.slope_of_X_ne hx, div_eq_iff (by decide)]
    decide
  rw [succ_nsmul, two_nsmul_genSeven, genSeven, ptSeven, ptSeven, ptSeven,
    Affine.Point.add_of_X_ne hx]
  simp only [Affine.Point.some.injEq, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY,
    hs, model_a₁, model_a₂, model_a₃]
  decide

private theorem four_nsmul_genSeven : (4 : ℕ) • genSeven = twoTorsionPoint 0 one_ne_zero := by
  have h4 : (4 : ℕ) = 2 + 2 := rfl
  rw [h4, add_nsmul, two_nsmul_genSeven, ptSeven]
  exact (add_self_eq_twoTorsionPoint_iff one_ne_zero _).mpr (by decide)

private theorem eight_nsmul_genSeven : (8 : ℕ) • genSeven = 0 := by
  have h8 : (8 : ℕ) = 4 + 4 := rfl
  rw [h8, add_nsmul, four_nsmul_genSeven, twoTorsionPoint_add_self]

private theorem five_nsmul_genSeven : (5 : ℕ) • genSeven = ptSeven 5 2 := by
  have h : (5 : ℕ) • genSeven = -((3 : ℕ) • genSeven) :=
    eq_neg_of_add_eq_zero_left (by rw [← add_nsmul]; exact eight_nsmul_genSeven)
  rw [h, three_nsmul_genSeven, ptSeven, ptSeven, Affine.Point.neg_some]
  simp only [Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
  decide

private theorem six_nsmul_genSeven : (6 : ℕ) • genSeven = ptSeven 1 3 := by
  have h : (6 : ℕ) • genSeven = -((2 : ℕ) • genSeven) :=
    eq_neg_of_add_eq_zero_left (by rw [← add_nsmul]; exact eight_nsmul_genSeven)
  rw [h, two_nsmul_genSeven, ptSeven, ptSeven, Affine.Point.neg_some]
  simp only [Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
  decide

private theorem seven_nsmul_genSeven : (7 : ℕ) • genSeven = -genSeven :=
  eq_neg_of_add_eq_zero_left (by rw [← succ_nsmul]; exact eight_nsmul_genSeven)

-- The multiples `[1..8] Q` of `Q = (3, 3)` have coordinate pairs
-- `(3, 1), (1, 1), (5, 1), (0, 1), (5, 1), (1, 1), (3, 1), (1, 0)`.
example :
    coordinates (0 : ZMod 7) 1 ((1 : ℕ) • genSeven) = ⟨3, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((2 : ℕ) • genSeven) = ⟨1, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((3 : ℕ) • genSeven) = ⟨5, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((4 : ℕ) • genSeven) = ⟨0, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((5 : ℕ) • genSeven) = ⟨5, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((6 : ℕ) • genSeven) = ⟨1, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((7 : ℕ) • genSeven) = ⟨3, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((8 : ℕ) • genSeven) = ⟨1, 0⟩ := by
  rw [one_nsmul, two_nsmul_genSeven, three_nsmul_genSeven, four_nsmul_genSeven,
    five_nsmul_genSeven, six_nsmul_genSeven, seven_nsmul_genSeven, eight_nsmul_genSeven]
  simp only [coordinates_neg, genSeven, ptSeven, coordinates_some, coordinates_twoTorsionPoint,
    coordinates_zero, and_self]

-- For `(m, n) = (5, 3)`, both `[5] Q` and `[3] Q` have coordinate pair `(5, 1)`, their cross
-- difference vanishes, and `[5 + 3] Q = [8] Q = 0`.
example :
    coordinates (0 : ZMod 7) 1 ((5 : ℤ) • genSeven) = ⟨5, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((3 : ℤ) • genSeven) = ⟨5, 1⟩ ∧
    (coordinates (0 : ZMod 7) 1 ((5 : ℤ) • genSeven)).cross
      (coordinates (0 : ZMod 7) 1 ((3 : ℤ) • genSeven)) = 0 ∧
    ((5 : ℤ) + 3) • genSeven = 0 := by
  have h5 : (5 : ℤ) • genSeven = ptSeven 5 2 :=
    (natCast_zsmul genSeven 5).trans five_nsmul_genSeven
  have h3 : (3 : ℤ) • genSeven = ptSeven 5 5 :=
    (natCast_zsmul genSeven 3).trans three_nsmul_genSeven
  have h8 : ((5 : ℤ) + 3) • genSeven = 0 := by
    norm_num only
    exact (natCast_zsmul genSeven 8).trans eight_nsmul_genSeven
  refine ⟨?_, ?_, (cross_coordinates_zsmul_eq_zero_iff one_ne_zero).mpr (.inr h8), h8⟩
  · rw [h5, ptSeven, coordinates_some]
  · rw [h3, ptSeven, coordinates_some]

-- For `(m, n) = (3, 1)`, the coordinate pairs are `(5, 1)` and `(3, 1)` with cross difference
-- `5 - 3 = 2 ≠ 0`, so neither `[3 - 1] Q` nor `[3 + 1] Q` vanishes.
example :
    coordinates (0 : ZMod 7) 1 ((3 : ℤ) • genSeven) = ⟨5, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 ((1 : ℤ) • genSeven) = ⟨3, 1⟩ ∧
    (coordinates (0 : ZMod 7) 1 ((3 : ℤ) • genSeven)).cross
      (coordinates (0 : ZMod 7) 1 ((1 : ℤ) • genSeven)) ≠ 0 ∧
    ((3 : ℤ) - 1) • genSeven ≠ 0 ∧ ((3 : ℤ) + 1) • genSeven ≠ 0 := by
  have h3p : (3 : ℤ) • genSeven = ptSeven 5 5 :=
    (natCast_zsmul genSeven 3).trans three_nsmul_genSeven
  have h3 : coordinates (0 : ZMod 7) 1 ((3 : ℤ) • genSeven) = ⟨5, 1⟩ := by
    rw [h3p, ptSeven, coordinates_some]
  have h1 : coordinates (0 : ZMod 7) 1 ((1 : ℤ) • genSeven) = ⟨3, 1⟩ := by
    rw [one_zsmul, genSeven, ptSeven, coordinates_some]
  have hcross : (coordinates (0 : ZMod 7) 1 ((3 : ℤ) • genSeven)).cross
      (coordinates (0 : ZMod 7) 1 ((1 : ℤ) • genSeven)) ≠ 0 := by
    rw [h3, h1, Pair.cross_def]
    decide
  exact ⟨h3, h1, hcross,
    not_or.mp ((cross_coordinates_zsmul_eq_zero_iff one_ne_zero).not.mp hcross)⟩

-- At `m = n = 0`, both pairs are `(1, 0)` with cross difference `1 · 0 - 1 · 0 = 0`, matching
-- `[0 - 0] P = 0` on both sides of `cross_coordinates_zsmul_eq_zero_iff`.
example (P : E) :
    (coordinates (0 : ZMod 7) 1 ((0 : ℤ) • P)).cross
      (coordinates (0 : ZMod 7) 1 ((0 : ℤ) • P)) = 0 ∧
    ((0 : ℤ) - 0) • P = 0 :=
  ⟨(cross_coordinates_zsmul_eq_zero_iff one_ne_zero).mpr (.inl (by simp)), by simp⟩

-- With step `w = 6` and `q = 7 = 1 · 6 + 1`, `[7] Q = -Q ≠ 0` and the pairs of `[6] Q` and
-- `[1] Q` have nonzero cross difference.
example :
    (7 : ℤ) = 1 * 6 + 1 ∧
    (7 : ℤ) • genSeven = -genSeven ∧
    (7 : ℤ) • genSeven ≠ 0 ∧
    (coordinates (0 : ZMod 7) 1 ((1 * 6 : ℤ) • genSeven)).cross
      (coordinates (0 : ZMod 7) 1 ((1 : ℤ) • genSeven)) ≠ 0 := by
  have h7 : (7 : ℤ) • genSeven = -genSeven :=
    (natCast_zsmul genSeven 7).trans seven_nsmul_genSeven
  have h6 : (6 : ℤ) • genSeven = ptSeven 1 3 :=
    (natCast_zsmul genSeven 6).trans six_nsmul_genSeven
  refine ⟨by decide, h7, ?_, ?_⟩
  · rw [h7, neg_ne_zero, genSeven, ptSeven]
    exact Affine.Point.some_ne_zero _
  · rw [one_mul, h6, one_zsmul, genSeven, ptSeven, ptSeven, coordinates_some, coordinates_some,
      Pair.cross_def]
    decide

-- With step `w = 6` and `q = 8 = 1 · 6 + 2`, `[8] Q = 0`, `[6] Q = (1, 3)` and `[2] Q = (1, 4)`
-- both have coordinate pair `(1, 1)` and vanishing cross difference `1 · 1 - 1 · 1 = 0`.
example :
    (8 : ℤ) = 1 * 6 + 2 ∧
    (8 : ℤ) • genSeven = 0 ∧
    (6 : ℤ) • genSeven = .some 1 3 nonsingular_one_three ∧
    (2 : ℤ) • genSeven = .some 1 4 nonsingular_one_four ∧
    (coordinates (0 : ZMod 7) 1 ((1 * 6 : ℤ) • genSeven)).cross
      (coordinates (0 : ZMod 7) 1 ((2 : ℤ) • genSeven)) = 0 := by
  have h8 : (8 : ℤ) • genSeven = 0 :=
    (natCast_zsmul genSeven 8).trans eight_nsmul_genSeven
  have h6 : (6 : ℤ) • genSeven = ptSeven 1 3 :=
    (natCast_zsmul genSeven 6).trans six_nsmul_genSeven
  have h2 : (2 : ℤ) • genSeven = ptSeven 1 4 :=
    (natCast_zsmul genSeven 2).trans two_nsmul_genSeven
  refine ⟨by decide, h8, ?_, ?_,
    cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero h8 (.inl (by decide))⟩
  · rw [h6, ptSeven]
  · rw [h2, ptSeven]

-- The stage-2 criterion applies directly to `[8] Q = 0` with step `w = 6`.
example : ∃ i : ℤ, 2 * |(8 : ℤ) - i * 6| ≤ 6 ∧
    (coordinates (0 : ZMod 7) 1 ((i * 6) • genSeven)).cross
      (coordinates (0 : ZMod 7) 1 (|(8 : ℤ) - i * 6| • genSeven)) = 0 :=
  exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero
    ((natCast_zsmul genSeven 8).trans eight_nsmul_genSeven) (by decide)

end Seven

end TauCeti.Montgomery
