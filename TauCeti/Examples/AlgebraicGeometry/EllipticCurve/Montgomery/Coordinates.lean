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

Applied to scalar multiples of the generator `Q = (3, 3)` of order `8` over `𝔽₇`, the
cross-difference criterion `cross_coordinates_zsmul_eq_zero_iff` separates pairs `(m, n)` whose
sum or difference kills `Q` (such as `(5, 3)`, where both `[5]Q` and `[3]Q` have `x`-coordinate
`5` and `[8]Q = 0`) from pairs where neither `[m - n]Q` nor `[m + n]Q` vanishes (such as
`(3, 1)`, where `[2]Q ≠ 0` and `[4]Q ≠ 0`). With step `w = 6`, writing `q = i w ± j` with
`2 j ≤ w` handles midpoint remainders such as `15 = 2 · 6 + 3` that a strict bound `2 j < w`
would miss, has `j = 0` only when `6 ∣ q`, and gives vanishing cross difference between `[6]Q`
and `[2]Q` for `q = 8 = 6 + 2` while `[7]Q = -Q ≠ 0` leaves `[6]Q` and `[1]Q` distinct
projectively.
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

private theorem two_zsmul_some_three_three
    (h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3) :
    (2 : ℤ) • (Affine.Point.some 3 3 h : E) = .some 1 4 nonsingular_one_four := by
  have hY : (3 : ZMod 7) ≠ (model (0 : ZMod 7) 1).toAffine.negY 3 3 := by
    simp only [Affine.negY, model_a₁, model_a₃]
    decide
  have hslope : (model (0 : ZMod 7) 1).toAffine.slope 3 3 3 3 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hY]
    simp only [Affine.negY, model_a₁, model_a₂, model_a₃, model_a₄]
    exact (div_eq_iff (by decide)).mpr (by decide)
  rw [two_zsmul, Affine.Point.add_self_of_Y_ne hY, Affine.Point.some.injEq, hslope]
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, model_a₁, model_a₂, model_a₃]
  decide

private theorem four_zsmul_some_three_three
    (h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3) :
    (4 : ℤ) • (Affine.Point.some 3 3 h : E) = twoTorsionPoint 0 one_ne_zero := by
  have h4 : (4 : ℤ) = 2 + 2 := rfl
  rw [h4, add_zsmul, two_zsmul_some_three_three h]
  exact (add_self_eq_twoTorsionPoint_iff one_ne_zero nonsingular_one_four).mpr (by decide)

private theorem eight_zsmul_some_three_three
    (h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3) :
    (8 : ℤ) • (Affine.Point.some 3 3 h : E) = 0 := by
  have h8 : (8 : ℤ) = 4 + 4 := rfl
  rw [h8, add_zsmul, four_zsmul_some_three_three h, twoTorsionPoint_add_self]

private theorem coordinates_three_zsmul_some_three_three
    (h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3) :
    coordinates (0 : ZMod 7) 1 ((3 : ℤ) • .some 3 3 h) = ⟨5, 1⟩ := by
  have h3 : (3 : ℤ) = 2 + 1 := rfl
  have hX : (1 : ZMod 7) ≠ 3 := by decide
  have hslope : (model (0 : ZMod 7) 1).toAffine.slope 1 3 4 3 = 3 := by
    rw [Affine.slope_of_X_ne hX]
    exact (div_eq_iff (by decide)).mpr (by decide)
  rw [h3, add_zsmul, one_zsmul, two_zsmul_some_three_three h,
    Affine.Point.add_of_X_ne hX, coordinates_some, hslope]
  ext
  · simp only [Affine.addX, model_a₁, model_a₂]
    decide
  · rfl

-- Over `𝔽₇` with `Q = (3, 3)` of order `8`, `(m, n) = (5, 3)` gives `x([5]Q) = x([3]Q) = 5`,
-- vanishing cross difference, and `[5 + 3]Q = [8]Q = 0`.
example :
    let h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide
    let Q : E := .some 3 3 h
    coordinates 0 1 ((5 : ℤ) • Q) = ⟨5, 1⟩ ∧
      coordinates 0 1 ((3 : ℤ) • Q) = ⟨5, 1⟩ ∧
      (coordinates 0 1 ((5 : ℤ) • Q)).cross (coordinates 0 1 ((3 : ℤ) • Q)) = 0 ∧
      ((5 : ℤ) + 3) • Q = 0 := by
  intro h Q
  have h8 : ((5 : ℤ) + 3) • Q = 0 := eight_zsmul_some_three_three h
  have h5 : (5 : ℤ) • Q = -((3 : ℤ) • Q) :=
    eq_neg_of_add_eq_zero_left ((add_zsmul Q 5 3).symm.trans h8)
  have hc3 : coordinates 0 1 ((3 : ℤ) • Q) = ⟨5, 1⟩ :=
    coordinates_three_zsmul_some_three_three h
  have hc5 : coordinates 0 1 ((5 : ℤ) • Q) = ⟨5, 1⟩ := by
    rw [h5, coordinates_neg, hc3]
  exact ⟨hc5, hc3, (cross_coordinates_zsmul_eq_zero_iff one_ne_zero).mpr (.inr h8), h8⟩

-- For `(m, n) = (3, 1)`, the `x`-coordinates are `5` and `3`, the cross difference `5 - 3` is
-- nonzero, and neither `[2]Q` nor `[4]Q` vanishes.
example :
    let h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide
    let Q : E := .some 3 3 h
    coordinates 0 1 ((3 : ℤ) • Q) = ⟨5, 1⟩ ∧
      coordinates 0 1 ((1 : ℤ) • Q) = ⟨3, 1⟩ ∧
      (coordinates 0 1 ((3 : ℤ) • Q)).cross (coordinates 0 1 ((1 : ℤ) • Q)) = 5 - 3 ∧
      (5 - 3 : ZMod 7) ≠ 0 ∧
      ((3 : ℤ) - 1) • Q ≠ 0 ∧ ((3 : ℤ) + 1) • Q ≠ 0 := by
  intro h Q
  have hc3 : coordinates 0 1 ((3 : ℤ) • Q) = ⟨5, 1⟩ :=
    coordinates_three_zsmul_some_three_three h
  have hc1 : coordinates 0 1 ((1 : ℤ) • Q) = ⟨3, 1⟩ := by
    rw [one_zsmul, coordinates_some]
  have hcross :
      (coordinates 0 1 ((3 : ℤ) • Q)).cross (coordinates 0 1 ((1 : ℤ) • Q)) = 5 - 3 := by
    rw [hc3, hc1, Pair.cross_def, mul_one, mul_one]
  have hne : (5 - 3 : ZMod 7) ≠ 0 := by decide
  have hnot := not_or.mp
    ((cross_coordinates_zsmul_eq_zero_iff (A := (0 : ZMod 7)) one_ne_zero).not.mp
      (hcross.symm ▸ hne))
  exact ⟨hc3, hc1, hcross, hne, hnot.1, hnot.2⟩

-- With step `w = 6` and `q = 7 = 6 + 1`, `[7]Q = -Q ≠ 0`, and the coordinate pairs of `[6]Q`
-- and `[1]Q` have nonzero cross difference because neither `[5]Q` nor `[7]Q` vanishes.
example :
    let h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide
    let Q : E := .some 3 3 h
    (7 : ℤ) • Q = -Q ∧ (7 : ℤ) • Q ≠ 0 ∧
      (coordinates 0 1 ((6 : ℤ) • Q)).cross (coordinates 0 1 ((1 : ℤ) • Q)) ≠ 0 := by
  intro h Q
  have h8 : ((7 : ℤ) + 1) • Q = 0 := eight_zsmul_some_three_three h
  have h7 : (7 : ℤ) • Q = -Q :=
    eq_neg_of_add_eq_zero_left (((add_zsmul Q 7 1).trans (by rw [one_zsmul])).symm.trans h8)
  have h7ne : (7 : ℤ) • Q ≠ 0 := by
    rw [h7, neg_ne_zero]
    exact Affine.Point.some_ne_zero _
  have h6 : (6 : ℤ) • Q = -((2 : ℤ) • Q) :=
    eq_neg_of_add_eq_zero_left ((add_zsmul Q 6 2).symm.trans h8)
  refine ⟨h7, h7ne, ?_⟩
  have h2 : (2 : ℤ) • Q = .some 1 4 nonsingular_one_four := two_zsmul_some_three_three h
  rw [h6, h2, coordinates_neg, one_zsmul, coordinates_some, coordinates_some, Pair.cross_def]
  decide

-- With step `w = 6` and `q = 8 = 6 + 2`, `[8]Q = 0`, `[6]Q = (1, 3)` and `[2]Q = (1, 4)` both
-- have coordinate pair `(1, 1)` with cross difference `1 · 1 - 1 · 1 = 0`, and
-- `exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero` produces a witness.
example :
    let h : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide
    let Q : E := .some 3 3 h
    (8 : ℤ) • Q = 0 ∧
      (6 : ℤ) • Q = .some 1 3 nonsingular_one_three ∧
      (2 : ℤ) • Q = .some 1 4 nonsingular_one_four ∧
      (coordinates 0 1 ((6 : ℤ) • Q)).cross (coordinates 0 1 ((2 : ℤ) • Q)) = 1 * 1 - 1 * 1 ∧
      (coordinates 0 1 ((6 : ℤ) • Q)).cross (coordinates 0 1 ((2 : ℤ) • Q)) = 0 ∧
      ∃ i : ℤ, 2 * |(8 : ℤ) - i * 6| ≤ 6 ∧
        (coordinates 0 1 ((i * 6) • Q)).cross
          (coordinates 0 1 (|(8 : ℤ) - i * 6| • Q)) = 0 := by
  intro h Q
  have h8 : (8 : ℤ) • Q = 0 := eight_zsmul_some_three_three h
  have h2 : (2 : ℤ) • Q = .some 1 4 nonsingular_one_four := two_zsmul_some_three_three h
  have h6 : (6 : ℤ) • Q = .some 1 3 nonsingular_one_three := by
    have hneg : (6 : ℤ) • Q = -((2 : ℤ) • Q) :=
      eq_neg_of_add_eq_zero_left ((add_zsmul Q 6 2).symm.trans h8)
    rw [hneg, h2]
    simp only [Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
    decide
  refine ⟨h8, h6, h2, ?_,
    cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero h8 (.inl rfl),
    exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero h8 (by norm_num)⟩
  rw [h6, h2, coordinates_some, coordinates_some, Pair.cross_def]

end Seven

-- At `m = n = 0`, both multiples are infinity `(1, 0)` with cross difference `1 · 0 - 1 · 0 = 0`
-- and `[0]Q = 0`, consistent with both sides of `cross_coordinates_zsmul_eq_zero_iff`.
example {K : Type*} [Field K] [DecidableEq K] {A B : K} (hB : B ≠ 0)
    (Q : (model A B).toAffine.Point) :
    (coordinates A B ((0 : ℤ) • Q)).cross (coordinates A B ((0 : ℤ) • Q)) = 1 * 0 - 1 * 0 ∧
      ((0 : ℤ) - 0) • Q = 0 ∧
      (coordinates A B ((0 : ℤ) • Q)).cross (coordinates A B ((0 : ℤ) • Q)) = 0 := by
  refine ⟨by simp, by simp, ?_⟩
  exact (cross_coordinates_zsmul_eq_zero_iff hB).mpr (.inl (by simp))

-- With step `w = 6`, `13 = 2 · 6 + 1` and `17 = 3 · 6 - 1` have strict remainder `2 j < 6`,
-- whereas `15 = 2 · 6 + 3` requires the non-strict midpoint bound `2 j ≤ 6`, and `j = 0` occurs
-- within `2 j ≤ 6` exactly when `6 ∣ q`.
example :
    (13 : ℤ) = 2 * 6 + 1 ∧ (17 : ℤ) = 3 * 6 - 1 ∧ (15 : ℤ) = 2 * 6 + 3 ∧
      (¬ ∃ i j : ℤ, ((15 : ℤ) = i * 6 + j ∨ (15 : ℤ) = i * 6 - j) ∧ 0 < j ∧ 2 * j < 6) ∧
      ∀ q i : ℤ, 2 * |q - i * 6| ≤ 6 → (|q - i * 6| = 0 ↔ 6 ∣ q) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rintro ⟨i, j, h, hj₀, hj₃⟩
    omega
  · intro q i hle
    rw [abs_eq_zero]
    rcases abs_cases (q - i * 6) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] at hle
    · exact ⟨fun _ ↦ ⟨i, by omega⟩, fun ⟨_, _⟩ ↦ by omega⟩
    · exact ⟨fun _ ↦ ⟨i, by omega⟩, fun ⟨_, _⟩ ↦ by omega⟩

end TauCeti.Montgomery
