/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Set.Card
import TauCeti.Data.Int.Round

/-!
# Examples of coordinate pairs, projective `x`-coordinates and the stage-2 criterion

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

For the stage-2 cross-difference criterion on the same curve over `𝔽₇`, the point `Q = (3, 3)` has
order `8`, with coordinate pairs `(3, 1)`, `(1, 1)`, `(5, 1)`, `(0, 1)`, `(5, 1)`, `(1, 1)`,
`(3, 1)` and `(1, 0)` for `[1..8]Q`. The cross difference vanishes at `(m, n) = (5, 3)` (where
`[8]Q = 0`) and `(5, -3)` (using signed integer scalars), and does not vanish at `(3, 1)` (where
neither `[2]Q` nor `[4]Q` vanishes). At step `w = 6`, `q = 7 = 6 + 1` gives `[7]Q = -Q ≠ 0` and
nonzero cross difference, while `q = 8 = 6 + 2` gives `[8]Q = 0` and vanishing cross difference
between `[6]Q = (1, 3)` and `[2]Q = (1, 4)`. Purely over `ℤ`, the step `w = 6` represents `13` and
`17` within distance `1` and hits the endpoint `j = 3 = w / 2` at `q = 15`, showing that a strict
bound `0 < j < w / 2` would miss midpoints, while `j = 0` occurs exactly when `6 ∣ q`. The
degenerate pair `(m, n) = (0, 0)` is checked generically over any field. The finite arithmetic is
verified by kernel reduction.
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

/-! ### The stage-2 cross-difference criterion -/

private theorem nonsingular_three_three : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private theorem nonsingular_five_five : (model (0 : ZMod 7) 1).toAffine.Nonsingular 5 5 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointThree : E := .some 3 3 nonsingular_three_three

private theorem two_zsmul_pointThree :
    (2 : ℤ) • pointThree = .some 1 4 nonsingular_one_four := by
  have hy : (3 : ZMod 7) ≠ (model (0 : ZMod 7) 1).toAffine.negY 3 3 := by
    simp only [Affine.negY, model_a₁, model_a₃]
    decide
  have hsl : (model (0 : ZMod 7) 1).toAffine.slope 3 3 3 3 = 0 := by
    simp only [Affine.slope_of_Y_ne rfl hy, Affine.negY, model_a₁, model_a₂, model_a₃, model_a₄]
    rw [div_eq_iff (by decide)]
    decide
  rw [two_zsmul, pointThree, Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq]
  simp only [Affine.addX, Affine.addY, Affine.negAddY, hsl, Affine.negY, model_a₁, model_a₂,
    model_a₃]
  decide

private theorem three_zsmul_pointThree :
    (3 : ℤ) • pointThree = .some 5 5 nonsingular_five_five := by
  have h3 : (3 : ℤ) = 2 + 1 := rfl
  have hx : (1 : ZMod 7) ≠ 3 := by decide
  have hsl : (model (0 : ZMod 7) 1).toAffine.slope 1 3 4 3 = 3 := by
    simp only [Affine.slope_of_X_ne hx]
    rw [div_eq_iff (by decide)]
    decide
  rw [h3, add_zsmul, one_zsmul, two_zsmul_pointThree, pointThree, Affine.Point.add_of_X_ne hx,
    Affine.Point.some.injEq]
  simp only [Affine.addX, Affine.addY, Affine.negAddY, hsl, Affine.negY, model_a₁, model_a₂,
    model_a₃]
  decide

private theorem four_zsmul_pointThree :
    (4 : ℤ) • pointThree = twoTorsionPoint 0 one_ne_zero := by
  have h4 : (4 : ℤ) = 2 + 2 := rfl
  rw [h4, add_zsmul, two_zsmul_pointThree]
  exact (add_self_eq_twoTorsionPoint_iff one_ne_zero nonsingular_one_four).mpr (by decide)

private theorem eight_zsmul_pointThree : (8 : ℤ) • pointThree = 0 := by
  have h8 : (8 : ℤ) = 4 + 4 := rfl
  rw [h8, add_zsmul, four_zsmul_pointThree, twoTorsionPoint_add_self]

private theorem addOrderOf_pointThree : addOrderOf pointThree = 8 := by
  refine addOrderOf_eq_prime_pow (p := 2) (n := 2) ?_ ?_
  · simpa [← natCast_zsmul, four_zsmul_pointThree] using
      twoTorsionPoint_ne_zero (0 : ZMod 7) one_ne_zero
  · simpa [← natCast_zsmul] using eight_zsmul_pointThree

private theorem five_zsmul_pointThree : (5 : ℤ) • pointThree = -((3 : ℤ) • pointThree) := by
  have h5 : (5 : ℤ) = 8 - 3 := rfl
  rw [h5, sub_zsmul, eight_zsmul_pointThree, zero_add]

private theorem six_zsmul_pointThree :
    (6 : ℤ) • pointThree = .some 1 3 nonsingular_one_three := by
  have h6 : (6 : ℤ) = 8 - 2 := rfl
  rw [h6, sub_zsmul, eight_zsmul_pointThree, zero_add, two_zsmul_pointThree,
    Affine.Point.neg_some, Affine.Point.some.injEq]
  simp only [Affine.negY, model_a₁, model_a₃]
  decide

private theorem seven_zsmul_pointThree : (7 : ℤ) • pointThree = -pointThree := by
  have h7 : (7 : ℤ) = 8 - 1 := rfl
  rw [h7, sub_zsmul, eight_zsmul_pointThree, zero_add, one_zsmul]

-- `Q = (3, 3)` has order `8`, and its multiples `[1..8]Q` have coordinate pairs
-- `(3, 1)`, `(1, 1)`, `(5, 1)`, `(0, 1)`, `(5, 1)`, `(1, 1)`, `(3, 1)` and `(1, 0)`.
example : addOrderOf pointThree = 8 ∧
    coordinates 0 1 ((1 : ℤ) • pointThree) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((2 : ℤ) • pointThree) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((3 : ℤ) • pointThree) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((4 : ℤ) • pointThree) = ⟨0, 1⟩ ∧
    coordinates 0 1 ((5 : ℤ) • pointThree) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((6 : ℤ) • pointThree) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((7 : ℤ) • pointThree) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((8 : ℤ) • pointThree) = ⟨1, 0⟩ := by
  rw [addOrderOf_pointThree, one_zsmul, two_zsmul_pointThree, five_zsmul_pointThree,
    three_zsmul_pointThree, four_zsmul_pointThree, six_zsmul_pointThree, seven_zsmul_pointThree,
    eight_zsmul_pointThree]
  simp [pointThree]

-- `(m, n) = (5, 3)`: `x([5]Q) = x([3]Q) = 5`, the cross difference vanishes, `[5 + 3]Q = [8]Q = 0`,
-- while `[5 - 3]Q = [2]Q ≠ 0`.
example : coordinates 0 1 ((5 : ℤ) • pointThree) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((3 : ℤ) • pointThree) = ⟨5, 1⟩ ∧
    (coordinates 0 1 ((5 : ℤ) • pointThree)).cross (coordinates 0 1 ((3 : ℤ) • pointThree)) = 0 ∧
    ((5 : ℤ) + 3) • pointThree = 0 ∧ ((5 : ℤ) - 3) • pointThree ≠ 0 := by
  have hsum : ((5 : ℤ) + 3) • pointThree = 0 := eight_zsmul_pointThree
  have hdiff : ((5 : ℤ) - 3) • pointThree ≠ 0 := by
    have h2 : (5 : ℤ) - 3 = 2 := rfl
    rw [h2, two_zsmul_pointThree]
    exact Affine.Point.some_ne_zero _
  have hcross : (coordinates 0 1 ((5 : ℤ) • pointThree)).cross
      (coordinates 0 1 ((3 : ℤ) • pointThree)) = 0 :=
    (cross_coordinates_zsmul_eq_zero_iff (one_ne_zero : (1 : ZMod 7) ≠ 0)).mpr (.inr hsum)
  refine ⟨?_, ?_, hcross, hsum, hdiff⟩
  · rw [five_zsmul_pointThree, coordinates_neg, three_zsmul_pointThree, coordinates_some]
  · rw [three_zsmul_pointThree, coordinates_some]

-- `(m, n) = (3, 1)`: `x([3]Q) = 5` and `x([1]Q) = 3`, so the cross difference is `5 - 3 ≠ 0`,
-- and by `cross_coordinates_zsmul_eq_zero_iff` neither `[2]Q` nor `[4]Q` vanishes.
example : (coordinates 0 1 ((3 : ℤ) • pointThree)).cross
      (coordinates 0 1 ((1 : ℤ) • pointThree)) = 2 ∧
    ((3 : ℤ) - 1) • pointThree ≠ 0 ∧ ((3 : ℤ) + 1) • pointThree ≠ 0 := by
  have hcross : (coordinates 0 1 ((3 : ℤ) • pointThree)).cross
      (coordinates 0 1 ((1 : ℤ) • pointThree)) = 2 := by
    rw [three_zsmul_pointThree, one_zsmul, pointThree, coordinates_some, coordinates_some,
      Pair.cross_def]
    decide
  have hne : (coordinates 0 1 ((3 : ℤ) • pointThree)).cross
      (coordinates 0 1 ((1 : ℤ) • pointThree)) ≠ 0 := by
    rw [hcross]
    decide
  rw [ne_eq, cross_coordinates_zsmul_eq_zero_iff (one_ne_zero : (1 : ZMod 7) ≠ 0), not_or] at hne
  exact ⟨hcross, hne.1, hne.2⟩

-- Signs are handled in `ℤ`: for `(m, n) = (5, -3)`, the difference `(5 - (-3)) • Q = [8]Q`
-- vanishes while `(5 + (-3)) • Q = [2]Q ≠ 0`, and the cross difference vanishes.
example : (coordinates 0 1 ((5 : ℤ) • pointThree)).cross
      (coordinates 0 1 ((-3 : ℤ) • pointThree)) = 0 ∧
    ((5 : ℤ) - (-3)) • pointThree = 0 ∧ ((5 : ℤ) + (-3)) • pointThree ≠ 0 := by
  have hdiff : ((5 : ℤ) - (-3)) • pointThree = 0 := eight_zsmul_pointThree
  have hsum : ((5 : ℤ) + (-3)) • pointThree ≠ 0 := by
    have h2 : (5 : ℤ) + (-3) = 2 := rfl
    rw [h2, two_zsmul_pointThree]
    exact Affine.Point.some_ne_zero _
  exact ⟨(cross_coordinates_zsmul_eq_zero_iff (one_ne_zero : (1 : ZMod 7) ≠ 0)).mpr (.inl hdiff),
    hdiff, hsum⟩

-- Step `w = 6` on `Q = (3, 3)`: `q = 7 = 6 + 1` gives `[7]Q = -Q ≠ 0`, and the coordinate pairs
-- of `[6]Q = (1, 3)` and `[1]Q = (3, 3)` have nonzero cross difference.
example : (7 : ℤ) • pointThree = -pointThree ∧ (7 : ℤ) • pointThree ≠ 0 ∧
    (coordinates 0 1 ((1 * 6 : ℤ) • pointThree)).cross
      (coordinates 0 1 ((1 : ℤ) • pointThree)) ≠ 0 := by
  refine ⟨seven_zsmul_pointThree, ?_, ?_⟩
  · rw [seven_zsmul_pointThree, neg_ne_zero]
    exact Affine.Point.some_ne_zero _
  · rw [one_mul, six_zsmul_pointThree, one_zsmul, pointThree, coordinates_some, coordinates_some,
      Pair.cross_def]
    decide

-- Step `w = 6` on `Q = (3, 3)`: `q = 8 = 6 + 2` gives `[8]Q = 0`, `[6]Q = (1, 3)` and
-- `[2]Q = (1, 4)` both have coordinate pair `(1, 1)`, and their cross difference vanishes.
example : (8 : ℤ) • pointThree = 0 ∧
    (6 : ℤ) • pointThree = .some 1 3 nonsingular_one_three ∧
    (2 : ℤ) • pointThree = .some 1 4 nonsingular_one_four ∧
    coordinates 0 1 ((1 * 6 : ℤ) • pointThree) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((2 : ℤ) • pointThree) = ⟨1, 1⟩ ∧
    (coordinates 0 1 ((1 * 6 : ℤ) • pointThree)).cross
      (coordinates 0 1 ((2 : ℤ) • pointThree)) = 0 := by
  refine ⟨eight_zsmul_pointThree, six_zsmul_pointThree, two_zsmul_pointThree, ?_, ?_, ?_⟩
  · rw [one_mul, six_zsmul_pointThree, coordinates_some]
  · rw [two_zsmul_pointThree, coordinates_some]
  · exact cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero
      eight_zsmul_pointThree (.inl (by norm_num))

-- The existential stage-2 criterion applies directly at `q = 8` and `w = 6` (where the unique
-- witness is `i = 1` with `j = 2`).
example : ∃ i : ℤ, 2 * |(8 : ℤ) - i * 6| ≤ 6 ∧
    (coordinates 0 1 ((i * 6) • pointThree)).cross
      (coordinates 0 1 (|(8 : ℤ) - i * 6| • pointThree)) = 0 :=
  exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero eight_zsmul_pointThree (by norm_num)

end Seven

/-! ### Nearest-multiple decomposition and the zero-index boundary -/

-- For `w = 6`, `13 = 2 · 6 + 1` and `17 = 3 · 6 - 1` have offset `1 ≤ 3`, while the midpoint
-- `q = 15 = 2 · 6 + 3` requires the closed bound `0 ≤ j ≤ w / 2`: no strict offset `0 < j < 3`
-- represents `15`.
example : ((13 : ℤ) = 2 * 6 + 1 ∧ 2 * |(13 : ℤ) - 2 * 6| ≤ 6 ∧
    (17 : ℤ) = 3 * 6 - 1 ∧ 2 * |(17 : ℤ) - 3 * 6| ≤ 6 ∧
    (15 : ℤ) = 2 * 6 + 3 ∧ 2 * |(15 : ℤ) - 2 * 6| ≤ 6) ∧
    ¬ ∃ i j : ℤ, 0 < j ∧ j < 3 ∧ ((15 : ℤ) = i * 6 + j ∨ (15 : ℤ) = i * 6 - j) := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨i, j, hj0, hj3, h | h⟩ <;> omega

-- For `w = 6`, a nearest multiple `i` (`2 * |q - i * 6| ≤ 6`, guaranteed for every `q` by
-- `Int.exists_two_mul_abs_sub_mul_le`) achieves offset `j = 0` exactly when `6 ∣ q`.
example (q : ℤ) : ∃ i : ℤ, 2 * |q - i * 6| ≤ 6 ∧ (|q - i * 6| = 0 ↔ (6 : ℤ) ∣ q) := by
  obtain ⟨i, hi⟩ := Int.exists_two_mul_abs_sub_mul_le q (by norm_num : (6 : ℤ) ≠ 0)
  rw [abs_of_pos (by norm_num : (0 : ℤ) < 6)] at hi
  refine ⟨i, hi, ⟨fun h0 ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩⟩
  · have hq : q - i * 6 = 0 := abs_eq_zero.mp h0
    exact ⟨i, by omega⟩
  · have hle : |q - i * 6| ≤ 3 := by omega
    rw [abs_le] at hle
    exact abs_eq_zero.mpr (by omega)

-- At `m = n = 0`, both coordinate pairs are `(1, 0)`, their cross difference is
-- `1 · 0 - 1 · 0 = 0`, and both `(0 - 0) • Q` and `(0 + 0) • Q` vanish, consistent with both
-- sides of `cross_coordinates_zsmul_eq_zero_iff`.
example {K : Type*} [Field K] [DecidableEq K] {A B : K} (Q : (model A B).toAffine.Point) :
    coordinates A B ((0 : ℤ) • Q) = ⟨1, 0⟩ ∧
      (coordinates A B ((0 : ℤ) • Q)).cross (coordinates A B ((0 : ℤ) • Q)) = 0 ∧
      ((0 : ℤ) - 0) • Q = 0 ∧ ((0 : ℤ) + 0) • Q = 0 := by
  refine ⟨by simp, ?_, by simp, by simp⟩
  exact cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero (zero_zsmul Q) (.inl rfl)

end TauCeti.Montgomery
