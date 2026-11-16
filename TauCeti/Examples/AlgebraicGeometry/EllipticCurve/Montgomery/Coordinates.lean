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

For the point `Q = (3, 3)` of order `8` on `y² = x³ + x` over `𝔽₇`, the cross-difference
criterion `cross_coordinates_zsmul_eq_zero_iff` is illustrated on `(m, n) = (5, 3)` (matching
`x = 5` and `[8]Q = 0`), `(m, n) = (3, 1)` (distinct `x`-coordinates `5` and `3`, with neither
`[2]Q` nor `[4]Q` vanishing), and `m = n = 0` at infinity, together with step `w = 6` at `q = 7`
and `q = 8`. Nearest-multiple decompositions for `w = 6` also illustrate the divisibility test
`Int.abs_sub_mul_eq_zero_iff_dvd` and the midpoint obstruction `15 = 2 · 6 + 3` characterized by
`Int.exists_two_mul_abs_sub_mul_lt_iff`. The finite arithmetic is verified by kernel reduction.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1.
* P. Zimmermann, *20 years of ECM*, ANTS VII, Lecture Notes in Computer Science 4076 (2006),
  §1.
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

private theorem nonsingular_five_two : (model (0 : ZMod 7) 1).toAffine.Nonsingular 5 2 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private theorem nonsingular_five_five : (model (0 : ZMod 7) 1).toAffine.Nonsingular 5 5 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def generatorSeven : E :=
  .some 3 3 nonsingular_three_three

private theorem two_nsmul_generatorSeven :
    (2 : ℕ) • generatorSeven = .some 1 4 nonsingular_one_four := by
  have hy : (3 : ZMod 7) ≠ (model (0 : ZMod 7) 1).toAffine.negY 3 3 := by
    simp only [Affine.negY, model_a₁, model_a₃]
    decide
  have hsl : (model (0 : ZMod 7) 1).toAffine.slope 3 3 3 3 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy, div_eq_zero_iff]
    left
    simp only [model_a₁, model_a₂, model_a₄]
    decide
  rw [two_nsmul, generatorSeven, Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq]
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hsl,
    model_a₁, model_a₂, model_a₃]
  decide

private theorem three_nsmul_generatorSeven :
    (3 : ℕ) • generatorSeven = .some 5 5 nonsingular_five_five := by
  have hx : (1 : ZMod 7) ≠ 3 := by decide
  have hsl : (model (0 : ZMod 7) 1).toAffine.slope 1 3 4 3 = 3 := by
    rw [Affine.slope_of_X_ne hx, div_eq_iff (by decide)]
    decide
  rw [succ_nsmul, two_nsmul_generatorSeven, generatorSeven, Affine.Point.add_of_X_ne hx,
    Affine.Point.some.injEq]
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hsl,
    model_a₁, model_a₂, model_a₃]
  decide

private theorem four_nsmul_generatorSeven :
    (4 : ℕ) • generatorSeven = twoTorsionPoint 0 one_ne_zero := by
  have h22 : (4 : ℕ) = 2 + 2 := rfl
  rw [h22, add_nsmul, two_nsmul_generatorSeven]
  exact (add_self_eq_twoTorsionPoint_iff one_ne_zero nonsingular_one_four).mpr (by decide)

private theorem eight_nsmul_generatorSeven : (8 : ℕ) • generatorSeven = 0 := by
  have h44 : (8 : ℕ) = 4 + 4 := rfl
  rw [h44, add_nsmul, four_nsmul_generatorSeven, twoTorsionPoint_add_self]

private theorem eight_zsmul_generatorSeven : (8 : ℤ) • generatorSeven = 0 :=
  (natCast_zsmul generatorSeven 8).trans eight_nsmul_generatorSeven

private theorem five_nsmul_generatorSeven :
    (5 : ℕ) • generatorSeven = .some 5 2 nonsingular_five_two := by
  have hsum : (5 : ℕ) • generatorSeven + (3 : ℕ) • generatorSeven = 0 := by
    rw [← add_nsmul]
    exact eight_nsmul_generatorSeven
  rw [eq_neg_of_add_eq_zero_left hsum, three_nsmul_generatorSeven]
  simp only [Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
  decide

private theorem six_nsmul_generatorSeven :
    (6 : ℕ) • generatorSeven = .some 1 3 nonsingular_one_three := by
  have hsum : (6 : ℕ) • generatorSeven + (2 : ℕ) • generatorSeven = 0 := by
    rw [← add_nsmul]
    exact eight_nsmul_generatorSeven
  rw [eq_neg_of_add_eq_zero_left hsum, two_nsmul_generatorSeven]
  simp only [Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
  decide

private theorem seven_zsmul_generatorSeven : (7 : ℤ) • generatorSeven = -generatorSeven := by
  have hsum : (7 : ℤ) • generatorSeven + (1 : ℤ) • generatorSeven = 0 := by
    rw [← add_zsmul]
    exact eight_zsmul_generatorSeven
  simpa only [one_zsmul] using eq_neg_of_add_eq_zero_left hsum

-- `(m, n) = (5, 3)` on `Q = (3, 3)` of order `8`: both `[5]Q` and `[3]Q` have coordinate pair
-- `(5, 1)`, their cross difference vanishes, and `[5 + 3]Q = [8]Q = 0`.
example :
    coordinates 0 1 ((5 : ℤ) • generatorSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((3 : ℤ) • generatorSeven) = ⟨5, 1⟩ ∧
    (coordinates 0 1 ((5 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((3 : ℤ) • generatorSeven)) = 0 ∧
    ((5 : ℤ) + 3) • generatorSeven = 0 := by
  have h₅ : (5 : ℤ) • generatorSeven = .some 5 2 nonsingular_five_two :=
    (natCast_zsmul generatorSeven 5).trans five_nsmul_generatorSeven
  have h₃ : (3 : ℤ) • generatorSeven = .some 5 5 nonsingular_five_five :=
    (natCast_zsmul generatorSeven 3).trans three_nsmul_generatorSeven
  refine ⟨by rw [h₅, coordinates_some], by rw [h₃, coordinates_some],
    (cross_coordinates_zsmul_eq_zero_iff one_ne_zero).mpr (.inr eight_zsmul_generatorSeven),
    eight_zsmul_generatorSeven⟩

-- `(m, n) = (3, 1)` on `Q = (3, 3)`: `[3]Q` and `[1]Q` have coordinate pairs `(5, 1)` and
-- `(3, 1)`, cross difference `5 - 3 = 2 ≠ 0`, and neither `[2]Q` nor `[4]Q` vanishes.
example :
    coordinates 0 1 ((3 : ℤ) • generatorSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((1 : ℤ) • generatorSeven) = ⟨3, 1⟩ ∧
    (coordinates 0 1 ((3 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((1 : ℤ) • generatorSeven)) = 2 ∧
    ((3 : ℤ) - 1) • generatorSeven ≠ 0 ∧
    ((3 : ℤ) + 1) • generatorSeven ≠ 0 := by
  have h₃' : (3 : ℤ) • generatorSeven = .some 5 5 nonsingular_five_five :=
    (natCast_zsmul generatorSeven 3).trans three_nsmul_generatorSeven
  have h₃ : coordinates 0 1 ((3 : ℤ) • generatorSeven) = ⟨5, 1⟩ := by
    rw [h₃', coordinates_some]
  have h₁ : coordinates 0 1 ((1 : ℤ) • generatorSeven) = ⟨3, 1⟩ := by
    rw [one_zsmul, generatorSeven, coordinates_some]
  have hcross : (coordinates 0 1 ((3 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((1 : ℤ) • generatorSeven)) = 2 := by
    rw [h₃, h₁, Pair.cross_def]
    decide
  have hne : ¬ (((3 : ℤ) - 1) • generatorSeven = 0 ∨ ((3 : ℤ) + 1) • generatorSeven = 0) := by
    rw [← cross_coordinates_zsmul_eq_zero_iff (A := (0 : ZMod 7)) one_ne_zero, hcross]
    decide
  exact ⟨h₃, h₁, hcross, not_or.mp hne⟩

-- `m = n = 0`: both coordinate pairs are `(1, 0)`, the cross difference `1 · 0 - 1 · 0` is `0`,
-- and `[0]Q = 0`.
example :
    coordinates 0 1 ((0 : ℤ) • generatorSeven) = ⟨1, 0⟩ ∧
    (coordinates 0 1 ((0 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((0 : ℤ) • generatorSeven)) = 0 ∧
    (0 : ℤ) • generatorSeven = 0 := by
  simp

-- Step `w = 6` at `q = 7 = 6 + 1`: `[7]Q = -Q ≠ 0`, `[5]Q ≠ 0`, and the coordinate pairs of
-- `[6]Q` and `[1]Q` have nonzero cross difference.
example :
    (7 : ℤ) • generatorSeven = -generatorSeven ∧
    (7 : ℤ) • generatorSeven ≠ 0 ∧
    (coordinates 0 1 ((6 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((1 : ℤ) • generatorSeven)) ≠ 0 := by
  have h₇ : (7 : ℤ) • generatorSeven ≠ 0 := by
    rw [seven_zsmul_generatorSeven, neg_ne_zero, generatorSeven]
    exact Affine.Point.some_ne_zero _
  have h₅ : ((6 : ℤ) - 1) • generatorSeven ≠ 0 := by
    have hsub : (6 : ℤ) - 1 = (5 : ℕ) := rfl
    rw [hsub, natCast_zsmul, five_nsmul_generatorSeven]
    exact Affine.Point.some_ne_zero _
  refine ⟨seven_zsmul_generatorSeven, h₇, ?_⟩
  rw [Ne, cross_coordinates_zsmul_eq_zero_iff one_ne_zero, not_or]
  exact ⟨h₅, h₇⟩

-- Step `w = 6` at `q = 8 = 6 + 2`: `[8]Q = 0`, `[6]Q = (1, 3)` and `[2]Q = (1, 4)` both have
-- coordinate pair `(1, 1)` with cross difference `1 · 1 - 1 · 1 = 0`, and the stage-2 existence
-- theorem applies directly.
example :
    (8 : ℤ) • generatorSeven = 0 ∧
    (6 : ℤ) • generatorSeven = .some 1 3 nonsingular_one_three ∧
    (2 : ℤ) • generatorSeven = .some 1 4 nonsingular_one_four ∧
    coordinates 0 1 ((6 : ℤ) • generatorSeven) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((2 : ℤ) • generatorSeven) = ⟨1, 1⟩ ∧
    (coordinates 0 1 ((6 : ℤ) • generatorSeven)).cross
      (coordinates 0 1 ((2 : ℤ) • generatorSeven)) = 0 ∧
    ∃ i : ℤ, 2 * |(8 : ℤ) - i * 6| ≤ 6 ∧
      (coordinates 0 1 ((i * 6) • generatorSeven)).cross
        (coordinates 0 1 (|(8 : ℤ) - i * 6| • generatorSeven)) = 0 := by
  have h₆ : (6 : ℤ) • generatorSeven = .some 1 3 nonsingular_one_three :=
    (natCast_zsmul generatorSeven 6).trans six_nsmul_generatorSeven
  have h₂ : (2 : ℤ) • generatorSeven = .some 1 4 nonsingular_one_four :=
    (natCast_zsmul generatorSeven 2).trans two_nsmul_generatorSeven
  refine ⟨eight_zsmul_generatorSeven, h₆, h₂, by rw [h₆, coordinates_some],
    by rw [h₂, coordinates_some], ?_,
    exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero eight_zsmul_generatorSeven
      (by decide)⟩
  rw [h₆, h₂, coordinates_some, coordinates_some, Pair.cross_def, sub_self]

end Seven

/-! ### Nearest multiples for step `w = 6` -/

-- `13 = 2 · 6 + 1`, `17 = 3 · 6 - 1` and `12 = 2 · 6 + 0`: the baby-step index `|q - i · 6|`
-- vanishes if and only if `6 ∣ q`.
example :
    ((13 : ℤ) = 2 * 6 + 1 ∧ 2 * |(13 : ℤ) - 2 * 6| ≤ 6 ∧ ¬ (6 : ℤ) ∣ 13) ∧
    ((17 : ℤ) = 3 * 6 - 1 ∧ 2 * |(17 : ℤ) - 3 * 6| ≤ 6 ∧ ¬ (6 : ℤ) ∣ 17) ∧
    (|(12 : ℤ) - 2 * 6| = 0 ∧ (6 : ℤ) ∣ 12) := by
  have h₁₃ : ¬ (6 : ℤ) ∣ 13 := by
    rw [← Int.abs_sub_mul_eq_zero_iff_dvd (c := 2) (by decide)]
    decide
  have h₁₇ : ¬ (6 : ℤ) ∣ 17 := by
    rw [← Int.abs_sub_mul_eq_zero_iff_dvd (c := 3) (by decide)]
    decide
  have h₁₂ : (6 : ℤ) ∣ 12 :=
    (Int.abs_sub_mul_eq_zero_iff_dvd (c := 2) (by decide)).mp (by decide)
  exact ⟨⟨by decide, by decide, h₁₃⟩, ⟨by decide, by decide, h₁₇⟩, ⟨by decide, h₁₂⟩⟩

-- At the midpoint `q = 15 = 2 · 6 + 3`, the non-strict bound `2 · |15 - 2 · 6| ≤ 6` holds,
-- whereas no integer multiple of `6` lies strictly closer than `6 / 2 = 3`.
example :
    2 * |(15 : ℤ) - 2 * 6| ≤ |6| ∧
    ¬ ∃ i : ℤ, 2 * |(15 : ℤ) - i * 6| < |(6 : ℤ)| := by
  refine ⟨by decide, ?_⟩
  rw [Int.exists_two_mul_abs_sub_mul_lt_iff (by decide)]
  decide

end TauCeti.Montgomery
