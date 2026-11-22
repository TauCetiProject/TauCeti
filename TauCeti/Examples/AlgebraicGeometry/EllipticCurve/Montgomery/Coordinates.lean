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
import TauCeti.Data.Int.Round
import TauCeti.Examples.AlgebraicGeometry.EllipticCurve.Montgomery.CurveX3AddX

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
`15 = 2 · 6 + 3` that a strict inequality `2 j < w` would miss, and has `j = 0` only when
`6 ∣ q`. Over any field, `m = n = 0` compares infinity with itself.
Nearest-multiple decompositions for `w = 6` also illustrate the divisibility test
`Int.abs_sub_mul_eq_zero_iff_dvd_of_lt` and the midpoint obstruction characterized by
`Int.exists_two_mul_abs_sub_mul_lt_iff`. The finite arithmetic is verified by kernel reduction.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1.
* P. Zimmermann, *20 years of ECM*, ANTS VII, Lecture Notes in Computer Science 4076 (2006),
  §1.
-/

public section

namespace TauCeti.Montgomery

open TauCeti.Examples.Montgomery TauCeti.Examples.Montgomery.CurveX3AddX

section Seven

local instance fibresPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Coordinate pairs -/

-- Infinity, the distinguished point `(0, 0)` and the point `(1, 3)` have coordinate pairs
-- `(1, 0)`, `(0, 1)` and `(1, 1)`.
example : coordinates (0 : ZMod 7) 1 0 = ⟨1, 0⟩ ∧
    coordinates (0 : ZMod 7) 1 (twoTorsionPoint 0 one_ne_zero) = ⟨0, 1⟩ ∧
    coordinates (0 : ZMod 7) 1 pointOneThreeSeven = ⟨1, 1⟩ :=
  ⟨coordinates_zero .., coordinates_twoTorsionPoint _, coordinates_some ..⟩

-- The point `(1, 4)` is the negative of `(1, 3)` and has the same coordinate pair `(1, 1)`.
example : pointOneFourSeven = -pointOneThreeSeven ∧
    coordinates (0 : ZMod 7) 1 pointOneFourSeven = ⟨1, 1⟩ := by
  refine ⟨?_, coordinates_some ..⟩
  simp only [pointOneFourSeven, pointOneThreeSeven, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.negY, model_a₁, model_a₃, WeierstrassCurve.Affine.Point.some.injEq]
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

private theorem eight_nsmul_pointThreeThreeSeven : (8 : ℕ) • pointThreeThreeSeven = 0 := by
  rw [← addOrderOf_pointThreeThreeSeven, addOrderOf_nsmul_eq_zero]

private theorem five_nsmul_pointThreeThreeSeven :
    (5 : ℕ) • pointThreeThreeSeven = -Affine.Point.some 5 5 nonsingular_five_five_seven := by
  apply eq_neg_of_add_eq_zero_left
  rw [← three_nsmul_pointThreeThreeSeven, ← add_nsmul]
  exact eight_nsmul_pointThreeThreeSeven

private theorem six_nsmul_pointThreeThreeSeven :
    (6 : ℕ) • pointThreeThreeSeven = .some 1 3 nonsingular_one_three_seven := by
  have hneg : -Affine.Point.some 1 4 nonsingular_one_four_seven =
      .some 1 3 nonsingular_one_three_seven := by
    simp only [Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
    decide
  rw [← hneg]
  apply eq_neg_of_add_eq_zero_left
  rw [← two_nsmul_pointThreeThreeSeven, ← add_nsmul]
  exact eight_nsmul_pointThreeThreeSeven

private theorem seven_nsmul_pointThreeThreeSeven :
    (7 : ℕ) • pointThreeThreeSeven = -pointThreeThreeSeven := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [succ_nsmul] using eight_nsmul_pointThreeThreeSeven

-- The multiples `[1..8]Q` of `Q = (3, 3)` have coordinate pairs with `x`-coordinates
-- `3, 1, 5, 0, 5, 1, 3, ∞`, and `Q` has order `8`.
example : addOrderOf pointThreeThreeSeven = 8 ∧
    coordinates 0 1 ((1 : ℕ) • pointThreeThreeSeven) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((2 : ℕ) • pointThreeThreeSeven) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((3 : ℕ) • pointThreeThreeSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((4 : ℕ) • pointThreeThreeSeven) = ⟨0, 1⟩ ∧
    coordinates 0 1 ((5 : ℕ) • pointThreeThreeSeven) = ⟨5, 1⟩ ∧
    coordinates 0 1 ((6 : ℕ) • pointThreeThreeSeven) = ⟨1, 1⟩ ∧
    coordinates 0 1 ((7 : ℕ) • pointThreeThreeSeven) = ⟨3, 1⟩ ∧
    coordinates 0 1 ((8 : ℕ) • pointThreeThreeSeven) = ⟨1, 0⟩ := by
  refine ⟨addOrderOf_pointThreeThreeSeven, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [one_nsmul, pointThreeThreeSeven, coordinates_some]
  · rw [two_nsmul_pointThreeThreeSeven, coordinates_some]
  · rw [three_nsmul_pointThreeThreeSeven, coordinates_some]
  · rw [four_nsmul_pointThreeThreeSeven, coordinates_twoTorsionPoint]
  · rw [five_nsmul_pointThreeThreeSeven, coordinates_neg, coordinates_some]
  · rw [six_nsmul_pointThreeThreeSeven, coordinates_some]
  · rw [seven_nsmul_pointThreeThreeSeven, coordinates_neg, pointThreeThreeSeven, coordinates_some]
  · rw [eight_nsmul_pointThreeThreeSeven, coordinates_zero]

-- `(m, n) = (5, 3)`: `[5]Q` and `[3]Q` share coordinate pair `(5, 1)` since `[5 + 3]Q = [8]Q = 0`.
example : (coordinates 0 1 ((5 : ℤ) • pointThreeThreeSeven)).cross
    (coordinates 0 1 ((3 : ℤ) • pointThreeThreeSeven)) = 0 := by
  have h8 : ((5 : ℤ) + 3) • pointThreeThreeSeven = 0 := by
    have h8z : ((5 : ℤ) + 3) = (8 : ℕ) := rfl
    rw [h8z, natCast_zsmul, eight_nsmul_pointThreeThreeSeven]
  exact (cross_coordinates_zsmul_eq_zero_iff (one_ne_zero : (1 : ZMod 7) ≠ 0)).mpr (.inr h8)

-- `(m, n) = (3, 1)`: scaled representatives `(3, 2)` of `[3]Q` (`3 ≡ 2 · 5`) and `(2, 3)` of
-- `[1]Q` (`2 ≡ 3 · 3`) have nonvanishing cross difference, equivalent via
-- `cross_eq_zero_iff_zsmul_eq_zero_of_cross_coordinates_eq_zero` to `[2]Q ≠ 0 ∧ [4]Q ≠ 0`.
example : (⟨3, 2⟩ : Pair (ZMod 7)).cross ⟨2, 3⟩ ≠ 0 ∧
    (2 : ℤ) • pointThreeThreeSeven ≠ 0 ∧ (4 : ℤ) • pointThreeThreeSeven ≠ 0 := by
  have h3 :
      (⟨3, 2⟩ : Pair (ZMod 7)).cross (coordinates 0 1 ((3 : ℤ) • pointThreeThreeSeven)) = 0 := by
    have h3z : (3 : ℤ) = (3 : ℕ) := rfl
    rw [h3z, natCast_zsmul, three_nsmul_pointThreeThreeSeven, coordinates_some, Pair.cross_def]
    decide
  have h1 :
      (⟨2, 3⟩ : Pair (ZMod 7)).cross (coordinates 0 1 ((1 : ℤ) • pointThreeThreeSeven)) = 0 := by
    rw [one_zsmul, pointThreeThreeSeven, coordinates_some, Pair.cross_def]
    decide
  have h2ne : (2 : ℤ) • pointThreeThreeSeven ≠ 0 := by
    have h2z : (2 : ℤ) = (2 : ℕ) := rfl
    rw [h2z, natCast_zsmul, two_nsmul_pointThreeThreeSeven]
    exact Affine.Point.some_ne_zero _
  have h4ne : (4 : ℤ) • pointThreeThreeSeven ≠ 0 := by
    have h4z : (4 : ℤ) = (4 : ℕ) := rfl
    rw [h4z, natCast_zsmul, four_nsmul_pointThreeThreeSeven]
    exact twoTorsionPoint_ne_zero 0 one_ne_zero
  refine ⟨?_, h2ne, h4ne⟩
  rw [Ne, cross_eq_zero_iff_zsmul_eq_zero_of_cross_coordinates_eq_zero
    (one_ne_zero : (1 : ZMod 7) ≠ 0) (Pair.ne_zero_iff.mpr (.inl (by decide)))
    (Pair.ne_zero_iff.mpr (.inl (by decide))) h3 h1]
  have hsub : ((3 : ℤ) - 1) = 2 := rfl
  have hadd : ((3 : ℤ) + 1) = 4 := rfl
  rw [hsub, hadd]
  exact not_or.mpr ⟨h2ne, h4ne⟩

-- `(m, n) = (3, 1)` on `Q = (3, 3)`: the coordinate pairs `(5, 1)` of `[3]Q` and `(3, 1)` of
-- `[1]Q` have cross difference `5 - 3 = 2 ≠ 0`, so neither `[2]Q` nor `[4]Q` vanishes.
example :
    (coordinates 0 1 ((3 : ℤ) • pointThreeThreeSeven)).cross
      (coordinates 0 1 ((1 : ℤ) • pointThreeThreeSeven)) = 2 ∧
    ((3 : ℤ) - 1) • pointThreeThreeSeven ≠ 0 ∧
    ((3 : ℤ) + 1) • pointThreeThreeSeven ≠ 0 := by
  have hcross : (coordinates 0 1 ((3 : ℤ) • pointThreeThreeSeven)).cross
      (coordinates 0 1 ((1 : ℤ) • pointThreeThreeSeven)) = 2 := by
    have h3z : (3 : ℤ) = (3 : ℕ) := rfl
    rw [h3z, natCast_zsmul, three_nsmul_pointThreeThreeSeven, one_zsmul, pointThreeThreeSeven,
      coordinates_some, coordinates_some, Pair.cross_def]
    decide
  have hne : ¬ (((3 : ℤ) - 1) • pointThreeThreeSeven = 0 ∨
      ((3 : ℤ) + 1) • pointThreeThreeSeven = 0) := by
    rw [← cross_coordinates_zsmul_eq_zero_iff (A := (0 : ZMod 7)) one_ne_zero, hcross]
    decide
  exact ⟨hcross, not_or.mp hne⟩

-- With step `w = 6`: `q = 7 = 6 + 1` leaves `[7]Q = -Q ≠ 0`, so `[6]Q = (1, 3)` and `[1]Q = (3, 3)`
-- have nonzero cross difference, while `q = 8 = 6 + 2` annihilates `Q` and gives vanishing cross
-- difference between `[6]Q = (1, 3)` and `[2]Q = (1, 4)`, with
-- `exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero` producing a witness.
example : (7 : ℤ) • pointThreeThreeSeven ≠ 0 ∧
    (coordinates 0 1 ((6 : ℤ) • pointThreeThreeSeven)).cross
      (coordinates 0 1 ((1 : ℤ) • pointThreeThreeSeven)) ≠ 0 ∧
    (8 : ℤ) • pointThreeThreeSeven = 0 ∧
    (coordinates 0 1 ((6 : ℤ) • pointThreeThreeSeven)).cross
      (coordinates 0 1 ((2 : ℤ) • pointThreeThreeSeven)) = 0 ∧
    ∃ i : ℤ, 2 * |(8 : ℤ) - i * 6| ≤ 6 ∧
      (coordinates 0 1 ((i * 6) • pointThreeThreeSeven)).cross
        (coordinates 0 1 (|(8 : ℤ) - i * 6| • pointThreeThreeSeven)) = 0 := by
  have h8z : (8 : ℤ) • pointThreeThreeSeven = 0 := by
    have h8 : (8 : ℤ) = (8 : ℕ) := rfl
    rw [h8, natCast_zsmul, eight_nsmul_pointThreeThreeSeven]
  have h6 : (6 : ℤ) = (6 : ℕ) := rfl
  refine ⟨?_, ?_, h8z, cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero h8z (.inl (by norm_num)),
    exists_two_mul_abs_sub_mul_le_and_cross_coordinates_eq_zero h8z (by norm_num)⟩
  · have h7 : (7 : ℤ) = (7 : ℕ) := rfl
    rw [h7, natCast_zsmul, seven_nsmul_pointThreeThreeSeven, neg_ne_zero, pointThreeThreeSeven]
    exact Affine.Point.some_ne_zero _
  · rw [h6, natCast_zsmul, six_nsmul_pointThreeThreeSeven, one_zsmul, pointThreeThreeSeven,
      coordinates_some, coordinates_some, Pair.cross_def]
    decide

end Seven

-- At `m = n = 0`, both multiples are infinity `(1, 0)` with cross difference `1 · 0 - 1 · 0 = 0`
-- and `[0]Q = 0`, consistent with both sides of `cross_coordinates_zsmul_eq_zero_iff`.
example {K : Type*} [Field K] [DecidableEq K] (A B : K)
    (Q : (model A B).toAffine.Point) :
    (coordinates A B ((0 : ℤ) • Q)).cross (coordinates A B ((0 : ℤ) • Q)) = 1 * 0 - 1 * 0 ∧
      ((0 : ℤ) - 0) • Q = 0 ∧ ((0 : ℤ) + 0) • Q = 0 ∧
      (coordinates A B ((0 : ℤ) • Q)).cross (coordinates A B ((0 : ℤ) • Q)) = 0 :=
  ⟨by simp, by simp, by simp,
    cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero (zero_zsmul Q) (.inr rfl)⟩

-- With step `w = 6`, `13 = 2 · 6 + 1` and `17 = 3 · 6 - 1` have strict remainder `2 j < 6`,
-- whereas `15 = 2 · 6 + 3` requires the non-strict midpoint bound `2 j ≤ 6`, and `j = 0` occurs
-- within `2 j ≤ 6` exactly when `6 ∣ q`.
example :
    (13 : ℤ) = 2 * 6 + 1 ∧ (17 : ℤ) = 3 * 6 - 1 ∧ (15 : ℤ) = 2 * 6 + 3 ∧
      (¬ ∃ i j : ℤ, ((15 : ℤ) = i * 6 + j ∨ (15 : ℤ) = i * 6 - j) ∧ 0 ≤ j ∧ 2 * j < 6) ∧
      ∀ q i : ℤ, 2 * |q - i * 6| ≤ 6 → (|q - i * 6| = 0 ↔ 6 ∣ q) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun q i hle ↦
    Int.abs_sub_mul_eq_zero_iff_dvd_of_two_mul_le (hle.trans (le_abs_self 6))⟩
  rintro ⟨i, j, h, hj₀, hj₃⟩
  omega

/-! ### Nearest multiples for step `w = 6` -/

-- `13 = 2 · 6 + 1`, `17 = 3 · 6 - 1` and `12 = 2 · 6 + 0`: the baby-step index `|q - i · 6|`
-- vanishes if and only if `6 ∣ q`.
example :
    ((13 : ℤ) = 2 * 6 + 1 ∧ 2 * |(13 : ℤ) - 2 * 6| ≤ 6 ∧ ¬ (6 : ℤ) ∣ 13) ∧
    ((17 : ℤ) = 3 * 6 - 1 ∧ 2 * |(17 : ℤ) - 3 * 6| ≤ 6 ∧ ¬ (6 : ℤ) ∣ 17) ∧
    (|(12 : ℤ) - 2 * 6| = 0 ∧ (6 : ℤ) ∣ 12) := by
  have h₁₃ : ¬ (6 : ℤ) ∣ 13 := by
    rw [← Int.abs_sub_mul_eq_zero_iff_dvd_of_lt (c := 2) (by decide)]
    decide
  have h₁₇ : ¬ (6 : ℤ) ∣ 17 := by
    rw [← Int.abs_sub_mul_eq_zero_iff_dvd_of_lt (c := 3) (by decide)]
    decide
  have h₁₂ : (6 : ℤ) ∣ 12 :=
    (Int.abs_sub_mul_eq_zero_iff_dvd_of_lt (c := 2) (by decide)).mp (by decide)
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
