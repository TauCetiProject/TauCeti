/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder
import TauCeti.Examples.AlgebraicGeometry.EllipticCurve.Montgomery.Basic
import TauCeti.Examples.AlgebraicGeometry.EllipticCurve.Montgomery.CurveX3AddX
import TauCeti.NumberTheory.LcmUpto

/-!
# Examples of Montgomery reduction and stage-1 detection

Starting from `(22, 1)` modulo `35` on the curve `y² = x³ + x` with scaled doubling parameters
`(N, D) = (2, 4)` — which reduces to `(2, 0)` of order `2` modulo `5` and `(1, 3)` of order `4`
modulo `7` — the multiples `m = 2, 3, 4` exhibit all three stage-1 gcd outcomes on one curve:

* At `m = 2`, doubling `(22, 1)` gives `(21, 25)`: modulo `5` it represents `[2](2, 0) = 0` so
  `5 ∣ gcd(25, 35)`, while modulo `7` it reduces to `(0, 4) ≠ 0`, representing `[2](1, 3) = (0, 0)`;
  the original point `(1, 3)` has order `4`, which does not divide `2`, so
  `prime_dvd_gcd_iff_addOrderOf_dvd` gives `¬ 7 ∣ gcd(25, 35)` and
  `one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd` certifies a proper factor
  (`gcd(25, 35) = 5`).
* At `m = 3`, differential addition of `(21, 25)` and `(22, 1)` with difference `(22, 1)` gives
  `(1, 8)`, representing `[3](2, 0) = (2, 0)` modulo `5` and `[3](1, 3) = (1, 4)` modulo `7`;
  neither order divides `3`, so neither prime divides `gcd(8, 35) = 1`.
* At `m = 4`, doubling `(21, 25)` gives `(9, 0)`: both point orders divide `4`, annihilating both
  reductions and giving the inconclusive `gcd(0, 35) = 35`.

Separately, `(1, 3)` over `ZMod 7` has order `4`, whose only prime divisor `2` is at most `3` yet
`4` divides neither `Nat.lcmUpto 2 = 2` nor `Nat.lcmUpto 3 = 6` (`4 ∣ Nat.lcmUpto 4 = 12`),
illustrating that prime-divisor smoothness is strictly weaker than powersmoothness. Further
examples show that `B ≠ 0` and nonzeroness of the reduced pair are both required for the converse
of `prime_dvd_gcd_iff_addOrderOf_dvd`, and that `addOrderOf P ∣ m` cannot be strengthened to
divisibility by the group cardinality (`4 ∤ 2` over `ZMod 5`). The remaining examples separate
the three gcd outcomes on raw residues, record a proper gcd for a prime-power modulus, verify
reduction of pairs, doubling, and ring subtraction along `ZMod.castHom` (including the
divisibility requirement for `ZMod n →+* ZMod d`), and derive the three outcomes from `(22, 1)`
via the generic doubling and differential-addition lemmas.
-/

public section

namespace TauCeti.Montgomery

open TauCeti.Examples.Montgomery TauCeti.Examples.Montgomery.CurveX3AddX WeierstrassCurve

local instance detectionPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance detectionPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem addOrderOf_pointTwoZeroFive : addOrderOf pointTwoZeroFive = 2 :=
  addOrderOf_eq_two_five (Affine.Point.some_ne_zero _)

private theorem three_pointTwoZeroFive : (3 : ℕ) • pointTwoZeroFive = pointTwoZeroFive := by
  have h3 : (3 : ℕ) = 2 + 1 := rfl
  rw [h3, add_nsmul, two_nsmul_eq_zero_five, zero_add, one_nsmul]

private theorem pointOneThreeSeven_double :
    pointOneThreeSeven + pointOneThreeSeven = twoTorsionPoint 0 (by decide) :=
  (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three_seven).mpr (by decide)

private theorem four_pointOneThreeSeven : (4 : ℕ) • pointOneThreeSeven = 0 := by
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  simp only [h4, mul_nsmul, two_nsmul, pointOneThreeSeven_double, twoTorsionPoint_add_self]

private theorem three_pointOneThreeSeven :
    (3 : ℕ) • pointOneThreeSeven = .some 1 4 nonsingular_one_four_seven := by
  have hneg : -Affine.Point.some 1 3 nonsingular_one_three_seven =
      .some 1 4 nonsingular_one_four_seven := by
    simp only [Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
    decide
  rw [← hneg, ← pointOneThreeSeven]
  apply eq_neg_of_add_eq_zero_left
  simpa only [succ_nsmul] using four_pointOneThreeSeven

private theorem addOrderOf_pointOneThreeSeven : addOrderOf pointOneThreeSeven = 4 := by
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ four_pointOneThreeSeven
  rw [pow_one, two_nsmul, pointOneThreeSeven_double]
  exact twoTorsionPoint_ne_zero 0 (by decide)

-- Starting pair `(22, 1)` modulo `35` reduces to `(2, 1)` (the coordinate pair of `(2, 0)` over
-- `ZMod 5`) and to `(1, 1)` (the coordinate pair of `(1, 3)` over `ZMod 7`), and produces
-- `(21, 25)`, `(1, 8)`, `(9, 0)` at `m = 2, 3, 4`.
example : (Pair.mk 22 1 : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) =
      coordinates 0 1 pointTwoZeroFive ∧
    (Pair.mk 22 1 : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) =
      coordinates 0 1 pointOneThreeSeven ∧
    double (2 : ZMod 35) 4 ⟨22, 1⟩ = ⟨21, 25⟩ ∧
    diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ ∧
    double (2 : ZMod 35) 4 ⟨21, 25⟩ = ⟨9, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pointTwoZeroFive, coordinates_some]
    ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  · rw [pointOneThreeSeven, coordinates_some]
    ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  · ext <;> norm_num [double_x, double_z] <;> decide
  · ext <;> norm_num [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  · ext <;> norm_num [double_x, double_z] <;> decide

-- Modulo 5, (21, 25) represents infinity (1, 0); modulo 7 it reduces to (0, 4).
example : (Pair.mk 21 25 : Pair (ZMod 35)).map
      (ZMod.castHom (by norm_num : 5 ∣ 35) (ZMod 5)) = ⟨1, 0⟩ ∧
    (Pair.mk 21 25 : Pair (ZMod 35)).map
      (ZMod.castHom (by norm_num : 7 ∣ 35) (ZMod 7)) = ⟨0, 4⟩ := by
  constructor <;> (ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide)

-- Exact stage-1 characterization at `m = 2` on `R = (21, 25)`: `5 ∣ gcd(25, 35)` because
-- `addOrderOf (2, 0) = 2 ∣ 2`, whereas `¬ 7 ∣ gcd(25, 35)` because `addOrderOf (1, 3) = 4 ∤ 2`.
example : 5 ∣ Nat.gcd (25 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (25 : ZMod 35).val 35 := by
  constructor
  · rw [prime_dvd_gcd_iff_addOrderOf_dvd (n := 35) (p := 5) (A := 0) (B := 1) (m := 2)
      (by decide) one_ne_zero pointTwoZeroFive ⟨21, 25⟩ ?_ ?_, addOrderOf_pointTwoZeroFive]
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [two_nsmul_eq_zero_five, coordinates_zero, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
  · rw [prime_dvd_gcd_iff_addOrderOf_dvd (n := 35) (p := 7) (A := 0) (B := 1) (m := 2)
      (by decide) one_ne_zero pointOneThreeSeven ⟨21, 25⟩ ?_ ?_, addOrderOf_pointOneThreeSeven]
    · decide
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [two_nsmul, pointOneThreeSeven_double, coordinates_twoTorsionPoint, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide

-- Point-order proper-factor certification at `m = 2`: `addOrderOf (2, 0) ∣ 2` modulo `5` and
-- `¬ addOrderOf (1, 3) ∣ 2` modulo `7` certify `1 < gcd(25, 35) < 35`.
example : 1 < Nat.gcd (25 : ZMod 35).val 35 ∧ Nat.gcd (25 : ZMod 35).val 35 < 35 := by
  refine one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd
    (n := 35) (p := 5) (A := 0) (B := 1) (m := 2)
    (by decide) pointTwoZeroFive ⟨21, 25⟩ (by rw [addOrderOf_pointTwoZeroFive]) ?_
    (q := 7) (A' := 0) (B' := 1) (by decide) one_ne_zero pointOneThreeSeven
    (by rw [addOrderOf_pointOneThreeSeven]; decide) ?_ ?_
  · rw [two_nsmul_eq_zero_five, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [two_nsmul, pointOneThreeSeven_double, coordinates_twoTorsionPoint, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Exact stage-1 characterization at `m = 3` on `R = (1, 8)`: `(1, 8)` represents
-- `[3](2, 0) = (2, 0)` modulo `5` and `[3](1, 3) = (1, 4)` modulo `7`, and neither prime divides
-- `gcd(8, 35) = 1`.
example : ¬ 5 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧
    Nat.gcd (8 : ZMod 35).val 35 = 1 := by
  refine ⟨?_, ?_, by decide⟩
  · rw [prime_dvd_gcd_iff_addOrderOf_dvd (n := 35) (p := 5) (A := 0) (B := 1) (m := 3)
      (by decide) one_ne_zero pointTwoZeroFive ⟨1, 8⟩ ?_ ?_, addOrderOf_pointTwoZeroFive]
    · decide
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [three_pointTwoZeroFive, pointTwoZeroFive, coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
  · rw [prime_dvd_gcd_iff_addOrderOf_dvd (n := 35) (p := 7) (A := 0) (B := 1) (m := 3)
      (by decide) one_ne_zero pointOneThreeSeven ⟨1, 8⟩ ?_ ?_, addOrderOf_pointOneThreeSeven]
    · decide
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [three_pointOneThreeSeven, coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide

-- Over ZMod 7, (1, 3) has order 4: its only prime divisor is 2 ≤ 3, yet neither M(2) = 2 nor
-- M(3) = 6 annihilates it, whereas M(4) = 12 does.
example : ¬ addOrderOf pointOneThreeSeven ∣ Nat.lcmUpto 2 ∧
    ¬ addOrderOf pointOneThreeSeven ∣ Nat.lcmUpto 3 ∧
    addOrderOf pointOneThreeSeven ∣ Nat.lcmUpto 4 := by
  rw [addOrderOf_pointOneThreeSeven]
  decide

-- Modulo 5, (21, 25) is already infinity (1, 0); modulo 7 it reduces to (0, 4), representing the
-- two-torsion point (0, 0) of order 2. Doubling (21, 25) modulo 35 gives (9, 0), whose denominator
-- vanishes modulo both 5 and 7 and produces the inconclusive outcome gcd(0, 35) = 35.
example : double (2 : ZMod 35) 4 ⟨21, 25⟩ = ⟨9, 0⟩ ∧
    5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
    7 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
    Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  refine ⟨by ext <;> norm_num [double_x, double_z] <;> decide, ?_, ?_, by decide⟩
  · apply prime_dvd_gcd_of_addOrderOf_dvd (n := 35) (p := 5) (A := 0) (B := 1)
      (m := (2 : ℕ).lcmUpto) (by decide) 0 ⟨9, 0⟩ (Nat.dvd_lcmUpto (by simp) (by simp))
    rw [nsmul_zero, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · apply prime_dvd_gcd_of_addOrderOf_dvd (n := 35) (p := 7) (A := 0) (B := 1)
      (m := (2 : ℕ).lcmUpto) (by decide) (twoTorsionPoint 0 (by decide)) ⟨9, 0⟩
      (Nat.dvd_lcmUpto (by simp) (by simp))
    rw [Nat.lcmUpto_two, two_nsmul, twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Sharpness of `addOrderOf P ∣ m`: over `ZMod 5`, `model 0 1` has native group cardinality `4`,
-- so `5 ∣ gcd(25, 35)` at `m = 2` holds even though `¬ Nat.card (model 0 1).toAffine.Point ∣ 2`.
example : 5 ∣ Nat.gcd (25 : ZMod 35).val 35 ∧
    ¬ Nat.card (model (0 : ZMod 5) 1).toAffine.Point ∣ 2 := by
  rw [card_point_five]
  decide

-- Sharpness of `B ≠ 0` and `R.map f ≠ 0` in `prime_dvd_gcd_iff_addOrderOf_dvd`:
-- on the cusp `model 0 0` over `ZMod 5`, `(1, 1)` is nonsingular with coordinate pair `(1, 0) ≠ 0`
-- so `5 ∣ gcd(0, 35)` at `m = 1` without `addOrderOf (1, 1) ∣ 1`; and on `model 0 1` over `ZMod 7`,
-- `R = 0` gives `7 ∣ gcd(0, 35)` at `m = 1` without `addOrderOf pointOneThreeSeven ∣ 1`.
example : (∃ hns : (model (0 : ZMod 5) 0).toAffine.Nonsingular 1 1,
      ((⟨1, 0⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) ≠ 0) ∧
      ((⟨1, 0⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
        (coordinates 0 0 ((1 : ℕ) • .some 1 1 hns)) = 0 ∧
      5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
      ¬ addOrderOf (.some 1 1 hns : (model (0 : ZMod 5) 0).toAffine.Point) ∣ 1) ∧
    (((0 : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 ((1 : ℕ) • pointOneThreeSeven)) = 0 ∧
      7 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
      ¬ addOrderOf pointOneThreeSeven ∣ 1) := by
  refine ⟨⟨?_, ?_, ?_, by decide, ?_⟩,
    ⟨by simp, by decide, by rw [addOrderOf_pointOneThreeSeven]; decide⟩⟩
  · simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]
    decide
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [one_nsmul, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero, one_nsmul]
    exact Affine.Point.some_ne_zero _

-- The three gcd outcomes: no factor, a proper factor, and total annihilation.
example : Nat.gcd (1 : ZMod 35).val 35 = 1 ∧
    Nat.gcd (25 : ZMod 35).val 35 = 5 ∧ Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  decide

-- Proper prime-power gcds do not require two distinct prime divisors.
example : Nat.gcd (3 : ZMod 9).val 9 = 3 ∧
    ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (3 : ZMod 9) =
      ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (0 : ZMod 9) := by
  decide

-- The gcd/reduction bridge also includes modulus zero and negative integers.
example : 5 ∣ Nat.gcd (-15 : ZMod 0).val 0 := by
  rw [ZMod.dvd_gcd_val_iff_castHom_eq_zero _ (dvd_zero 5)]
  decide

/-! ### Reduction checks along `ZMod.castHom` -/

-- (22, 1) modulo 35 maps to (2, 1) over ZMod 5 and (1, 1) over ZMod 7, and doubling commutes
-- with reduction: double 2 4 (22, 1) = (21, 25) maps to double 2 4 (2, 1) = (1, 0) and
-- double 2 4 (1, 1) = (0, 4).
example :
    let φ₅ := ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)
    let φ₇ := ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)
    let S : Pair (ZMod 35) := ⟨22, 1⟩
    S.map φ₅ = ⟨2, 1⟩ ∧ S.map φ₇ = ⟨1, 1⟩ ∧
      (double 2 4 S).map φ₅ = double 2 4 ⟨2, 1⟩ ∧ double (2 : ZMod 5) 4 ⟨2, 1⟩ = ⟨1, 0⟩ ∧
      (double 2 4 S).map φ₇ = double 2 4 ⟨1, 1⟩ ∧ double (2 : ZMod 7) 4 ⟨1, 1⟩ = ⟨0, 4⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext <;> simp only [map_double, Pair.map_x, Pair.map_z, double_x, double_z] <;> decide)

-- Ring subtraction (3 : ZMod 35) - 5 = 33 maps to 3 = -2 in ZMod 5 and 5 = -2 in ZMod 7,
-- whereas truncated natural subtraction 3 - 5 = 0 in ℕ maps to 0.
example :
    let φ₅ := ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)
    let φ₇ := ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)
    (3 : ZMod 35) - 5 = 33 ∧
      φ₅ ((3 : ZMod 35) - 5) = 3 ∧ (3 : ZMod 5) = -2 ∧
      φ₇ ((3 : ZMod 35) - 5) = 5 ∧ (5 : ZMod 7) = -2 ∧
      φ₅ (((3 - 5 : ℕ) : ZMod 35)) = 0 ∧ φ₅ (((3 - 5 : ℕ) : ZMod 35)) ≠ -2 := by
  decide

-- ZMod.castHom requires divisibility rather than primality, and no ring hom ZMod 35 →+* ZMod 3
-- exists because 3 does not divide 35.
example :
    Nonempty (ZMod 35 →+* ZMod 5) ∧ Nonempty (ZMod 9 →+* ZMod 3) ∧
      IsEmpty (ZMod 35 →+* ZMod 3) :=
  ⟨⟨ZMod.castHom (by decide) (ZMod 5)⟩, ⟨ZMod.castHom (by decide) (ZMod 3)⟩,
    ⟨fun f ↦ (by decide : (35 : ZMod 3) ≠ 0)
      (by rw [← map_ofNat f 35, (by decide : (35 : ZMod 35) = 0), map_zero])⟩⟩

/-! ### The three gcd outcomes from `(22, 1)` modulo `35` -/

private theorem map_castHom_twentyTwo_one {p : ℕ} (hp : p ∣ 35) {x y : ZMod p}
    (hns : (model (0 : ZMod p) 1).toAffine.Nonsingular x y)
    (hx : ZMod.castHom hp (ZMod p) (22 : ZMod 35) = x) :
    (⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p)) =
      coordinates 0 1 (.some x y hns) := by
  ext <;> simp only [Pair.map_x, Pair.map_z, coordinates_some, hx, map_one]

private theorem double_twentyTwo_one : double (2 : ZMod 35) 4 ⟨22, 1⟩ = ⟨21, 25⟩ := by
  ext <;> simp only [double_x, double_z] <;> decide

private theorem diffAdd_twentyOne_twentyFive :
    diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ := by
  ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

private theorem double_twentyOne_twentyFive : double (2 : ZMod 35) 4 ⟨21, 25⟩ = ⟨9, 0⟩ := by
  ext <;> simp only [double_x, double_z] <;> decide

private theorem cross_double_twentyTwo_one {p : ℕ} [Fact p.Prime] (hp : p ∣ 35)
    (h4 : (4 : ZMod p) ≠ 0) {P : (model (0 : ZMod p) 1).toAffine.Point}
    (hmap : (⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p)) = coordinates 0 1 P) :
    (⟨21, 25⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p)) ≠ 0 ∧
      ((⟨21, 25⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p))).cross
        (coordinates 0 1 ((2 : ℕ) • P)) = 0 := by
  rw [← double_twentyTwo_one, map_double, hmap, two_nsmul]
  simpa only [map_ofNat] using
    double_coordinates (N := (2 : ZMod p)) (D := 4) h4 (by ring) P

private theorem cross_diffAdd_twentyOne_twentyFive {p : ℕ} [Fact p.Prime] (hp : p ∣ 35)
    (h2 : (2 : ZMod p) ≠ 0) (h22 : ZMod.castHom hp (ZMod p) (22 : ZMod 35) ≠ 0)
    {P : (model (0 : ZMod p) 1).toAffine.Point}
    (hmap : (⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p)) = coordinates 0 1 P) :
    (⟨1, 8⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p)) ≠ 0 ∧
      ((⟨1, 8⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p))).cross
        (coordinates 0 1 ((3 : ℕ) • P)) = 0 := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h4_eq : (4 : ZMod p) = 2 * 2 := by ring
    rw [h4_eq]
    exact mul_ne_zero h2 h2
  have h2P := cross_double_twentyTwo_one hp h4 hmap
  have hP0 : P ≠ 0 := (coordinates_z_eq_zero_iff one_ne_zero).not.mp <| by
    rw [← hmap, Pair.map_z, map_one]
    exact one_ne_zero
  have hPT : P ≠ twoTorsionPoint 0 one_ne_zero :=
    (coordinates_x_eq_zero_iff one_ne_zero).not.mp <| by
      rw [← hmap, Pair.map_x]
      exact h22
  rw [← diffAdd_twentyOne_twentyFive, map_diffAdd, hmap]
  refine ⟨(diffAdd_nsmul_ne_zero_iff_of_cross_eq_zero h2 one_ne_zero P 1
      h2P.1 (coordinates_ne_zero one_ne_zero _) (coordinates_ne_zero one_ne_zero _)
      h2P.2 (by simp) (by simp)).mpr ⟨hP0, hPT⟩,
    diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P 1
      h2P.2 (by simp) (by simp)⟩

private theorem cross_double_twentyOne_twentyFive {p : ℕ} [Fact p.Prime] (hp : p ∣ 35)
    (h4 : (4 : ZMod p) ≠ 0) {P : (model (0 : ZMod p) 1).toAffine.Point}
    (hmap : (⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p)) = coordinates 0 1 P) :
    (⟨9, 0⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p)) ≠ 0 ∧
      ((⟨9, 0⟩ : Pair (ZMod 35)).map (ZMod.castHom hp (ZMod p))).cross
        (coordinates 0 1 ((4 : ℕ) • P)) = 0 := by
  have h2P := cross_double_twentyTwo_one hp h4 hmap
  have h4nat : (4 : ℕ) = 2 * 2 := rfl
  rw [← double_twentyOne_twentyFive, map_double, h4nat, mul_nsmul, two_nsmul]
  simpa only [map_ofNat] using
    double_coordinates_of_cross_eq_zero (N := (2 : ZMod p)) (D := 4) h4 (by ring) h2P.1 h2P.2

-- Outcome m = 2: double 2 4 (22, 1) = (21, 25); (2, 0) over ZMod 5 has order 2 ∣ 2 so 5 divides
-- gcd(25, 35), while (1, 3) over ZMod 7 has order 4 ∤ 2 so 7 does not divide gcd(25, 35),
-- certifying the proper factor gcd(25, 35) = 5.
example : double (2 : ZMod 35) 4 ⟨22, 1⟩ = ⟨21, 25⟩ ∧
    5 ∣ Nat.gcd (25 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (25 : ZMod 35).val 35 ∧
    (1 < Nat.gcd (25 : ZMod 35).val 35 ∧ Nat.gcd (25 : ZMod 35).val 35 < 35) ∧
    Nat.gcd (25 : ZMod 35).val 35 = 5 := by
  have h5 := cross_double_twentyTwo_one (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_two_zero_five (by decide))
  have h7 := cross_double_twentyTwo_one (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_one_three_seven (by decide))
  have hm5 : addOrderOf pointTwoZeroFive ∣ 2 := by rw [addOrderOf_pointTwoZeroFive]
  have h7_not_dvd : ¬ 7 ∣ Nat.gcd (25 : ZMod 35).val 35 :=
    (prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero pointOneThreeSeven ⟨21, 25⟩
      h7.1 h7.2).not.mpr (by rw [addOrderOf_pointOneThreeSeven]; decide)
  exact ⟨double_twentyTwo_one,
    (prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero pointTwoZeroFive ⟨21, 25⟩
      h5.1 h5.2).mpr hm5,
    h7_not_dvd,
    one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd (by decide) pointTwoZeroFive ⟨21, 25⟩ hm5 h5.2
      (by decide)
      (((25 : ZMod 35).dvd_gcd_val_iff_castHom_eq_zero (by decide)).not.mp h7_not_dvd),
    by decide⟩

-- Outcome m = 3: diffAdd (double 2 4 (22, 1)) (22, 1) (22, 1) = (1, 8); neither order 2 over
-- ZMod 5 nor order 4 over ZMod 7 divides 3, so neither 5 nor 7 divides gcd(8, 35) = 1.
example : diffAdd (double (2 : ZMod 35) 4 ⟨22, 1⟩) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ ∧
    ¬ 5 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧
    Nat.gcd (8 : ZMod 35).val 35 = 1 := by
  have h5 := cross_diffAdd_twentyOne_twentyFive (by decide) (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_two_zero_five (by decide))
  have h7 := cross_diffAdd_twentyOne_twentyFive (by decide) (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_one_three_seven (by decide))
  exact ⟨by rw [double_twentyTwo_one, diffAdd_twentyOne_twentyFive],
    (prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero pointTwoZeroFive ⟨1, 8⟩
      h5.1 h5.2).not.mpr (by rw [addOrderOf_pointTwoZeroFive]; decide),
    (prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero pointOneThreeSeven ⟨1, 8⟩
      h7.1 h7.2).not.mpr (by rw [addOrderOf_pointOneThreeSeven]; decide),
    by decide⟩

-- Outcome m = 4: double 2 4 (double 2 4 (22, 1)) = (9, 0); both order 2 over ZMod 5 and order 4
-- over ZMod 7 divide 4, so both 5 and 7 divide the inconclusive gcd(0, 35) = 35.
example : double (2 : ZMod 35) 4 (double 2 4 ⟨22, 1⟩) = ⟨9, 0⟩ ∧
    5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧ 7 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
    Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  have h5 := cross_double_twentyOne_twentyFive (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_two_zero_five (by decide))
  have h7 := cross_double_twentyOne_twentyFive (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_one_three_seven (by decide))
  exact ⟨by rw [double_twentyTwo_one, double_twentyOne_twentyFive],
    (prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero pointTwoZeroFive ⟨9, 0⟩
      h5.1 h5.2).mpr (by rw [addOrderOf_pointTwoZeroFive]; decide),
    (prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero pointOneThreeSeven ⟨9, 0⟩
      h7.1 h7.2).mpr (by rw [addOrderOf_pointOneThreeSeven]),
    by decide⟩

end TauCeti.Montgomery
