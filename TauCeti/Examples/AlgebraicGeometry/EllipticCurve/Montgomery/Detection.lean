/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.DiffAdd
import TauCeti.Examples.AlgebraicGeometry.EllipticCurve.Montgomery.Basic
import TauCeti.NumberTheory.LcmUpto

/-!
# Examples of Montgomery stage-1 detection

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
divisibility by the group cardinality (`4 ∤ 2` over `ZMod 5`).
-/

public section

namespace TauCeti.Montgomery

open TauCeti.Examples.Montgomery WeierstrassCurve

local instance detectionPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance detectionPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem nonsingular_two_zero_five :
    (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointFive : (model (0 : ZMod 5) 1).toAffine.Point :=
  .some 2 0 nonsingular_two_zero_five

private theorem addOrderOf_pointFive : addOrderOf pointFive = 2 :=
  addOrderOf_eq_two_five (Affine.Point.some_ne_zero _)

private theorem three_pointFive : (3 : ℕ) • pointFive = pointFive := by
  have h3 : (3 : ℕ) = 2 + 1 := rfl
  rw [h3, add_nsmul, two_nsmul_eq_zero_five, zero_add, one_nsmul]

private noncomputable def pointSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 3 nonsingular_one_three_seven

private theorem pointSeven_double : pointSeven + pointSeven = twoTorsionPoint 0 (by decide) :=
  (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three_seven).mpr (by decide)

private theorem four_pointSeven : (4 : ℕ) • pointSeven = 0 := by
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  simp only [h4, mul_nsmul, two_nsmul, pointSeven_double, twoTorsionPoint_add_self]

private theorem three_pointSeven :
    (3 : ℕ) • pointSeven = .some 1 4 nonsingular_one_four_seven := by
  have hneg : -Affine.Point.some 1 3 nonsingular_one_three_seven =
      .some 1 4 nonsingular_one_four_seven := by
    simp only [Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃, Affine.Point.some.injEq]
    decide
  rw [← hneg, ← pointSeven]
  apply eq_neg_of_add_eq_zero_left
  simpa only [succ_nsmul] using four_pointSeven

private theorem addOrderOf_pointSeven : addOrderOf pointSeven = 4 := by
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ four_pointSeven
  rw [pow_one, two_nsmul, pointSeven_double]
  exact twoTorsionPoint_ne_zero 0 (by decide)

-- Starting pair `(22, 1)` modulo `35` reduces to `(2, 1)` (the coordinate pair of `(2, 0)` over
-- `ZMod 5`) and to `(1, 1)` (the coordinate pair of `(1, 3)` over `ZMod 7`), and produces
-- `(21, 25)`, `(1, 8)`, `(9, 0)` at `m = 2, 3, 4`.
example : (Pair.mk 22 1 : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) =
      coordinates 0 1 pointFive ∧
    (Pair.mk 22 1 : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) =
      coordinates 0 1 pointSeven ∧
    double (2 : ZMod 35) 4 ⟨22, 1⟩ = ⟨21, 25⟩ ∧
    diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ ∧
    double (2 : ZMod 35) 4 ⟨21, 25⟩ = ⟨9, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pointFive, coordinates_some]
    ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  · rw [pointSeven, coordinates_some]
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
      (by decide) one_ne_zero pointFive ⟨21, 25⟩ ?_ ?_, addOrderOf_pointFive]
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [two_nsmul_eq_zero_five, coordinates_zero, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
  · rw [prime_dvd_gcd_iff_addOrderOf_dvd (n := 35) (p := 7) (A := 0) (B := 1) (m := 2)
      (by decide) one_ne_zero pointSeven ⟨21, 25⟩ ?_ ?_, addOrderOf_pointSeven]
    · decide
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [two_nsmul, pointSeven_double, coordinates_twoTorsionPoint, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide

-- Point-order proper-factor certification at `m = 2`: `addOrderOf (2, 0) ∣ 2` modulo `5` and
-- `¬ addOrderOf (1, 3) ∣ 2` modulo `7` certify `1 < gcd(25, 35) < 35`.
example : 1 < Nat.gcd (25 : ZMod 35).val 35 ∧ Nat.gcd (25 : ZMod 35).val 35 < 35 := by
  refine one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd
    (n := 35) (p := 5) (A := 0) (B := 1) (m := 2)
    (by decide) pointFive ⟨21, 25⟩ (by rw [addOrderOf_pointFive]) ?_
    (q := 7) (A' := 0) (B' := 1) (by decide) one_ne_zero pointSeven
    (by rw [addOrderOf_pointSeven]; decide) ?_ ?_
  · rw [two_nsmul_eq_zero_five, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [two_nsmul, pointSeven_double, coordinates_twoTorsionPoint, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Exact stage-1 characterization at `m = 3` on `R = (1, 8)`: `(1, 8)` represents
-- `[3](2, 0) = (2, 0)` modulo `5` and `[3](1, 3) = (1, 4)` modulo `7`, and neither prime divides
-- `gcd(8, 35) = 1`.
example : ¬ 5 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧
    Nat.gcd (8 : ZMod 35).val 35 = 1 := by
  refine ⟨?_, ?_, by decide⟩
  · rw [prime_dvd_gcd_iff_addOrderOf_dvd (n := 35) (p := 5) (A := 0) (B := 1) (m := 3)
      (by decide) one_ne_zero pointFive ⟨1, 8⟩ ?_ ?_, addOrderOf_pointFive]
    · decide
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [three_pointFive, pointFive, coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
  · rw [prime_dvd_gcd_iff_addOrderOf_dvd (n := 35) (p := 7) (A := 0) (B := 1) (m := 3)
      (by decide) one_ne_zero pointSeven ⟨1, 8⟩ ?_ ?_, addOrderOf_pointSeven]
    · decide
    · rw [Pair.ne_zero_iff]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [three_pointSeven, coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide

-- Over ZMod 7, (1, 3) has order 4: its only prime divisor is 2 ≤ 3, yet neither M(2) = 2 nor
-- M(3) = 6 annihilates it, whereas M(4) = 12 does.
example : ¬ addOrderOf pointSeven ∣ Nat.lcmUpto 2 ∧
    ¬ addOrderOf pointSeven ∣ Nat.lcmUpto 3 ∧
    addOrderOf pointSeven ∣ Nat.lcmUpto 4 := by
  rw [addOrderOf_pointSeven]
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
-- `R = 0` gives `7 ∣ gcd(0, 35)` at `m = 1` without `addOrderOf pointSeven ∣ 1`.
example : (∃ hns : (model (0 : ZMod 5) 0).toAffine.Nonsingular 1 1,
      ((⟨1, 0⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) ≠ 0) ∧
      ((⟨1, 0⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
        (coordinates 0 0 ((1 : ℕ) • .some 1 1 hns)) = 0 ∧
      5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
      ¬ addOrderOf (.some 1 1 hns : (model (0 : ZMod 5) 0).toAffine.Point) ∣ 1) ∧
    (((0 : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 ((1 : ℕ) • pointSeven)) = 0 ∧
      7 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
      ¬ addOrderOf pointSeven ∣ 1) := by
  refine ⟨⟨?_, ?_, ?_, by decide, ?_⟩, ⟨by simp, by decide, by rw [addOrderOf_pointSeven]; decide⟩⟩
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

end TauCeti.Montgomery
