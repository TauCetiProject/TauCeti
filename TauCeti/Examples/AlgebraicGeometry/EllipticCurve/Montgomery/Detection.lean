/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder
import TauCeti.NumberTheory.LcmUpto

/-!
# Examples of Montgomery reduction and stage-1 detection

The raw pair `(21, 25)` modulo `35` represents infinity modulo `5`, while modulo `7` it reduces
to `(0, 4)`, representing the distinguished two-torsion point `(0, 0)` with nonzero denominator.
Because the distinguished two-torsion point over `ZMod 5` has additive order `2`, the stage-1
multiplier `Nat.lcmUpto 2 = 2` annihilates it, and nonvanishing modulo `7` certifies a proper
factor of `35` at `B₁ = 2`. Doubling `(21, 25)` modulo `35` gives `(9, 0)`: infinity remains at
infinity modulo `5` and doubling annihilates the two-torsion point modulo `7`, so the doubled
pair's denominator vanishes modulo both `5` and `7` and `gcd(0, 35) = 35` is inconclusive.

Separately, the affine point `(1, 3)` on `y² = x³ + x` over `ZMod 7` has additive order `4`:
its only prime divisor `2` is at most `3`, yet `4` divides neither `Nat.lcmUpto 2 = 2` nor
`Nat.lcmUpto 3 = 6`, whereas `4 ∣ Nat.lcmUpto 4 = 12`, illustrating that prime-divisor
smoothness is strictly weaker than powersmoothness (`B₁ = 3` versus `B₁ = 4`). Further examples
separate the three gcd outcomes on raw residues, record a proper gcd for a prime-power modulus,
verify reduction of pairs, doubling, and ring subtraction along `ZMod.castHom` (including the
divisibility requirement for `ZMod n →+* ZMod d`), and exhibit all three gcd outcomes (`m = 2`,
`m = 3`, `m = 4`) on `y² = x³ + x` modulo `35` from the starting pair `(22, 1)`.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

local instance detectionPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance detectionPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem nonsingular_one_three :
    (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 3 nonsingular_one_three

private theorem pointSeven_double : pointSeven + pointSeven = twoTorsionPoint 0 (by decide) :=
  (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three).mpr (by decide)

private theorem four_pointSeven : (4 : ℕ) • pointSeven = 0 := by
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  simp only [h4, mul_nsmul, two_nsmul, pointSeven_double, twoTorsionPoint_add_self]

private theorem addOrderOf_pointSeven : addOrderOf pointSeven = 4 := by
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ four_pointSeven
  rw [pow_one, two_nsmul, pointSeven_double]
  exact twoTorsionPoint_ne_zero 0 (by decide)

-- Modulo 5, (21, 25) represents infinity (1, 0); modulo 7 it reduces to (0, 4).
example : (Pair.mk 21 25 : Pair (ZMod 35)).map
      (ZMod.castHom (by norm_num : 5 ∣ 35) (ZMod 5)) = ⟨1, 0⟩ ∧
    (Pair.mk 21 25 : Pair (ZMod 35)).map
      (ZMod.castHom (by norm_num : 7 ∣ 35) (ZMod 7)) = ⟨0, 4⟩ := by
  constructor <;> (ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide)

-- Stage-1 detection at B₁ = 2 (M(2) = 2): the two-torsion point over ZMod 5 has order 2 ≤ 2.
example : 5 ∣ Nat.gcd (25 : ZMod 35).val 35 := by
  apply prime_dvd_gcd_of_addOrderOf_dvd (n := 35) (p := 5) (A := 0) (B := 1)
    (m := (2 : ℕ).lcmUpto) (by decide) (twoTorsionPoint 0 (by decide)) ⟨21, 25⟩
    (Nat.dvd_lcmUpto (by simp) (by simp))
  rw [Nat.lcmUpto_two, two_nsmul, twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def]
  simp only [Pair.map_x, Pair.map_z]
  decide

-- Nonvanishing at 7 upgrades stage-1 detection at B₁ = 2 to a proper factor certificate.
example : 1 < Nat.gcd (25 : ZMod 35).val 35 ∧ Nat.gcd (25 : ZMod 35).val 35 < 35 := by
  refine one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd
    (n := 35) (p := 5) (A := 0) (B := 1) (m := (2 : ℕ).lcmUpto)
    (by decide) (twoTorsionPoint 0 (by decide)) ⟨21, 25⟩
    (Nat.dvd_lcmUpto_iff.mpr ?_) ?_ (q := 7) (by decide) (by decide)
  · intro q _ hq
    rw [addOrderOf_twoTorsionPoint 0 (by decide)] at hq
    exact Nat.le_of_dvd (by decide) hq
  · rw [Nat.lcmUpto_two, two_nsmul, twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def]
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

private theorem nonsingular_two_zero :
    (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointFive : (model (0 : ZMod 5) 1).toAffine.Point :=
  .some 2 0 nonsingular_two_zero

private theorem two_pointFive : (2 : ℕ) • pointFive = 0 := by
  rw [two_nsmul]
  exact Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])

private theorem addOrderOf_pointFive : addOrderOf pointFive = 2 :=
  addOrderOf_eq_prime two_pointFive (Affine.Point.some_ne_zero _)

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
    (map_castHom_twentyTwo_one (by decide) nonsingular_two_zero (by decide))
  have h7 := cross_double_twentyTwo_one (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_one_three (by decide))
  have hm5 : addOrderOf pointFive ∣ 2 := by rw [addOrderOf_pointFive]
  have h7_not_dvd : ¬ 7 ∣ Nat.gcd (25 : ZMod 35).val 35 :=
    (prime_dvd_gcd_iff_addOrderOf_dvd one_ne_zero (by decide) pointSeven ⟨21, 25⟩
      h7.1 h7.2).not.mpr (by rw [addOrderOf_pointSeven]; decide)
  exact ⟨double_twentyTwo_one,
    (prime_dvd_gcd_iff_addOrderOf_dvd one_ne_zero (by decide) pointFive ⟨21, 25⟩
      h5.1 h5.2).mpr hm5,
    h7_not_dvd,
    one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd (by decide) pointFive ⟨21, 25⟩ hm5 h5.2 (by decide)
      (((25 : ZMod 35).dvd_gcd_val_iff_castHom_eq_zero (by decide)).not.mp h7_not_dvd),
    by decide⟩

-- Outcome m = 3: diffAdd (double 2 4 (22, 1)) (22, 1) (22, 1) = (1, 8); neither order 2 over
-- ZMod 5 nor order 4 over ZMod 7 divides 3, so neither 5 nor 7 divides gcd(8, 35) = 1.
example : diffAdd (double (2 : ZMod 35) 4 ⟨22, 1⟩) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ ∧
    ¬ 5 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (8 : ZMod 35).val 35 ∧
    Nat.gcd (8 : ZMod 35).val 35 = 1 := by
  have h5 := cross_diffAdd_twentyOne_twentyFive (by decide) (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_two_zero (by decide))
  have h7 := cross_diffAdd_twentyOne_twentyFive (by decide) (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_one_three (by decide))
  exact ⟨by rw [double_twentyTwo_one, diffAdd_twentyOne_twentyFive],
    (prime_dvd_gcd_iff_addOrderOf_dvd one_ne_zero (by decide) pointFive ⟨1, 8⟩
      h5.1 h5.2).not.mpr (by rw [addOrderOf_pointFive]; decide),
    (prime_dvd_gcd_iff_addOrderOf_dvd one_ne_zero (by decide) pointSeven ⟨1, 8⟩
      h7.1 h7.2).not.mpr (by rw [addOrderOf_pointSeven]; decide),
    by decide⟩

-- Outcome m = 4: double 2 4 (double 2 4 (22, 1)) = (9, 0); both order 2 over ZMod 5 and order 4
-- over ZMod 7 divide 4, so both 5 and 7 divide the inconclusive gcd(0, 35) = 35.
example : double (2 : ZMod 35) 4 (double 2 4 ⟨22, 1⟩) = ⟨9, 0⟩ ∧
    5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧ 7 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
    Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  have h5 := cross_double_twentyOne_twentyFive (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_two_zero (by decide))
  have h7 := cross_double_twentyOne_twentyFive (by decide) (by decide)
    (map_castHom_twentyTwo_one (by decide) nonsingular_one_three (by decide))
  exact ⟨by rw [double_twentyTwo_one, double_twentyOne_twentyFive],
    (prime_dvd_gcd_iff_addOrderOf_dvd one_ne_zero (by decide) pointFive ⟨9, 0⟩
      h5.1 h5.2).mpr (by rw [addOrderOf_pointFive]; decide),
    (prime_dvd_gcd_iff_addOrderOf_dvd one_ne_zero (by decide) pointSeven ⟨9, 0⟩
      h7.1 h7.2).mpr (by rw [addOrderOf_pointSeven]),
    by decide⟩

end TauCeti.Montgomery
