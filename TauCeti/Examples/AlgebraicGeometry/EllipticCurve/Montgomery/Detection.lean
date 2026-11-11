/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
import TauCeti.NumberTheory.LcmUpto

/-!
# Examples of Montgomery stage-1 detection

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
smoothness is strictly weaker than powersmoothness (`B₁ = 3` versus `B₁ = 4`). The remaining
examples separate the three gcd outcomes and record a proper gcd for a prime-power modulus.
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

end TauCeti.Montgomery
