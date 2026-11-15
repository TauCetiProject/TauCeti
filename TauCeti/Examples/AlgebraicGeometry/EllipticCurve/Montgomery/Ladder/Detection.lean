/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder.Detection
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Suyama.Point

/-!
# Examples of Montgomery ladder reduction and factor detection

These examples exercise modular reduction of binary Montgomery ladder derivations and the
resulting stage-1 and stage-2 gcd certificates:

* Reduction modulo divisors via `ZMod.castHom`, pushing a ladder derivation over `ZMod 35` to
  both `ZMod 5` and `ZMod 7`, preserving modular subtraction, and contrasting valid quotient
  maps with the empty hom-set `ZMod 35 →+* ZMod 3`.
* All three stage-1 gcd outcomes (`5`, `1`, and `35`) on the single curve `(A, B, N, D) =
  (0, 1, 2, 4)` modulo `35` from the starting pair `(22, 1)` at indices `m = 2, 3, 4`.
* Odd-index detection at `m = 1` through the distinguished two-torsion point `(0, 0)` even when
  its order `2` does not divide `m`, together with characteristic-two coverage modulo `6`.
* A two-stage computation modulo `35` on `(A, B, N, D) = (1, 1, 3, 4)` from `(3, 1)` where
  stage 1 (`M = 2`) yields `gcd = 1` and stage 2 (`q = 2`) isolates the proper factor `7`.
* Division-free stage-1 detection from Suyama's polynomial seed `(u³, v³)` over `ZMod n`.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

local instance ladderDetectionPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance ladderDetectionPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance ladderDetectionPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

-- Reduction sends (22, 1) modulo 35 to (2, 1) modulo 5 and (1, 1) modulo 7, and pushes any
-- binary ladder derivation to both prime quotients simultaneously.
example {n : ℕ} {U V : Pair (ZMod 35)} (h : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ n U V) :
    LadderRel (2 : ZMod 5) 4 ⟨2, 1⟩ n
      (U.map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)))
      (V.map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))) ∧
    LadderRel (2 : ZMod 7) 4 ⟨1, 1⟩ n
      (U.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)))
      (V.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))) := by
  have h5 : (⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) =
      ⟨2, 1⟩ := by
    ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have h7 : (⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) =
      ⟨1, 1⟩ := by
    ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  refine ⟨?_, ?_⟩
  · simpa only [map_ofNat, h5] using h.map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))
  · simpa only [map_ofNat, h7] using h.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))

-- Ring subtraction in ZMod 35 reduces to -2 in both quotients, unlike truncated Nat subtraction;
-- ZMod.castHom needs divisibility (including non-prime targets) and fails when p does not divide n.
example :
    ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) ((3 : ZMod 35) - 5) = -2 ∧
    ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) ((3 : ZMod 35) - 5) = -2 ∧
    (((3 - 5 : ℕ) : ZMod 5) = 0) ∧
    Nonempty (ZMod 35 →+* ZMod 5) ∧
    Nonempty (ZMod 9 →+* ZMod 3) ∧
    IsEmpty (ZMod 35 →+* ZMod 3) := by
  refine ⟨by decide, by decide, by decide,
    ⟨ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)⟩,
    ⟨ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)⟩, ⟨fun f ↦ ?_⟩⟩
  have h35 : f ((35 : ℕ) : ZMod 35) = 0 := by
    have hz : ((35 : ℕ) : ZMod 35) = 0 := by decide
    rw [hz, map_zero]
  rw [map_natCast] at h35
  exact absurd h35 (by decide)

private theorem nonsingular_two_zero_mod5 :
    (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff,
    model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
  decide

private noncomputable def pointFive : (model (0 : ZMod 5) 1).toAffine.Point :=
  .some 2 0 nonsingular_two_zero_mod5

private theorem two_pointFive : (2 : ℕ) • pointFive = 0 := by
  rw [two_nsmul, pointFive]
  exact Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])

private theorem addOrderOf_pointFive : addOrderOf pointFive = 2 :=
  addOrderOf_eq_prime two_pointFive (Affine.Point.some_ne_zero _)

private theorem nonsingular_one_three_mod7 :
    (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff,
    model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
  decide

private noncomputable def pointSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 3 nonsingular_one_three_mod7

private theorem pointSeven_double :
    pointSeven + pointSeven = twoTorsionPoint (0 : ZMod 7) (by decide) :=
  (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three_mod7).mpr (by decide)

private theorem four_pointSeven : (4 : ℕ) • pointSeven = 0 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl]
  simp only [mul_nsmul, two_nsmul, pointSeven_double, twoTorsionPoint_add_self]

private theorem addOrderOf_pointSeven : addOrderOf pointSeven = 4 := by
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ four_pointSeven
  rw [pow_one, two_nsmul, pointSeven_double]
  exact twoTorsionPoint_ne_zero 0 (by decide)

private theorem ladder_one :
    LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 1 ⟨11, 18⟩ ⟨21, 25⟩ := by
  convert (LadderRel.zero (N := (2 : ZMod 35)) (D := 4) (S := ⟨22, 1⟩)).bit true
    using 1 <;> norm_num <;> ext <;>
    norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

private theorem ladder_two :
    LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ (Nat.lcmUpto 2) ⟨21, 30⟩ ⟨9, 2⟩ := by
  rw [Nat.lcmUpto_two]
  convert ladder_one.bit false using 1 <;> norm_num <;> ext <;>
    norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

private theorem ladder_three :
    LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 3 ⟨9, 2⟩ ⟨9, 0⟩ := by
  convert ladder_one.bit true using 1 <;> norm_num <;> ext <;>
    norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

private theorem ladder_four :
    LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 4 ⟨29, 0⟩ ⟨29, 22⟩ := by
  have h2 : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 2 ⟨21, 30⟩ ⟨9, 2⟩ := by
    simpa [Nat.lcmUpto_two] using ladder_two
  convert h2.bit false using 1 <;> norm_num <;> ext <;>
    norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

-- m = 2 on (0, 1, 2, 4) from (22, 1): stage 1 certifies a proper factor (gcd = 5).
example : 1 < Nat.gcd (30 : ZMod 35).val 35 ∧ Nat.gcd (30 : ZMod 35).val 35 < 35 ∧
    Nat.gcd (30 : ZMod 35).val 35 = 5 := by
  have hcert := ladder_two.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd
    (p := 5) (q := 7) (A := 0) (B := 1) (A' := 0) (B' := 1)
    (P := pointFive) (Q := pointSeven)
    (by decide) (by decide)
    (by rw [addOrderOf_pointFive, Nat.lcmUpto_two])
    (by simp only [pointFive, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide)
    (by simp only [pointSeven, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)
    (by rw [addOrderOf_pointSeven, Nat.lcmUpto_two]; decide)
    ((some_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three_mod7).not.mpr (by decide))
  exact ⟨hcert.1, hcert.2, by decide⟩

-- m = 3 on (0, 1, 2, 4) from (22, 1): neither prime divides the denominator gcd (gcd = 1).
example : ¬ 5 ∣ Nat.gcd (2 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (2 : ZMod 35).val 35 ∧
    Nat.gcd (2 : ZMod 35).val 35 = 1 := by
  refine ⟨?_, ?_, by decide⟩
  · rw [ladder_three.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint
      (p := 5) (A := 0) (B := 1) (P := pointFive)
      (by decide) (by decide) (by decide) (by decide)
      (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide)
      (by simp only [pointFive, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)]
    rw [addOrderOf_pointFive]
    exact not_or.mpr ⟨by decide,
      (some_eq_twoTorsionPoint_iff (by decide) nonsingular_two_zero_mod5).not.mpr (by decide)⟩
  · rw [ladder_three.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint
      (p := 7) (A := 0) (B := 1) (P := pointSeven)
      (by decide) (by decide) (by decide) (by decide)
      (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide)
      (by simp only [pointSeven, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)]
    rw [addOrderOf_pointSeven]
    exact not_or.mpr ⟨by decide,
      (some_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three_mod7).not.mpr (by decide)⟩

-- m = 4 on (0, 1, 2, 4) from (22, 1): both primes divide the denominator gcd (gcd = 35).
example : 5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧ 7 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
    Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  refine ⟨?_, ?_, by decide⟩
  · exact ladder_four.prime_dvd_gcd_of_addOrderOf_dvd (p := 5) (A := 0) (B := 1) (P := pointFive)
      (by decide) (by decide) (by rw [addOrderOf_pointFive]; decide)
      (by simp only [pointFive, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)
  · exact ladder_four.prime_dvd_gcd_of_addOrderOf_dvd (p := 7) (A := 0) (B := 1) (P := pointSeven)
      (by decide) (by decide) (by rw [addOrderOf_pointSeven])
      (by simp only [pointSeven, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)

-- At odd index m = 1, the seed (15, 1) reduces modulo 5 to the distinguished point (0, 0):
-- 5 divides the gcd through the P = twoTorsionPoint disjunct even though 2 does not divide 1.
example :
    let P₅ := twoTorsionPoint (0 : ZMod 5) (by decide : (1 : ZMod 5) ≠ 0)
    ¬ addOrderOf P₅ ∣ 1 ∧
      5 ∣ Nat.gcd (25 : ZMod 35).val 35 ∧
      ¬ 7 ∣ Nat.gcd (25 : ZMod 35).val 35 := by
  intro P₅
  have h1 : LadderRel (2 : ZMod 35) 4 ⟨15, 1⟩ 1 ⟨25, 25⟩ ⟨14, 25⟩ := by
    convert (LadderRel.zero (N := (2 : ZMod 35)) (D := 4) (S := ⟨15, 1⟩)).bit true
      using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  refine ⟨by rw [addOrderOf_twoTorsionPoint]; decide, ?_, ?_⟩
  · rw [h1.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint
      (p := 5) (A := 0) (B := 1) (P := P₅)
      (by decide) (by decide) (by decide) (by decide)
      (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide)
      (by simp only [P₅, coordinates_twoTorsionPoint, Pair.cross_def,
        Pair.map_x, Pair.map_z]; decide)]
    exact .inr rfl
  · rw [h1.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint
      (p := 7) (A := 0) (B := 1) (P := pointSeven)
      (by decide) (by decide) (by decide) (by decide)
      (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide)
      (by simp only [pointSeven, coordinates_some, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)]
    rw [addOrderOf_pointSeven]
    exact not_or.mpr ⟨by decide,
      (some_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three_mod7).not.mpr (by decide)⟩

-- Characteristic two (p = 2 dividing n = 6) is covered without any odd-prime restriction.
example : 2 ∣ Nat.gcd (2 : ZMod 6).val 6 := by
  have h1 : LadderRel (0 : ZMod 6) 1 ⟨2, 1⟩ 1 ⟨4, 2⟩ ⟨3, 2⟩ := by
    convert (LadderRel.zero (N := (0 : ZMod 6)) (D := 1) (S := ⟨2, 1⟩)).bit true
      using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  rw [h1.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint
    (p := 2) (A := 0) (B := 1) (P := twoTorsionPoint (0 : ZMod 2) (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide)
    (by simp only [coordinates_twoTorsionPoint, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)]
  exact .inr rfl

-- Two-stage ladder factor certificate on (A, B, N, D) = (1, 1, 3, 4) modulo 35 from (3, 1):
-- stage 1 at M = 2 misses both primes (gcd = 1), and stage 2 at q = 2 isolates 7.
private theorem nonsingular_three_two_mod7 :
    (model (1 : ZMod 7) 1).toAffine.Nonsingular 3 2 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff,
    model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
  decide

private noncomputable def stageTwoPointSeven : (model (1 : ZMod 7) 1).toAffine.Point :=
  .some 3 2 nonsingular_three_two_mod7

private theorem four_stageTwoPointSeven : (4 : ℕ) • stageTwoPointSeven = 0 := by
  have hd1 := double_cross_eq_zero_of_cross_eq_zero (N := (3 : ZMod 7)) (D := 4)
    (by decide) (Pair.cross_self (coordinates 1 1 stageTwoPointSeven))
  have hd2 := double_cross_eq_zero_of_cross_eq_zero (N := (3 : ZMod 7)) (D := 4) (by decide) hd1
  have heval : double (3 : ZMod 7) 4 (double 3 4 (coordinates 1 1 stageTwoPointSeven)) =
      ⟨4, 0⟩ := by
    ext <;> simp only [stageTwoPointSeven, coordinates_some, double_x, double_z] <;> decide
  rw [heval] at hd2
  have hfour : (4 : ℕ) • stageTwoPointSeven =
      (stageTwoPointSeven + stageTwoPointSeven) + (stageTwoPointSeven + stageTwoPointSeven) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    simp only [mul_nsmul, two_nsmul]
  rw [hfour]
  have hz : (coordinates 1 1
      ((stageTwoPointSeven + stageTwoPointSeven) +
        (stageTwoPointSeven + stageTwoPointSeven))).z = 0 := by
    have h4z : 4 * (coordinates 1 1
        ((stageTwoPointSeven + stageTwoPointSeven) +
          (stageTwoPointSeven + stageTwoPointSeven))).z = 0 := by
      simpa [Pair.cross_def] using hd2
    exact (mul_eq_zero.mp h4z).resolve_left (by decide)
  exact (coordinates_z_eq_zero_iff (by decide : (1 : ZMod 7) ≠ 0)).mp hz

example :
    Nat.gcd (9 : ZMod 35).val 35 = 1 ∧
    1 < Nat.gcd ([(⟨15, 14⟩ : Pair (ZMod 35)).cross ⟨1, 0⟩]).prod.val 35 ∧
    Nat.gcd ([(⟨15, 14⟩ : Pair (ZMod 35)).cross ⟨1, 0⟩]).prod.val 35 < 35 ∧
    Nat.gcd ([(⟨15, 14⟩ : Pair (ZMod 35)).cross ⟨1, 0⟩]).prod.val 35 = 7 := by
  have hs1a : LadderRel (3 : ZMod 35) 4 ⟨3, 1⟩ 1 ⟨1, 12⟩ ⟨11, 29⟩ := by
    convert (LadderRel.zero (N := (3 : ZMod 35)) (D := 4) (S := ⟨3, 1⟩)).bit true
      using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have hs1 : LadderRel (3 : ZMod 35) 4 ⟨3, 1⟩ 2 ⟨1, 9⟩ ⟨11, 13⟩ := by
    convert hs1a.bit false using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have hg1 : LadderRel (3 : ZMod 35) 4 ⟨1, 9⟩ 1 ⟨1, 9⟩ ⟨15, 14⟩ := by
    convert (LadderRel.zero (N := (3 : ZMod 35)) (D := 4) (S := ⟨1, 9⟩)).bit true
      using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have hg : LadderRel (3 : ZMod 35) 4 ⟨1, 9⟩ (1 * 2) ⟨15, 14⟩ ⟨1, 9⟩ := by
    convert hg1.bit false using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have hb : LadderRel (3 : ZMod 35) 4 ⟨1, 9⟩ 0 ⟨1, 0⟩ ⟨1, 9⟩ := .zero
  have hcert := hs1.one_lt_gcd_prod_cross_and_lt_of_addOrderOf_dvd_mul
    (p := 7) (r := 5) (A := 1) (B := 1) (q := 2) (i := 1) (w := 2) (j := 0)
    (P := stageTwoPointSeven) hg hb (by decide) (by decide)
    [(⟨15, 14⟩, ⟨1, 0⟩)] (by simp)
    (addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_stageTwoPointSeven)
    (.inl (by norm_num))
    (by simp only [stageTwoPointSeven, coordinates_some,
      Pair.cross_def, Pair.map_x, Pair.map_z]; decide)
    (by decide) (by decide)
    (by simp only [List.mem_singleton, forall_eq, Pair.cross_def, Pair.map_x, Pair.map_z]; decide)
  exact ⟨by decide, hcert.1, hcert.2, by simp only [Pair.cross_def, List.prod_singleton]; decide⟩

-- Suyama's polynomial seed (u³, v³) and polynomial doubling constants run in ZMod n without
-- divisions and feed directly into stage-1 ladder detection modulo any odd prime p | n.
example {n p m : ℕ} [Fact p.Prime] (hpn : p ∣ n) (h₂ : (2 : ZMod p) ≠ 0) (σ : ZMod n)
    (hB : suyamaB (ZMod.castHom hpn (ZMod p) σ) ≠ 0) {R T : Pair (ZMod n)}
    (hlad : LadderRel ((suyamaV σ - suyamaU σ) ^ 3 * (3 * suyamaU σ + suyamaV σ))
      (16 * suyamaU σ ^ 3 * suyamaV σ) ⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ m R T)
    (hm : addOrderOf (suyamaPoint h₂ hB) ∣ m) :
    p ∣ Nat.gcd R.z.val n := by
  let σp : ZMod p := ZMod.castHom hpn (ZMod p) σ
  have hσ : σp ≠ 0 := fun h0 ↦ suyamaV_ne_zero hB (by simp [σp, suyamaV_def, h0])
  have hu : σp ^ 2 ≠ 5 := by
    intro hu0
    have hU : suyamaU σp = 0 := by rw [suyamaU_def]; exact sub_eq_zero.mpr hu0
    have hX : suyamaX σp = 0 := by rw [suyamaX_def, hU]; simp
    exact hB (by rw [suyamaB_def, hX]; simp)
  have hND : 4 * ZMod.castHom hpn (ZMod p)
        ((suyamaV σ - suyamaU σ) ^ 3 * (3 * suyamaU σ + suyamaV σ)) =
      (suyamaA σp + 2) * ZMod.castHom hpn (ZMod p) (16 * suyamaU σ ^ 3 * suyamaV σ) := by
    simpa only [σp, suyamaU_def, suyamaV_def, map_mul, map_sub, map_add, map_pow, map_ofNat] using
      suyama_doubling_relation h₂ hσ hu
  have hmap : (⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair (ZMod n)).map (ZMod.castHom hpn (ZMod p)) =
      ⟨suyamaU σp ^ 3, suyamaV σp ^ 3⟩ := by
    ext <;> simp only [σp, Pair.map_x, Pair.map_z, suyamaU_def, suyamaV_def,
      map_pow, map_sub, map_mul, map_ofNat]
  have hSP : ((⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair (ZMod n)).map
      (ZMod.castHom hpn (ZMod p))).cross
      (coordinates (suyamaA σp) (suyamaB σp) (suyamaPoint h₂ hB)) = 0 := by
    rw [hmap]
    exact cross_coordinates_suyamaPoint h₂ hB
  exact hlad.prime_dvd_gcd_of_addOrderOf_dvd hpn hND hm hSP

end TauCeti.Montgomery
