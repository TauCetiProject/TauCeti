/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection

/-!
# Examples of Montgomery reduction and stage-1 detection

Modulo `35` with `(A, B, N, D) = (0, 1, 2, 4)`, the starting pair `(22, 1)` reduces to `(2, 1)`
modulo `5` (representing the two-torsion point `(2, 0)` of order `2`) and to `(1, 1)` modulo `7`
(representing `(1, 3)` of order `4`). Running the binary ladder from `(22, 1)` exhibits all three
gcd outcomes on a single curve:

* `m = 2 = (2 : ℕ).lcmUpto` gives `(21, 30)` with `gcd(30, 35) = 5`, a proper factor certified by
  `LadderRel.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd`;
* `m = 3` gives `(9, 2)` with `gcd(2, 35) = 1`, where `LadderRel.prime_dvd_gcd_iff_addOrderOf_dvd`
  shows neither `5` nor `7` divides the gcd;
* `m = 4` gives `(29, 0)` with `gcd(0, 35) = 35`, where both orders divide `4`.

Additional checks verify compatibility of `double` and ring subtraction with `ZMod.castHom`,
non-existence of `ZMod 35 →+* ZMod 3`, powersmoothness versus prime-divisor smoothness (`4` does
not divide `Nat.lcmUpto 3 = 6`), and prime-power gcds modulo `9`.
-/

namespace TauCeti.Montgomery

open WeierstrassCurve

/-! ### Reduction checks along `ZMod.castHom` -/

-- (22, 1) modulo 35 reduces to (2, 1) modulo 5 and (1, 1) modulo 7, and doubling commutes.
example :
    let φ₅ := ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)
    let φ₇ := ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)
    let S : Pair (ZMod 35) := ⟨22, 1⟩
    S.map φ₅ = ⟨2, 1⟩ ∧ S.map φ₇ = ⟨1, 1⟩ ∧
      (double 2 4 S).map φ₅ = double 2 4 ⟨2, 1⟩ ∧ (double 2 4 S).map φ₅ = ⟨1, 0⟩ ∧
      (double 2 4 S).map φ₇ = double 2 4 ⟨1, 1⟩ ∧ (double 2 4 S).map φ₇ = ⟨0, 4⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (ext <;> simp only [map_double, Pair.map_x, Pair.map_z,
    double_x, double_z] <;> decide)

-- Ring subtraction in ZMod 35 commutes with reduction, unlike truncated natural subtraction.
example :
    let φ₅ := ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)
    let φ₇ := ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)
    (3 : ZMod 35) - 5 = 33 ∧ φ₅ ((3 : ZMod 35) - 5) = -2 ∧ φ₇ ((3 : ZMod 35) - 5) = -2 ∧
      φ₅ (((3 - 5 : ℕ) : ZMod 35)) = 0 ∧ φ₅ (((3 - 5 : ℕ) : ZMod 35)) ≠ -2 := by
  decide

-- ZMod.castHom requires divisibility rather than primality, and no ring hom ZMod 35 →+* ZMod 3
-- exists because 3 does not divide 35.
example :
    Nonempty (ZMod 35 →+* ZMod 5) ∧ Nonempty (ZMod 9 →+* ZMod 3) ∧
      IsEmpty (ZMod 35 →+* ZMod 3) := by
  refine ⟨⟨ZMod.castHom (by decide) (ZMod 5)⟩, ⟨ZMod.castHom (by decide) (ZMod 3)⟩, ⟨fun f ↦ ?_⟩⟩
  have h35 : f (35 : ℕ) = 0 := by
    have h0 : ((35 : ℕ) : ZMod 35) = 0 := by decide
    rw [h0, map_zero]
  rw [map_natCast] at h35
  exact absurd h35 (by decide)

/-! ### Binary-ladder gcd outcomes from `(22, 1)` modulo `35` -/

-- At m = 2 = (2 : ℕ).lcmUpto, (2, 0) mod 5 (order 2 ≤ 2) is annihilated while (1, 3) mod 7
-- (order 4) is not, certifying a proper factor gcd(30, 35) = 5.
example : (1 < Nat.gcd (30 : ZMod 35).val 35 ∧ Nat.gcd (30 : ZMod 35).val 35 < 35) ∧
    Nat.gcd (30 : ZMod 35).val 35 = 5 := by
  refine ⟨?_, by decide⟩
  have hND5 : 4 * ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) (2 : ZMod 35) =
      (0 + 2) * ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) 4 := by decide
  have hD7 : ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) (4 : ZMod 35) ≠ 0 := by decide
  have hND7 : 4 * ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) (2 : ZMod 35) =
      (0 + 2) * ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) 4 := by decide
  have hS5 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) =
      ⟨2, 1⟩ := by ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have hS7 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) =
      ⟨1, 1⟩ := by ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have hSnz7 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) ≠
      0 := by rw [hS7, Pair.ne_zero_iff]; decide
  have hndvd7 : ¬ (4 : ℕ) ∣ (2 : ℕ).lcmUpto := by rw [Nat.lcmUpto_two]; decide
  have h₁ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 1 ⟨11, 18⟩ ⟨21, 25⟩ := by
    convert (LadderRel.zero (N := (2 : ZMod 35)) (D := 4) (S := ⟨22, 1⟩)).bit true using 1
    · rfl
    · simp only [↓reduceIte]; ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
    · simp only [↓reduceIte]; ext <;> simp only [double_x, double_z] <;> decide
  have h₂ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ (2 : ℕ).lcmUpto ⟨21, 30⟩ ⟨9, 2⟩ := by
    rw [Nat.lcmUpto_two]
    convert h₁.bit false using 1
    · rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]; ext <;> simp only [double_x, double_z] <;> decide
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hns5 : (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]; decide +revert
  have hns7 : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]; decide +revert
  let P5 : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 hns5
  have hord5 : addOrderOf P5 = 2 := addOrderOf_eq_prime
    (by rw [two_nsmul]; exact Affine.Point.add_self_of_Y_eq (by
      simp only [Affine.negY, model_a₁, model_a₃]; ring)) (Affine.Point.some_ne_zero _)
  let P7 : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 hns7
  have h2P7 : P7 + P7 = twoTorsionPoint 0 one_ne_zero :=
    (add_self_eq_twoTorsionPoint_iff one_ne_zero hns7).mpr rfl
  have hord7 : addOrderOf P7 = 4 := addOrderOf_eq_prime_pow (p := 2) (n := 1)
    (by rw [pow_one, two_nsmul, h2P7]; exact twoTorsionPoint_ne_zero 0 one_ne_zero)
    (by change (2 * 2 : ℕ) • P7 = 0; simp only [mul_nsmul, two_nsmul, h2P7,
      twoTorsionPoint_add_self])
  exact h₂.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd (by decide) hND5
    (P := P5) (by rw [hS5]; simp only [P5, coordinates_some, Pair.cross_def]; ring)
    (by rw [hord5, Nat.lcmUpto_two]) (by decide) one_ne_zero hD7 hND7 hSnz7
    (Q := P7) (by rw [hS7]; simp only [P7, coordinates_some, Pair.cross_def]; ring)
    ((some_eq_twoTorsionPoint_iff one_ne_zero hns7).not.mpr one_ne_zero) (by rwa [hord7])

-- At m = 3, neither 2 nor 4 divides 3, so neither 5 nor 7 divides gcd(2, 35) = 1.
example : (¬ 5 ∣ Nat.gcd (2 : ZMod 35).val 35 ∧ ¬ 7 ∣ Nat.gcd (2 : ZMod 35).val 35) ∧
    Nat.gcd (2 : ZMod 35).val 35 = 1 := by
  refine ⟨?_, by decide⟩
  have hD5 : ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) (4 : ZMod 35) ≠ 0 := by decide
  have hND5 : 4 * ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) (2 : ZMod 35) =
      (0 + 2) * ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) 4 := by decide
  have hD7 : ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) (4 : ZMod 35) ≠ 0 := by decide
  have hND7 : 4 * ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) (2 : ZMod 35) =
      (0 + 2) * ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) 4 := by decide
  have hS5 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) =
      ⟨2, 1⟩ := by ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have hS7 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) =
      ⟨1, 1⟩ := by ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have hSnz5 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) ≠
      0 := by rw [hS5, Pair.ne_zero_iff]; decide
  have hSnz7 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) ≠
      0 := by rw [hS7, Pair.ne_zero_iff]; decide
  have h2ne0 : (2 : ZMod 5) ≠ 0 := by decide
  have h2ndvd3 : ¬ (2 : ℕ) ∣ 3 := by decide
  have h4ndvd3 : ¬ (4 : ℕ) ∣ 3 := by decide
  have h₁ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 1 ⟨11, 18⟩ ⟨21, 25⟩ := by
    convert (LadderRel.zero (N := (2 : ZMod 35)) (D := 4) (S := ⟨22, 1⟩)).bit true using 1
    · rfl
    · simp only [↓reduceIte]; ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
    · simp only [↓reduceIte]; ext <;> simp only [double_x, double_z] <;> decide
  have h₃ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 3 ⟨9, 2⟩ ⟨9, 0⟩ := by
    convert h₁.bit true using 1
    · rfl
    · simp only [↓reduceIte]; ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
    · simp only [↓reduceIte]; ext <;> simp only [double_x, double_z] <;> decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hns5 : (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]; decide +revert
  have hns7 : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]; decide +revert
  let P5 : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 hns5
  have hord5 : addOrderOf P5 = 2 := addOrderOf_eq_prime
    (by rw [two_nsmul]; exact Affine.Point.add_self_of_Y_eq (by
      simp only [Affine.negY, model_a₁, model_a₃]; ring)) (Affine.Point.some_ne_zero _)
  let P7 : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 hns7
  have h2P7 : P7 + P7 = twoTorsionPoint 0 one_ne_zero :=
    (add_self_eq_twoTorsionPoint_iff one_ne_zero hns7).mpr rfl
  have hord7 : addOrderOf P7 = 4 := addOrderOf_eq_prime_pow (p := 2) (n := 1)
    (by rw [pow_one, two_nsmul, h2P7]; exact twoTorsionPoint_ne_zero 0 one_ne_zero)
    (by change (2 * 2 : ℕ) • P7 = 0; simp only [mul_nsmul, two_nsmul, h2P7,
      twoTorsionPoint_add_self])
  exact ⟨(h₃.prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero hD5 hND5 hSnz5
      (P := P5) (by rw [hS5]; simp only [P5, coordinates_some, Pair.cross_def]; ring)
      ((some_eq_twoTorsionPoint_iff one_ne_zero hns5).not.mpr h2ne0)).not.mpr (by rwa [hord5]),
    (h₃.prime_dvd_gcd_iff_addOrderOf_dvd (by decide) one_ne_zero hD7 hND7 hSnz7
      (P := P7) (by rw [hS7]; simp only [P7, coordinates_some, Pair.cross_def]; ring)
      ((some_eq_twoTorsionPoint_iff one_ne_zero hns7).not.mpr one_ne_zero)).not.mpr
      (by rwa [hord7])⟩

-- At m = 4, both orders 2 and 4 divide 4, so both 5 and 7 divide gcd(0, 35) = 35.
example : (5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧ 7 ∣ Nat.gcd (0 : ZMod 35).val 35) ∧
    Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  refine ⟨?_, by decide⟩
  have hND5 : 4 * ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) (2 : ZMod 35) =
      (0 + 2) * ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) 4 := by decide
  have hND7 : 4 * ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) (2 : ZMod 35) =
      (0 + 2) * ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) 4 := by decide
  have hS5 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) =
      ⟨2, 1⟩ := by ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have hS7 : (Pair.mk (22 : ZMod 35) 1).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) =
      ⟨1, 1⟩ := by ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have h2dvd4 : (2 : ℕ) ∣ 4 := by decide
  have h₁ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 1 ⟨11, 18⟩ ⟨21, 25⟩ := by
    convert (LadderRel.zero (N := (2 : ZMod 35)) (D := 4) (S := ⟨22, 1⟩)).bit true using 1
    · rfl
    · simp only [↓reduceIte]; ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
    · simp only [↓reduceIte]; ext <;> simp only [double_x, double_z] <;> decide
  have h₂ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 2 ⟨21, 30⟩ ⟨9, 2⟩ := by
    convert h₁.bit false using 1
    · rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]; ext <;> simp only [double_x, double_z] <;> decide
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have h₄ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 4 ⟨29, 0⟩ ⟨29, 22⟩ := by
    convert h₂.bit false using 1
    · rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]; ext <;> simp only [double_x, double_z] <;> decide
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hns5 : (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]; decide +revert
  have hns7 : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]; decide +revert
  let P5 : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 hns5
  have hord5 : addOrderOf P5 = 2 := addOrderOf_eq_prime
    (by rw [two_nsmul]; exact Affine.Point.add_self_of_Y_eq (by
      simp only [Affine.negY, model_a₁, model_a₃]; ring)) (Affine.Point.some_ne_zero _)
  let P7 : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 hns7
  have h2P7 : P7 + P7 = twoTorsionPoint 0 one_ne_zero :=
    (add_self_eq_twoTorsionPoint_iff one_ne_zero hns7).mpr rfl
  have hord7 : addOrderOf P7 = 4 := addOrderOf_eq_prime_pow (p := 2) (n := 1)
    (by rw [pow_one, two_nsmul, h2P7]; exact twoTorsionPoint_ne_zero 0 one_ne_zero)
    (by change (2 * 2 : ℕ) • P7 = 0; simp only [mul_nsmul, two_nsmul, h2P7,
      twoTorsionPoint_add_self])
  exact ⟨h₄.prime_dvd_gcd_of_addOrderOf_dvd (by decide) hND5
      (P := P5) (by rw [hS5]; simp only [P5, coordinates_some, Pair.cross_def]; ring)
      (by rwa [hord5]),
    h₄.prime_dvd_gcd_of_addOrderOf_dvd (by decide) hND7
      (P := P7) (by rw [hS7]; simp only [P7, coordinates_some, Pair.cross_def]; ring)
      (by rw [hord7])⟩

/-! ### Powersmoothness and representative-level checks -/

-- Stage-1 powersmooth detection at B₁ = 2 via prime_dvd_gcd_lcmUpto_of_addOrderOf_le.
example : 5 ∣ Nat.gcd (25 : ZMod 35).val 35 := by
  have hU : (Pair.mk (21 : ZMod 35) 25).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)) =
      ⟨1, 0⟩ := by ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply prime_dvd_gcd_lcmUpto_of_addOrderOf_le (n := 35) (p := 5) (B₁ := 2) (A := 0) (B := 1)
    (by decide +revert) (twoTorsionPoint 0 one_ne_zero) ⟨21, 25⟩
  · rw [addOrderOf_twoTorsionPoint]
  · rw [Nat.lcmUpto_two, two_nsmul, twoTorsionPoint_add_self, coordinates_zero, hU, Pair.cross_def]
    ring

-- Over ZMod 7, (1, 3) has order 4: its only prime divisor is 2 ≤ 3, yet neither M(2) = 2 nor
-- M(3) = 6 annihilates it, whereas M(4) = 12 does.
example [Fact (Nat.Prime 7)] :
    ∃ P7 : (model (0 : ZMod 7) 1).toAffine.Point,
      ¬ addOrderOf P7 ∣ Nat.lcmUpto 2 ∧ ¬ addOrderOf P7 ∣ Nat.lcmUpto 3 ∧
        addOrderOf P7 ∣ Nat.lcmUpto 4 := by
  have hdiv : ¬ (4 : ℕ) ∣ Nat.lcmUpto 2 ∧ ¬ (4 : ℕ) ∣ Nat.lcmUpto 3 ∧
      (4 : ℕ) ∣ Nat.lcmUpto 4 := by decide +revert
  have hns7 : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
      model_a₄, model_a₆]; decide +revert
  let P7 : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 hns7
  have h2P7 : P7 + P7 = twoTorsionPoint 0 one_ne_zero :=
    (add_self_eq_twoTorsionPoint_iff one_ne_zero hns7).mpr rfl
  have hord7 : addOrderOf P7 = 4 := addOrderOf_eq_prime_pow (p := 2) (n := 1)
    (by rw [pow_one, two_nsmul, h2P7]; exact twoTorsionPoint_ne_zero 0 one_ne_zero)
    (by change (2 * 2 : ℕ) • P7 = 0; simp only [mul_nsmul, two_nsmul, h2P7,
      twoTorsionPoint_add_self])
  exact ⟨P7, by rwa [hord7]⟩

-- Proper prime-power gcds do not require two distinct prime divisors.
example : Nat.gcd (3 : ZMod 9).val 9 = 3 ∧
    ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (3 : ZMod 9) =
      ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (0 : ZMod 9) := by
  decide

-- The gcd/reduction bridge also includes modulus zero and negative integers.
example : 5 ∣ Nat.gcd (-15 : ZMod 0).val 0 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [ZMod.dvd_gcd_val_iff_castHom_eq_zero _ (dvd_zero 5)]
  decide +revert

end TauCeti.Montgomery
