/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder.Detection
import TauCeti.NumberTheory.LcmUpto

/-!
# Examples of binary Montgomery-ladder stage-1 detection

Over `ZMod 35` with `(A, B, N, D) = (0, 1, 2, 4)` and starting pair `(22, 1)`, the curve
`y² = x³ + x` reduces modulo `5` with point `P₅ = (2, 0)` of additive order `2` and modulo `7`
with point `P₇ = (1, 3)` of additive order `4`. Neither point is the distinguished two-torsion
point `(0, 0)`, so `LadderRel.prime_dvd_gcd_iff_addOrderOf_dvd` characterizes divisibility of
`Nat.gcd U.z.val 35` for every index `m` and every derivation `LadderRel 2 4 ⟨22, 1⟩ m U V`:
`5` divides the gcd iff `2 ∣ m`, and `7` divides the gcd iff `4 ∣ m`.

This single curve realizes all three stage-1 gcd outcomes:
* odd `m` (such as `m = 3`) yields `gcd = 1` (no factor found);
* `2 ∣ m` with `¬ 4 ∣ m` (such as `m = 2 = Nat.lcmUpto 2` and `m = 6 = Nat.lcmUpto 3`) yields
  `gcd = 5`, certified as a proper factor by
  `LadderRel.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd`;
* `4 ∣ m` (such as `m = 4` and `m = 12 = Nat.lcmUpto 4`) yields `gcd = 35` (simultaneous
  annihilation modulo both primes).

The file also exhibits explicit binary ladder derivations for `m = 2, 3, 4`, verifies the
pair-level order-mismatch certificate on `(21, 25)` and `diffAdd (21, 25) (22, 1) (22, 1) = (1, 8)`,
exercises projective point-count detection over `ZMod 5`, and records a negative control at the
distinguished two-torsion point `(0, 0)` showing why `P ≠ twoTorsionPoint A hB` cannot be dropped
from the equivalence.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

local instance ladderDetectionPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance ladderDetectionPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem nonsingular_two_zero_five :
    (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointFive : (model (0 : ZMod 5) 1).toAffine.Point :=
  .some 2 0 nonsingular_two_zero_five

private theorem two_pointFive : (2 : ℕ) • pointFive = 0 := by
  rw [two_nsmul, pointFive, Affine.Point.add_self_of_Y_eq]
  simp only [Affine.negY, model_a₁, model_a₃]
  decide

private theorem addOrderOf_pointFive : addOrderOf pointFive = 2 := by
  refine addOrderOf_eq_prime two_pointFive ?_
  exact Affine.Point.some_ne_zero nonsingular_two_zero_five

private theorem pointFive_ne_twoTorsionPoint :
    pointFive ≠ twoTorsionPoint 0 (by decide) := by
  rw [pointFive, ne_eq, some_eq_twoTorsionPoint_iff (by decide)]
  decide

private theorem nonsingular_one_three_seven :
    (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 3 nonsingular_one_three_seven

private theorem pointSeven_double : pointSeven + pointSeven = twoTorsionPoint 0 (by decide) :=
  (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three_seven).mpr (by decide)

private theorem four_pointSeven : (4 : ℕ) • pointSeven = 0 := by
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  simp only [h4, mul_nsmul, two_nsmul, pointSeven_double, twoTorsionPoint_add_self]

private theorem addOrderOf_pointSeven : addOrderOf pointSeven = 4 := by
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ four_pointSeven
  rw [pow_one, two_nsmul, pointSeven_double]
  exact twoTorsionPoint_ne_zero 0 (by decide)

private theorem pointSeven_ne_twoTorsionPoint :
    pointSeven ≠ twoTorsionPoint 0 (by decide) := by
  rw [pointSeven, ne_eq, some_eq_twoTorsionPoint_iff (by decide)]
  decide

private theorem five_dvd_gcd_iff {m : ℕ} {U V : Pair (ZMod 35)}
    (h : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ m U V) :
    5 ∣ Nat.gcd U.z.val 35 ↔ 2 ∣ m := by
  rw [← addOrderOf_pointFive]
  refine h.prime_dvd_gcd_iff_addOrderOf_dvd (p := 5) (A := 0) (B := 1) (by decide)
    (by decide) (by decide) (by decide) (by decide) pointFive
    (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide) ?_
    pointFive_ne_twoTorsionPoint
  rw [pointFive, coordinates_some, Pair.cross_def]
  simp only [Pair.map_x, Pair.map_z]
  decide

private theorem seven_dvd_gcd_iff {m : ℕ} {U V : Pair (ZMod 35)}
    (h : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ m U V) :
    7 ∣ Nat.gcd U.z.val 35 ↔ 4 ∣ m := by
  rw [← addOrderOf_pointSeven]
  refine h.prime_dvd_gcd_iff_addOrderOf_dvd (p := 7) (A := 0) (B := 1) (by decide)
    (by decide) (by decide) (by decide) (by decide) pointSeven
    (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide) ?_
    pointSeven_ne_twoTorsionPoint
  rw [pointSeven, coordinates_some, Pair.cross_def]
  simp only [Pair.map_x, Pair.map_z]
  decide

private theorem gcd_35_trichotomy {g : ℕ} (hg : g ∣ 35) :
    (¬ 5 ∣ g → ¬ 7 ∣ g → g = 1) ∧
    (5 ∣ g → ¬ 7 ∣ g → g = 5) ∧
    (5 ∣ g → 7 ∣ g → g = 35) := by
  have hle : g ≤ 35 := Nat.le_of_dvd (by decide) hg
  have hall : ∀ k ≤ 35, k ∣ 35 → k = 1 ∨ k = 5 ∨ k = 7 ∨ k = 35 := by decide
  rcases hall g hle hg with rfl | rfl | rfl | rfl <;> decide

-- Universal trichotomy across all multipliers `m` and all binary ladder derivations from `(22, 1)`:
-- odd `m` gives `gcd = 1`; `2 ∣ m` with `¬ 4 ∣ m` gives `gcd = 5`; `4 ∣ m` gives `gcd = 35`.
example {m : ℕ} {U V : Pair (ZMod 35)} (h : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ m U V) :
    (¬ 2 ∣ m → Nat.gcd U.z.val 35 = 1) ∧
    (2 ∣ m → ¬ 4 ∣ m → Nat.gcd U.z.val 35 = 5) ∧
    (4 ∣ m → Nat.gcd U.z.val 35 = 35) := by
  have h5 := five_dvd_gcd_iff h
  have h7 := seven_dvd_gcd_iff h
  have htri := gcd_35_trichotomy (Nat.gcd_dvd_right U.z.val 35)
  refine ⟨fun h2 ↦ htri.1 (h5.not.mpr h2) (h7.not.mpr fun h4 ↦ h2 (dvd_trans (by decide) h4)),
    fun h2 h4 ↦ htri.2.1 (h5.mpr h2) (h7.not.mpr h4),
    fun h4 ↦ htri.2.2 (h5.mpr (dvd_trans (by decide) h4)) (h7.mpr h4)⟩

-- Stage-1 powersmooth multipliers on the same curve:
-- `B₁ = 2` (`M(2) = 2`) and `B₁ = 3` (`M(3) = 6`) both certify a proper factor (`gcd = 5`),
-- whereas `B₁ = 4` (`M(4) = 12`) annihilates both primes (`gcd = 35`).
example {U₂ V₂ U₃ V₃ U₄ V₄ : Pair (ZMod 35)}
    (h₂ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ (Nat.lcmUpto 2) U₂ V₂)
    (h₃ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ (Nat.lcmUpto 3) U₃ V₃)
    (h₄ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ (Nat.lcmUpto 4) U₄ V₄) :
    (1 < Nat.gcd U₂.z.val 35 ∧ Nat.gcd U₂.z.val 35 < 35) ∧
    (1 < Nat.gcd U₃.z.val 35 ∧ Nat.gcd U₃.z.val 35 < 35) ∧
    Nat.gcd U₄.z.val 35 = 35 := by
  have hcert {m : ℕ} {U V : Pair (ZMod 35)} (h : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ m U V)
      (h2 : 2 ∣ m) (h4 : ¬ 4 ∣ m) :
      1 < Nat.gcd U.z.val 35 ∧ Nat.gcd U.z.val 35 < 35 := by
    refine h.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd (p := 5) (A := 0) (B := 1)
      (by decide) (by decide) pointFive (by rw [addOrderOf_pointFive]; exact h2) ?_
      (q := 7) (A' := 0) (B' := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      pointSeven (by rw [addOrderOf_pointSeven]; exact h4)
      (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide) ?_
      pointSeven_ne_twoTorsionPoint
    · rw [pointFive, coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
    · rw [pointSeven, coordinates_some, Pair.cross_def]
      simp only [Pair.map_x, Pair.map_z]
      decide
  refine ⟨hcert h₂ (by decide) (by decide), hcert h₃ (by decide) (by decide), ?_⟩
  have htri := gcd_35_trichotomy (Nat.gcd_dvd_right U₄.z.val 35)
  exact htri.2.2 ((five_dvd_gcd_iff h₄).mpr (by decide)) ((seven_dvd_gcd_iff h₄).mpr (by decide))

-- Explicit binary ladder derivations over `ZMod 35` for `m = 2, 3, 4` realizing the three gcd
-- outcomes `5`, `1`, and `35` on one curve.
example :
    (∃ V, LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 2 ⟨21, 30⟩ V) ∧ Nat.gcd (30 : ZMod 35).val 35 = 5 ∧
    (∃ V, LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 3 ⟨9, 2⟩ V) ∧ Nat.gcd (2 : ZMod 35).val 35 = 1 ∧
    (∃ V, LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 4 ⟨29, 0⟩ V) ∧ Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  have h₁ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 1 ⟨11, 18⟩ ⟨21, 25⟩ := by
    convert (LadderRel.zero (N := (2 : ZMod 35)) (D := 4) (S := ⟨22, 1⟩)).bit true using 1 <;>
      norm_num
    · ext <;> norm_num [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
    · ext <;> norm_num [double_x, double_z] <;> decide
  have h₂ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 2 ⟨21, 30⟩ ⟨9, 2⟩ := by
    convert h₁.bit false using 1 <;> norm_num
    · ext <;> norm_num [double_x, double_z] <;> decide
    · ext <;> norm_num [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  have h₃ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 3 ⟨9, 2⟩ ⟨9, 0⟩ := by
    convert h₁.bit true using 1 <;> norm_num
    · ext <;> norm_num [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
    · ext <;> norm_num [double_x, double_z] <;> decide
  have h₄ : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 4 ⟨29, 0⟩ ⟨29, 22⟩ := by
    convert h₂.bit false using 1 <;> norm_num
    · ext <;> norm_num [double_x, double_z] <;> decide
    · ext <;> norm_num [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  exact ⟨⟨_, h₂⟩, by decide, ⟨_, h₃⟩, by decide, ⟨_, h₄⟩, by decide⟩

-- Pair-level order-mismatch certificate on `(21, 25)` at `m = 2`:
-- `addOrderOf P₅ = 2 ∣ 2` detects `5`, while `addOrderOf P₇ = 4 ∤ 2` certifies `¬ 7 ∣ gcd`,
-- and the next odd step `diffAdd (21, 25) (22, 1) (22, 1) = (1, 8)` has `gcd(8, 35) = 1`
-- representing `[3]P₅ = P₅` over `ZMod 5` and `[3]P₇ = -P₇` over `ZMod 7`.
example :
    (1 < Nat.gcd (25 : ZMod 35).val 35 ∧ Nat.gcd (25 : ZMod 35).val 35 < 35) ∧
    diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ ∧
    Nat.gcd (8 : ZMod 35).val 35 = 1 ∧
    ((Pair.mk (1 : ZMod 35) 8).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
      (coordinates 0 1 ((3 : ℕ) • pointFive)) = 0 ∧
    ((Pair.mk (1 : ZMod 35) 8).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
      (coordinates 0 1 ((3 : ℕ) • pointSeven)) = 0 := by
  have h25_5 :
      ((Pair.mk (21 : ZMod 35) 25).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
        (coordinates 0 1 ((2 : ℕ) • pointFive)) = 0 := by
    rw [two_pointFive, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  have h25_7 :
      ((Pair.mk (21 : ZMod 35) 25).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 ((2 : ℕ) • pointSeven)) = 0 := by
    rw [two_nsmul, pointSeven_double, coordinates_twoTorsionPoint, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  have h3_5 : (3 : ℕ) • pointFive = pointFive := by
    simpa [two_pointFive] using succ_nsmul pointFive 2
  have h3_7 : (3 : ℕ) • pointSeven = -pointSeven := by
    apply eq_neg_of_add_eq_zero_left
    rw [← succ_nsmul, four_pointSeven]
  refine ⟨?_, by ext <;> norm_num [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide, by decide,
    ?_, ?_⟩
  · refine one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd (n := 35) (p := 5) (m := 2)
      (A := 0) (B := 1) (by decide) pointFive ⟨21, 25⟩ (by rw [addOrderOf_pointFive]) h25_5
      (q := 7) (A' := 0) (B' := 1) (by decide) (by decide) pointSeven
      (by rw [addOrderOf_pointSeven]; decide)
      (by simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z]; decide) h25_7
  · rw [h3_5, pointFive, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [h3_7, coordinates_neg, pointSeven, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Projective point-count detection over `ZMod 5`: `model 0 1` is elliptic with `pointCount = 4`,
-- so `LadderRel.prime_dvd_gcd_of_pointCount_dvd` detects `5` at `m = Nat.lcmUpto 4 = 12` without
-- determining `addOrderOf pointFive`.
example {U V : Pair (ZMod 35)} (h : LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ (Nat.lcmUpto 4) U V) :
    5 ∣ Nat.gcd U.z.val 35 := by
  have : (model (0 : ZMod 5) 1).IsElliptic :=
    (isElliptic_model_iff_ne_zero (A := (0 : ZMod 5)) (B := 1)).mpr (by decide)
  have hcount : (model (0 : ZMod 5) 1).pointCount = 4 := by
    rw [WeierstrassCurve.pointCount_def,
      Nat.card_congr (Equiv.subtypeEquivRight
        (q := fun xy : ZMod 5 × ZMod 5 ↦ xy.2 ^ 2 = xy.1 ^ 3 + xy.1)
        fun xy ↦ by rw [Affine.equation_iff]; simp),
      Nat.card_eq_fintype_card]
    decide
  refine h.prime_dvd_gcd_of_pointCount_dvd (p := 5) (A := 0) (B := 1) (by decide) (by decide)
    pointFive (by rw [hcount]; decide) ?_
  rw [pointFive, coordinates_some, Pair.cross_def]
  simp only [Pair.map_x, Pair.map_z]
  decide

-- Negative control and forward generality at the distinguished two-torsion point `(0, 0)`:
-- at `m = 1`, a one-bit ladder derivation produces the zero raw pair, so `5 ∣ gcd(0, 35)` holds
-- even though `2 ∤ 1` (showing `P ≠ twoTorsionPoint A hB` cannot be dropped from
-- `LadderRel.prime_dvd_gcd_iff_addOrderOf_dvd`). By contrast, forward detection via
-- `LadderRel.prime_dvd_gcd_of_addOrderOf_dvd` still applies at `(0, 0)` for every even index.
example :
    LadderRel (2 : ZMod 35) 4 ⟨0, 1⟩ 1 0 ⟨4, 0⟩ ∧
    5 ∣ Nat.gcd (0 : Pair (ZMod 35)).z.val 35 ∧
    ¬ addOrderOf (twoTorsionPoint (0 : ZMod 5) (B := 1) (by decide)) ∣ 1 := by
  refine ⟨?_, by decide, by rw [addOrderOf_twoTorsionPoint]; decide⟩
  convert (LadderRel.zero (N := (2 : ZMod 35)) (D := 4) (S := ⟨0, 1⟩)).bit true using 1 <;>
    norm_num
  ext <;> norm_num [diffAdd_x, diffAdd_z, Pair.cross_def]

example {U V : Pair (ZMod 35)} (h : LadderRel (2 : ZMod 35) 4 ⟨0, 1⟩ 2 U V) :
    5 ∣ Nat.gcd U.z.val 35 := by
  refine h.prime_dvd_gcd_of_addOrderOf_dvd (p := 5) (A := 0) (B := 1) (by decide) (by decide)
    (twoTorsionPoint 0 (by decide)) (by rw [addOrderOf_twoTorsionPoint]) ?_
  rw [coordinates_twoTorsionPoint, Pair.cross_def]
  simp only [Pair.map_x, Pair.map_z]
  decide

end TauCeti.Montgomery
