/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.StageTwo.Product

/-!
# Examples of batched stage-2 detection

The distinguished point `T = (0, 0)` over `𝔽₇` is nonzero, but `[2]T = 0`.
With stage-1 multiplier `M = 1` and `q = 1 + 1 = 2`, the baby and giant steps are both `T`.
The representatives `(7, 1)` and `(0, 1)` modulo `35` give cross difference `7`.
A batch containing this entry and a unit cross difference detects a proper factor.
Adding a cross difference `5` instead masks both proper leaf gcds with product gcd `35`.
-/

public section

namespace TauCeti.Montgomery

local instance stageTwoProductPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private noncomputable def point : (model (0 : ZMod 7) 1).toAffine.Point :=
  twoTorsionPoint 0 (by decide)

private theorem coordinates_point : coordinates 0 1 point = ⟨0, 1⟩ := by
  rw [point, twoTorsionPoint_def, coordinates_some]

private def batch : List (Pair (ZMod 35) × Pair (ZMod 35)) :=
  [(⟨7, 1⟩, ⟨0, 1⟩), (⟨1, 0⟩, ⟨0, 1⟩)]

private theorem representatives_point :
    ((⟨7, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 point) = 0 ∧
      ((⟨0, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 point) = 0 := by
  rw [coordinates_point]
  simp only [Pair.cross_def, Pair.map_x, Pair.map_z]
  decide

-- Stage one has not annihilated T; the extra multiplier q = 2 does.
example : (1 : ℕ) • point ≠ 0 ∧ addOrderOf point ∣ 1 * 2 := by
  simp only [one_nsmul, one_mul, point, addOrderOf_twoTorsionPoint,
    twoTorsionPoint_ne_zero, ne_eq, not_false_eq_true, dvd_refl, and_self]

-- One detecting entry suffices: no hypotheses are imposed on the other entry.
example : 7 ∣ Nat.gcd (batch.map (Function.uncurry Pair.cross)).prod.val 35 := by
  apply prime_dvd_gcd_prod_cross_of_addOrderOf_dvd_mul (p := 7) (A := 0) (B := 1)
    (M := 1) (q := 2) (i := 1) (w := 1) (j := 1) (R := ⟨7, 1⟩) (S := ⟨0, 1⟩)
    (by decide) (by decide) point batch (by simp [batch])
  · simp [point, addOrderOf_twoTorsionPoint]
  · exact .inl (by norm_num)
  · simpa only [one_mul, one_zsmul, one_nsmul] using representatives_point.1
  · simpa only [one_zsmul, one_nsmul] using representatives_point.2

-- Every entry avoids 5, so the batch gcd is proper, not merely divisible by 7.
example : 1 < Nat.gcd (batch.map (Function.uncurry Pair.cross)).prod.val 35 ∧
    Nat.gcd (batch.map (Function.uncurry Pair.cross)).prod.val 35 < 35 := by
  refine one_lt_gcd_prod_cross_and_lt_of_addOrderOf_dvd_mul (p := 7) (A := 0) (B := 1)
    (M := 1) (q := 2) (i := 1) (w := 1) (j := 1) (R := ⟨7, 1⟩) (S := ⟨0, 1⟩)
    (by decide) (by decide) point batch (by simp [batch])
    (by simp [point, addOrderOf_twoTorsionPoint]) (.inl (by norm_num)) ?_ ?_
    (by decide : Nat.Prime 5) (by decide) ?_
  · simpa only [one_mul, one_zsmul, one_nsmul] using representatives_point.1
  · simpa only [one_zsmul, one_nsmul] using representatives_point.2
  · intro T hT
    simp only [batch, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl <;>
      simp only [Pair.cross_def, Pair.map_x, Pair.map_z] <;> decide

-- The empty batch has no detecting entry, and its gcd is one.
example : Nat.gcd
    (([] : List (Pair (ZMod 35) × Pair (ZMod 35))).map
      (Function.uncurry Pair.cross)).prod.val 35 = 1 := by
  decide

-- Different leaves can detect different primes, giving the inconclusive product gcd n.
example :
    Nat.gcd ((⟨7, 1⟩ : Pair (ZMod 35)).cross ⟨0, 1⟩).val 35 = 7 ∧
    Nat.gcd ((⟨5, 1⟩ : Pair (ZMod 35)).cross ⟨0, 1⟩).val 35 = 5 ∧
    Nat.gcd
      (([(⟨7, 1⟩, ⟨0, 1⟩), (⟨5, 1⟩, ⟨0, 1⟩)] :
        List (Pair (ZMod 35) × Pair (ZMod 35))).map
          (Function.uncurry Pair.cross)).prod.val 35 = 35 := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Function.uncurry_apply_pair, Pair.cross_def]
  decide

end TauCeti.Montgomery
