/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Pair
import Mathlib.Data.ZMod.Basic

/-!
# Examples of raw projective pairs

Over `ℚ`, the pairs `(2, 4)` and `(1, 2)` have cross difference `2 · 2 - 1 · 4 = 0`, differ by
the scalar `2`, and define the same point of the projective line.

The zero pair `(0, 0)` has vanishing cross difference with every pair. In particular `(1, 0)`
and `(0, 1)`, which stand for infinity and for `0` and have cross difference `1`, are both
related to `(0, 0)`: vanishing of the cross difference is not transitive through the zero pair,
which is why `Pair.cross_eq_zero_trans` asks for a nonzero middle pair and why `(0, 0)` is not a
point of the projective line.

Over `ZMod 15`, scaling `(1, 1)` by the non-unit `5` gives `(5, 5)`. Its cross difference with
`(1, 1)` vanishes, yet its reduction modulo `5` is the zero pair while that of `(1, 1)` is not:
over a ring, projective equivalence of raw pairs is scaling by a unit, which preserves vanishing
cross differences by `Pair.smul_cross_eq_zero_iff` and reduces to a unit modulo every prime
divisor. Scaling `(1, 1)` by the unit `2` keeps its reduction modulo `5` nonzero.
-/

namespace TauCeti.Montgomery

/-! ### Proportional pairs over `ℚ` -/

-- `(2, 4)` and `(1, 2)` satisfy `2 · 2 = 1 · 4`.
example : (⟨2, 4⟩ : Pair ℚ).cross ⟨1, 2⟩ = 0 := by
  norm_num [Pair.cross_def]

-- They differ by the scalar `2`.
example : (2 : ℚ) • (⟨1, 2⟩ : Pair ℚ) = ⟨2, 4⟩ := by
  ext <;> norm_num

-- The scalar is recovered from the vanishing cross difference.
example : ∃ c : ℚ, c • (⟨1, 2⟩ : Pair ℚ) = ⟨2, 4⟩ :=
  (Pair.cross_eq_zero_iff_exists_smul (Pair.ne_zero_iff.mpr (.inl one_ne_zero))).mp
    (by norm_num [Pair.cross_def])

-- They define the same point of the projective line.
example : Pair.toProj (⟨2, 4⟩ : Pair ℚ) (Pair.ne_zero_iff.mpr (.inl two_ne_zero)) =
    Pair.toProj ⟨1, 2⟩ (Pair.ne_zero_iff.mpr (.inl one_ne_zero)) := by
  rw [Pair.toProj_eq_toProj_iff]
  norm_num [Pair.cross_def]

/-! ### The zero pair -/

-- Infinity `(1, 0)` and the pair `(0, 1)` both have vanishing cross difference with `(0, 0)`,
-- but not with each other.
example : (⟨1, 0⟩ : Pair ℚ).cross 0 = 0 ∧ (0 : Pair ℚ).cross ⟨0, 1⟩ = 0 ∧
    (⟨1, 0⟩ : Pair ℚ).cross ⟨0, 1⟩ ≠ 0 := by
  norm_num [Pair.cross_def]

-- So transitivity fails through the zero pair.
example : ¬ ∀ p q r : Pair ℚ, p.cross q = 0 → q.cross r = 0 → p.cross r = 0 := fun h ↦ by
  have := h ⟨1, 0⟩ 0 ⟨0, 1⟩ (Pair.cross_zero _) (Pair.zero_cross _)
  norm_num [Pair.cross_def] at this

/-! ### Scaling by a non-unit over `ZMod 15` -/

-- Scaling `(1, 1)` by `5` gives `(5, 5)`, which has vanishing cross difference with `(1, 1)`.
example : (5 : ZMod 15) • (⟨1, 1⟩ : Pair (ZMod 15)) = ⟨5, 5⟩ ∧
    (⟨5, 5⟩ : Pair (ZMod 15)).cross ⟨1, 1⟩ = 0 := by
  simp only [Pair.ext_iff, Pair.smul_x, Pair.smul_z, Pair.cross_def]
  decide

-- The scalar `5` is not a unit of `ZMod 15`.
example : ¬ IsUnit (5 : ZMod 15) := by
  simpa using (ZMod.isUnit_iff_coprime 5 15).not.mpr (by decide)

-- Modulo `5`, the pair `(5, 5)` reduces to `(0, 0)`, while `(1, 1)` reduces to a nonzero pair.
example : (⟨5, 5⟩ : Pair (ZMod 15)).map (ZMod.castHom (by decide : 5 ∣ 15) (ZMod 5)) = 0 ∧
    (⟨1, 1⟩ : Pair (ZMod 15)).map (ZMod.castHom (by decide : 5 ∣ 15) (ZMod 5)) ≠ 0 := by
  simp only [Pair.ext_iff, Pair.ne_zero_iff, Pair.map_x, Pair.map_z, Pair.zero_x, Pair.zero_z,
    map_ofNat, map_one]
  decide

-- Scaling by the unit `2` instead keeps the reduction modulo `5` nonzero.
example : IsUnit (2 : ZMod 15) ∧
    ((2 : ZMod 15) • (⟨1, 1⟩ : Pair (ZMod 15))).map
      (ZMod.castHom (by decide : 5 ∣ 15) (ZMod 5)) ≠ 0 := by
  refine ⟨by simpa using (ZMod.isUnit_iff_coprime 2 15).mpr (by decide), ?_⟩
  simp only [Pair.ne_zero_iff, Pair.map_x, Pair.map_z, Pair.smul_x, Pair.smul_z, mul_one,
    map_ofNat]
  decide

end TauCeti.Montgomery
