/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Limit

/-!
# Tests of Tate's limit

* A constant function along the identity has Tate limit zero, and the distance bound
  `C / (d - 1)` is attained there.
* A function that already scales exactly is its own Tate limit.
* The hypothesis `1 < d` cannot be dropped: along the successor map with `d = 1`, the normalized
  iterates of `n ↦ n` diverge.
* On an elliptic curve, the Tate limit of half the naïve height under doubling is half the
  canonical height, and the Tate limit along tripling with factor `9` is the canonical height.
-/

open Filter Topology TauCeti

/-- Along the identity with `d = 2`, the constant function `1` has Tate limit zero. -/
example : tateLimit (id : ℕ → ℕ) 2 (fun _ ↦ 1) = 0 :=
  tateLimit_unique (C' := 1) (by norm_num) (fun _ ↦ by simp) fun _ ↦ by simp

/-- The distance bound `C / (d - 1)` of `abs_tateLimit_sub_le` is attained: here `C = 1` and
`d = 2`, and the Tate limit `0` lies at distance exactly `1` from the constant `1`. -/
example (n : ℕ) :
    |tateLimit (id : ℕ → ℕ) 2 (fun _ ↦ 1) n - 1| = |(1 : ℝ) - 2 * 1| / (2 - 1) := by
  rw [tateLimit_unique (C' := 1) (g := fun _ ↦ 0) (by norm_num) (fun _ ↦ by simp)
    fun _ ↦ by simp]
  norm_num

/-- A function that scales exactly by `2` along doubling is its own Tate limit. -/
example : tateLimit (fun x : ℝ ↦ 2 * x) 2 id = id :=
  tateLimit_eq_self fun _ ↦ rfl

/-- With `d = 1` the normalized iterates of `n ↦ n` along the successor map at `0` are
`0, 1, 2, …`, which diverge: Tate's construction needs `1 < d`. -/
example (L : ℝ) :
    ¬ Tendsto (fun n : ℕ ↦ ((Nat.succ^[n] 0 : ℕ) : ℝ) / 1 ^ n) atTop (𝓝 L) := by
  simp only [Nat.succ_iterate, zero_add, one_pow, div_one]
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop L

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Height.AdmissibleAbsValues F] [DecidableEq F]
  {W : Affine F} [W.toAffine.IsElliptic]

/-- Under doubling, the Tate limit of half the naïve height is half the canonical height. -/
example (P : W.Point) :
    tateLimit (fun Q : W.Point ↦ 2 • Q) 4 ((1 / 2 : ℝ) • Point.naiveHeight) P =
      P.canonicalHeight / 2 := by
  rw [tateLimit_smul, Pi.smul_apply, smul_eq_mul,
    Point.canonicalHeight_eq_tateLimit (m := 2) one_lt_two]
  norm_num
  ring

/-- Tripling with factor `9` recovers the canonical height. -/
example (P : W.Point) :
    tateLimit (fun Q : W.Point ↦ 3 • Q) 9 Point.naiveHeight P = P.canonicalHeight := by
  rw [Point.canonicalHeight_eq_tateLimit (m := 3) (by norm_num)]
  norm_num

end WeierstrassCurve.Affine
