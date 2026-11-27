/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Extended natural numbers as extended nonnegative reals

The `WithTop.recTopCoe` expression used for extended hitting-time means agrees with the
canonical coercion from `ℕ∞` to `ℝ≥0∞`. An element `v` of `ℕ∞`, seen in `ℝ≥0∞`, is the number of
`k : ℕ` with `k < v`, and its real part is `v.toNat`.
-/

public section

open scoped ENNReal

namespace WithTop

/-- Sending infinity to infinity and natural numbers to their casts is `ENat.toENNReal`.
Use explicitly: as a global simp rule, this can leave a cast of `WithTop` infinity that
simp lemmas for `ENat` infinity do not match. -/
theorem recTopCoe_top_natCast_eq_toENNReal (t : WithTop ℕ) :
    t.recTopCoe (⊤ : ℝ≥0∞) (fun n => (n : ℝ≥0∞)) = ENat.toENNReal t := by
  induction t using WithTop.recTopCoe with
  | top => exact ENat.toENNReal_top.symm
  | coe n => exact (ENat.toENNReal_coe n).symm

end WithTop

namespace ENat

/-- An element of `ℕ∞`, seen in `ℝ≥0∞`, is the sum over `k : ℕ` of the indicators of `k < v`. -/
theorem toENNReal_eq_tsum_ite (v : ℕ∞) :
    (v : ℝ≥0∞) = ∑' k : ℕ, if (k : ℕ∞) < v then 1 else 0 := by
  induction v using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [tsum_eq_sum (s := Finset.range n) fun k hk ↦ by simp_all]
    rw [Finset.sum_congr rfl (g := fun _ ↦ (1 : ℝ≥0∞)) fun k hk ↦ by
      simp only [Finset.mem_range] at hk; simp [hk]]
    simp

/-- The real part of an element of `ℕ∞`, seen in `ℝ≥0∞`, is its `toNat`; both are `0` at `⊤`. -/
@[simp]
theorem toReal_toENNReal (v : ℕ∞) : (v : ℝ≥0∞).toReal = (v.toNat : ℝ) := by
  induction v using ENat.recTopCoe <;> simp

end ENat
