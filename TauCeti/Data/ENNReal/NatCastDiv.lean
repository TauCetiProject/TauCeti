/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Basic.ENNReal.Inv

/-!
# Multiples and quotients of natural numbers in `ℝ≥0∞`

* `ENNReal.natCast_div_natCast_lt_ofReal_iff`: for a positive natural number `n`, the quotient
  `m / n` in `ℝ≥0∞` is below `ENNReal.ofReal ε` exactly when `m < ε * n` in `ℝ`.
* `ENNReal.natCast_mul_ofReal_le_ofReal_iff`: for `b ≥ 0`, the multiple `n * ofReal a` in `ℝ≥0∞`
  is at most `ofReal b` exactly when `n * a ≤ b` in `ℝ`. This reads a bound `#Z * δ ≤ E` on a
  number of points carrying a quantum `δ` of energy back in `ℝ`.
* `Set.finite_of_forall_finset_card_mul_le`: a set all of whose finite subsets `T` satisfy
  `#T * δ ≤ E` in `ℝ≥0∞`, for `δ ≠ 0` and `E ≠ ∞`, is finite. This is how a set of points each
  carrying a fixed quantum `δ` of a total energy `E` is shown to be finite.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- For a positive natural number `n`, the quotient `m / n` in `ℝ≥0∞` is below `ENNReal.ofReal ε`
exactly when `m < ε * n` in `ℝ`. -/
theorem natCast_div_natCast_lt_ofReal_iff {m n : ℕ} (hn : 0 < n) {ε : ℝ} :
    (m : ℝ≥0∞) / n < ENNReal.ofReal ε ↔ (m : ℝ) < ε * n := by
  -- Clear the denominator in `ℝ≥0∞`, then compare a natural number with a real.
  rw [ENNReal.div_lt_iff (by simp [hn.ne']) (by simp), ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul' (Nat.cast_nonneg n)]
  exact ENNReal.natCast_lt_ofReal

/-- For `b ≥ 0`, the multiple `n * ofReal a` in `ℝ≥0∞` is at most `ofReal b` exactly when
`n * a ≤ b` in `ℝ`. -/
theorem natCast_mul_ofReal_le_ofReal_iff {n : ℕ} {a b : ℝ} (hb : 0 ≤ b) :
    (n : ℝ≥0∞) * ENNReal.ofReal a ≤ ENNReal.ofReal b ↔ n * a ≤ b := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hb]

end ENNReal

/-- A set all of whose finite subsets `T` satisfy `#T * δ ≤ E`, for `δ ≠ 0` and `E ≠ ∞`, is
finite. -/
theorem Set.finite_of_forall_finset_card_mul_le {α : Type*} {Z : Set α} {δ E : ℝ≥0∞}
    (hδ : δ ≠ 0) (hE : E ≠ ∞) (h : ∀ T : Finset α, ↑T ⊆ Z → T.card * δ ≤ E) : Z.Finite := by
  by_contra hinf
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_mul_gt hδ hE
  obtain ⟨T, hTZ, hTk⟩ := Set.Infinite.exists_subset_card_eq hinf k
  exact (h T hTZ).not_gt (hTk ▸ hk)
