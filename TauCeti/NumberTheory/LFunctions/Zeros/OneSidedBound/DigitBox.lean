/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.SparseExponents
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.SparsePlaceScales

/-!
# Digit boxes at large cyclotomic towers

At polynomial-sized dyadic towers, a fixed dimension suffices for the modular Behrend
construction. The side length may vary with the tower. Its sphere-count bound pays for the
required number of sparse places with a loss of at most `log b`.

The scale selection follows `New.Parameters.exists_isSparse_of_ranks` in
`grh/src/New/Reduction/Data/Existence.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound

/-- If `log b` grows at least like `x ^ ε`, then a single dimension works for the sparse-place
construction at all sufficiently large scales: one can fit a positive Behrend digit box
whose sphere-count bound, multiplied by `log b`, covers the entire tower degree. -/
theorem eventually_exists_sparse_place_digit_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ᶠ x : ℝ in atTop, ∀ (s : ℕ) (b : ℝ),
      x ^ (11 : ℕ) ≤ (2 : ℝ) ^ s → (2 : ℝ) ^ s ≤ x ^ (12 : ℕ) →
      x ^ ε ≤ log b →
      ∃ H : ℕ, 0 < H ∧ (2 * l₀ s * H) ^ n ≤ 2 ^ s ∧
        (towerDeg s : ℝ) ≤ ((H : ℝ) ^ n / (n * H ^ 2)) * log b := by
  let δ := min (ε / 6) 1
  have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
  have hδ₁ : δ ≤ 1 := min_le_right ..
  have hδε : δ ≤ ε / 6 := min_le_left ..
  obtain ⟨n, hn, he⟩ := eventually_sparse_place_parameter_bounds hδ (hδ₁.trans (by norm_num))
  refine ⟨n, hn, ?_⟩
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with x hx hx₁ s b hlo hup hb
  obtain ⟨hW₁, hW, ho, hbase, _⟩ := hx s hlo hup
  have ho' : (2 : ℝ) ^ s ≤ (x ^ δ) ^ (n + 1) := ho.trans (pow_le_pow_right₀ hW₁ (by omega))
  obtain ⟨H, hH, hfit, hbudget⟩ := exists_sparse_place_digit_bound hn hW ho' hbase
  have hlog : (x ^ δ) ^ (6 : ℕ) ≤ log b := by
    rw [← rpow_mul_natCast (zero_le_one.trans hx₁)]
    exact (rpow_le_rpow_of_exponent_le hx₁ ((le_div_iff₀ (by norm_num)).mp hδε)).trans hb
  exact ⟨H, hH, hfit, hbudget.trans (mul_le_mul_of_nonneg_left hlog (by positivity))⟩

end TauCeti.OneSidedBound
