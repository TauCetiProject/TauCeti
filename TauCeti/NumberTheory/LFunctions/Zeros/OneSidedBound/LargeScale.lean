/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Ranks
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Scales

/-!
# Simultaneous choice of ranks and cutoffs

The large cutoff must be rounded to a multiple of the cyclotomic order at the very same
rank used to choose the sparse places and the level primes. The least dyadic rank fixes
that order as a function of the initial cutoff, so the polynomial bound for the order
can be used in the rounding theorem without changing the rank.

The choices are those of `New.eventually_exists_data_of_isAdmissibleData` in
`grh/src/New/Reduction/Data/Existence.lean` in [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Data/Existence.lean
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound.Parameters

/-- For every sufficiently large integer `x`, the least dyadic chain length and least
ternary target rank admit the prescribed separated cutoffs. In particular `b` is rounded
to a multiple of `q₁ * x₁` for the tower determined by that chain length. The same tower
satisfies the sparsity threshold and the search-modulus bound for the level primes.
The real parameter `C` is the required lower bound for `log (log b)`. -/
theorem eventually_exists_admissible_ranks_and_scales (P : Parameters) (C : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∃ e e' x₁ b : ℕ,
      let m : ℕ := 2 ^ e
      let r : ℕ := 3 ^ e'
      let s := 22 * e
      0 < e ∧ 0 < e' ∧
        IsLeast {u : ℕ | (∃ i : ℕ, u = 2 ^ i) ∧ √(x : ℝ) ≤ u} m ∧
        IsLeast {u : ℕ | (∃ i : ℕ, u = 3 ^ i) ∧ x ^ 5 ≤ u} r ∧
        (m : ℝ) < 2 * √(x : ℝ) ∧ r < 3 * x ^ 5 ∧
        (s : ℝ) ≤ 32 * log (x : ℝ) ∧ P.q₁ s ≤ x ^ 12 ∧
        P.q₂ s ≤ x ^ (33 * (P.q₀ * P.d)) ∧
        2 * l₀ s * ((r + 1 - m) * (5 * r) + 1) < 2 ^ s ∧
        x₁ = ⌊exp ((x : ℝ) ^ (ε / 6))⌋₊ ∧ 0 < x₁ ∧ 0 < b ∧
        IsLeast {n : ℕ | P.q₁ s * x₁ ∣ n ∧ exp ((x : ℝ) ^ ε) < (n : ℝ)} b ∧
        (x : ℝ) ^ (ε / 6) - 1 ≤ log x₁ ∧
        (x : ℝ) ^ ε ≤ log b ∧ log b ≤ (x : ℝ) ^ ε + 1 ∧
        C ≤ log (log b) ∧ (log b) ^ (100 : ℕ) ≤ x ∧
        x ^ (10 ^ 6) ≤ x₁ ∧ x₁ ^ (10 ^ 6) ≤ b ∧ (log x₁) ^ (6 : ℕ) ≤ log b := by
  have hranks := eventually_exists_admissible_ranks P.q₀ P.d P.q₀_pos
  have hcanonical : ∀ (x e : ℕ),
      IsLeast {u : ℕ | (∃ i : ℕ, u = 2 ^ i) ∧ √(x : ℝ) ≤ u} (2 ^ e) →
        e = Nat.clog 4 x := by
    intro x e hm
    have hsq (i : ℕ) : ((2 ^ i : ℕ) : ℝ) ^ 2 = ((4 ^ i : ℕ) : ℝ) := by
      push_cast
      rw [← pow_mul, pow_mul']
      norm_num
    have hmem (i : ℕ) : √(x : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) ↔ x ≤ 4 ^ i := by
      rw [sqrt_le_iff, hsq, and_iff_right (Nat.cast_nonneg _), Nat.cast_le]
    let f := Nat.clog 4 x
    have hef : (2 ^ e : ℕ) ≤ 2 ^ f :=
      hm.2 ⟨⟨f, rfl⟩, (hmem f).mpr (Nat.le_pow_clog (by decide) x)⟩
    exact le_antisymm ((pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hef)
      ((Nat.clog_le_iff_le_pow (by decide)).mpr ((hmem e).mp hm.1.2))
  let q (x : ℕ) := P.q₁ (22 * Nat.clog 4 x)
  have hq : ∀ᶠ x : ℕ in atTop, (q x : ℝ) ≤ (x : ℝ) ^ (12 : ℝ) := by
    filter_upwards [hranks] with x ⟨e, _, _, _, hm, _, _, _, _, _, hq₁, _, _⟩
    rw [← Nat.cast_ofNat (R := ℝ) (n := 12), Real.rpow_natCast]
    exact_mod_cast (by simpa only [q, ← hcanonical x e hm, q₁_def, towerDeg_def, l₀_def] using hq₁ :
      q x ≤ x ^ 12)
  have hscales := eventually_exists_admissible_scales (C := C) hε (10 ^ 6) (10 ^ 6) 100
    (by norm_num; linarith only [hε']) (Eventually.of_forall fun x ↦ P.q₁_pos _) hq
  filter_upwards [hranks, hscales] with x hr hs
  obtain ⟨e, e', he, he', hm, hr, hm', hr', hlog, _, hq₁, hq₂, hsparse⟩ := hr
  rw [← hcanonical x e hm] at hs
  obtain ⟨x₁, b, hcutoffs⟩ := hs
  exact ⟨e, e', x₁, b, he, he', hm, hr, hm', hr', hlog,
    by simpa only [q₁_def, towerDeg_def, l₀_def] using hq₁,
    by simpa only [q₂_def] using hq₂, by simpa only [l₀_def] using hsparse, hcutoffs⟩

end TauCeti.OneSidedBound.Parameters
