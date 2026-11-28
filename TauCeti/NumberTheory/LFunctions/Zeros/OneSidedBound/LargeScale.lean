/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.AdmissibleScale
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.DigitBox
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Ranks
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Scales

/-!
# Simultaneous choice of ranks and cutoffs

The large cutoff must be rounded to a multiple of the cyclotomic order at the very same
rank used to choose the sparse places and the level primes. The least dyadic rank fixes
that order as a function of the initial cutoff, so the polynomial bound for the order
can be used in the rounding theorem without changing the rank. The digit box for the
sparse places must fit in that tower, with a cardinality budget paid by the same rounded
cutoff.

The choices are those of `New.eventually_exists_data_of_isAdmissibleData` in
`grh/src/New/Reduction/Data/Existence.lean` in [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Data/Existence.lean
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound.Parameters

private theorem eq_clog_four_of_isLeast_two_pow {x e : ℕ}
    (hm : IsLeast {u : ℕ | (∃ i : ℕ, u = 2 ^ i) ∧ √(x : ℝ) ≤ u} (2 ^ e)) :
    e = Nat.clog 4 x := by
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

/-- For every sufficiently large integer `x`, the least dyadic chain length and least
ternary target rank form an admissible scale with the prescribed separated cutoffs. In particular
`b` is rounded to a multiple of `q₁ * x₁` for the tower determined by that chain length. The same
tower satisfies the sparsity threshold and the search-modulus bound for the level primes.
A fixed digit dimension `n` works at all sufficiently large cutoffs; at each cutoff the
side length `H` fits modulo `2 ^ s` and its sphere-count lower bound, multiplied by `log b`,
covers the tower degree. The real parameter `C` is the required lower bound for `log (log b)`. -/
theorem eventually_exists_admissible_ranks_and_scales (P : Parameters) (C : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ n : ℕ, 0 < n ∧ ∀ᶠ x : ℕ in atTop, ∃ (D : AdmissibleScale P C x) (H : ℕ),
      let m : ℕ := 2 ^ D.e
      let r : ℕ := 3 ^ D.e'
      let s := 22 * D.e
      IsLeast {u : ℕ | (∃ i : ℕ, u = 2 ^ i) ∧ √(x : ℝ) ≤ u} m ∧
        IsLeast {u : ℕ | (∃ i : ℕ, u = 3 ^ i) ∧ x ^ 5 ≤ u} r ∧
        (m : ℝ) < 2 * √(x : ℝ) ∧ r < 3 * x ^ 5 ∧ P.q₁ s ≤ x ^ 12 ∧
        P.q₂ s ≤ x ^ (33 * (P.q₀ * P.d)) ∧
        2 * l₀ s * ((r + 1 - m) * (5 * r) + 1) < 2 ^ s ∧
        D.x₁ = ⌊exp ((x : ℝ) ^ (ε / 6))⌋₊ ∧
        IsLeast {j : ℕ | P.q₁ s * D.x₁ ∣ j ∧ exp ((x : ℝ) ^ ε) < (j : ℝ)} D.b ∧
        (x : ℝ) ^ (ε / 6) - 1 ≤ log D.x₁ ∧
        (x : ℝ) ^ ε ≤ log D.b ∧ log D.b ≤ (x : ℝ) ^ ε + 1 ∧
        0 < H ∧ (2 * l₀ s * H) ^ n ≤ 2 ^ s ∧
        (towerDeg s : ℝ) ≤ ((H : ℝ) ^ n / (n * H ^ 2)) * log D.b := by
  have hranks := eventually_exists_admissible_ranks P.q₀ P.d P.q₀_pos
  let q (x : ℕ) := P.q₁ (22 * Nat.clog 4 x)
  have hq : ∀ᶠ x : ℕ in atTop, (q x : ℝ) ≤ (x : ℝ) ^ (12 : ℝ) := by
    filter_upwards [hranks] with x ⟨e, _, _, _, hm, _, _, _, _, _, _, hq₁, _, _⟩
    rw [← Nat.cast_ofNat (R := ℝ) (n := 12), Real.rpow_natCast]
    exact_mod_cast (by
      simpa only [q, ← eq_clog_four_of_isLeast_two_pow hm, q₁_def, towerDeg_def, l₀_def] using hq₁ :
      q x ≤ x ^ 12)
  have hscales := eventually_exists_admissible_scales (C := C) hε (10 ^ 6) (10 ^ 6) 100
    (by norm_num; linarith only [hε']) (Eventually.of_forall fun x ↦ P.q₁_pos _) hq
  obtain ⟨n, hn, hbox⟩ := eventually_exists_sparse_place_digit_bound hε
  refine ⟨n, hn, ?_⟩
  filter_upwards [hranks, hscales, tendsto_natCast_atTop_atTop.eventually hbox] with x hr hs hdigit
  obtain ⟨e, e', he, he', hm, hr, hm', hr', hlog, hlo, _, hq₁, hq₂, hsparse⟩ := hr
  rw [← eq_clog_four_of_isLeast_two_pow hm] at hs
  obtain ⟨x₁, b, hex, _, _, hb, hlogx₁, hlogb, hlogb', hC, h100, hxx₁, hx₁b, hlogpow⟩ := hs
  have horder : P.q₁ (22 * e) ≤ x ^ 12 := by
    simpa only [q₁_def, towerDeg_def, l₀_def] using hq₁
  have hup : 2 ^ (22 * e) ≤ P.q₁ (22 * e) := by
    have hfactor : 0 < P.q₀ * (3 * l₀ (22 * e)) :=
      Nat.mul_pos P.q₀_pos (by rw [l₀_def]; positivity)
    rw [q₁_def, towerDeg_def, ← mul_assoc]
    exact Nat.le_mul_of_pos_left _ hfactor
  obtain ⟨H, hH, hfit, hcard⟩ := hdigit (22 * e) (b : ℝ) (by exact_mod_cast hlo)
    (by exact_mod_cast hup.trans horder) hlogb
  let D : AdmissibleScale P C x :=
    { e := e, e' := e', x₁ := x₁, b := b
      e_pos := he, e'_pos := he'
      sqrt_le := by exact_mod_cast hm.1.2
      le_two_mul_sqrt := by exact_mod_cast hm'.le
      pow_five_le := hr.1.2, le_three_mul_pow_five := hr'.le
      tower_le := by exact_mod_cast hlog
      level_mul_dvd_b := hb.1.1
      le_log_log := hC, log_pow_le := h100
      first_pow_le := hxx₁, second_pow_le := hx₁b, log_second_pow_le := hlogpow }
  exact ⟨D, H, hm, hr, hm', hr', horder,
    by simpa only [q₂_def] using hq₂, by simpa only [l₀_def] using hsparse,
    hex, hb, hlogx₁, hlogb, hlogb', hH, hfit, hcard⟩

end TauCeti.OneSidedBound.Parameters
