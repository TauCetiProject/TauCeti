/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Sums over dyadic scales

For a base `b > 1` and an exponent `δ > 0`, the sum of `min (b ^ j u) ((b ^ j u) ^ (-δ))` over
any finite set of integers `j` is at most `(1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹`, for every real `u`.
For `u > 0`, the terms with `b ^ j u ≤ 1` are at most `b ^ j u`, a geometric series of ratio
`b⁻¹` whose largest term is at most `1`, and the terms with `b ^ j u > 1` are `(b ^ j u) ^ (-δ)`,
a geometric series of ratio `b ^ (-δ)` whose largest term is below `1`. For `u ≤ 0` every term is
nonpositive.

With `b = 2` this is how per-scale estimates of the shape "at most `2 ^ j ‖h‖` for small scales and
at most `(2 ^ j ‖h‖) ^ (-δ)` for large ones" are summed into a bound uniform in `h`, as in the
verification of Hörmander's condition for the kernel of a Fourier multiplier cut into
Littlewood–Paley pieces.

Similarly, for `0 < α < 1`, a nonnegative sequence with `2^{jα} gⱼ ≤ a` and `2^{jα} gⱼ ≤ b 2^j d`
sums to at most `C (a + b) d^α`: the second bound is the better one while `2^j d ≤ 1`, and the
first beyond. Applied to the increments `gⱼ = |fⱼ(x) - fⱼ(y)|` at distance `d = |x - y|` of
pieces with `‖fⱼ‖_∞ ≲ 2^{-jα}` and Lipschitz constants `≲ 2^{j(1-α)}`, this shows that `∑ⱼ fⱼ` is
`α`-Hölder.

For `0 < s < t` the same bound sums `(2^j)^s (1 + 2^j r)^(-t)` over `j ∈ ℕ` to at most
`C r^(-s)`, uniformly in `r > 0`: with `u = 2^j r`, the term is `r^(-s)` times
`u^s (1 + u)^(-t) ≤ min (u^s) ((u^s)^(-(t - s)/s))`. These are the sums of the dyadic pieces of a
kernel with the size `(2^j)^s` at scale `2^{-j}` and rapid decay beyond it, evaluated at
distance `r`: they give the bound `C r^(-s)` of the whole kernel. For `r` bounded below by `ρ > 0`
and `t > s` a natural number, the terms are moreover at most `ρ^(-t) (2^(s - t))^j`, a geometric
sequence.

When a series `∑ⱼ fⱼ` has terms bounded both by `D (2^j)^(s + 1) d` and by
`C (2^j)^s (1 + 2^j r)^(-N)`, each term is at most the interpolation `A^δ B^(1 - δ)` of the two
bounds `A` and `B`, for `0 ≤ δ ≤ 1`. The interpolated bounds are of the previous shape with
exponents `s + δ` and `N (1 - δ)`, so the series sums to at most
`E D^δ C^(1 - δ) d^δ r^(-(s + δ))` when `0 < s + δ < N (1 - δ)`. This is how increments of a
kernel at distance `d`, cut into dyadic pieces, are bounded by `d^δ`.

For `Q ≥ 1`, at most `2Q + 1` dyadic scales `2^k` are comparable to a given `2^j` up to the factor
`Q`, that is, satisfy `2^j ≤ Q 2^k` and `2^k ≤ Q 2^j`, and for these `2^{σ (j - k)} ≤ Q ^ |σ|`.
These count and weigh the Littlewood–Paley pieces met by a translated piece.

For `u > 0` and an integer `k`, the weights `2^{u(j-k)}` of the integers `j < k` sum to at most
`1 / (2^u - 1)`: they form a geometric series of ratio `2^{-u}` starting at `2^{-u}`. This sums
lower-frequency contributions with a gain over the Littlewood–Paley decomposition.

For `ε > 0`, the two-sided series `∑_{m ∈ ℤ} 2^{-ε |m|}` in `ℝ≥0∞` is finite, being the
bilateral geometric series of ratio `2^{-ε}`. For `σ ≥ 1` the shifted sums
`∑_{j ∈ ℤ} 2^{-ε |x - σ j|}` are at most `2^ε ∑_{m ∈ ℤ} 2^{-ε |m|}`, uniformly in `x`, since the
points `σ j` are `1`-separated. These sum per-scale bounds over the dyadic time shells
`|s - t| ≈ 2^j` in the endpoint Strichartz estimate.

For a term `y ∈ ℝ≥0∞` with the dyadic weight `2^{lσ}`, shifting the index of the weight by each
`d` in a finite set `S` and summing multiplies the weighted term by `∑_{d ∈ S} 2^{dσ}`. This
collects the estimates of a block by its neighbouring blocks in the Littlewood–Paley
decomposition.
Underlying this, for `b > 0` the weight `(b^{j+k})^s` of a shifted index is the product
`(b^j)^s (b^k)^s` in `ℝ≥0∞`.

Finally, for a base `b > 1`, a function `R` antitone on `(0, ∞)` is bounded by step functions
built from its values at the left endpoints of the scales `b ^ n s`: on `(0, s]` by the values
`R (b⁻¹ ^ (n + 1) s)` on `(b⁻¹ ^ (n + 1) s, b⁻¹ ^ n s]`, and on `[s, ∞)` by the values `R (b ^ n s)`
on `[b ^ n s, b ^ (n + 1) s)`. Taking `Lᵖ` norms of these step functions bounds that of `R` by
dyadic series.

## Main declarations

* `TauCeti.sum_min_zpow_mul_rpow_neg_le`: the uniform bound over any finite set of scales.
* `TauCeti.exists_tsum_rpow_mul_one_add_rpow_neg_le`: for `0 < s < t`,
  `∑ⱼ (2^j)^s (1 + 2^j r)^(-t) ≤ C r^(-s)` for every `r > 0`.
* `TauCeti.exists_tsum_le_mul_rpow_of_rpow_mul_le`: for `0 < α < 1`, a nonnegative sequence with
  `2^{jα} gⱼ ≤ a` and `2^{jα} gⱼ ≤ b 2^j d` sums to at most `C (a + b) d^α`.
* `TauCeti.rpow_mul_one_add_rpow_neg_le`: `(2^j)^s (1 + 2^j r)^(-N) ≤ ρ^(-N) (2^(s - N))^j` for
  `r ≥ ρ > 0`.
* `TauCeti.exists_norm_le_of_hasSum_of_le_of_le`: a series whose terms are bounded by
  `D (2^j)^(s + 1) d` and by `C (2^j)^s (1 + 2^j r)^(-N)` sums to at most
  `E D^δ C^(1 - δ) d^δ r^(-(s + δ))`.
* `TauCeti.card_filter_two_pow_le_mul_two_pow_le`: for `Q ≥ 1`, at most `2Q + 1` indices `k` have
  `2^j ≤ Q 2^k` and `2^k ≤ Q 2^j`, and for these `2^{σ (j - k)} ≤ Q ^ |σ|`
  (`TauCeti.two_rpow_mul_sub_le_rpow_abs`).
* `TauCeti.sum_ite_two_rpow_le`: `∑_{j ∈ F, j < k} 2^{u(j-k)} ≤ 1 / (2^u - 1)` for `u > 0`.
* `TauCeti.summable_two_rpow_neg_mul_abs`: `m ↦ 2^{-r|m|}` is summable over `ℤ` for `r > 0`.
* `TauCeti.tsum_two_rpow_neg_mul_abs_ne_top`, `TauCeti.tsum_two_rpow_neg_mul_abs_sub_le`: the
  two-sided series `∑_{m ∈ ℤ} 2^{-ε |m|}` is finite and bounds its shifts by `σ`-separated points.
* `TauCeti.ofReal_zpow_add_rpow`: the weight `(b^{j+k})^s` is the product of `(b^j)^s` and
  `(b^k)^s`.
* `TauCeti.sum_ofReal_two_zpow_add_rpow_mul`: shifting the dyadic weight `2^{lσ}` of a term by
  each element of a finite set `S` and summing multiplies it by `∑_{d ∈ S} 2^{dσ}`.
* `TauCeti.tsum_ofReal_two_zpow_rpow_mul_le_of_eq_zero`: a dyadically weighted series whose terms
  vanish outside a window `j - L < k < j + L` is at most `(∑_{-L < d < L} 2^{dσ}) 2^{jσ}` times a
  bound on its terms.
* `TauCeti.sum_range_sub_le_tsum`: a sum over the truncation `-N ≤ k < N` of `ℤ` is at most the
  sum over all of `ℤ`.
* `AntitoneOn.le_tsum_indicator_Ioc`, `AntitoneOn.le_tsum_indicator_Ico`: a function antitone on
  `(0, ∞)` is bounded on `(0, s]` and on `[s, ∞)` by its values at the left endpoints of the
  intervals between consecutive scales `b ^ n s`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., proof of Theorem 6.2.7.
-/

public section

namespace TauCeti

open Finset

/-- For `b > 1` and `δ > 0`, summing `min (b ^ j u) ((b ^ j u) ^ (-δ))` over any finite set of
integers `j` gives at most `(1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹`, independently of `u`. For `b = 2` the
first summand is `2`. -/
theorem sum_min_zpow_mul_rpow_neg_le {b δ : ℝ} (hb : 1 < b) (hδ : 0 < δ) (u : ℝ) (s : Finset ℤ) :
    ∑ j ∈ s, min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ (1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹ := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hb1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  set q : ℝ := b ^ (-δ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  -- For `u ≤ 0` every term is nonpositive.
  obtain hu | hu := le_or_gt u 0
  · exact (sum_nonpos fun j _ ↦ (min_le_left _ _).trans
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu)).trans
      (add_nonneg (inv_nonneg.2 (sub_nonneg.2 hb1.le)) (inv_nonneg.2 (sub_nonneg.2 hq1.le)))
  obtain ⟨m, hlo, hhi⟩ := exists_mem_Ico_zpow hu hb
  -- The comparison function on `ℤ`: `b ^ (i + 1)` for `i < 0` and `q ^ i` for `i ≥ 0`.
  set f : ℤ → ℝ := fun i ↦ if i < 0 then b ^ (i + 1) else q ^ i
  have hf : HasSum f ((1 - q)⁻¹ + (1 - b⁻¹)⁻¹) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · convert hasSum_geometric_of_lt_one hq0 hq1 using 2 with n
      simp [f]
    · convert hasSum_geometric_of_lt_one (inv_nonneg.2 hb0.le) hb1 using 2 with n
      have hn : (-((n : ℤ) + 1)) < 0 := by omega
      simp only [f, hn, ite_true]
      rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, zpow_neg, zpow_natCast, inv_pow]
  -- Since `b ^ m ≤ u < b ^ (m + 1)`, the term of index `j` is at most `f (j + m)`.
  have hterm (j : ℤ) : min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ f (j + m) := by
    by_cases hj : j + m < 0
    · simp only [f, hj, ite_true]
      refine (min_le_left _ _).trans ?_
      rw [add_assoc, zpow_add₀ hb0.ne']
      gcongr
    · simp only [f, hj, ite_false]
      refine (min_le_right _ _).trans ?_
      rw [Real.rpow_zpow_comm hb0.le, zpow_add₀ hb0.ne']
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by linarith)
  calc ∑ j ∈ s, min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ ∑ j ∈ s, f (j + m) :=
        sum_le_sum fun j _ ↦ hterm j
    _ = ∑ i ∈ s.map (addRightEmbedding m), f i := by simp
    _ ≤ (1 - q)⁻¹ + (1 - b⁻¹)⁻¹ := sum_le_hasSum _ (fun i _ ↦ by positivity) hf
    _ = (1 - b⁻¹)⁻¹ + (1 - q)⁻¹ := add_comm _ _

/-- With `u = 2^j r`, the term `(2^j)^s (1 + 2^j r)^(-t)` is `r^(-s)` times
`u^s (1 + u)^(-t) ≤ min (u^s) ((u^s)^(-δ))`, where `u^s = b^j r^s` for `b = 2^s` and
`δ = (t - s) / s`. -/
private theorem rpow_mul_one_add_rpow_neg_le_mul_min {s t r : ℝ} (hs : 0 < s) (hst : s < t)
    (hr : 0 < r) (j : ℕ) :
    ((2 : ℝ) ^ j) ^ s * (1 + 2 ^ j * r) ^ (-t) ≤ r ^ (-s) *
      min ((2 ^ s) ^ (j : ℤ) * r ^ s) (((2 ^ s) ^ (j : ℤ) * r ^ s) ^ (-((t - s) / s))) := by
  set u : ℝ := 2 ^ j * r
  have hu : 0 < u := by positivity
  have hbj : ((2 : ℝ) ^ s) ^ (j : ℤ) * r ^ s = u ^ s := by
    simp only [u]
    rw [zpow_natCast, Real.rpow_pow_comm zero_le_two, Real.mul_rpow (by positivity) hr.le]
  have hj : ((2 : ℝ) ^ j) ^ s = r ^ (-s) * u ^ s := by
    simp only [u]
    rw [Real.mul_rpow (by positivity) hr.le, Real.rpow_neg hr.le, mul_left_comm,
      inv_mul_cancel₀ (by positivity), mul_one]
  rw [hbj, hj, mul_assoc]
  refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) (by positivity)
  · exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith))
  · have hsδ : s * -((t - s) / s) = s + -t := by
      field_simp
      ring
    rw [← Real.rpow_mul hu.le, hsδ, Real.rpow_add hu]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hu (le_add_of_nonneg_left zero_le_one) (by linarith))
      (by positivity)

/-- **Dyadic sums with polynomial decay.** For `0 < s < t` there is `C ≥ 0` such that for every
`r > 0` the series `∑ⱼ (2^j)^s (1 + 2^j r)^(-t)` over `j ∈ ℕ` converges, with sum at most
`C r^(-s)`. -/
theorem exists_tsum_rpow_mul_one_add_rpow_neg_le {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      Summable (fun j : ℕ ↦ ((2 : ℝ) ^ j) ^ s * (1 + 2 ^ j * r) ^ (-t)) ∧
        ∑' j : ℕ, ((2 : ℝ) ^ j) ^ s * (1 + 2 ^ j * r) ^ (-t) ≤ C * r ^ (-s) := by
  -- The terms are bounded by `r^(-s) min (b^j r^s) ((b^j r^s)^(-δ))`, whose finite sums are
  -- bounded uniformly in `r` by `sum_min_zpow_mul_rpow_neg_le`.
  set b : ℝ := 2 ^ s
  set δ : ℝ := (t - s) / s
  have hb : 1 < b := Real.one_lt_rpow one_lt_two hs
  have hδ : 0 < δ := div_pos (by linarith) hs
  set C : ℝ := (1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹
  have hC : 0 ≤ C := by
    have := sub_pos.2 (inv_lt_one_of_one_lt₀ hb)
    have := sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith : -δ < 0))
    positivity
  refine ⟨C, hC, fun r hr ↦ ?_⟩
  set f : ℕ → ℝ := fun j ↦ ((2 : ℝ) ^ j) ^ s * (1 + 2 ^ j * r) ^ (-t)
  have hf0 : ∀ j, 0 ≤ f j := fun j ↦ by positivity
  have hsum (N : ℕ) : ∑ j ∈ Finset.range N, f j ≤ C * r ^ (-s) := by
    calc ∑ j ∈ Finset.range N, f j
        ≤ ∑ j ∈ Finset.range N,
            r ^ (-s) * min (b ^ (j : ℤ) * r ^ s) ((b ^ (j : ℤ) * r ^ s) ^ (-δ)) :=
          Finset.sum_le_sum fun j _ ↦ rpow_mul_one_add_rpow_neg_le_mul_min hs hst hr j
      _ = r ^ (-s) * ∑ i ∈ (Finset.range N).map (Nat.castEmbedding : ℕ ↪ ℤ),
            min (b ^ i * r ^ s) ((b ^ i * r ^ s) ^ (-δ)) := by
          rw [Finset.mul_sum, Finset.sum_map]
          simp only [Nat.castEmbedding_apply, zpow_natCast]
      _ ≤ r ^ (-s) * C :=
          mul_le_mul_of_nonneg_left (sum_min_zpow_mul_rpow_neg_le hb hδ _ _) (by positivity)
      _ = C * r ^ (-s) := mul_comm _ _
  exact ⟨summable_of_sum_range_le hf0 hsum, Real.tsum_le_of_sum_range_le hf0 hsum⟩

/-- **Summing two dyadic bounds.** For `0 < α < 1` there is `C ≥ 0` such that every nonnegative
sequence with `2^{jα} gⱼ ≤ a` and `2^{jα} gⱼ ≤ b 2^j d` for all `j`, where `a, b, d ≥ 0`, is
summable with `∑ⱼ gⱼ ≤ C (a + b) d^α`. -/
theorem exists_tsum_le_mul_rpow_of_rpow_mul_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℕ → ℝ) {a b d : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ d → (∀ j, 0 ≤ g j) →
      (∀ j : ℕ, 2 ^ (α * j) * g j ≤ a) → (∀ j : ℕ, 2 ^ (α * j) * g j ≤ b * 2 ^ j * d) →
      Summable g ∧ ∑' j, g j ≤ C * (a + b) * d ^ α := by
  -- The ratios `q = 2^{-α} < 1` of the first bounds and `2 q = 2^{1-α} > 1` of the second.
  set q : ℝ := ((2 : ℝ) ^ α)⁻¹ with hq_def
  have h2α : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow one_lt_two hα0
  have h2α' : (2 : ℝ) ^ α < 2 := by simpa using Real.rpow_lt_rpow_of_exponent_lt one_lt_two hα1
  have hq0 : 0 < q := inv_pos.2 (by positivity)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ h2α
  have h2q : 1 < 2 * q := by
    rw [hq_def, ← div_eq_mul_inv, one_lt_div (by positivity)]
    exact h2α'
  have hpow : ∀ j : ℕ, (2 : ℝ) ^ (α * j) = (q ^ j)⁻¹ := fun j ↦ by
    rw [hq_def, inv_pow, inv_inv, Real.rpow_mul_natCast zero_le_two]
  set C₁ : ℝ := (1 - q)⁻¹
  set C₂ : ℝ := 2 * q * (2 * q - 1)⁻¹
  have hC₁ : 0 ≤ C₁ := by have := sub_pos.2 hq1; positivity
  have hC₂ : 0 ≤ C₂ := by have := sub_pos.2 h2q; positivity
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun g a b d ha0 hb0 hd0 hg0 ha hb ↦ ?_⟩
  have hga : ∀ j, g j ≤ a * q ^ j := fun j ↦ by
    have h := ha j
    rw [hpow, inv_mul_le_iff₀ (by positivity)] at h
    linarith
  have hgb : ∀ j, g j ≤ b * d * (2 * q) ^ j := fun j ↦ by
    have h := hb j
    rw [hpow, inv_mul_le_iff₀ (by positivity)] at h
    calc g j ≤ q ^ j * (b * 2 ^ j * d) := h
      _ = b * d * (2 * q) ^ j := by ring
  have hgeo := summable_geometric_of_lt_one hq0.le hq1
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hga (hgeo.mul_left a)
  refine ⟨hgs, ?_⟩
  rcases le_or_gt 1 d with hd | hd
  · -- For `d ≥ 1` the first bounds suffice.
    calc ∑' j, g j ≤ ∑' j, a * q ^ j := hgs.tsum_le_tsum hga (hgeo.mul_left a)
      _ = a * C₁ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
      _ ≤ (C₁ + C₂) * (a + b) * 1 := by nlinarith
      _ ≤ (C₁ + C₂) * (a + b) * d ^ α := by
          gcongr
          exact Real.one_le_rpow hd hα0.le
  rcases hd0.eq_or_lt with hd0 | hd0
  · -- For `d = 0` the second bounds vanish.
    have hg : ∀ j, g j = 0 := fun j ↦ le_antisymm ((hgb j).trans_eq (by simp [← hd0])) (hg0 j)
    simp only [hg, tsum_zero]
    positivity
  -- For `0 < d < 1` split the sum at the scale `J` with `1 < 2^J d ≤ 2`: the second bounds sum
  -- to `b C₂ d^α` below it, and the first bounds to `a C₁ d^α` above it.
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (one_le_inv₀ hd0 |>.2 hd.le) one_lt_two
  set J := n + 1
  set t := (2 : ℝ) ^ J * d
  have ht1 : 1 < t := by
    have h := mul_lt_mul_of_pos_right hn2 hd0
    rwa [inv_mul_cancel₀ hd0.ne'] at h
  have ht2 : t ≤ 2 := by
    have h := mul_le_mul_of_nonneg_right hn1 hd0.le
    rw [inv_mul_cancel₀ hd0.ne'] at h
    calc t = 2 * (2 ^ n * d) := by simp only [t, J, pow_succ]; ring
      _ ≤ 2 := by linarith
  -- `q^J t^α = d^α`, since `t = 2^J d`.
  have hqJ : q ^ J * t ^ α = d ^ α := by
    have h2J : ((2 : ℝ) ^ J) ^ α = ((2 : ℝ) ^ α) ^ J := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm, Real.rpow_mul zero_le_two,
        Real.rpow_natCast]
    rw [Real.mul_rpow (by positivity) hd0.le, h2J, hq_def, inv_pow, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  have hqd : q ^ J ≤ d ^ α := by
    rw [← hqJ]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow ht1.le hα0.le)
  have hdq : d * (2 * q) ^ J ≤ 2 * q * d ^ α := by
    have ht : t ^ (1 - α) * t ^ α = t := by
      rw [← Real.rpow_add (by positivity), sub_add_cancel, Real.rpow_one]
    have h2 : (2 : ℝ) ^ (1 - α) = 2 * q := by
      rw [Real.rpow_sub two_pos, Real.rpow_one, hq_def, div_eq_mul_inv]
    calc d * (2 * q) ^ J = t ^ (1 - α) * (q ^ J * t ^ α) := by
          rw [← mul_assoc, mul_comm _ (q ^ J), mul_assoc, ht]
          simp only [t]
          ring
      _ ≤ 2 ^ (1 - α) * d ^ α := by
          rw [hqJ]
          gcongr
      _ = 2 * q * d ^ α := by rw [h2]
  have hlow : ∑ j ∈ range J, g j ≤ b * C₂ * d ^ α := by
    have := sub_pos.2 h2q
    calc ∑ j ∈ range J, g j ≤ ∑ j ∈ range J, b * d * (2 * q) ^ j := sum_le_sum fun j _ ↦ hgb j
      _ = b * d * (((2 * q) ^ J - 1) / (2 * q - 1)) := by rw [← mul_sum, geom_sum_eq h2q.ne']
      _ ≤ b * (d * (2 * q) ^ J) * (2 * q - 1)⁻¹ := by
          rw [div_eq_mul_inv, ← mul_assoc, mul_assoc b]
          gcongr
          linarith
      _ ≤ b * (2 * q * d ^ α) * (2 * q - 1)⁻¹ := by gcongr
      _ = b * C₂ * d ^ α := by ring
  have hhigh : ∑' j, g (j + J) ≤ a * C₁ * d ^ α := by
    calc ∑' j, g (j + J) ≤ ∑' j, a * q ^ J * q ^ j :=
          ((summable_nat_add_iff J).2 hgs).tsum_le_tsum
            (fun j ↦ (hga (j + J)).trans_eq (by ring)) (hgeo.mul_left _)
      _ = a * C₁ * q ^ J := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
          ring
      _ ≤ a * C₁ * d ^ α := by gcongr
  rw [← hgs.sum_add_tsum_nat_add J]
  have : 0 ≤ d ^ α := by positivity
  nlinarith [mul_nonneg ha0 hC₂, mul_nonneg hb0 hC₁]

/-- For `r ≥ ρ > 0`, the term `(2^j)^s (1 + 2^j r)^(-N)` is at most `ρ^(-N) q^j` with
`q = 2^(s - N)`: a geometric sequence, of ratio `q < 1` when `s < N`. -/
theorem rpow_mul_one_add_rpow_neg_le {s ρ r : ℝ} {N : ℕ} (hρ : 0 < ρ) (hr : ρ ≤ r) (j : ℕ) :
    ((2 : ℝ) ^ j) ^ s * (1 + 2 ^ j * r) ^ (-(N : ℝ)) ≤
      ρ ^ (-(N : ℝ)) * ((2 : ℝ) ^ (s - N)) ^ j := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hle : (1 + 2 ^ j * r) ^ (-(N : ℝ)) ≤ (2 ^ j * ρ) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by simp)
  calc ((2 : ℝ) ^ j) ^ s * (1 + 2 ^ j * r) ^ (-(N : ℝ))
      ≤ ((2 : ℝ) ^ j) ^ s * (2 ^ j * ρ) ^ (-(N : ℝ)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ρ ^ (-(N : ℝ)) * ((2 : ℝ) ^ j) ^ (s + -(N : ℝ)) := by
        rw [Real.mul_rpow h2.le hρ.le, Real.rpow_add h2]
        ring
    _ = ρ ^ (-(N : ℝ)) * ((2 : ℝ) ^ (s - N)) ^ j := by
        rw [← sub_eq_add_neg, Real.rpow_pow_comm zero_le_two]

/-- **Summing interpolated dyadic bounds.** For `0 < δ < 1` and `0 < s + δ < N (1 - δ)` there is
`E ≥ 0` such that, if `L = ∑ⱼ fⱼ` in a normed group with `‖fⱼ‖ ≤ D (2^j)^(s + 1) d` and
`‖fⱼ‖ ≤ C (2^j)^s (1 + 2^j r)^(-N)` for all `j`, where `C, D, d ≥ 0` and `r > 0`, then
`‖L‖ ≤ E D^δ C^(1 - δ) d^δ r^(-(s + δ))`. -/
theorem exists_norm_le_of_hasSum_of_le_of_le {s δ : ℝ} {N : ℕ} (hsδ : 0 < s + δ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hN : s + δ < N * (1 - δ)) :
    ∃ E, 0 ≤ E ∧ ∀ {F : Type*} [NormedAddCommGroup F] {f : ℕ → F} {L : F} {C D d r : ℝ},
      HasSum f L → 0 ≤ C → 0 ≤ D → 0 ≤ d → 0 < r →
      (∀ j, ‖f j‖ ≤ D * ((2 : ℝ) ^ j) ^ (s + 1) * d) →
      (∀ j, ‖f j‖ ≤ C * ((2 : ℝ) ^ j) ^ s * (1 + 2 ^ j * r) ^ (-(N : ℝ))) →
      ‖L‖ ≤ E * D ^ δ * C ^ (1 - δ) * d ^ δ * r ^ (-(s + δ)) := by
  obtain ⟨E, hE0, hE⟩ := exists_tsum_rpow_mul_one_add_rpow_neg_le hsδ hN
  refine ⟨E, hE0, fun {F} _ {f L C D d r} hf hC hD hd hr hA hB ↦ ?_⟩
  obtain ⟨hsum, hle⟩ := hE r hr
  set c := D ^ δ * C ^ (1 - δ) * d ^ δ with hc
  -- The interpolated bound of the `j`-th term.
  have hterm (j : ℕ) : ‖f j‖ ≤ c * (((2 : ℝ) ^ j) ^ (s + δ) *
      (1 + 2 ^ j * r) ^ (-(N * (1 - δ)))) := by
    refine (Real.le_rpow_mul_rpow_of_le_of_le (norm_nonneg _) (hA j) (hB j) hδ0.le
      hδ1.le).trans_eq ?_
    have hexp : ((2 : ℝ) ^ j) ^ (s + δ) = ((2 : ℝ) ^ j) ^ ((s + 1) * δ) *
        ((2 : ℝ) ^ j) ^ (s * (1 - δ)) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    rw [hexp, show -(N * (1 - δ)) = -(N : ℝ) * (1 - δ) by ring, hc]
    simp (disch := positivity) only [Real.mul_rpow, ← Real.rpow_mul]
    ring
  calc ‖L‖ ≤ c * ∑' j : ℕ, ((2 : ℝ) ^ j) ^ (s + δ) * (1 + 2 ^ j * r) ^ (-(N * (1 - δ))) :=
        tsum_of_norm_bounded (hsum.mul_left c).hasSum hterm |>.trans_eq' (by rw [hf.tsum_eq])
          |>.trans_eq (tsum_mul_left)
    _ ≤ c * (E * r ^ (-(s + δ))) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = E * D ^ δ * C ^ (1 - δ) * d ^ δ * r ^ (-(s + δ)) := by ring

/-- **Counting comparable dyadic scales.** If `Q ≥ 1`, at most `2Q + 1` indices `k` satisfy both
`2^j ≤ Q 2^k` and `2^k ≤ Q 2^j`. -/
theorem card_filter_two_pow_le_mul_two_pow_le (s : Finset ℕ) (j : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ((s.filter fun k ↦ (2 : ℝ) ^ j ≤ Q * 2 ^ k ∧ (2 : ℝ) ^ k ≤ Q * 2 ^ j).card : ℝ) ≤
      2 * Q + 1 := by
  set d := ⌊Q⌋₊
  -- A power `2^i ≤ Q` has `i < 2^i ≤ Q`, so `i ≤ d`.
  have hd {i l : ℕ} (h : (2 : ℝ) ^ i ≤ Q * 2 ^ l) : i - l ≤ d := by
    refine Nat.le_floor ((Nat.cast_le.2 (Nat.lt_two_pow_self).le).trans ?_)
    rcases le_total l i with hli | hil
    · rw [Nat.cast_pow, Nat.cast_ofNat]
      have h2 : (2 : ℝ) ^ (i - l) * 2 ^ l ≤ Q * 2 ^ l := by rwa [← pow_add, Nat.sub_add_cancel hli]
      exact le_of_mul_le_mul_right h2 (by positivity)
    · simpa [Nat.sub_eq_zero_of_le hil] using hQ
  have hsub : (s.filter fun k ↦ (2 : ℝ) ^ j ≤ Q * 2 ^ k ∧ (2 : ℝ) ^ k ≤ Q * 2 ^ j) ⊆
      Finset.Icc (j - d) (j + d) := fun k hk ↦ by
    obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.1 hk).2
    have := hd h₁
    have := hd h₂
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  calc ((s.filter fun k ↦ (2 : ℝ) ^ j ≤ Q * 2 ^ k ∧ (2 : ℝ) ^ k ≤ Q * 2 ^ j).card : ℝ)
      ≤ (Finset.Icc (j - d) (j + d)).card := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 * d + 1 := by
        rw [Nat.card_Icc]
        exact_mod_cast (by omega : j + d + 1 - (j - d) ≤ 2 * d + 1)
    _ ≤ 2 * Q + 1 := by gcongr; exact Nat.floor_le (by linarith)

/-- If `2^j ≤ Q 2^k` and `2^k ≤ Q 2^j`, then `2^{σ (j - k)} ≤ Q ^ |σ|` for every real `σ`. -/
theorem two_rpow_mul_sub_le_rpow_abs {j k : ℕ} {Q : ℝ} (h₁ : (2 : ℝ) ^ j ≤ Q * 2 ^ k)
    (h₂ : (2 : ℝ) ^ k ≤ Q * 2 ^ j) (σ : ℝ) :
    (2 : ℝ) ^ (σ * ((j : ℝ) - k)) ≤ Q ^ |σ| := by
  have hle {i l : ℕ} (h : (2 : ℝ) ^ i ≤ Q * 2 ^ l) : (2 : ℝ) ^ ((i : ℝ) - l) ≤ Q := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast, Real.rpow_natCast, div_le_iff₀ (by positivity)]
    exact h
  rcases le_total 0 σ with hσ | hσ
  · rw [abs_of_nonneg hσ, mul_comm, Real.rpow_mul zero_le_two]
    exact Real.rpow_le_rpow (by positivity) (hle h₁) hσ
  · rw [abs_of_nonpos hσ, show σ * ((j : ℝ) - k) = ((k : ℝ) - j) * -σ by ring,
      Real.rpow_mul zero_le_two]
    exact Real.rpow_le_rpow (by positivity) (hle h₂) (by linarith)

/-- For `u > 0`, the weights `2^{u(j-k)}` of the indices `j < k` in any finite set of integers sum
to at most `1 / (2^u - 1)`, the sum of the geometric series of ratio `2^{-u}` without its first
term. -/
theorem sum_ite_two_rpow_le {u : ℝ} (hu : 0 < u) (F : Finset ℤ) (k : ℤ) :
    ∑ j ∈ F, (if j < k then (2 : ℝ) ^ (u * (j - k : ℝ)) else 0) ≤ 1 / (2 ^ u - 1) := by
  set q : ℝ := (2 : ℝ) ^ (-u)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have key : ∀ j ∈ F.filter (· < k), (2 : ℝ) ^ (u * (j - k : ℝ)) = q * q ^ (k - j - 1).toNat := by
    intro j hj
    have hjk : j < k := (Finset.mem_filter.1 hj).2
    have hcast : (((k - j - 1).toNat : ℕ) : ℝ) = k - j - 1 := by
      have : ((k - j - 1).toNat : ℤ) = k - j - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [← Real.rpow_natCast, hcast, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
    congr 1
    ring
  rw [← Finset.sum_filter, Finset.sum_congr rfl key, ← Finset.mul_sum,
    ← Finset.sum_image (g := fun j : ℤ ↦ (k - j - 1).toNat) (f := fun n : ℕ ↦ q ^ n)]
  · calc q * ∑ n ∈ (F.filter (· < k)).image fun j : ℤ ↦ (k - j - 1).toNat, q ^ n
        ≤ q * ∑' n : ℕ, q ^ n :=
          mul_le_mul_of_nonneg_left (Summable.sum_le_tsum _ (fun _ _ ↦ by positivity)
            (summable_geometric_of_lt_one hq0 hq1)) hq0
      _ = 1 / (2 ^ u - 1) := by
          have h2 : (1 : ℝ) < 2 ^ u := Real.one_lt_rpow one_lt_two hu
          rw [tsum_geometric_of_lt_one hq0 hq1, show q = (2 ^ u)⁻¹ from Real.rpow_neg zero_le_two u]
          field_simp
  · intro x hx y hy hxy
    have := (Finset.mem_filter.1 hx).2
    have := (Finset.mem_filter.1 hy).2
    simp only at hxy
    omega

open scoped ENNReal NNReal

/-- `m ↦ 2^{-r|m|}` is summable over `ℤ` for `r > 0`: it is the bilateral geometric series of ratio
`2^{-r} < 1`. -/
theorem summable_two_rpow_neg_mul_abs {r : ℝ} (hr : 0 < r) :
    Summable fun m : ℤ ↦ (2 : ℝ) ^ (-r * |(m : ℝ)|) := by
  refine (summable_pow_natAbs (r := (2 : ℝ) ^ (-r)) (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))).congr fun m ↦ ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, Nat.cast_natAbs, Int.cast_abs]

/-- `∑_{m ∈ ℤ} 2^{-ε |m|}` is finite for `ε > 0`: it is the bilateral geometric series of ratio
`2^{-ε} < 1`. -/
theorem tsum_two_rpow_neg_mul_abs_ne_top {ε : ℝ} (hε : 0 < ε) :
    ∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(ε * |(m : ℝ)|)) ≠ ∞ := by
  have hterm (m : ℤ) :
      (2 : ℝ≥0∞) ^ (-(ε * |(m : ℝ)|)) = ENNReal.ofReal ((2 : ℝ) ^ (-ε * |(m : ℝ)|)) := by
    rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat, neg_mul]
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
    (summable_two_rpow_neg_mul_abs hε)]
  exact ENNReal.ofReal_ne_top

/-- For `σ ≥ 1` and `ε > 0`, `∑_{j ∈ ℤ} 2^{-ε |x - σ j|}` is bounded uniformly in `x`: the points
`σ j` are `1`-separated, so the sum is at most `2^ε ∑_{m ∈ ℤ} 2^{-ε |m|}`. -/
theorem tsum_two_rpow_neg_mul_abs_sub_le {σ ε : ℝ} (hσ : 1 ≤ σ) (hε : 0 < ε) (x : ℝ) :
    ∑' j : ℤ, (2 : ℝ≥0∞) ^ (-(ε * |x - σ * j|)) ≤
      2 ^ ε * ∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(ε * |(m : ℝ)|)) := by
  have hσ0 : 0 < σ := one_pos.trans_le hσ
  have hfl := Int.floor_le (x / σ)
  have hlt := Int.lt_floor_add_one (x / σ)
  set n : ℤ := ⌊x / σ⌋
  have hj (j : ℤ) : (2 : ℝ≥0∞) ^ (-(ε * |x - σ * j|)) ≤
      2 ^ ε * (2 : ℝ≥0∞) ^ (-(ε * |((j - n : ℤ) : ℝ)|)) := by
    rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    -- `|x - σ j| ≥ |x / σ - j| ≥ |j - n| - 1`.
    have h1 : |x / σ - j| ≤ |x - σ * j| := by
      rw [show x - σ * j = σ * (x / σ - j) by field_simp, abs_mul, abs_of_pos hσ0]
      exact le_mul_of_one_le_left (abs_nonneg _) hσ
    have h2 : |((j - n : ℤ) : ℝ)| - 1 ≤ |x / σ - j| := by
      have h := abs_sub_le (j : ℝ) (x / σ) (n : ℝ)
      rw [abs_sub_comm (j : ℝ) (x / σ), abs_of_nonneg (by linarith : 0 ≤ x / σ - n)] at h
      push_cast
      linarith
    nlinarith
  calc _ ≤ ∑' j : ℤ, 2 ^ ε * (2 : ℝ≥0∞) ^ (-(ε * |((j - n : ℤ) : ℝ)|)) := tsum_le_tsum hj
    _ = 2 ^ ε * ∑' j : ℤ, (2 : ℝ≥0∞) ^ (-(ε * |((j - n : ℤ) : ℝ)|)) := ENNReal.tsum_mul_left
    _ = _ := by
        congr 1
        exact (Equiv.subRight n).tsum_eq fun m : ℤ ↦ (2 : ℝ≥0∞) ^ (-(ε * |(m : ℝ)|))

/-- **Splitting a shifted weight.** For `b > 0`, the weight `(b^{j+k})^s` of the index `j + k` is
the product of the weights `(b^j)^s` and `(b^k)^s`. -/
theorem ofReal_zpow_add_rpow {b : ℝ} (hb : 0 < b) (s : ℝ) (j k : ℤ) :
    ENNReal.ofReal ((b ^ (j + k)) ^ s) =
      ENNReal.ofReal ((b ^ j) ^ s) * ENNReal.ofReal ((b ^ k) ^ s) := by
  rw [zpow_add₀ hb.ne', Real.mul_rpow (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity)]

/-- **Shifting a dyadic weight.** Shifting the index of the weight `2^{lσ}` of a term `y` by `d`
costs the factor `2^{dσ}`: `∑_{d ∈ S} 2^{(d + l)σ} y = (∑_{d ∈ S} 2^{dσ}) 2^{lσ} y`. -/
theorem sum_ofReal_two_zpow_add_rpow_mul (σ : ℝ) (S : Finset ℤ) (l : ℤ) (y : ℝ≥0∞) :
    ∑ d ∈ S, ENNReal.ofReal (((2 : ℝ) ^ (d + l)) ^ σ) * y =
      ((∑ d ∈ S, (((2 : ℝ) ^ d) ^ σ).toNNReal : ℝ≥0) : ℝ≥0∞) *
        (ENNReal.ofReal (((2 : ℝ) ^ l) ^ σ) * y) := by
  rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [ENNReal.ofNNReal_toNNReal, ofReal_zpow_add_rpow two_pos]
  ring

/-- **Dyadic weights over a window.** If `w k` vanishes for `k` outside the window
`j - L < k < j + L` and is at most `B` inside it, then
`∑ₖ 2^{kσ} w k ≤ (∑_{-L < d < L} 2^{dσ}) 2^{jσ} B`. -/
theorem tsum_ofReal_two_zpow_rpow_mul_le_of_eq_zero (σ : ℝ) {L : ℕ} {j : ℤ} {w : ℤ → ℝ≥0∞}
    {B : ℝ≥0∞} (hfar : ∀ k ∉ Finset.Ioo (j - L) (j + L), w k = 0) (hnear : ∀ k, w k ≤ B) :
    ∑' k : ℤ, ENNReal.ofReal (((2 : ℝ) ^ k) ^ σ) * w k ≤
      ((∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal : ℝ≥0) : ℝ≥0∞) *
        (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * B) := by
  rw [tsum_eq_sum (s := Finset.Ioo (j - L) (j + L)) fun k hk ↦ by rw [hfar k hk, mul_zero],
    show Finset.Ioo (j - L) (j + L) = (Finset.Ioo (-(L : ℤ)) L).map (addRightEmbedding j) by
      rw [Finset.map_add_right_Ioo, neg_add_eq_sub, add_comm (L : ℤ)],
    Finset.sum_map, ← sum_ofReal_two_zpow_add_rpow_mul]
  refine Finset.sum_le_sum fun d _ ↦ ?_
  rw [addRightEmbedding_apply]
  gcongr
  exact hnear _

/-- A sum over the truncation `-N ≤ k < N` is at most the sum over all of `ℤ`. -/
theorem sum_range_sub_le_tsum (f : ℤ → ℝ≥0∞) (N : ℕ) :
    ∑ i ∈ Finset.range (2 * N), f ((i : ℤ) - N) ≤ ∑' k, f k := by
  rw [← Finset.sum_image (g := fun i : ℕ ↦ (i : ℤ) - N) (f := f)
    fun i _ i' _ h ↦ by simpa using h]
  exact sum_le_tsum _

end TauCeti

namespace AntitoneOn

open Set
open scoped ENNReal

/-- For a base `b > 1`, a function antitone on `(0, ∞)` is bounded on `(0, s]` by the step function
taking, on each interval `(b⁻¹ ^ (n + 1) s, b⁻¹ ^ n s]`, its value at the left endpoint. -/
theorem le_tsum_indicator_Ioc {R : ℝ → ℝ≥0∞} (hR : AntitoneOn R (Ioi 0)) {b : ℝ} (hb : 1 < b)
    {s u : ℝ} (hu : 0 < u) (hus : u ≤ s) :
    R u ≤ ∑' n : ℕ, (Ioc (b⁻¹ ^ (n + 1) * s) (b⁻¹ ^ n * s)).indicator
      (fun _ ↦ R (b⁻¹ ^ (n + 1) * s)) u := by
  have hs : 0 < s := hu.trans_le hus
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near ((one_le_div hu).2 hus) hb
  have hmem : u ∈ Ioc (b⁻¹ ^ (n + 1) * s) (b⁻¹ ^ n * s) := by
    rw [inv_pow, inv_pow, ← div_eq_inv_mul, ← div_eq_inv_mul]
    rw [div_lt_iff₀ hu, mul_comm] at hn₂
    rw [le_div_iff₀ hu, mul_comm] at hn₁
    exact ⟨(div_lt_iff₀ (by positivity)).2 hn₂, (le_div_iff₀ (by positivity)).2 hn₁⟩
  refine le_trans ?_ (le_tsum _ n)
  rw [indicator_of_mem hmem]
  exact hR (show 0 < b⁻¹ ^ (n + 1) * s by positivity) hu hmem.1.le

/-- For a base `b > 1`, a function antitone on `(0, ∞)` is bounded on `[s, ∞)`, `s > 0`, by the
step function taking, on each interval `[b ^ n s, b ^ (n + 1) s)`, its value at the left
endpoint. -/
theorem le_tsum_indicator_Ico {R : ℝ → ℝ≥0∞} (hR : AntitoneOn R (Ioi 0)) {b : ℝ} (hb : 1 < b)
    {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    R u ≤ ∑' n : ℕ, (Ico (b ^ n * s) (b ^ (n + 1) * s)).indicator (fun _ ↦ R (b ^ n * s)) u := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near ((one_le_div hs).2 hsu) hb
  have hmem : u ∈ Ico (b ^ n * s) (b ^ (n + 1) * s) :=
    ⟨(le_div_iff₀ hs).1 hn₁, (div_lt_iff₀ hs).1 hn₂⟩
  refine le_trans ?_ (le_tsum _ n)
  rw [indicator_of_mem hmem]
  exact hR (show 0 < b ^ n * s by positivity) (hs.trans_le hsu) hmem.1

end AntitoneOn
