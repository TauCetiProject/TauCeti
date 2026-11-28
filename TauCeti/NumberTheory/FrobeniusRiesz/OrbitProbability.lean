/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Chernoff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub

/-!
# The three bad-orbit probability bounds

For a Bernoulli sample of tops on a Frobenius orbit, the failure budget has three terms:
a short window with too many tops, a run of tiles without a mark, and a longer window with
more tops than the binomial cutoff. The sum of these terms is at most a constant times `x⁻²`
with the indicated density and window cutoffs, uniformly in the orbit length.

The three-term decomposition and the logarithmic tile cutoff are from L. Alpöge's
`Formalism.MainNotions.G.TopChoiceBounds.good_orbit_failure_prob_le`.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

namespace TauCeti.FrobeniusRiesz

/-- The lower bound for the mass of a marked tile with `3 * r` occupied cells, `3 * r + 1`
empty cells, and cell width `⌈1 / δ⌉`. The selection rates lie between `ω * δ` and `δ`. -/
noncomputable def markedTileMassBound (r : ℕ) (δ ω : ℝ) : ℝ :=
  let u := ⌈δ⁻¹⌉₊
  (1 - δ) ^ (u * (3 * r + 1)) * (((u / 2 : ℕ) : ℝ) * ω * δ * (1 - δ) ^ (u - 1)) ^ (3 * r)

/-- The marked-tile mass bound in terms of the cell width and selection rates. -/
theorem markedTileMassBound_def (r : ℕ) (δ ω : ℝ) :
    markedTileMassBound r δ ω =
      (1 - δ) ^ (⌈δ⁻¹⌉₊ * (3 * r + 1)) *
        (((⌈δ⁻¹⌉₊ / 2 : ℕ) : ℝ) * ω * δ * (1 - δ) ^ (⌈δ⁻¹⌉₊ - 1)) ^ (3 * r) := (rfl)

private theorem markedTileCellBounds {δ ω : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / 10) (hω : ω ∈ Icc (3 / 4) 1) :
    let u := ⌈δ⁻¹⌉₊
    (1 - δ) ^ u ∈ Icc (1 / 4) 1 ∧
      ((u / 2 : ℕ) : ℝ) * ω * δ * (1 - δ) ^ (u - 1) ∈ Icc (1 / 16) 1 := by
  let u := ⌈δ⁻¹⌉₊
  have hu₁ : 1 ≤ (u : ℝ) * δ := (inv_le_iff_one_le_mul₀ hδ).mp (Nat.le_ceil _)
  have hu₂ : (u : ℝ) * δ ≤ 1 + δ := by
    simpa [add_mul, inv_mul_cancel₀ hδ.ne'] using
      mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (inv_nonneg.mpr hδ.le)).le hδ.le
  have hb : 0 < 1 - δ := by linarith
  have hb₁ : 1 - δ ≤ 1 := by linarith
  have hfloor : (u : ℝ) - 1 ≤ 2 * ((u / 2 : ℕ) : ℝ) := by
    have hn : u ≤ 2 * (u / 2) + 1 := by omega
    exact sub_le_iff_le_add.mpr (by exact_mod_cast hn)
  have hcap : 2 * ((u / 2 : ℕ) : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast (Nat.mul_div_le u 2)
  have hfloorδ : (1 / 3 : ℝ) ≤ ((u / 2 : ℕ) : ℝ) * δ := by
    linarith [mul_le_mul_of_nonneg_right hfloor hδ.le]
  have hcapδ : ((u / 2 : ℕ) : ℝ) * δ ≤ 1 := by
    linarith [mul_le_mul_of_nonneg_right hcap hδ.le]
  have hpow : (1 / 4 : ℝ) ≤ (1 - δ) ^ u := by
    have hh := neg_log_one_sub_le_add_two_mul_sq (x := δ) (by linarith)
    have hlog : (33 / 25 : ℝ) ≤ log (2 * 2) := by
      rw [log_mul (by norm_num) (by norm_num)]
      linarith [log_two_gt_d9]
    apply (log_le_log_iff (by norm_num) (pow_pos hb _)).mp
    rw [one_div, log_inv, log_pow]
    have hstep : -log (1 - δ) ≤ (6 / 5) * δ := by
      nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hsmall)]
    norm_num at hlog
    linarith [mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg u)]
  have hcell : (1 / 4 : ℝ) ≤ ((u / 2 : ℕ) : ℝ) * ω * δ := by
    calc
      _ = (1 / 3 : ℝ) * (3 / 4) := by norm_num
      _ ≤ (((u / 2 : ℕ) : ℝ) * δ) * ω := by gcongr; exact hω.1
      _ = _ := by ring
  have hcell₁ : ((u / 2 : ℕ) : ℝ) * ω * δ ≤ 1 := by
    rw [mul_right_comm]
    exact (mul_le_mul hcapδ hω.2 (by linarith [hω.1]) zero_le_one).trans_eq (one_mul 1)
  have hpow' : (1 / 4 : ℝ) ≤ (1 - δ) ^ (u - 1) :=
    hpow.trans (pow_le_pow_of_le_one hb.le hb₁ (Nat.sub_le ..))
  have h₁ : (1 - δ) ^ (u - 1) ≤ 1 := pow_le_one₀ hb.le hb₁
  refine ⟨⟨hpow, pow_le_one₀ hb.le hb₁⟩, ⟨?_, ?_⟩⟩
  · calc
      (1 / 16 : ℝ) = (1 / 4 : ℝ) * (1 / 4) := by norm_num
      _ ≤ _ := mul_le_mul hcell hpow' (by norm_num) (by linarith)
  · simpa only [one_mul] using
      mul_le_mul hcell₁ h₁ (pow_nonneg hb.le _) (zero_le_one (α := ℝ))

/-- For small density and profile at least `3 / 4`, the marked-tile mass bound has a
positive lower bound independent of the density. -/
theorem markedTileMassBound_mem_Icc (r : ℕ) {δ ω : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / 10) (hω : ω ∈ Icc (3 / 4) 1) :
    markedTileMassBound r δ ω ∈ Icc ((1 / 10 : ℝ) ^ (6 * r + 1)) 1 := by
  obtain ⟨he, ho⟩ := markedTileCellBounds hδ hsmall hω
  rw [markedTileMassBound_def, pow_mul]
  -- Use one factor `1 / 4` per empty cell and `1 / 16` per occupied cell.
  constructor
  · calc
      _ = (1 / 10 : ℝ) * ((1 / 10 : ℝ) ^ 6) ^ r := by
        rw [pow_succ, pow_mul, mul_comm]
      _ ≤ (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ 3 * (1 / 16 : ℝ) ^ 3) ^ r := by
        gcongr <;> norm_num
      _ = (1 / 4 : ℝ) ^ (3 * r + 1) * (1 / 16 : ℝ) ^ (3 * r) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, pow_succ]
        ring
      _ ≤ _ := mul_le_mul
        (pow_le_pow_left₀ (by norm_num) he.1 _) (pow_le_pow_left₀ (by norm_num) ho.1 _)
        (by positivity) (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans he.1) _)
  · have he₀ := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans he.1
    have ho₀ := (by norm_num : (0 : ℝ) ≤ 1 / 16).trans ho.1
    simpa only [one_mul] using
      mul_le_mul (pow_le_one₀ he₀ he.2) (pow_le_one₀ ho₀ ho.2) (pow_nonneg ho₀ _)
        (zero_le_one (α := ℝ))

/-- A run of `M` tiles with a marking probability bounded below by `10⁻⁽⁶ʳ⁺¹⁾` has a
no-mark probability bound of at most `x^(-c)` once `M ≥ 10^(6*r+1) * c * log x`. -/
private theorem markedTileGap_le_rpow {r M : ℕ} {q c x : ℝ}
    (hx : 0 < x) (hq : q ∈ Icc ((1 / 10 : ℝ) ^ (6 * r + 1)) 1)
    (hM : (10 : ℝ) ^ (6 * r + 1) * c * log x ≤ M) : (1 - q) ^ M ≤ x ^ (-c) := by
  have hMq : c * log x ≤ (M : ℝ) * q := by
    calc
      _ = ((10 : ℝ) ^ (6 * r + 1) * c * log x) * (1 / 10 : ℝ) ^ (6 * r + 1) := by
        have hinv : (10 : ℝ) ^ (6 * r + 1) * (1 / 10 : ℝ) ^ (6 * r + 1) = 1 := by
          rw [← mul_pow]; norm_num
        calc
          _ = (10 ^ (6 * r + 1) * (1 / 10 : ℝ) ^ (6 * r + 1)) * (c * log x) := by
            rw [hinv, one_mul]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul hM hq.1 (by positivity) (Nat.cast_nonneg _)
  calc
    _ ≤ exp (-q) ^ M := pow_le_pow_left₀ (sub_nonneg.mpr hq.2) (one_sub_le_exp_neg q) _
    _ ≤ x ^ (-c) := by
      rw [← exp_natCast_mul, rpow_def_of_pos hx]
      exact exp_le_exp.mpr (by linarith)

/-- Numerical bad-orbit budget for the short window, marked-tile gap and long window terms.
Here `d` controls the decay of the selection density, `h` the orbit length, `L` the short
window length, `M` the number of tiles tested, and `G, k` the binomial window size and cutoff. -/
theorem badOrbitProbabilityBound_le {x d h ω : ℝ} {n L r M G k : ℕ} (δ : unitInterval)
    (hx : 1 ≤ x) (hδ : 0 < (δ : ℝ)) (hsmall : (δ : ℝ) ≤ 1 / 10)
    (hd : (δ : ℝ) ≤ x ^ (-d)) (hω : ω ∈ Icc (3 / 4) 1)
    (hn : (n : ℝ) ≤ 2 * x ^ h) (hr : h + 2 ≤ d * (r - 1 : ℕ))
    (hM : (10 : ℝ) ^ (6 * r + 1) * (h + 3) * log x ≤ M)
    (hk : 6 * (G : ℝ) * (δ : ℝ) ≤ k) (hklog : (h + 3) * log x ≤ log 2 * k) :
    (n : ℝ) * (L.choose (r - 1) : ℝ) * (δ : ℝ) ^ (r - 1) +
      n * (1 - markedTileMassBound r δ ω) ^ M + n * (binomial G δ).real (Ici k) ≤
      (2 * (L : ℝ) ^ (r - 1) + 4) * x ^ (-2 : ℝ) := by
  have hx₀ : 0 < x := by positivity
  have hshort : (δ : ℝ) ^ (r - 1) ≤ x ^ (-(h + 2)) := by
    calc
      _ ≤ (x ^ (-d)) ^ (r - 1) := by gcongr
      _ = x ^ ((-d) * (r - 1 : ℕ)) := by rw [rpow_mul hx₀.le, rpow_natCast]
      _ ≤ _ := rpow_le_rpow_of_exponent_le hx (by linarith)
  have htile := markedTileMassBound_mem_Icc r hδ hsmall hω
  have hgap := markedTileGap_le_rpow hx₀ htile hM
  have hlong : (binomial G δ).real (Ici k) ≤ x ^ (-(h + 3)) := by
    refine (TauCeti.Probability.measureReal_binomial_Ici_le_half_pow δ hk).trans ?_
    have hhalf : (1 / 2 : ℝ) = exp (-log 2) := by
      rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 2), one_div]
    rw [hhalf, ← exp_natCast_mul, rpow_def_of_pos hx₀]
    exact exp_le_exp.mpr (by linarith)
  have hchoose : (L.choose (r - 1) : ℝ) ≤ (L : ℝ) ^ (r - 1) := by
    exact_mod_cast Nat.choose_le_pow L (r - 1)
  calc
    _ ≤ (2 * x ^ h) * (L : ℝ) ^ (r - 1) * x ^ (-(h + 2)) +
        (2 * x ^ h) * x ^ (-(h + 3)) + (2 * x ^ h) * x ^ (-(h + 3)) := by
      gcongr
      exact pow_nonneg (sub_nonneg.mpr htile.2) _
    _ = 2 * (L : ℝ) ^ (r - 1) * x ^ (-2 : ℝ) + 2 * x ^ (-3 : ℝ) + 2 * x ^ (-3 : ℝ) := by
      have hx₂ : x ^ h * x ^ (-(h + 2)) = x ^ (-2 : ℝ) := by
        rw [← rpow_add hx₀]; congr 1; ring
      have hx₃ : x ^ h * x ^ (-(h + 3)) = x ^ (-3 : ℝ) := by
        rw [← rpow_add hx₀]; congr 1; ring
      calc
        _ = (2 * (L : ℝ) ^ (r - 1)) * (x ^ h * x ^ (-(h + 2))) +
            2 * (x ^ h * x ^ (-(h + 3))) + 2 * (x ^ h * x ^ (-(h + 3))) := by ring
        _ = _ := by rw [hx₂, hx₃]
    _ ≤ _ := by
      have := rpow_le_rpow_of_exponent_le hx (by norm_num : (-3 : ℝ) ≤ -2)
      linarith

/-- Uniform bad-orbit budget at the small positive density `x^(-d)` for all short windows of
length at most `L₀`. The threshold is independent of the orbit, tile and binomial window sizes. -/
theorem eventually_badOrbitProbabilityBound_le {d h : ℝ} {r : ℕ} (L₀ : ℕ)
    (hd : 0 < d) (hr : h + 2 ≤ d * (r - 1 : ℕ)) :
    ∀ᶠ x : ℝ in atTop, ∃ δ : unitInterval, (δ : ℝ) = x ^ (-d) ∧ (δ : ℝ) ∈ Ioc 0 (1 / 10) ∧
      ∀ (ω : ℝ) (n L M G k : ℕ),
        ω ∈ Icc (3 / 4) 1 → (n : ℝ) ≤ 2 * x ^ h → L ≤ L₀ →
        (10 : ℝ) ^ (6 * r + 1) * (h + 3) * log x ≤ M →
        6 * (G : ℝ) * (δ : ℝ) ≤ k → (h + 3) * log x ≤ log 2 * k →
        (n : ℝ) * (L.choose (r - 1) : ℝ) * (δ : ℝ) ^ (r - 1) +
          n * (1 - markedTileMassBound r δ ω) ^ M + n * (binomial G δ).real (Ici k) ≤
          (2 * (L₀ : ℝ) ^ (r - 1) + 4) * x ^ (-2 : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_neg_atTop hd).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))]
    with x hx hsmall
  have hpos : 0 < x ^ (-d) := by positivity
  let δ : unitInterval := ⟨x ^ (-d), hpos.le, hsmall.le.trans (by norm_num)⟩
  refine ⟨δ, rfl, ⟨hpos, hsmall.le⟩, ?_⟩
  intro ω n L M G k hω hn hL hM hk hklog
  refine (badOrbitProbabilityBound_le δ hx hpos hsmall.le le_rfl hω hn hr hM hk hklog).trans ?_
  gcongr

end TauCeti.FrobeniusRiesz
