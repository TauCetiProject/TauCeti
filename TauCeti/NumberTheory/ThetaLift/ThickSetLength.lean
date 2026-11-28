/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The relation length of a thick set for theta chains

The length of the forbidden relations has to be long enough for the local congruence
argument, but short enough for the construction of a dense thick set. The explicit
choice below bounds both logarithmic depth thresholds and grows at most logarithmically
with the scale, uniformly in the ranks and host size. The local depth requirement
is the one used in Levent Alpöge's formal proof of GRH, in `GlobalTheory.depth_spec`.
-/

public section

open Filter Real
open scoped Topology

namespace TauCeti.ThetaLift

/-- The even length used when excluding short relations in a thick set at scale `x`
with accuracy exponent `ε`. -/
noncomputable def thickSetLength (x ε : ℝ) : ℕ :=
  10 * ⌈405 * log x⌉₊ + 2 * ⌈30 / ε⌉₊ + 22

/-- The two rounded logarithmic contributions to the thick-set length. -/
theorem thickSetLength_def (x ε : ℝ) :
    thickSetLength x ε = 10 * ⌈405 * log x⌉₊ + 2 * ⌈30 / ε⌉₊ + 22 := (rfl)

/-- The thick-set relation length is at least `22`, including at scales where the
logarithmic terms round to zero. -/
theorem le_thickSetLength (x ε : ℝ) : 22 ≤ thickSetLength x ε := by
  rw [thickSetLength_def]
  omega

/-- The thick-set length is even. -/
@[simp] theorem even_thickSetLength (x ε : ℝ) : Even (thickSetLength x ε) := by
  rw [thickSetLength_def]
  exact ⟨5 * ⌈405 * log x⌉₊ + ⌈30 / ε⌉₊ + 11, by omega⟩

private theorem ceil_logb_le_thickSetTerm {b x z : ℝ} (hb : 1 < b) (hx : 0 < x)
    (hz : 0 ≤ z) (h : z ≤ x ^ (405 * log b)) : ⌈logb b z⌉₊ ≤ ⌈405 * log x⌉₊ := by
  rcases hz.eq_or_lt with rfl | hz
  · simp
  apply Nat.ceil_mono
  rw [logb_le_iff_le_rpow hb hz, rpow_def_of_pos (by linarith : 0 < b)]
  rw [rpow_def_of_pos hx] at h
  convert h using 2
  ring

/-- The relation length accommodates the base-ten congruence depth threshold
for source rank `k` and chain length `m`. -/
theorem congruenceDepth_le_thickSetLength {x ε : ℝ} {k m : ℕ} (hx : 0 < x)
    (hk : (k : ℝ) / m ≤ x ^ (405 * log 10 - 2 * ε)) :
    2 * ⌈logb 10 (k * x ^ (2 * ε) / m)⌉₊ + 2 ≤ thickSetLength x ε := by
  have h : k * x ^ (2 * ε) / m ≤ x ^ (405 * log 10) := calc
    _ = (k / (m : ℝ)) * x ^ (2 * ε) := mul_div_right_comm ..
    _ ≤ x ^ (405 * log 10 - 2 * ε) * x ^ (2 * ε) := by gcongr
    _ = _ := by rw [← rpow_add hx, sub_add_cancel]
  have hceil := ceil_logb_le_thickSetTerm (by norm_num : (1 : ℝ) < 10) hx (by positivity) h
  rw [thickSetLength_def]
  omega

/-- The relation length accommodates the base-five orbit threshold for host group size
`A`, final column rank `N` and chain length `m`. -/
theorem orbitDepth_le_thickSetLength {x ε : ℝ} {m A N : ℕ} (hx : 0 < x)
    (hA : (A : ℝ) ≤ x ^ (3 : ℝ)) (hN : (N : ℝ) ≤ x ^ (403 : ℝ)) :
    10 * ⌈logb 5 ((A : ℝ) * N / m)⌉₊ + 20 ≤ thickSetLength x ε := by
  have h : (A : ℝ) * N / m ≤ x ^ (405 * log 5) := by
    rcases le_or_gt 1 x with hx₁ | hx₁
    · calc
        _ ≤ (A : ℝ) * N := div_nat_le_self_of_nonneg (by positivity) m
        _ ≤ x ^ (3 : ℝ) * x ^ (403 : ℝ) := by gcongr
        _ = x ^ (406 : ℝ) := by rw [← rpow_add hx]; norm_num
        _ ≤ _ := rpow_le_rpow_of_exponent_le hx₁ (by linarith [log_five_gt_d9])
    · have hA' : (A : ℝ) < 1 := hA.trans_lt (rpow_lt_one hx.le hx₁ (by norm_num))
      have hAn : A < 1 := by exact_mod_cast hA'
      simp [Nat.lt_one_iff.mp hAn, rpow_nonneg hx.le]
  have hceil := ceil_logb_le_thickSetTerm (by norm_num : (1 : ℝ) < 5) hx (by positivity) h
  rw [thickSetLength_def]
  omega

/-- At thick-set density `δ ≥ x⁻ᵋ`, the depth threshold `k xᵋ / (m δ)` is reached by
some power of `ℓ - 1` within the available relation length. This applies to every
prime `ℓ ≥ 11`; primality is not needed for the power comparison. -/
theorem exists_congruenceDepth_le_thickSetLength {x ε δ : ℝ} {k m ℓ : ℕ}
    (hx : 0 < x) (hδ : x ^ (-ε) ≤ δ) (hℓ : 11 ≤ ℓ)
    (hk : (k : ℝ) / m ≤ x ^ (405 * log 10 - 2 * ε)) :
    ∃ j : ℕ, (k : ℝ) * x ^ ε / (m * δ) ≤ ((ℓ : ℝ) - 1) ^ j ∧
      2 * j + 2 ≤ thickSetLength x ε := by
  let z : ℝ := k * x ^ (2 * ε) / m
  let j := ⌈logb 10 z⌉₊
  refine ⟨j, ?_, congruenceDepth_le_thickSetLength (m := m) hx hk⟩
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzj : z ≤ (10 : ℝ) ^ j := by
    rcases hz.eq_or_lt with hz | hz
    · rw [← hz]; positivity
    rw [← rpow_natCast]
    exact (logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 10) hz).mp (Nat.le_ceil _)
  have hℓ' : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hbase : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  calc
    _ = (k * x ^ ε / m) / δ := by rw [div_div]
    _ ≤ (k * x ^ ε / m) / x ^ (-ε) := by gcongr
    _ = z := by
      have hpow : x ^ ε * x ^ ε = x ^ (2 * ε) := by rw [← rpow_add hx, two_mul]
      dsimp only [z]
      rw [rpow_neg hx.le, div_inv_eq_mul, div_mul_eq_mul_div, mul_assoc, hpow]
    _ ≤ (10 : ℝ) ^ j := hzj
    _ ≤ _ := by gcongr

/-- An explicit logarithmic upper bound for the relation length. The accuracy term
is truncated at zero, as is its natural-number ceiling. -/
theorem thickSetLength_le {x ε : ℝ} (hx : 1 ≤ x) :
    (thickSetLength x ε : ℝ) ≤ 4050 * log x + 2 * max (30 / ε) 0 + 34 := by
  have hx' : 0 ≤ 405 * log x := by positivity [log_nonneg hx]
  have h₁ := Nat.ceil_lt_add_one hx'
  have h₂ : (⌈30 / ε⌉₊ : ℝ) < max (30 / ε) 0 + 1 :=
    (Nat.cast_le.mpr (Nat.ceil_mono (le_max_left _ _))).trans_lt
      (Nat.ceil_lt_add_one (le_max_right _ _))
  rw [thickSetLength_def]
  push_cast
  linarith

/-- The thick-set relation length is eventually at most `C * log x` for every `C > 4050`.
The threshold may depend on `ε` but not on any ranks or field degrees. -/
theorem eventually_thickSetLength_le_mul_log (ε : ℝ) {C : ℝ} (hC : 4050 < C) :
    ∀ᶠ x : ℝ in atTop, (thickSetLength x ε : ℝ) ≤ C * log x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), tendsto_log_atTop.eventually_ge_atTop
    ((2 * max (30 / ε) 0 + 34) / (C - 4050))] with x hx hlog
  have h := (div_le_iff₀ (sub_pos.mpr hC)).mp hlog
  linarith [thickSetLength_le (ε := ε) hx]

/-- The logarithmic length is eventually below the squared-logarithm cutoff used in
the construction of dense thick sets. -/
theorem eventually_thickSetLength_le_log_sq (ε : ℝ) :
    ∀ᶠ x : ℝ in atTop, (thickSetLength x ε : ℝ) ≤ (log x) ^ 2 := by
  filter_upwards [eventually_thickSetLength_le_mul_log ε (by norm_num : (4050 : ℝ) < 4051),
    tendsto_log_atTop.eventually_ge_atTop 4051] with x hx hlog
  exact hx.trans (by nlinarith)

end TauCeti.ThetaLift
