/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.Continued
import TauCeti.Analysis.Complex.Sector.Bounds
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Analysis.SpecialFunctions.Beta.Complex
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Expansion of Stieltjes transforms (DLMF 2.6.27–2.6.30)

Let `f` be locally integrable on `[0, ∞)` with an expansion at `+∞`
`f(t) = ∑_{k<n} a_k t^{-k-α} + f_n(t)`, `f_n(t) = O(t^{-n-α})`, where `0 < α < 1`. Its Stieltjes
transform `∫₀^∞ f(t) / (t + z) dt` then has, for every `z` in the slit plane, the exact expansion
(DLMF 2.6.27)

`∫₀^∞ f(t) / (t + z) dt = π / sin (π α) ∑_{k<n} (-1)^k a_k z^{-k-α}
  + ∑_{s<n} (-1)^s 𝓜f(s + 1) z^{-s-1} + R_n(z)`,

`R_n(z) = (-1)ⁿ z⁻ⁿ ∫₀^∞ tⁿ f_n(t) / (t + z) dt` (DLMF 2.6.30), where
`𝓜f = mellinContAtTop f a (k ↦ k + α) n` is the Mellin transform of `f` continued through the
first `n` terms of the expansion (DLMF 2.5.28). In DLMF's notation `(s - 1)! c_s = (-1)^s 𝓜f(s)`,
so the second sum is `-∑_{s=1}^n (s - 1)! c_s z^{-s}`. The remainder is `O(‖z‖^{-n-α})` as
`z → ∞` in every closed sector `|arg z| ≤ π - δ`, `δ > 0`, so the identity is the asymptotic
expansion of the Stieltjes transform. The second sum is the part that termwise integration of the
expansion of `f` misses (DLMF 2.6.6–2.6.7).

For `α = 1`, where the terms of the expansion of `f` are `a_k t^{-k-1}`, the model integral
`∫₀^∞ t^{-1} / (t + z) dt` diverges at `0`, the continued Mellin transform has its poles exactly at
the points `s + 1` where the second sum evaluates it, and `log z` appears (DLMF 2.6.28):

`∫₀^∞ f(t) / (t + z) dt = ∑_{s<n} (-1)^s z^{-s-1} (a_s log z + d_s) + R_n(z)`,

with the same remainder `R_n` and `R_n(z) = O(‖z‖^{-n-1} log ‖z‖)` in closed sectors. The
constants are the finite parts `d_s = lim_{w → s+1} (𝓜f(w) + a_s / (w - s - 1))` of the continued
Mellin transform at its poles (DLMF 2.6.29, `TauCeti.tendsto_mellinContAtTop_add_inv_smul`); they
appear in the statement as `mellinContAtTop f a (k ↦ k + 1) n (s + 1)`, whose defining formula
drops the singular term at `w = s + 1`.

## Main results

* `TauCeti.stieltjes_eq`: the exact identity DLMF 2.6.27, for `z` in the slit plane.
* `TauCeti.isBigO_stieltjes_remainder`: `R_n(z) = O(‖z‖^{-n-α})` in closed sectors.
* `TauCeti.stieltjes_eq_log`: the exact identity DLMF 2.6.28 for `α = 1`.
* `TauCeti.isBigO_stieltjes_log_remainder`: `R_n(z) = O(‖z‖^{-n-1} log ‖z‖)` in closed sectors,
  for `α = 1`.

## Implementation notes

DLMF derives 2.6.27 by distributional methods. Here it is proved by induction on `n`, without
distributions. The case `n = 0` is the definition of `R_0`. Passing from `n` to `n + 1`
uses `tⁿ⁺¹ / (t + z) = tⁿ - z tⁿ / (t + z)`: the first part gives
`∫₀^∞ tⁿ f_{n+1}(t) dt`, which is `𝓜f(n + 1)` because the Mellin integral of `f_{n+1}`
converges absolutely at `n + 1`. The new term `a_n t^{-n-α}` contributes the model integral
`∫₀^∞ t^{-α} / (t + z) dt = π / sin (π α) * z^{-α}` (`Complex.integral_cpow_neg_mul_inv_add`).
The continued Mellin transform at `s + 1 ≤ n` is unchanged by subtracting the term `k = n`.

For `α = 1` the integral `∫₀^∞ tⁿ f_{n+1}(t) dt` diverges at `0`, so the induction step splits
`(0, ∞)` at `1` instead: on `(0, 1]` it keeps `f_n`, on `(1, ∞)` it subtracts the new term
`a_n t^{-n-1}`, whose contribution `∫₁^∞ t^{-1} / (t + z) dt = z⁻¹ log (1 + z)` combines with
`∫₀¹ 1 / (t + z) dt = log (1 + z) - log z` into `z⁻¹ log z`
(`Complex.integral_Ioi_inv_mul_inv_add`). What remains is `∫₀¹ tⁿ f_n + ∫₁^∞ tⁿ f_{n+1}`, which is
the continued Mellin transform at its pole `n + 1` with the singular term dropped.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.6(ii), equations (2.6.8)–(2.6.30),
  <https://dlmf.nist.gov/2.6.ii>.
-/

public section

open Filter Set Complex MeasureTheory Asymptotics
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {α : ℝ} {f : ℝ → E} {a : ℕ → E}

/-! ### Integrability of the remainders -/

/-- Near `0`, `t ^ m f(t)` is integrable on `(0, 1]`. -/
private theorem integrableOn_Ioc_pow_smul (hf : LocallyIntegrableOn f (Ici 0)) (m : ℕ) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ m • f t) (Ioc 0 1) := by
  refine ((hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).mono_set
    Ioc_subset_Icc_self).bdd_smul 1
    (by fun_prop : Continuous fun t : ℝ ↦ (t : ℂ) ^ m).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_pow, norm_real, Real.norm_of_nonneg ht.1.le]
  exact pow_le_one₀ ht.1.le ht.2

/-- Near `0`, `t ^ m t ^ (-k-α) c` is integrable on `(0, 1]` for `k + α < m + 1`. -/
private theorem integrableOn_Ioc_pow_smul_cpow_smul {m k : ℕ} (hkm : (k : ℝ) + α < m + 1)
    (c : E) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ m • ((t : ℂ) ^ (-((k : ℂ) + α)) • c)) (Ioc 0 1) := by
  refine (integrableOn_Ioc_cpow_smul_cpow_smul (z := (m : ℂ) + 1) (w := -((k : ℂ) + α))
    (by simp only [add_re, neg_re, natCast_re, ofReal_re, one_re]; linarith) c).congr_fun
    (fun t _ ↦ ?_) measurableSet_Ioc
  simp only [add_sub_cancel_right, cpow_natCast]

/-- Near `0`, `t ^ m` times the remainder after `j` terms, `j + α < m + 2`, is integrable on
`(0, 1]`. -/
private theorem integrableOn_Ioc_pow_smul_sub_sum
    (hf : LocallyIntegrableOn f (Ici 0)) {m j : ℕ} (hj : (j : ℝ) + α < m + 2) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ m •
      (f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k)) (Ioc 0 1) := by
  simp_rw [smul_sub, Finset.smul_sum]
  refine (integrableOn_Ioc_pow_smul hf m).sub (integrable_finsetSum _ fun k hk ↦
    integrableOn_Ioc_pow_smul_cpow_smul ?_ (a k))
  have hk : (k : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.mp hk
  linarith

/-- At `+∞`, `t ^ (w - 1)` times the remainder after `j ≥ Re w` terms is integrable on
`(1, ∞)`. -/
private theorem integrableOn_Ioi_cpow_smul_sub_sum (hα₀ : 0 < α)
    (hf : LocallyIntegrableOn f (Ici 0)) {j : ℕ}
    (hj : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((j : ℂ) + α)))
    {w : ℂ} (hw : w.re ≤ j) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (w - 1) •
      (f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k)) (Ioi 1) := by
  refine integrableOn_Ioi_cpow_smul_of_isBigO
    ((hf.mono_set Ioi_subset_Ici_self).sub (locallyIntegrableOn_sum_cpow_smul _ a j))
    (a := j + α) ?_ (by linarith)
  have h := hj.trans (isBigO_ofReal_cpow_rpow (eventually_gt_atTop 0) (-((j : ℂ) + α)))
  rwa [show (-((j : ℂ) + α)).re = -((j : ℝ) + α) by simp] at h

/-- `t ^ m (t + z)⁻¹` times the remainder after `j` terms, `m ≤ j` and `j + α < m + 2`, is
integrable on `(0, ∞)` for `z` in the slit plane. -/
private theorem integrableOn_pow_mul_inv_add_smul_sub_sum (hα₀ : 0 < α)
    (hf : LocallyIntegrableOn f (Ici 0)) {j : ℕ}
    (hj : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((j : ℂ) + α)))
    {m : ℕ} (hjm : (j : ℝ) + α < m + 2) (hmj : m ≤ j) {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ m * ((t : ℂ) + z)⁻¹) •
      (f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k)) (Ioi 0) := by
  obtain ⟨c, hc, hcz⟩ := exists_pos_mul_one_add_le_norm_ofReal_add hz
  have hinv {t : ℝ} (ht : 0 < t) : ‖((t : ℂ) + z)⁻¹‖ ≤ c⁻¹ * (1 + t)⁻¹ := by
    rw [norm_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) (hcz t ht.le)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- on `(0, 1]` the factor `(t + z)⁻¹` is bounded
    refine IntegrableOn.congr_fun ((integrableOn_Ioc_pow_smul_sub_sum (a := a) hf hjm).bdd_smul
      c⁻¹ (by fun_prop : Measurable fun t : ℝ ↦ ((t : ℂ) + z)⁻¹).aestronglyMeasurable ?_)
      (fun t _ ↦ by rw [Pi.smul_apply', smul_smul, mul_comm]) measurableSet_Ioc
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine (hinv ht.1).trans (mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ ?_))
    linarith [ht.1]
  · -- on `(1, ∞)` it is at most `c⁻¹ t⁻¹`
    refine ((integrableOn_Ioi_cpow_smul_sub_sum hα₀ hf hj (w := m)
      (by simpa using hmj)).norm.const_mul c⁻¹).mono'
      ((by fun_prop : Measurable fun t : ℝ ↦
        (t : ℂ) ^ m * ((t : ℂ) + z)⁻¹).aestronglyMeasurable.smul
      (((hf.mono_set Ioi_subset_Ici_self).sub (locallyIntegrableOn_sum_cpow_smul _ a j)).mono_set
        (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
    have ht0 : 0 < t := one_pos.trans ht
    simp only [norm_smul, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ht0.le,
      norm_cpow_eq_rpow_re_of_pos ht0, sub_re, natCast_re, one_re]
    rw [Real.rpow_sub_one ht0.ne', Real.rpow_natCast, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc t ^ m * ‖((t : ℂ) + z)⁻¹‖ ≤ t ^ m * (c⁻¹ * (1 + t)⁻¹) := by gcongr; exact hinv ht0
      _ ≤ t ^ m * (c⁻¹ * t⁻¹) := by gcongr; linarith
      _ = c⁻¹ * (t ^ m / t) := by ring

/-- `tⁿ` times the remainder after `n + 1` terms is integrable on `(0, ∞)`. -/
private theorem integrableOn_pow_smul_sub_sum_succ (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k)
      =O[atTop] fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + α))) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n •
      (f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine (integrableOn_Ioc_pow_smul_sub_sum hf (by push_cast; linarith)).union ?_
  simpa only [add_sub_cancel_right, cpow_natCast] using
    integrableOn_Ioi_cpow_smul_sub_sum hα₀ hf hn (w := (n : ℂ) + 1) (by simp)

/-! ### The expansion -/

/-- An expansion at `+∞` through `n + 1` terms gives one through `n` terms. -/
private theorem isBigO_sub_sum_of_succ {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k)
      =O[atTop] fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + α))) :
    (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)) := by
  have hle : (fun t : ℝ ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + α))) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [norm_cpow_eq_rpow_re_of_pos (one_pos.trans_le ht),
      norm_cpow_eq_rpow_re_of_pos (one_pos.trans_le ht), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le ht
      (by simp only [neg_re, add_re, natCast_re, ofReal_re, one_re, Nat.cast_add_one]; linarith)
  have hterm : (fun t : ℝ ↦ (t : ℂ) ^ (-((n : ℂ) + α)) • a n) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)) :=
    IsBigO.of_bound ‖a n‖ (Eventually.of_forall fun t ↦ by rw [norm_smul, mul_comm])
  refine ((hn.trans hle).add hterm).congr_left fun t ↦ ?_
  rw [Finset.sum_range_succ]
  abel

/-- Subtracting the term `k = n` does not change the continued Mellin transform at `s + 1`,
`s < n`. -/
private theorem mellinContAtTop_succ_natCast_add_one [CompleteSpace E] (hα₀ : 0 < α)
    (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)))
    {s : ℕ} (hs : s < n) :
    mellinContAtTop f a (fun k ↦ (k : ℂ) + α) (n + 1) ((s : ℂ) + 1) =
      mellinContAtTop f a (fun k ↦ (k : ℂ) + α) n ((s : ℂ) + 1) := by
  have hs' : (s : ℝ) + 1 ≤ n := by exact_mod_cast hs
  exact mellinContAtTop_succ (integrableOn_Ioi_cpow_smul_sub_sum hα₀ hf hn (by simpa using hs'))
    (Or.inr (by simp only [add_re, natCast_re, ofReal_re, one_re]; linarith))

/-- At `n + 1`, the continued Mellin transform through `n + 1` terms is the absolutely convergent
Mellin integral of the remainder `f_{n+1}`. -/
private theorem mellinContAtTop_natCast_add_one_eq_integral [CompleteSpace E] (hα₀ : 0 < α)
    (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k)
      =O[atTop] fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + α))) :
    mellinContAtTop f a (fun k ↦ (k : ℂ) + α) (n + 1) ((n : ℂ) + 1) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n •
        (f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k) := by
  have h := integrableOn_pow_smul_sub_sum_succ hα₀ hα₁ hf hn
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (h.mono_set Ioc_subset_Ioi_self) (h.mono_set (Ioi_subset_Ioi zero_le_one)),
    mellinContAtTop_def]
  simp only [add_sub_cancel_right, cpow_natCast]
  -- on `(0, 1]` the subtracted terms integrate to the principal parts
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ n • ((t : ℂ) ^ (-((k : ℂ) + α)) • a k) =
        ((n : ℂ) + 1 - ((k : ℂ) + α))⁻¹ • a k := by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := integral_Ioc_cpow_smul_cpow_smul (z := (n : ℂ) + 1) (w := -((k : ℂ) + α))
      (by simp only [add_re, neg_re, natCast_re, ofReal_re, one_re]; linarith) (a k)
    simpa only [add_sub_cancel_right, cpow_natCast, ← sub_eq_add_neg] using h
  have hint (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • ((t : ℂ) ^ (-((k : ℂ) + α)) • a k)) (Ioc 0 1) := by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact integrableOn_Ioc_pow_smul_cpow_smul (by linarith) (a k)
  rw [← Finset.sum_congr rfl hterm]
  simp_rw [smul_sub (_ : ℂ) (f _), Finset.smul_sum]
  rw [integral_sub (integrableOn_Ioc_pow_smul hf n) (integrable_finsetSum _ hint),
    integral_finsetSum _ hint]
  abel

/-- Splitting `tⁿ⁺¹ / (t + z) = tⁿ - z tⁿ / (t + z)` in the remainder integral: the first part is
a Mellin integral, the second the remainder integral of one order lower. -/
private theorem integral_pow_succ_mul_inv_add_smul {z : ℂ} (hz : z ∈ slitPlane) {n : ℕ}
    {g : ℝ → E} (h₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • g t) (Ioi 0))
    (h₂ : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t) (Ioi 0)) :
    ((-1) ^ (n + 1) * z⁻¹ ^ (n + 1)) • ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) • g t =
      -(((-1) ^ n * z⁻¹ ^ (n + 1)) • ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n • g t) +
        ((-1) ^ n * z⁻¹ ^ n) • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  rw [← integral_smul, ← integral_smul, ← integral_smul, ← integral_neg,
    ← integral_add (f := fun t : ℝ ↦ -(((-1) ^ n * z⁻¹ ^ (n + 1)) • (t : ℂ) ^ n • g t))
      (g := fun t : ℝ ↦ ((-1) ^ n * z⁻¹ ^ n) • ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t)
      (h₁.smul _).neg (h₂.smul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  have hne : (t : ℂ) + z ≠ 0 := by
    simpa [add_comm] using slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht.le)
  simp only [smul_smul, ← neg_smul, ← add_smul]
  congr 1
  linear_combination (-((-1) ^ n * z⁻¹ ^ (n + 1) * (t : ℂ) ^ n)) * mul_inv_cancel₀ hne +
    ((-1) ^ n * z⁻¹ ^ n * (t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) * mul_inv_cancel₀ hz0

/-- Subtracting `t^{-n-α} c` from `g` subtracts the model integral
`∫₀^∞ t^{-α} / (t + z) dt = π / sin (π α) * z^{-α}` times `c` from the remainder integral. -/
private theorem integral_pow_mul_inv_add_smul_sub_cpow_smul [CompleteSpace E] (hα₀ : 0 < α)
    (hα₁ : α < 1) {z : ℂ} (hz : z ∈ slitPlane) {n : ℕ} {g : ℝ → E}
    (hg : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t) (Ioi 0)) (c : E) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) •
        (g t - (t : ℂ) ^ (-((n : ℂ) + α)) • c) =
      (∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t) -
        (((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * z ^ (-(α : ℂ))) • c := by
  have hmodel : EqOn (fun t : ℝ ↦ ((t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + z)⁻¹) • c)
      (fun t : ℝ ↦ ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • ((t : ℂ) ^ (-((n : ℂ) + α)) • c))
      (Ioi 0) := fun t (ht : 0 < t) ↦ by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    dsimp only
    rw [smul_smul, neg_add, cpow_add _ _ ht0, cpow_neg _ (n : ℂ), cpow_natCast]
    field_simp
  simp_rw [smul_sub]
  rw [integral_sub hg (IntegrableOn.congr_fun
      ((integrableOn_cpow_neg_mul_inv_add hα₀ hα₁ hz).smul_const c) hmodel measurableSet_Ioi),
    ← integral_cpow_neg_mul_inv_add hα₀ hα₁ hz, ← integral_smul_const,
    setIntegral_congr_fun measurableSet_Ioi hmodel]

/-- The induction step for `TauCeti.stieltjes_eq`: the right side of the expansion through
`n + 1` terms equals the right side through `n` terms. -/
private theorem stieltjes_rhs_succ [CompleteSpace E] (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k)
      =O[atTop] fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + α)))
    {z : ℂ} (hz : z ∈ slitPlane) :
    ∑ k ∈ Finset.range (n + 1),
        ((-1) ^ k * ((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * z ^ (-((k : ℂ) + α))) • a k +
      ∑ s ∈ Finset.range (n + 1), ((-1) ^ s * z⁻¹ ^ (s + 1)) •
        mellinContAtTop f a (fun k ↦ (k : ℂ) + α) (n + 1) ((s : ℂ) + 1) +
      ((-1) ^ (n + 1) * z⁻¹ ^ (n + 1)) • ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) •
          (f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =
    ∑ k ∈ Finset.range n,
        ((-1) ^ k * ((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * z ^ (-((k : ℂ) + α))) • a k +
      ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
        mellinContAtTop f a (fun k ↦ (k : ℂ) + α) n ((s : ℂ) + 1) +
      ((-1) ^ n * z⁻¹ ^ n) • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) •
        (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hn' := isBigO_sub_sum_of_succ hn
  set R : ℝ → E := fun t ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k with hR
  set R' : ℝ → E := fun t ↦ f t - ∑ k ∈ Finset.range (n + 1),
    (t : ℂ) ^ (-((k : ℂ) + α)) • a k with hR'
  have hRR' (t : ℝ) : R' t = R t - (t : ℂ) ^ (-((n : ℂ) + α)) • a n := by
    simp only [hR, hR', Finset.sum_range_succ]
    abel
  -- integrability of the integrands that appear
  have h₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • R' t) (Ioi 0) :=
    integrableOn_pow_smul_sub_sum_succ hα₀ hα₁ hf hn
  have h₂ := integrableOn_pow_mul_inv_add_smul_sub_sum hα₀ hf hn (m := n)
    (by push_cast; linarith) (Nat.le_succ n) hz
  have h₃ := integrableOn_pow_mul_inv_add_smul_sub_sum hα₀ hf hn' (m := n) (by linarith) le_rfl hz
  have hJ : ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • R' t =
      (∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • R t) -
        (((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * z ^ (-(α : ℂ))) • a n := by
    simp_rw [hRR']
    exact integral_pow_mul_inv_add_smul_sub_cpow_smul hα₀ hα₁ hz h₃ (a n)
  have hK : ((-1) ^ n * z⁻¹ ^ n) * (((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) *
      z ^ (-(α : ℂ))) = (-1) ^ n * ((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) *
        z ^ (-((n : ℂ) + α)) := by
    rw [neg_add, cpow_add _ _ hz0, cpow_neg _ (n : ℂ), cpow_natCast, inv_pow]
    ring
  have hM : ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
      mellinContAtTop f a (fun k ↦ (k : ℂ) + α) (n + 1) ((s : ℂ) + 1) =
      ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
        mellinContAtTop f a (fun k ↦ (k : ℂ) + α) n ((s : ℂ) + 1) :=
    Finset.sum_congr rfl fun s hs ↦ by
      rw [mellinContAtTop_succ_natCast_add_one hα₀ hf hn' (Finset.mem_range.mp hs)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hM,
    mellinContAtTop_natCast_add_one_eq_integral hα₀ hα₁ hf hn,
    integral_pow_succ_mul_inv_add_smul hz h₁ h₂, hJ, smul_sub, smul_smul, hK]
  simp only [hR', hR]
  abel

/-- **Expansion of the Stieltjes transform** (DLMF 2.6.27, `0 < α < 1`). Let `f` be locally
integrable on `[0, ∞)` with `f(t) - ∑_{k<n} a_k t^{-k-α} = O(t^{-n-α})` as `t → +∞`. Then for
every `z` in the slit plane

`∫₀^∞ f(t) / (t + z) dt = π / sin (π α) ∑_{k<n} (-1)^k a_k z^{-k-α}
  + ∑_{s<n} (-1)^s z^{-s-1} 𝓜f(s + 1) + (-1)ⁿ z⁻ⁿ ∫₀^∞ tⁿ f_n(t) / (t + z) dt`,

with `f_n(t) = f(t) - ∑_{k<n} a_k t^{-k-α}` and `𝓜f = mellinContAtTop f a (k ↦ k + α) n` the
continued Mellin transform. All powers of `z` are principal. The last term is the remainder
`R_n(z)` of DLMF 2.6.30, which is `O(‖z‖^{-n-α})` in closed sectors
(`TauCeti.isBigO_stieltjes_remainder`). -/
theorem stieltjes_eq [CompleteSpace E] (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)))
    {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) + z)⁻¹ • f t =
      ∑ k ∈ Finset.range n,
          ((-1) ^ k * ((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * z ^ (-((k : ℂ) + α))) • a k +
        ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
          mellinContAtTop f a (fun k ↦ (k : ℂ) + α) n ((s : ℂ) + 1) +
        ((-1) ^ n * z⁻¹ ^ n) • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) •
          (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [stieltjes_rhs_succ hα₀ hα₁ hf hn hz]
    exact ih (isBigO_sub_sum_of_succ hn)

/-! ### The expansion for `α = 1` -/

/-- At `n + 1`, the continued Mellin transform through `n + 1` terms of an expansion with
exponents `k + 1` is the finite part `∫₀¹ tⁿ f_n(t) dt + ∫₁^∞ tⁿ f_{n+1}(t) dt`: the term `k = n`,
whose pole is at `n + 1`, drops out of the defining formula. -/
private theorem mellinContAtTop_natCast_add_one_eq_integral_add [CompleteSpace E]
    (hf : LocallyIntegrableOn f (Ici 0)) (n : ℕ) :
    mellinContAtTop f a (fun k ↦ (k : ℂ) + 1) (n + 1) ((n : ℂ) + 1) =
      (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ n •
        (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k)) +
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ n •
        (f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + 1)) • a k) := by
  have hk' {k : ℕ} (hk : k ∈ Finset.range n) : (k : ℝ) < n := by
    exact_mod_cast Finset.mem_range.mp hk
  -- on `(0, 1]` the subtracted terms `k < n` integrate to the principal parts
  have hterm (k : ℕ) (hk : k ∈ Finset.range n) :
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ n • ((t : ℂ) ^ (-((k : ℂ) + 1)) • a k) =
        ((n : ℂ) + 1 - ((k : ℂ) + 1))⁻¹ • a k := by
    have h := integral_Ioc_cpow_smul_cpow_smul (z := (n : ℂ) + 1) (w := -((k : ℂ) + 1))
      (by simp only [add_re, neg_re, natCast_re, one_re]; linarith [hk' hk]) (a k)
    simpa only [add_sub_cancel_right, cpow_natCast, ← sub_eq_add_neg] using h
  have hint (k : ℕ) (hk : k ∈ Finset.range n) :
      IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • ((t : ℂ) ^ (-((k : ℂ) + 1)) • a k)) (Ioc 0 1) := by
    simpa only [ofReal_one] using
      integrableOn_Ioc_pow_smul_cpow_smul (α := 1) (m := n) (by linarith [hk' hk]) (a k)
  rw [mellinContAtTop_def, Finset.sum_range_succ (fun k ↦ ((n : ℂ) + 1 - ((k : ℂ) + 1))⁻¹ • a k),
    sub_self, inv_zero, zero_smul, add_zero, ← Finset.sum_congr rfl hterm]
  simp only [add_sub_cancel_right, cpow_natCast]
  simp_rw [smul_sub (_ : ℂ) (f _), Finset.smul_sum]
  rw [integral_sub (integrableOn_Ioc_pow_smul hf n) (integrable_finsetSum _ hint),
    integral_finsetSum _ hint]
  abel

/-- The pointwise identities behind `TauCeti.integral_pow_mul_inv_add_smul_eq_log`: with
`h = g - t^{-n-1} c`, on `(0, 1]` and on `(1, ∞)` respectively,
`tⁿ (t + z)⁻¹ g = z⁻¹ tⁿ g - z⁻¹ tⁿ⁺¹ (t + z)⁻¹ h - z⁻¹ (t + z)⁻¹ c` and
`tⁿ (t + z)⁻¹ g = z⁻¹ tⁿ h - z⁻¹ tⁿ⁺¹ (t + z)⁻¹ h + t⁻¹ (t + z)⁻¹ c`. -/
private theorem pow_mul_inv_add_smul_eq {z : ℂ} (hz : z ∈ slitPlane) {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x c : E) :
    ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • x =
        z⁻¹ • ((t : ℂ) ^ n • x) - z⁻¹ • (((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) •
          (x - (t : ℂ) ^ (-((n : ℂ) + 1)) • c)) - (z⁻¹ * ((t : ℂ) + z)⁻¹) • c ∧
      ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • x =
        z⁻¹ • ((t : ℂ) ^ n • (x - (t : ℂ) ^ (-((n : ℂ) + 1)) • c)) -
          z⁻¹ • (((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) • (x - (t : ℂ) ^ (-((n : ℂ) + 1)) • c)) +
          ((t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹) • c := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have htz : (t : ℂ) + z ≠ 0 := by
    simpa [add_comm] using slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht.le)
  have hp : (t : ℂ) ^ (-((n : ℂ) + 1)) = ((t : ℂ) ^ (n + 1))⁻¹ := by
    rw [cpow_neg, ← Nat.cast_add_one, cpow_natCast]
  have hg : (t : ℂ) ^ n * ((t : ℂ) + z)⁻¹ =
      z⁻¹ * (t : ℂ) ^ n - z⁻¹ * ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) := by
    field_simp
    ring
  have hc₁ : z⁻¹ * ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) * (t : ℂ) ^ (-((n : ℂ) + 1)) -
      z⁻¹ * ((t : ℂ) + z)⁻¹ = 0 := by
    rw [hp]
    field_simp
    ring
  have hc₂ : -(z⁻¹ * (t : ℂ) ^ n * (t : ℂ) ^ (-((n : ℂ) + 1))) +
      z⁻¹ * ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) * (t : ℂ) ^ (-((n : ℂ) + 1)) +
      (t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹ = 0 := by
    rw [hp]
    field_simp
    ring
  constructor
  · linear_combination (norm := module) hg • x - hc₁ • c
  · linear_combination (norm := module) hg • x - hc₂ • c

/-- The induction step of `TauCeti.stieltjes_eq_log` for a remainder `g`, with
`h = g - t^{-n-1} c`. Splitting `(0, ∞)` at `1` and using `(t + z)⁻¹ = z⁻¹ - z⁻¹ t (t + z)⁻¹`,

`∫₀^∞ tⁿ g / (t + z) dt = z⁻¹ (log z • c + ∫₀¹ tⁿ g + ∫₁^∞ tⁿ h) - z⁻¹ ∫₀^∞ tⁿ⁺¹ h / (t + z) dt`.

The term `log z • c` comes from `∫₀¹ (t + z)⁻¹ dt = log (1 + z) - log z` and
`∫₁^∞ t⁻¹ (t + z)⁻¹ dt = z⁻¹ log (1 + z)`. -/
private theorem integral_pow_mul_inv_add_smul_eq_log [CompleteSpace E] {z : ℂ}
    (hz : z ∈ slitPlane) {n : ℕ} {g : ℝ → E} (c : E)
    (h₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • g t) (Ioc 0 1))
    (h₂ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • (g t - (t : ℂ) ^ (-((n : ℂ) + 1)) • c))
      (Ioi 1))
    (h₃ : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t) (Ioi 0))
    (h₄ : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) •
      (g t - (t : ℂ) ^ (-((n : ℂ) + 1)) • c)) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t =
      z⁻¹ • (log z • c + ((∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ n • g t) +
        ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ n • (g t - (t : ℂ) ^ (-((n : ℂ) + 1)) • c))) -
      z⁻¹ • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) •
        (g t - (t : ℂ) ^ (-((n : ℂ) + 1)) • c) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ (z⁻¹ * ((t : ℂ) + z)⁻¹) • c) (Icc 0 1) :=
    ((continuousOn_const.mul ((continuous_ofReal.add continuous_const).continuousOn.inv₀
      fun t ht ↦ by simpa [add_comm] using
        slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht.1))).smul continuousOn_const)
  have h₅ : IntegrableOn (fun t : ℝ ↦ (z⁻¹ * ((t : ℂ) + z)⁻¹) • c) (Ioc 0 1) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h₆ := (Complex.integrableOn_Ioi_inv_mul_inv_add one_pos hz).smul_const c
  -- `∫₀¹ (t + z)⁻¹ dt = log (1 + z) - log z`
  have hlog : ∫ t in Ioc (0 : ℝ) 1, ((t : ℂ) + z)⁻¹ = log (1 + z) - log z := by
    have h := TauCeti.integral_inv_linear_mul_eq_log_sub (u := 1) (z₀ := z) (d := 1) (a₀ := 0)
      (b₀ := 1) fun t ht ↦ by
        rw [uIcc_of_le zero_le_one] at ht
        simpa only [one_mul, mul_one] using add_ofReal_mem_slitPlane hz ht.1
    rw [intervalIntegral.integral_of_le zero_le_one] at h
    simpa only [mul_one, one_mul, ofReal_zero, ofReal_one, add_zero, zero_add, add_comm z] using h
  have hu := Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)
  have hd := Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1)
  -- the integrals over `(0, 1]` and `(1, ∞)`, by the pointwise identities
  have hI₁ : ∫ t in Ioc (0 : ℝ) 1, ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t =
      z⁻¹ • (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ n • g t) -
        z⁻¹ • (∫ t in Ioc (0 : ℝ) 1, ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) •
          (g t - (t : ℂ) ^ (-((n : ℂ) + 1)) • c)) -
        (z⁻¹ * (log (1 + z) - log z)) • c := by
    rw [setIntegral_congr_fun measurableSet_Ioc fun t ht ↦
        (pow_mul_inv_add_smul_eq hz ht.1 (g t) c).1, integral_sub ?_ h₅, integral_sub ?_ ?_,
      integral_smul, integral_smul, integral_smul_const, integral_const_mul, hlog]
    · exact h₁.smul z⁻¹
    · exact (h₄.mono_set Ioc_subset_Ioi_self).smul z⁻¹
    · exact (h₁.smul z⁻¹).sub ((h₄.mono_set Ioc_subset_Ioi_self).smul z⁻¹)
  have hI₂ : ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t =
      z⁻¹ • (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ n • (g t - (t : ℂ) ^ (-((n : ℂ) + 1)) • c)) -
        z⁻¹ • (∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) •
          (g t - (t : ℂ) ^ (-((n : ℂ) + 1)) • c)) +
        (z⁻¹ * (log (1 + z) - log 1)) • c := by
    have h := Complex.integral_Ioi_inv_mul_inv_add one_pos hz
    rw [ofReal_one] at h
    have h₄' := h₄.mono_set (Ioi_subset_Ioi zero_le_one)
    rw [setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦
        (pow_mul_inv_add_smul_eq hz (one_pos.trans ht) (g t) c).2, integral_add ?_ h₆,
      integral_sub ?_ ?_, integral_smul, integral_smul, integral_smul_const, h]
    · exact h₂.smul z⁻¹
    · exact h₄'.smul z⁻¹
    · exact (h₂.smul z⁻¹).sub (h₄'.smul z⁻¹)
  rw [← hu, setIntegral_union hd measurableSet_Ioi (h₃.mono_set Ioc_subset_Ioi_self)
      (h₃.mono_set (Ioi_subset_Ioi zero_le_one)),
    setIntegral_union hd measurableSet_Ioi (h₄.mono_set Ioc_subset_Ioi_self)
      (h₄.mono_set (Ioi_subset_Ioi zero_le_one)), hI₁, hI₂, log_one]
  module

/-- The induction step for `TauCeti.stieltjes_eq_log`: the right side of the expansion through
`n + 1` terms equals the right side through `n` terms. -/
private theorem stieltjes_log_rhs_succ [CompleteSpace E] (hf : LocallyIntegrableOn f (Ici 0))
    {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + 1)) • a k)
      =O[atTop] fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + 1)))
    {z : ℂ} (hz : z ∈ slitPlane) :
    ∑ s ∈ Finset.range (n + 1), ((-1) ^ s * z⁻¹ ^ (s + 1)) •
        (log z • a s + mellinContAtTop f a (fun k ↦ (k : ℂ) + 1) (n + 1) ((s : ℂ) + 1)) +
      ((-1) ^ (n + 1) * z⁻¹ ^ (n + 1)) • ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) •
          (f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + 1)) • a k) =
    ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
        (log z • a s + mellinContAtTop f a (fun k ↦ (k : ℂ) + 1) n ((s : ℂ) + 1)) +
      ((-1) ^ n * z⁻¹ ^ n) • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) •
        (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k) := by
  -- the hypotheses in the form of the general lemmas, at `α = 1`
  have hn₁ : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1),
      (t : ℂ) ^ (-((k : ℂ) + ((1 : ℝ) : ℂ))) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + ((1 : ℝ) : ℂ))) := by
    simpa only [ofReal_one] using hn
  have hn₀ := isBigO_sub_sum_of_succ hn₁
  set R : ℝ → E := fun t ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k with hR
  set R' : ℝ → E := fun t ↦ f t - ∑ k ∈ Finset.range (n + 1),
    (t : ℂ) ^ (-((k : ℂ) + 1)) • a k with hR'
  have hRR' (t : ℝ) : R t - (t : ℂ) ^ (-((n : ℂ) + 1)) • a n = R' t := by
    simp only [hR, hR', Finset.sum_range_succ]
    abel
  have h₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • R t) (Ioc 0 1) := by
    simpa only [ofReal_one] using
      integrableOn_Ioc_pow_smul_sub_sum (α := 1) (a := a) hf (m := n) (j := n) (by linarith)
  have h₂ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • R' t) (Ioi 1) := by
    simpa only [ofReal_one, add_sub_cancel_right, cpow_natCast] using
      integrableOn_Ioi_cpow_smul_sub_sum one_pos hf hn₁ (w := (n : ℂ) + 1) (by simp)
  have h₃ : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • R t) (Ioi 0) := by
    simpa only [ofReal_one] using
      integrableOn_pow_mul_inv_add_smul_sub_sum one_pos hf hn₀ (m := n) (by linarith) le_rfl hz
  have h₄ : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ (n + 1) * ((t : ℂ) + z)⁻¹) • R' t)
      (Ioi 0) := by
    simpa only [ofReal_one] using
      integrableOn_pow_mul_inv_add_smul_sub_sum one_pos hf hn₁ (m := n + 1) (by push_cast; linarith)
        le_rfl hz
  have hM : ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
      (log z • a s + mellinContAtTop f a (fun k ↦ (k : ℂ) + 1) (n + 1) ((s : ℂ) + 1)) =
      ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
        (log z • a s + mellinContAtTop f a (fun k ↦ (k : ℂ) + 1) n ((s : ℂ) + 1)) :=
    Finset.sum_congr rfl fun s hs ↦ by
      simpa only [ofReal_one] using congrArg (fun m ↦ ((-1) ^ s * z⁻¹ ^ (s + 1)) •
        (log z • a s + m)) (mellinContAtTop_succ_natCast_add_one one_pos hf hn₀
          (Finset.mem_range.mp hs))
  have hstep := integral_pow_mul_inv_add_smul_eq_log hz (a n) h₁
    (by simpa only [hRR'] using h₂) h₃ (by simpa only [hRR'] using h₄)
  simp only [hRR'] at hstep
  rw [Finset.sum_range_succ, hM, mellinContAtTop_natCast_add_one_eq_integral_add hf n, hstep]
  module

/-- **Expansion of the Stieltjes transform** (DLMF 2.6.28, `α = 1`). Let `f` be locally integrable
on `[0, ∞)` with `f(t) - ∑_{k<n} a_k t^{-k-1} = O(t^{-n-1})` as `t → +∞`. Then for every `z` in
the slit plane

`∫₀^∞ f(t) / (t + z) dt = ∑_{s<n} (-1)^s z^{-s-1} (a_s log z + d_s)
  + (-1)ⁿ z⁻ⁿ ∫₀^∞ tⁿ f_n(t) / (t + z) dt`,

with `f_n(t) = f(t) - ∑_{k<n} a_k t^{-k-1}` and the principal logarithm and powers. The constants
`d_s = mellinContAtTop f a (k ↦ k + 1) n (s + 1)` (DLMF's constants with a tilde, not the `d_s` of
DLMF 2.6.21) are the finite parts of the continued Mellin transform `𝓜f` at its poles `s + 1`:
`d_s = lim_{w → s+1} (𝓜f(w) + a_s / (w - s - 1))` (DLMF 2.6.29;
`TauCeti.tendsto_mellinContAtTop_add_inv_smul`, when `f = O(t^c)` at `0+` with `c > -1`).
Explicitly, `d_s = ∫₀¹ tˢ f_s(t) dt + ∫₁^∞ tˢ f_{s+1}(t) dt`. The last term is the remainder
`R_n(z)` of DLMF 2.6.30, which is `O(‖z‖^{-n-1} log ‖z‖)` in closed sectors
(`TauCeti.isBigO_stieltjes_log_remainder`). -/
theorem stieltjes_eq_log [CompleteSpace E] (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + 1)))
    {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) + z)⁻¹ • f t =
      ∑ s ∈ Finset.range n, ((-1) ^ s * z⁻¹ ^ (s + 1)) •
          (log z • a s + mellinContAtTop f a (fun k ↦ (k : ℂ) + 1) n ((s : ℂ) + 1)) +
        ((-1) ^ n * z⁻¹ ^ n) • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) •
          (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [stieltjes_log_rhs_succ hf hn hz]
    refine ih ?_
    simpa only [ofReal_one] using
      isBigO_sub_sum_of_succ (α := 1) (by simpa only [ofReal_one] using hn)

/-! ### The remainder bound -/

/-- On the sector `|arg z| ≤ π - δ`, the integrand of the remainder is at most
`sin (δ / 2)⁻¹ tⁿ ‖x‖ / (t + ‖z‖)`. -/
private theorem norm_pow_mul_inv_add_smul_le_div {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : |z.arg| ≤ Real.pi - δ) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • x‖ ≤
      (Real.sin (δ / 2))⁻¹ * (t ^ n * ‖x‖ / (t + ‖z‖)) := by
  -- `‖t + z‖ ≥ sin (δ / 2) (t + ‖z‖)` on the sector
  have hinv : ‖z + t‖⁻¹ ≤ (Real.sin (δ / 2))⁻¹ * (t + ‖z‖)⁻¹ := by
    rw [← mul_inv, add_comm t]
    exact inv_anti₀ (mul_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [abs_nonneg z.arg, Real.pi_pos])) (by positivity))
      (sin_half_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le hδ.le hz t)
  rw [norm_smul, norm_mul, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg ht.le,
    add_comm (t : ℂ) z]
  calc t ^ n * ‖z + t‖⁻¹ * ‖x‖ ≤ t ^ n * ((Real.sin (δ / 2))⁻¹ * (t + ‖z‖)⁻¹) * ‖x‖ := by
        gcongr
    _ = _ := by ring

/-- For `0 < t ≤ T` and `‖z‖ ≥ 1` in the sector `|arg z| ≤ π - δ`, the integrand of the
remainder is at most `sin (δ / 2)⁻¹ (T + 1) / ‖z‖ ψ(t)` with `ψ(t) = ‖tⁿ (t + 1)⁻¹ x‖`. -/
private theorem norm_pow_mul_inv_add_smul_le_of_le {n : ℕ} {T δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : |z.arg| ≤ Real.pi - δ) (hr : 1 ≤ ‖z‖) {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : E) :
    ‖((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • x‖ ≤
      (Real.sin (δ / 2))⁻¹ * ((T + 1) / ‖z‖ * ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • x‖) := by
  have hψt : ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • x‖ = t ^ n * ‖x‖ / (t + 1) := by
    rw [← ofReal_one, ← ofReal_add]
    simp only [norm_smul, norm_mul, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (by linarith : 0 ≤ t + 1)]
    ring
  have hX : 0 ≤ t ^ n * ‖x‖ := by positivity
  refine (norm_pow_mul_inv_add_smul_le_div hδ hz ht x).trans
    (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [abs_nonneg z.arg]))))
  have hineq : ‖z‖ * (t + 1) ≤ (T + 1) * (t + ‖z‖) := by nlinarith
  rw [hψt, div_mul_div_comm, div_le_div_iff₀ (by positivity)
    (mul_pos (one_pos.trans_le hr) (by positivity))]
  nlinarith [mul_le_mul_of_nonneg_left hineq hX]

/-- If `‖x‖ ≤ C t^{-n-α}`, then on the sector `|arg z| ≤ π - δ` the integrand of the remainder
is at most `sin (δ / 2)⁻¹ C t^{-α} / (t + ‖z‖)`. -/
private theorem norm_pow_mul_inv_add_smul_le_of_norm_le {n : ℕ} {C δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : |z.arg| ≤ Real.pi - δ) {t : ℝ} (ht : 0 < t) {x : E}
    (hx : ‖x‖ ≤ C * ‖(t : ℂ) ^ (-((n : ℂ) + α))‖) :
    ‖((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • x‖ ≤
      (Real.sin (δ / 2))⁻¹ * (C * (t ^ (-α) / (t + ‖z‖))) := by
  refine (norm_pow_mul_inv_add_smul_le_div hδ hz ht x).trans
    (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [abs_nonneg z.arg]))))
  rw [norm_cpow_eq_rpow_re_of_pos ht] at hx
  simp only [neg_re, add_re, natCast_re, ofReal_re] at hx
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc t ^ n * ‖x‖ ≤ t ^ n * (C * t ^ (-((n : ℝ) + α))) := by gcongr
    _ = C * t ^ (-α) := by
      rw [neg_add, Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_natCast]
      field_simp

/-- The pointwise bound behind `TauCeti.isBigO_stieltjes_remainder`. Let `g = f_n` with
`‖g t‖ ≤ C t^{-n-α}` for `t ≥ T`, `T ≥ 1`, and let `z` lie in the sector `|arg z| ≤ π - δ`
with `‖z‖ ≥ 1`. Then the integrand of the remainder is at most
`sin (δ / 2)⁻¹ ((T + 1) / ‖z‖ ψ(t) + C t^{-α} / (t + ‖z‖))`, where
`ψ(t) = tⁿ ‖g t‖ / (t + 1)` is integrable. -/
private theorem norm_pow_mul_inv_add_smul_le {g : ℝ → E} {n : ℕ} {C T δ : ℝ}
    (hT : ∀ t, T ≤ t → ‖g t‖ ≤ C * ‖(t : ℂ) ^ (-((n : ℂ) + α))‖) (hT1 : 1 ≤ T)
    (hC0 : 0 < C) (hδ : 0 < δ) {z : ℂ} (hz : |z.arg| ≤ Real.pi - δ) (hr : 1 ≤ ‖z‖) {t : ℝ}
    (ht : 0 < t) :
    ‖((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t‖ ≤
      (Real.sin (δ / 2))⁻¹ * ((T + 1) / ‖z‖ * ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • g t‖ +
        C * (t ^ (-α) / (t + ‖z‖))) := by
  have hs : 0 ≤ (Real.sin (δ / 2))⁻¹ := inv_nonneg.mpr
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [abs_nonneg z.arg]))
  rw [mul_add]
  rcases le_total t T with htT | hTt
  · exact le_add_of_le_of_nonneg (norm_pow_mul_inv_add_smul_le_of_le hδ hz hr ht htT (g t))
      (by positivity)
  · exact le_add_of_nonneg_of_le (by positivity)
      (norm_pow_mul_inv_add_smul_le_of_norm_le hδ hz ht (hT t hTt))

/-- **The remainder of the Stieltjes expansion** (DLMF 2.6.30, `0 < α < 1`). If `f` is locally
integrable on `[0, ∞)` and `f(t) - ∑_{k<n} a_k t^{-k-α} = O(t^{-n-α})` as `t → +∞`, then the
remainder `R_n(z) = (-1)ⁿ z⁻ⁿ ∫₀^∞ tⁿ f_n(t) / (t + z) dt` of `TauCeti.stieltjes_eq` is
`O(‖z‖^{-n-α})` as `z → ∞` in every closed sector `|arg z| ≤ π - δ`, `δ > 0`. -/
theorem isBigO_stieltjes_remainder (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)))
    {δ : ℝ} (hδ : 0 < δ) :
    (fun z : ℂ ↦ ((-1) ^ n * z⁻¹ ^ n) • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) •
        (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {z | |z.arg| ≤ Real.pi - δ}]
      fun z ↦ ‖z‖ ^ (-((n : ℝ) + α)) := by
  set R : ℝ → E := fun t ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k
  -- `‖R t‖ ≤ C t^{-n-α}` for `t ≥ T ≥ 1`
  obtain ⟨C, hC0, hC⟩ := hn.exists_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hC.bound.and (eventually_ge_atTop 1))
  set ψ : ℝ → ℝ := fun t ↦ ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • R t‖
  have hψ : IntegrableOn ψ (Ioi 0) :=
    (integrableOn_pow_mul_inv_add_smul_sub_sum hα₀ hf hn (by linarith) le_rfl
      one_mem_slitPlane).norm
  have hΨ : 0 ≤ ∫ t in Ioi (0 : ℝ), ψ t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ ↦ norm_nonneg _
  have hlow : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 {z | |z.arg| ≤ Real.pi - δ},
      1 ≤ ‖z‖ ∧ |z.arg| ≤ Real.pi - δ :=
    ((tendsto_norm_cobounded_atTop.eventually_ge_atTop 1).filter_mono inf_le_left).and
      (eventually_inf_principal.mpr (Eventually.of_forall fun _ h ↦ h))
  refine IsBigO.of_bound ((Real.sin (δ / 2))⁻¹ * ((T + 1) * ∫ t in Ioi (0 : ℝ), ψ t) +
    (Real.sin (δ / 2))⁻¹ * (C * (Real.pi / Real.sin (Real.pi * α)))) ?_
  filter_upwards [hlow] with z ⟨hr, hz⟩
  have hr0 : 0 < ‖z‖ := one_pos.trans_le hr
  have hs0 : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [abs_nonneg z.arg, Real.pi_pos])
  -- integrate the pointwise bound, with the real model integral `∫₀^∞ t^{-α} / (t + ‖z‖) dt`
  have hmodel := integrableOn_rpow_neg_div_add α ‖z‖ hα₀ hα₁ hr0
  have hI := norm_integral_le_of_norm_le (((hψ.const_mul _).add (hmodel.const_mul C)).const_mul _)
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦
      norm_pow_mul_inv_add_smul_le (fun t ht ↦ (hT t ht).1) (hT T le_rfl).2 hC0 hδ hz hr ht)
  rw [integral_const_mul] at hI
  simp only [Pi.add_apply] at hI
  rw [integral_add (hψ.const_mul _) (hmodel.const_mul C), integral_const_mul,
    integral_const_mul, integral_rpow_neg_div_add α ‖z‖ hα₀ hα₁ hr0] at hI
  -- `‖z‖⁻¹ ≤ ‖z‖^{-α}` for `‖z‖ ≥ 1`
  have hrα : ‖z‖⁻¹ ≤ ‖z‖ ^ (-α) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hkey : (T + 1) / ‖z‖ * (∫ t in Ioi (0 : ℝ), ψ t) ≤
      (T + 1) * (∫ t in Ioi (0 : ℝ), ψ t) * ‖z‖ ^ (-α) := by
    rw [div_mul_eq_mul_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrα (mul_nonneg (by linarith [(hT T le_rfl).2]) hΨ)
  simp only [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv,
    Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]
  rw [neg_add, Real.rpow_add hr0, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← inv_pow]
  calc ‖z‖⁻¹ ^ n * ‖∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • R t‖
      ≤ ‖z‖⁻¹ ^ n * ((Real.sin (δ / 2))⁻¹ * ((T + 1) / ‖z‖ * (∫ t in Ioi (0 : ℝ), ψ t) +
          C * (Real.pi / Real.sin (Real.pi * α) * ‖z‖ ^ (-α)))) := by gcongr
    _ ≤ ‖z‖⁻¹ ^ n * ((Real.sin (δ / 2))⁻¹ * ((T + 1) * (∫ t in Ioi (0 : ℝ), ψ t) * ‖z‖ ^ (-α) +
          C * (Real.pi / Real.sin (Real.pi * α) * ‖z‖ ^ (-α)))) := by gcongr
    _ = _ := by ring


/-! ### The remainder bound for `α = 1` -/

/-- `log (T + r) - log T ≤ (log (T + 1) + 1) log r` for `T ≥ 1`, `r ≥ 1` and `log r ≥ 1`. -/
private theorem log_add_sub_log_le {T r : ℝ} (hT : 1 ≤ T) (hr : 1 ≤ r) (hlog : 1 ≤ Real.log r) :
    Real.log (T + r) - Real.log T ≤ (Real.log (T + 1) + 1) * Real.log r := by
  have h₁ : 0 ≤ Real.log T := Real.log_nonneg hT
  have h₂ : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have h₃ : Real.log (T + r) ≤ Real.log (T + 1) + Real.log r := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  nlinarith

/-- The integrated bound behind `TauCeti.isBigO_stieltjes_log_remainder`. Let `g = f_n` with
`‖g t‖ ≤ C t^{-n-1}` for `t ≥ T`, `T ≥ 1`, and let `z` lie in the sector `|arg z| ≤ π - δ` with
`log ‖z‖ ≥ 1`. Then the remainder integral is at most `K log ‖z‖ / ‖z‖`, where
`K = sin (δ / 2)⁻¹ ((T + 1) ∫₀^∞ ψ + C (log (T + 1) + 1))` and `ψ(t) = tⁿ ‖g t‖ / (t + 1)`: the
integral over `(0, T]` is compared with `ψ`, the integral over `(T, ∞)` with
`∫_T^∞ (t (t + ‖z‖))⁻¹ dt = (log (T + ‖z‖) - log T) / ‖z‖`. -/
private theorem norm_integral_pow_mul_inv_add_smul_le_log {g : ℝ → E} {n : ℕ} {C T δ : ℝ}
    (hT : ∀ t, T ≤ t → ‖g t‖ ≤ C * ‖(t : ℂ) ^ (-((n : ℂ) + 1))‖) (hT1 : 1 ≤ T) (hC0 : 0 < C)
    (hδ : 0 < δ) {z : ℂ} (hz : |z.arg| ≤ Real.pi - δ) (hr : 1 ≤ ‖z‖)
    (hlog : 1 ≤ Real.log ‖z‖)
    (hF : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t) (Ioi 0))
    (hψ : IntegrableOn (fun t : ℝ ↦ ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • g t‖) (Ioi 0)) :
    ‖∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t‖ ≤
      ((Real.sin (δ / 2))⁻¹ * ((T + 1) *
          ∫ t in Ioi (0 : ℝ), ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • g t‖) +
        (Real.sin (δ / 2))⁻¹ * (C * (Real.log (T + 1) + 1))) * (Real.log ‖z‖ / ‖z‖) := by
  have hT0 : 0 < T := one_pos.trans_le hT1
  have hr0 : 0 < ‖z‖ := one_pos.trans_le hr
  have hs : 0 ≤ (Real.sin (δ / 2))⁻¹ := inv_nonneg.mpr
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [abs_nonneg z.arg]))
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hF.mono_set Ioc_subset_Ioi_self) (hF.mono_set (Ioi_subset_Ioi hT0.le))
  rw [Ioc_union_Ioi_eq_Ioi hT0.le] at hsplit
  -- on `(0, T]`, compare with `ψ`
  have h₁ : ‖∫ t in Ioc (0 : ℝ) T, ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t‖ ≤
      (Real.sin (δ / 2))⁻¹ * ((T + 1) / ‖z‖ *
        ∫ t in Ioi (0 : ℝ), ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • g t‖) := by
    refine (norm_integral_le_of_norm_le ((hψ.mono_set (Ioc_subset_Ioi_self :
      Ioc (0 : ℝ) T ⊆ Ioi 0)).const_mul ((Real.sin (δ / 2))⁻¹ * ((T + 1) / ‖z‖))) ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ⟨ht0, htT⟩
      rw [mul_assoc]
      exact norm_pow_mul_inv_add_smul_le_of_le hδ hz hr ht0 htT (g t)
    · rw [integral_const_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (setIntegral_mono_set hψ
        (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (ae_of_all _ fun _ hx ↦ Ioc_subset_Ioi_self hx)) (by positivity)) hs
  -- on `(T, ∞)`, `tⁿ ‖g t‖ ≤ C t⁻¹`
  have hb := Real.integrableOn_Ioi_inv_mul_add hT0 hr0
  have hbval := Real.integral_Ioi_inv_mul_add hT0 hr0
  have h₂ : ‖∫ t in Ioi T, ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) • g t‖ ≤
      (Real.sin (δ / 2))⁻¹ * (C * ((Real.log (T + ‖z‖) - Real.log T) / ‖z‖)) := by
    refine (norm_integral_le_of_norm_le ((hb.const_mul C).const_mul (Real.sin (δ / 2))⁻¹)
      ?_).trans (by rw [integral_const_mul, integral_const_mul, hbval])
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : T < t)
    have ht0 : 0 < t := hT0.trans ht
    have h := norm_pow_mul_inv_add_smul_le_of_norm_le (α := 1) hδ hz ht0
      (by simpa only [ofReal_one] using hT t ht.le)
    have he : t⁻¹ / (t + ‖z‖) = (t * (t + ‖z‖))⁻¹ := by rw [mul_inv, div_eq_mul_inv]
    rwa [Real.rpow_neg_one, he] at h
  have hlogT := log_add_sub_log_le hT1 hr hlog
  rw [hsplit]
  calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    _ ≤ (Real.sin (δ / 2))⁻¹ * ((T + 1) *
          (∫ t in Ioi (0 : ℝ), ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) • g t‖) * Real.log ‖z‖ / ‖z‖) +
        (Real.sin (δ / 2))⁻¹ * (C * ((Real.log (T + 1) + 1) * Real.log ‖z‖ / ‖z‖)) := by
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ hs) (mul_le_mul_of_nonneg_left ?_ hs)
      · rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hlog) hr0.le
      · gcongr
    _ = _ := by ring

/-- **The remainder of the Stieltjes expansion for `α = 1`** (DLMF 2.6.30). If `f` is locally
integrable on `[0, ∞)` and `f(t) - ∑_{k<n} a_k t^{-k-1} = O(t^{-n-1})` as `t → +∞`, then the
remainder `R_n(z) = (-1)ⁿ z⁻ⁿ ∫₀^∞ tⁿ f_n(t) / (t + z) dt` of `TauCeti.stieltjes_eq_log` is
`O(‖z‖^{-n-1} log ‖z‖)` as `z → ∞` in every closed sector `|arg z| ≤ π - δ`, `δ > 0`. -/
theorem isBigO_stieltjes_log_remainder (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    (fun z : ℂ ↦ ((-1) ^ n * z⁻¹ ^ n) • ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ n * ((t : ℂ) + z)⁻¹) •
        (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {z | |z.arg| ≤ Real.pi - δ}]
      fun z ↦ ‖z‖ ^ (-((n : ℝ) + 1)) * Real.log ‖z‖ := by
  have hF {z : ℂ} (hz : z ∈ slitPlane) : IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n *
      ((t : ℂ) + z)⁻¹) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k))
      (Ioi 0) := by
    simpa only [ofReal_one] using integrableOn_pow_mul_inv_add_smul_sub_sum one_pos hf
      (by simpa only [ofReal_one] using hn) (m := n) (by linarith) le_rfl hz
  -- `‖f_n t‖ ≤ C t^{-n-1}` for `t ≥ T ≥ 1`
  obtain ⟨C, hC0, hC⟩ := hn.exists_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hC.bound.and (eventually_ge_atTop 1))
  have hlow : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 {z | |z.arg| ≤ Real.pi - δ},
      Real.exp 1 ≤ ‖z‖ ∧ |z.arg| ≤ Real.pi - δ :=
    ((tendsto_norm_cobounded_atTop.eventually_ge_atTop _).filter_mono inf_le_left).and
      (eventually_inf_principal.mpr (Eventually.of_forall fun _ h ↦ h))
  refine IsBigO.of_bound ((Real.sin (δ / 2))⁻¹ * ((T + 1) * ∫ t in Ioi (0 : ℝ),
      ‖((t : ℂ) ^ n * ((t : ℂ) + 1)⁻¹) •
        (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + 1)) • a k)‖) +
    (Real.sin (δ / 2))⁻¹ * (C * (Real.log (T + 1) + 1))) ?_
  filter_upwards [hlow] with z ⟨hr, hz⟩
  have hr1 : 1 ≤ ‖z‖ := (Real.one_le_exp zero_le_one).trans hr
  have hr0 : 0 < ‖z‖ := one_pos.trans_le hr1
  have hlog : 1 ≤ Real.log ‖z‖ := (Real.le_log_iff_exp_le hr0).mpr hr
  have hI := norm_integral_pow_mul_inv_add_smul_le_log (fun t ht ↦ (hT t ht).1) (hT T le_rfl).2
    hC0 hδ hz hr1 hlog (hF (mem_slitPlane_of_abs_arg_le hδ hz (norm_pos_iff.mp hr0)))
    (hF one_mem_slitPlane).norm
  rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, norm_inv,
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _) (zero_le_one.trans hlog)),
    neg_add, Real.rpow_add hr0, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast,
    Real.rpow_neg_one, ← inv_pow]
  refine (mul_le_mul_of_nonneg_left hI (by positivity)).trans_eq ?_
  ring

end TauCeti
