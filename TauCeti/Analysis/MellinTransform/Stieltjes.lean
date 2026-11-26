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
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Expansion of Stieltjes transforms (DLMF 2.6.27, 2.6.30)

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

The case `α = 1` (DLMF 2.6.28), where `log z` appears, is not treated here.

## Main results

* `TauCeti.stieltjes_eq`: the exact identity DLMF 2.6.27, for `z` in the slit plane.
* `TauCeti.isBigO_stieltjes_remainder`: `R_n(z) = O(‖z‖^{-n-α})` in closed sectors.

## Implementation notes

DLMF derives 2.6.27 by distributional methods. Here it is proved by induction on `n`, without
distributions. The case `n = 0` is the definition of `R_0`. Passing from `n` to `n + 1`
uses `tⁿ⁺¹ / (t + z) = tⁿ - z tⁿ / (t + z)`: the first part gives
`∫₀^∞ tⁿ f_{n+1}(t) dt`, which is `𝓜f(n + 1)` because the Mellin integral of `f_{n+1}`
converges absolutely at `n + 1`. The new term `a_n t^{-n-α}` contributes the model integral
`∫₀^∞ t^{-α} / (t + z) dt = π / sin (π α) * z^{-α}` (`Complex.integral_cpow_neg_mul_inv_add`).
The continued Mellin transform at `s + 1 ≤ n` is unchanged by subtracting the term `k = n`.

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

/-- Near `0`, `t ^ m t ^ (-k-α) c` is integrable on `(0, 1]` for `k ≤ m`. -/
private theorem integrableOn_Ioc_pow_smul_cpow_smul (hα₁ : α < 1) {m k : ℕ} (hk : k ≤ m)
    (c : E) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ m • ((t : ℂ) ^ (-((k : ℂ) + α)) • c)) (Ioc 0 1) := by
  have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
  refine (integrableOn_Ioc_cpow_smul_cpow_smul (z := (m : ℂ) + 1) (w := -((k : ℂ) + α))
    (by simp; linarith) c).congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
  simp only [add_sub_cancel_right, cpow_natCast]

/-- Near `0`, `t ^ m` times the remainder after `j ≤ m + 1` terms is integrable on `(0, 1]`. -/
private theorem integrableOn_Ioc_pow_smul_sub_sum (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) {m j : ℕ} (hj : j ≤ m + 1) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ m •
      (f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k)) (Ioc 0 1) := by
  simp_rw [smul_sub, Finset.smul_sum]
  exact (integrableOn_Ioc_pow_smul hf m).sub (integrable_finsetSum _ fun k hk ↦
    integrableOn_Ioc_pow_smul_cpow_smul hα₁
      (Nat.lt_succ_iff.mp ((Finset.mem_range.mp hk).trans_le hj)) (a k))

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

/-- `t ^ m (t + z)⁻¹` times the remainder after `j` terms, `m ≤ j ≤ m + 1`, is integrable on
`(0, ∞)` for `z` in the slit plane. -/
private theorem integrableOn_pow_mul_inv_add_smul_sub_sum (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) {j : ℕ}
    (hj : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((j : ℂ) + α)))
    {m : ℕ} (hjm : j ≤ m + 1) (hmj : m ≤ j) {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ m * ((t : ℂ) + z)⁻¹) •
      (f t - ∑ k ∈ Finset.range j, (t : ℂ) ^ (-((k : ℂ) + α)) • a k)) (Ioi 0) := by
  obtain ⟨c, hc, hcz⟩ := exists_pos_mul_one_add_le_norm_ofReal_add hz
  have hinv {t : ℝ} (ht : 0 < t) : ‖((t : ℂ) + z)⁻¹‖ ≤ c⁻¹ * (1 + t)⁻¹ := by
    rw [norm_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) (hcz t ht.le)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- on `(0, 1]` the factor `(t + z)⁻¹` is bounded
    refine IntegrableOn.congr_fun ((integrableOn_Ioc_pow_smul_sub_sum (a := a) hα₁ hf hjm).bdd_smul
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
    exact Real.rpow_le_rpow_of_exponent_le ht (by simp; linarith)
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
    (Or.inr (by simp; linarith))

/-- At `n + 1`, the continued Mellin transform through `n + 1` terms is the absolutely convergent
Mellin integral of the remainder `f_{n+1}`. -/
private theorem mellinContAtTop_natCast_add_one_eq_integral [CompleteSpace E] (hα₀ : 0 < α)
    (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k)
      =O[atTop] fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + α))) :
    mellinContAtTop f a (fun k ↦ (k : ℂ) + α) (n + 1) ((n : ℂ) + 1) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n •
        (f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k) := by
  have hIoi := integrableOn_Ioi_cpow_smul_sub_sum hα₀ hf hn (w := (n : ℂ) + 1) (by simp)
  simp only [add_sub_cancel_right, cpow_natCast] at hIoi
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (integrableOn_Ioc_pow_smul_sub_sum hα₁ hf le_rfl) hIoi,
    mellinContAtTop_def]
  simp only [add_sub_cancel_right, cpow_natCast]
  -- on `(0, 1]` the subtracted terms integrate to the principal parts
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ n • ((t : ℂ) ^ (-((k : ℂ) + α)) • a k) =
        ((n : ℂ) + 1 - ((k : ℂ) + α))⁻¹ • a k := by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := integral_Ioc_cpow_smul_cpow_smul (z := (n : ℂ) + 1) (w := -((k : ℂ) + α))
      (by simp; linarith) (a k)
    simpa only [add_sub_cancel_right, cpow_natCast, ← sub_eq_add_neg] using h
  have hint (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :=
    integrableOn_Ioc_pow_smul_cpow_smul hα₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (a k)
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
  have h₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n • R' t) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine (integrableOn_Ioc_pow_smul_sub_sum hα₁ hf le_rfl).union ?_
    simpa only [add_sub_cancel_right, cpow_natCast] using
      integrableOn_Ioi_cpow_smul_sub_sum hα₀ hf hn (w := (n : ℂ) + 1) (by simp)
  have h₂ := integrableOn_pow_mul_inv_add_smul_sub_sum hα₀ hα₁ hf hn (m := n) le_rfl
    (Nat.le_succ n) hz
  have h₃ := integrableOn_pow_mul_inv_add_smul_sub_sum hα₀ hα₁ hf hn' (m := n) (Nat.le_succ n)
    le_rfl hz
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

/-! ### The remainder bound -/

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
      (Real.sin (δ / 2))⁻¹ * ((T + 1) / ‖z‖ * ‖((t : ℂ) ^ n * ((t : ℂ) + ((1 : ℝ) : ℂ))⁻¹) • g t‖ +
        C * (t ^ (-α) / (t + ‖z‖))) := by
  have hs0 : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [abs_nonneg z.arg, Real.pi_pos])
  have hψt : ‖((t : ℂ) ^ n * ((t : ℂ) + ((1 : ℝ) : ℂ))⁻¹) • g t‖ = t ^ n * ‖g t‖ / (t + 1) := by
    rw [← ofReal_add]
    simp only [norm_smul, norm_mul, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (by linarith : 0 ≤ t + 1)]
    ring
  have hX : 0 ≤ t ^ n * ‖g t‖ := by positivity
  -- `‖t + z‖ ≥ sin (δ / 2) (t + ‖z‖)` on the sector
  have hinv : ‖z + t‖⁻¹ ≤ (Real.sin (δ / 2))⁻¹ * (t + ‖z‖)⁻¹ := by
    rw [← mul_inv, add_comm t]
    exact inv_anti₀ (by positivity)
      (sin_half_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le hδ.le hz t)
  rw [norm_smul, norm_mul, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg ht.le,
    add_comm (t : ℂ) z]
  calc t ^ n * ‖z + t‖⁻¹ * ‖g t‖ ≤ t ^ n * ((Real.sin (δ / 2))⁻¹ * (t + ‖z‖)⁻¹) * ‖g t‖ := by
        gcongr
    _ = (Real.sin (δ / 2))⁻¹ * (t ^ n * ‖g t‖ / (t + ‖z‖)) := by ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hs0.le)
      rcases le_total t T with htT | hTt
      · -- for `t ≤ T`, compare with `ψ`
        refine le_add_of_le_of_nonneg ?_ (by positivity)
        have hineq : ‖z‖ * (t + 1) ≤ (T + 1) * (t + ‖z‖) := by nlinarith
        rw [hψt, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hineq hX]
      · -- for `t ≥ T`, `tⁿ ‖g t‖ ≤ C t^{-α}`
        refine le_add_of_nonneg_of_le (by positivity) ?_
        have hgt := hT t hTt
        rw [norm_cpow_eq_rpow_re_of_pos ht] at hgt
        simp only [neg_re, add_re, natCast_re, ofReal_re] at hgt
        rw [← mul_div_assoc]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc t ^ n * ‖g t‖ ≤ t ^ n * (C * t ^ (-((n : ℝ) + α))) := by gcongr
          _ = C * t ^ (-α) := by
            rw [neg_add, Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_natCast]
            field_simp

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
  set ψ : ℝ → ℝ := fun t ↦ ‖((t : ℂ) ^ n * ((t : ℂ) + ((1 : ℝ) : ℂ))⁻¹) • R t‖
  have hψ : IntegrableOn ψ (Ioi 0) :=
    (integrableOn_pow_mul_inv_add_smul_sub_sum hα₀ hα₁ hf hn (Nat.le_succ n) le_rfl
      (ofReal_mem_slitPlane.mpr one_pos)).norm
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
  have hs0 : 0 ≤ (Real.sin (δ / 2))⁻¹ := inv_nonneg.mpr
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [abs_nonneg z.arg, Real.pi_pos])).le
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

end TauCeti
