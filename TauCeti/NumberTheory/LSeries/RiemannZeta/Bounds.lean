/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Right-half-plane integral representation and vertical bounds for `riemannZeta`

On `Re s > 1`, Euler–Maclaurin / Abel summation expresses the Riemann zeta function as

`ζ(s) = s / (s - 1) - s ∫₁^∞ {t} t^{-(s + 1)} dt`,

where `{t} = t - ⌊t⌋₊ ∈ [0, 1)` is the fractional part of `t`. Subtracting `(s - 1)⁻¹` gives

`riemannZeta₀ s = 1 - s ∫₁^∞ {t} t^{-(s + 1)} dt`.

Because `{t}` is bounded by `1`, the right-hand side is holomorphic on the entire open right
half-plane `Re s > 0`, so the identity principle extends both formulas from `Re s > 1` to
`Re s > 0`. Bounding `|{t}| ≤ 1` in the integral immediately gives the explicit vertical-line growth
bounds

`‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`   and   `‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s`

for all `Re s > 0` (including at `s = 1`, where Mathlib's junk value `(γ - log(4π)) / 2` has norm
strictly less than `2`). We also record the elementary bound `‖∏_{p ∣ N} (1 - p⁻ˢ)‖ ≤ N` on
`Re s ≥ 0` for the finite Euler-factor correction of the principal Dirichlet character mod `N`.

## Main results

* `TauCeti.riemannZeta₀_eq_one_sub_mul_integral`: the fractional-part integral formula for
  `riemannZeta₀` on `Re s > 0`.
* `TauCeti.riemannZeta_eq_div_sub_mul_integral`: `ζ(s) = s / (s - 1) - s ∫₁^∞ {t} t^{-(s + 1)} dt`
  for `Re s > 0` and `s ≠ 1`.
* `TauCeti.norm_riemannZeta₀_le_one_add_norm_div_re`: `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s` on
  `Re s > 0`.
* `TauCeti.norm_riemannZeta_le`: `‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s` on `Re s > 0`.
* `TauCeti.norm_prod_primeFactors_one_sub_cpow_neg_le`: `‖∏_{p ∣ N} (1 - p⁻ˢ)‖ ≤ N` for `N ≠ 0` and
  `Re s ≥ 0`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1, eq. (2.1.4).
* H. Davenport, *Multiplicative Number Theory*, Ch. 12 and Ch. 21.
-/

public section

open Complex Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace TauCeti

/-- On `[0, ∞)`, the fractional part `t - ⌊t⌋₊` lies in `[0, 1]`, so its complex cast has norm at
most `1`. -/
private lemma norm_sub_natFloor_le_one {t : ℝ} (ht : 0 ≤ t) :
    ‖((t - ⌊t⌋₊ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le ht))]
  linarith [Nat.lt_floor_add_one t]

/-- The integral `∫_{t > 1} (t - ⌊t⌋₊) t^{-(s + 1)} dt` is the Mellin transform at `-s` of the
indicator on `[1, ∞)` of `t ↦ t - ⌊t⌋₊`. -/
private lemma integral_sub_natFloor_eq_mellin (s : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      mellin ((Set.Ici (1 : ℝ)).indicator fun t : ℝ ↦ ((t - ⌊t⌋₊ : ℝ) : ℂ)) (-s) := by
  have hEq : Set.EqOn
      (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) •
        (Set.Ici (1 : ℝ)).indicator (fun u : ℝ ↦ ((u - ⌊u⌋₊ : ℝ) : ℂ)) t)
      ((Set.Ici (1 : ℝ)).indicator fun t : ℝ ↦
        ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 0) := by
    intro t _
    dsimp only
    by_cases h1 : 1 ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h1), Set.indicator_of_mem (Set.mem_Ici.mpr h1),
        smul_eq_mul, mul_comm, neg_add']
    · rw [Set.indicator_of_notMem (by simpa using h1), Set.indicator_of_notMem (by simpa using h1),
        smul_zero]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hEq,
    setIntegral_indicator measurableSet_Ici,
    Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr zero_lt_one), integral_Ici_eq_integral_Ioi]

/-- The fractional-part integral `s ↦ s ∫_{t > 1} (t - ⌊t⌋₊) t^{-(s + 1)} dt` is holomorphic on the
open right half-plane `Re s > 0`. -/
private lemma differentiableOn_mul_integral_sub_natFloor :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ s * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      {s | 0 < s.re} := by
  set u : ℝ → ℂ := (Set.Ici (1 : ℝ)).indicator fun t : ℝ ↦ ((t - ⌊t⌋₊ : ℝ) : ℂ)
  have hfl_meas : Measurable fun t : ℝ ↦ (⌊t⌋₊ : ℝ) :=
    Monotone.measurable fun _ _ h ↦ mod_cast Nat.floor_mono h
  have hu_meas : Measurable u :=
    (Complex.measurable_ofReal.comp (measurable_id.sub hfl_meas)).indicator measurableSet_Ici
  have hu_norm (t : ℝ) : ‖u t‖ ≤ 1 := by
    by_cases ht : 1 ≤ t
    · rw [show u t = ((t - ⌊t⌋₊ : ℝ) : ℂ) from Set.indicator_of_mem (Set.mem_Ici.mpr ht) _]
      exact norm_sub_natFloor_le_one (zero_le_one.trans ht)
    · rw [show u t = 0 from Set.indicator_of_notMem (by simpa using ht) _]
      simp
  have hloc : LocallyIntegrableOn u (Set.Ioi 0) :=
    ((memLp_top_of_bound hu_meas.aestronglyMeasurable 1
      (Eventually.of_forall hu_norm)).locallyIntegrable le_top).locallyIntegrableOn _
  have hO_top : u =O[atTop] fun t : ℝ ↦ t ^ (-(0 : ℝ)) := by
    refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun t ↦ ?_⟩
    simpa using hu_norm t
  intro s (hs : 0 < s.re)
  have hO_bot : u =O[𝓝[>] 0] fun t : ℝ ↦ t ^ (-((-s).re - 1)) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact (Set.indicator_of_notMem (by simpa using ht.2.not_ge) _).symm
  have hmellin : DifferentiableAt ℂ (fun z : ℂ ↦ mellin u (-z)) s :=
    (mellin_differentiableAt_of_isBigO_rpow (a := 0) hloc hO_top (by simpa using hs) hO_bot
      (by linarith)).comp s differentiableAt_id.neg
  simp_rw [integral_sub_natFloor_eq_mellin]
  exact (differentiableAt_id.mul hmellin).differentiableWithinAt

/-- On `Re z > 1`, `t ↦ ⌊t⌋₊ t^{-(z + 1)}` is integrable on `(1, ∞)`, since it is majorized by
`t ↦ t^{-z}`. -/
private lemma integrableOn_natFloor_mul_cpow {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun t : ℝ ↦ (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1))) (Set.Ioi 1) := by
  have hfl_meas : Measurable fun t : ℝ ↦ (⌊t⌋₊ : ℂ) :=
    Complex.measurable_ofReal.comp (Monotone.measurable fun _ _ h ↦ mod_cast Nat.floor_mono h)
  have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-(z + 1))) (Set.Ioi 1) := fun t ht ↦
    (ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
      (ofReal_mem_slitPlane.mpr (zero_lt_one.trans ht))).continuousWithinAt
  refine (integrableOn_Ioi_cpow_of_lt (a := -z) (by simpa using hz) zero_lt_one).integrable.mono
    (hfl_meas.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, Complex.norm_natCast, norm_cpow_eq_rpow_re_of_pos ht0,
    norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [neg_re, add_re, one_re]
  calc (⌊t⌋₊ : ℝ) * t ^ (-(z.re + 1)) ≤ t * t ^ (-(z.re + 1)) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le ht0.le) (Real.rpow_nonneg ht0.le _)
    _ = t ^ (-z.re) := by
        rw [← Real.rpow_one_add' ht0.le (by linarith)]
        ring_nf

/-- **Fractional-part integral representation of `riemannZeta₀`.** For every `s` with `Re s > 0`,
`riemannZeta₀ s = 1 - s * ∫_{t > 1} (t - ⌊t⌋₊) t^{-(s + 1)} dt`. -/
theorem riemannZeta₀_eq_one_sub_mul_integral {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s =
      1 - s * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hLHS : AnalyticOnNhd ℂ riemannZeta₀ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hopen
  have hRHS : AnalyticOnNhd ℂ
      (fun z ↦ 1 - z * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)))
      {z : ℂ | 0 < z.re} :=
    ((differentiableOn_const 1).sub differentiableOn_mul_integral_sub_natFloor).analyticOnNhd hopen
  refine (hLHS.eqOn_of_preconnected_of_eventuallyEq hRHS
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) ?_) hs
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z (hz : 1 < z.re)
  have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
  have hO1 : (fun n : ℕ ↦ ∑ _k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) :=
    isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ by simp⟩
  have hζ : riemannZeta z =
      z * ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
    rw [← LSeries_one_eq_riemannZeta hz, LSeries_eq_mul_integral _ zero_le_one hz
      (LSeriesSummable_one_iff.mpr hz) hO1]
    simp
  have hint_t : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-z)) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hz) zero_lt_one
  have hsub_eq : ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) =
      (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-z)) -
        ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
    rw [← integral_sub hint_t (integrableOn_natFloor_mul_cpow hz)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hpow : (t : ℂ) * (t : ℂ) ^ (-(z + 1)) = (t : ℂ) ^ (-z) :=
      calc (t : ℂ) * (t : ℂ) ^ (-(z + 1))
          = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(z + 1)) := by rw [cpow_one]
        _ = (t : ℂ) ^ (-z) := by rw [← cpow_add _ _ ht_ne]; ring_nf
    push_cast
    rw [sub_mul, hpow]
  have hint_val : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-z) = 1 / (z - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using hz) zero_lt_one, ofReal_one, one_cpow,
      show -z + 1 = -(z - 1) by ring, neg_div_neg_eq]
  rw [riemannZeta₀, ite_eq_right hz1, hsub_eq, hint_val, mul_sub, ← hζ]
  field_simp [sub_ne_zero.mpr hz1]
  ring

/-- **Fractional-part integral representation of `riemannZeta`.** For `Re s > 0` and `s ≠ 1`,
`ζ(s) = s / (s - 1) - s * ∫_{t > 1} (t - ⌊t⌋₊) t^{-(s + 1)} dt`. -/
theorem riemannZeta_eq_div_sub_mul_integral {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s =
      s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_inv_sub_add hs1, riemannZeta₀_eq_one_sub_mul_integral hs]
  field_simp [sub_ne_zero.mpr hs1]
  ring

/-- On the open right half-plane `Re s > 0`, `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`. -/
theorem norm_riemannZeta₀_le_one_add_norm_div_re {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  rw [riemannZeta₀_eq_one_sub_mul_integral hs]
  have hint_bound : ‖∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
      1 / s.re := by
    calc ‖∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖
        ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
          refine norm_integral_le_of_norm_le
            (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
          have ht0 : 0 < t := zero_lt_one.trans ht
          rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
          simp only [neg_re, add_re, one_re]
          exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (norm_sub_natFloor_le_one ht0.le)
      _ = 1 / s.re := by
          rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
          ring
  calc ‖1 - s * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖(1 : ℂ)‖ + ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ :=
        (norm_sub_le _ _).trans (by rw [norm_mul])
    _ ≤ 1 + ‖s‖ * (1 / s.re) := by
        rw [norm_one]
        exact add_le_add_right (mul_le_mul_of_nonneg_left hint_bound (norm_nonneg s)) 1
    _ = 1 + ‖s‖ / s.re := by ring

/-- **Explicit vertical growth bound for `riemannZeta` on `Re s > 0`.** For every `s` with
`Re s > 0` (including `s = 1`, where `(1 - 1)⁻¹ = 0`),
`‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have hval : riemannZeta 1 = ((Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 : ℝ) := by
      rw [riemannZeta_one, ofReal_div, ofReal_sub, ofReal_log (by positivity : (0 : ℝ) ≤ 4 * π)]
      norm_cast
    have hlog_pos : 0 < Real.log (4 * π) :=
      Real.log_pos (by linarith [Real.two_le_pi])
    have hlog_lt : Real.log (4 * π) < 4 := by
      rw [Real.log_lt_iff_lt_exp (by positivity)]
      have h2e : (2 : ℝ) < Real.exp 1 := by
        linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
      have h16 : (16 : ℝ) < Real.exp 4 := by
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ < Real.exp 1 ^ 4 := pow_lt_pow_left₀ h2e (by norm_num) (by norm_num)
          _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
      linarith [Real.pi_lt_four]
    rw [hval, norm_real, Real.norm_eq_abs]
    simp only [sub_self, norm_zero, inv_zero, zero_add, norm_one, one_re, div_one]
    rw [abs_le]
    have hγ₁ := Real.one_half_lt_eulerMascheroniConstant
    have hγ₂ := Real.eulerMascheroniConstant_lt_two_thirds
    constructor <;> linarith
  · rw [riemannZeta_eq_inv_sub_add hs1]
    calc ‖(s - 1)⁻¹ + riemannZeta₀ s‖
        ≤ ‖(s - 1)⁻¹‖ + ‖riemannZeta₀ s‖ := norm_add_le _ _
      _ ≤ ‖s - 1‖⁻¹ + (1 + ‖s‖ / s.re) := by
          rw [norm_inv]
          exact add_le_add_right (norm_riemannZeta₀_le_one_add_norm_div_re hs) _
      _ = ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re := by ring

/-- On the closed right half-plane `Re s ≥ 0`, the finite Euler-factor product
`∏ p ∈ N.primeFactors, (1 - p⁻ˢ)` for `N ≠ 0` has norm at most `N`, since each factor at a prime
`p ∣ N` has norm at most `1 + p^{-Re s} ≤ 2 ≤ p`. -/
theorem norm_prod_primeFactors_one_sub_cpow_neg_le {N : ℕ} [NeZero N] {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ N := by
  rw [norm_prod]
  calc ∏ p ∈ N.primeFactors, ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖
      ≤ ∏ p ∈ N.primeFactors, (p : ℝ) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun p hp ↦ ?_
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
        have hcpow : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
          rw [norm_natCast_cpow_of_pos hprime.pos, neg_re]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
        calc ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
          _ ≤ 2 := by rw [norm_one]; linarith
          _ ≤ p := hp2
    _ = ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ N := by exact_mod_cast Nat.le_of_dvd (NeZero.pos N) (Nat.prod_primeFactors_dvd N)

end TauCeti
