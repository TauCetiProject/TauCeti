/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Chebyshev's inequality for the second moment

For any measure `μ` and any real function `Y` whose square is integrable, the set where `Y` is at
least `c > 0` has measure at most `(∫ Y²) / c²`. This is Markov's inequality applied to `Y²`.
Taking `Y = ‖Z‖` bounds the set where the norm of a function `Z` is at least `c`. Unlike
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `Y` is not centered at its mean, so the bound
applies directly to a deviation such as the error of an estimator.

Combining Chebyshev's inequality with the first Borel–Cantelli lemma shows that if the normalized
second moments `(∫ ‖Z k‖²) / b k ^ 2` are summable, then `(b k)⁻¹ • Z k` converges to `0` almost
everywhere.

## Main statements

* `TauCeti.meas_ge_le_integral_sq_div_sq`: Chebyshev's inequality for the second moment,
  `μ {c ≤ Y} ≤ (∫ Y²) / c²`, for any measure and without centering.
* `TauCeti.meas_gt_le_div_sq_of_integral_sq_le`: the uncentered Chebyshev inequality
  `μ {η < Y} ≤ v / η²` for a real `Y` with `∫ Y² ≤ v`.
* `TauCeti.ae_tendsto_inv_smul_zero_of_summable_integral_norm_sq`: summability of
  `(∫ ‖Z k‖²) / b k ^ 2` implies `(b k)⁻¹ • Z k → 0` almost everywhere.
* `TauCeti.ae_tendsto_div_zero_of_summable_integral_sq`: the real-valued specialization
  `Z k / b k → 0` almost everywhere.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.2: Chebyshev's inequality.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Chebyshev's inequality for the second moment.** For any measure, if `Y²` is integrable and
`0 < c`, the set where `Y` is at least `c` has measure at most `(∫ Y²) / c²`. Taking `Y = ‖Z‖`
gives the bound for the set where `‖Z‖` is at least `c`. Unlike
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `Y` is not centered at its mean. -/
theorem meas_ge_le_integral_sq_div_sq {Y : Ω → ℝ} (hY : Integrable (fun ω ↦ Y ω ^ 2) μ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ Y ω} ≤ ENNReal.ofReal ((∫ ω, Y ω ^ 2 ∂μ) / c ^ 2) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  calc μ {ω | c ≤ Y ω}
      ≤ μ {ω | ENNReal.ofReal (c ^ 2) ≤ ENNReal.ofReal (Y ω ^ 2)} :=
        measure_mono fun ω (hω : c ≤ Y ω) ↦
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le hω 2)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ) / ENNReal.ofReal (c ^ 2) :=
        meas_ge_le_lintegral_div hY.aemeasurable.ennreal_ofReal
          (ENNReal.ofReal_pos.2 hc2).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((∫ ω, Y ω ^ 2 ∂μ) / c ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hY (.of_forall fun ω ↦ by positivity),
          ENNReal.ofReal_div_of_pos hc2]

/-- **The uncentered Chebyshev inequality.** If `Y²` is integrable with `∫ Y² ≤ v` and `0 < η`,
then the set where `Y` exceeds `η` has measure at most `v / η²`. -/
theorem meas_gt_le_div_sq_of_integral_sq_le {Y : Ω → ℝ} (hY : Integrable (fun ω ↦ Y ω ^ 2) μ)
    {v η : ℝ} (hv : ∫ ω, Y ω ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    μ {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) :=
  calc μ {ω | η < Y ω}
      ≤ μ {ω | η ≤ Y ω} := measure_mono fun ω (hω : η < Y ω) ↦ hω.le
    _ ≤ ENNReal.ofReal ((∫ ω, Y ω ^ 2 ∂μ) / η ^ 2) := meas_ge_le_integral_sq_div_sq hY hη
    _ ≤ ENNReal.ofReal (v / η ^ 2) := by gcongr

/-- **Chebyshev–Borel–Cantelli almost-sure convergence.** If the normalized second moments
`(∫ ‖Z k‖²) / b k ^ 2` are summable, then `(b k)⁻¹ • Z k → 0` almost everywhere, for any measure
and any real sequence `b` (including terms where `b k = 0`). Integrability of `‖Z k‖²` is required
only eventually. -/
theorem ae_tendsto_inv_smul_zero_of_summable_integral_norm_sq
    [SeminormedAddGroup E] [SMulZeroClass ℝ E] [IsBoundedSMul ℝ E]
    {Z : ℕ → Ω → E} {b : ℕ → ℝ}
    (hint : ∀ᶠ k in atTop, Integrable (fun ω ↦ ‖Z k ω‖ ^ 2) μ)
    (hsum : Summable fun k ↦ (∫ ω, ‖Z k ω‖ ^ 2 ∂μ) / b k ^ 2) :
    ∀ᵐ ω ∂μ, Tendsto (fun k ↦ (b k)⁻¹ • Z k ω) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hint
  let Z' : ℕ → Ω → E := fun k ω ↦ if N ≤ k then (b k)⁻¹ • Z k ω else 0
  have h_ae : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Z' k ω) atTop (𝓝 0) := by
    refine TauCeti.MeasureTheory.ae_tendsto_of_tsum_dist_ge_ne_top (g := 0) fun ε hε ↦ ?_
    have hbound (k : ℕ) : μ {ω | ε ≤ dist (Z' k ω) 0} ≤
        ENNReal.ofReal (ε⁻¹ ^ 2 * ((∫ ω, ‖Z k ω‖ ^ 2 ∂μ) / b k ^ 2)) := by
      by_cases hkN : N ≤ k
      · simp only [Z', hkN, ite_true, dist_zero_right]
        by_cases hbk : b k = 0
        · have hempty : {ω | ε ≤ ‖(b k)⁻¹ • Z k ω‖} = ∅ :=
            Set.eq_empty_iff_forall_notMem.2 fun ω hω ↦ by
              have h0 : ‖(b k)⁻¹ • Z k ω‖ ≤ 0 := by
                simpa only [hbk, inv_zero, norm_zero, zero_mul] using norm_smul_le (b k)⁻¹ (Z k ω)
              linarith [Set.mem_ofPred_eq.mp hω]
          simp [hempty]
        · have hsub : {ω | ε ≤ ‖(b k)⁻¹ • Z k ω‖} ⊆ {ω | ε * |b k| ≤ ‖Z k ω‖} := fun ω hω ↦ by
            have h1 := norm_smul_le (b k)⁻¹ (Z k ω)
            rw [Real.norm_eq_abs, abs_inv, inv_mul_eq_div] at h1
            exact (le_div_iff₀ (abs_pos.2 hbk)).1 ((Set.mem_ofPred_eq.mp hω).trans h1)
          refine (measure_mono hsub).trans ((meas_ge_le_integral_norm_sq_div_sq (hN k hkN)
            (mul_pos hε (abs_pos.2 hbk))).trans_eq ?_)
          congr 1; rw [mul_pow, sq_abs]; field_simp
      · simp [Z', hkN, not_le_of_gt hε]
    exact ne_top_of_le_ne_top (hsum.mul_left (ε⁻¹ ^ 2)).tsum_ofReal_ne_top (tsum_le_tsum hbound)
  filter_upwards [h_ae] with ω hω
  refine hω.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  simp [Z', hk]

/-- **Chebyshev–Borel–Cantelli almost-sure convergence for real sequences.** If
`(∫ (Z k)²) / b k ^ 2` is summable, then `Z k / b k → 0` almost everywhere. -/
theorem ae_tendsto_div_zero_of_summable_integral_sq {Z : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    (hint : ∀ᶠ k in atTop, Integrable (fun ω ↦ Z k ω ^ 2) μ)
    (hsum : Summable fun k ↦ (∫ ω, Z k ω ^ 2 ∂μ) / b k ^ 2) :
    ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Z k ω / b k) atTop (𝓝 0) := by
  have hint' : ∀ᶠ k in atTop, Integrable (fun ω ↦ ‖Z k ω‖ ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hint
  have hsum' : Summable fun k ↦ (∫ ω, ‖Z k ω‖ ^ 2 ∂μ) / b k ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hsum
  filter_upwards [ae_tendsto_inv_smul_zero_of_summable_integral_norm_sq hint' hsum'] with ω hω
  simpa only [smul_eq_mul, inv_mul_eq_div] using hω

end TauCeti
