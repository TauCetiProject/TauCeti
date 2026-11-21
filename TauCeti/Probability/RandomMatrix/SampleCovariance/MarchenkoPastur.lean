/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.Stability
public import TauCeti.Probability.RandomMatrix.SampleCovariance.Approximation
public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.Analysis.Matrix.Resolvent.SampleCovariance
import TauCeti.Probability.Moments.SubGaussian
import TauCeti.Probability.RandomMatrix.QuadraticForm

/-!
# The almost-sure Marchenko–Pastur law

Let `Xₘ` be a `p(m) × n` matrix with `n = m + 1` columns, `p(m) ≥ 1` and `p(m) / n → y > 0`, and
let `Sₘ = Xₘ Xₘᴴ / n` be its sample covariance. This file proves that the empirical spectral
measures of `Sₘ` converge almost surely to the Marchenko–Pastur law `MP_y`.

The proof is the resolvent method. At a fixed spectral parameter `z` in the upper half-plane, the
exact identity for the trace of the sample covariance resolvent bounds `c` times the
Marchenko–Pastur residual `c z m² + (z + c - 1) m + 1` of `m = m_{L_S}(z)`, where `c = p / n`, by
the largest error of the leave-one-column-out quadratic forms against their normalized traces.
For independent entries of unit second moment that are directionally sub-Gaussian with a common
proxy, these errors tend to zero almost surely, so the residual does too. Stability of the
Marchenko–Pastur equation then identifies the limit. In this form the entries need not be
identically distributed, and there is no assumption on the coupling across sizes.

For the corners of one infinite array of i.i.d. complex entries with mean zero and unit second
absolute moment, `marchenkoPastur_ae` removes the sub-Gaussian assumption. Bounded centred
entries of unit variance are sub-Gaussian, so the first part gives the bounded case, and the
bounded-entry reduction `ae_tendsto_spectralMeasure_sampleCovariance_of_bounded_entries`
transfers it to finite variance. Real entries are the case of an entry law supported on `ℝ`.

## Main results

* `TauCeti.Probability.ae_tendsto_spectralMeasure_sampleCovariance_marchenkoPastur`: the
  almost-sure Marchenko–Pastur law for independent, directionally sub-Gaussian entries of unit
  second moment.
* `TauCeti.Probability.marchenkoPastur_ae`: the almost-sure Marchenko–Pastur law for the corners
  of an i.i.d. array with mean zero and unit second absolute moment.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), 611–677, Theorem 2.5 and its proof in §2.2.
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, 2nd ed.,
  Springer, 2010, §3.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Marchenko–Pastur law for sub-Gaussian entries.** Let `Xₘ` be a random `p(m) × (m + 1)`
complex matrix with `p(m) ≥ 1` and `p(m) / (m + 1) → y > 0`, whose entries are independent, have
unit second absolute moment and are directionally sub-Gaussian with a common proxy `K`. Then
almost surely the empirical spectral measures of the sample covariances `Xₘ Xₘᴴ / (m + 1)`
converge weakly to `MP_y`. The entry laws may vary with the size and the position, and the
matrices of different sizes may be coupled arbitrarily. -/
theorem ae_tendsto_spectralMeasure_sampleCovariance_marchenkoPastur
    {p : ℕ → ℕ} [∀ m, NeZero (p m)] {X : (m : ℕ) → Ω → Matrix (Fin (p m)) (Fin (m + 1)) ℂ}
    {K : ℝ≥0}
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦ fun ω ↦ X m ω ij.1 ij.2) P)
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * X m ω i j).re)
      (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ m i j, ∫ ω, ‖X m ω i j‖ ^ 2 ∂P = 1)
    {y : ℝ≥0} (hy : 0 < y) (hp : Tendsto (fun m ↦ (p m : ℝ) / (m + 1)) atTop (𝓝 y)) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ (X m ω).sampleCovariance.spectralMeasure
      (isHermitian_sampleCovariance _)) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  let c (m : ℕ) : ℝ≥0 := (p m : ℝ≥0) / (m + 1)
  have hc' : Tendsto (fun m ↦ (c m : ℝ)) atTop (𝓝 y) := by simpa [c] using hp
  have hc : Tendsto c atTop (𝓝 y) := NNReal.tendsto_coe.1 hc'
  have hdim : ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in atTop, (p m : ℝ) ≤ C * (m + 1) := by
    refine ⟨y + 1, by positivity, ?_⟩
    filter_upwards [hp.eventually (gt_mem_nhds (lt_add_one (y : ℝ)))] with m hm
    exact ((div_lt_iff₀ (by positivity)).1 hm).le
  refine (ae_tendsto_marchenkoPastur_iff_ae_quadratic_tendsto_zero hc).2 fun z hz ↦ ?_
  filter_upwards [ae_tendsto_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace
    hind hX hunit hdim hz.ne'] with ω hω
  set s := fun m ↦ resolventTransform
    ((X m ω).sampleCovariance.spectralMeasure (isHermitian_sampleCovariance _) : Measure ℝ) z
  set r := fun m ↦ (c m : ℂ) * z * (s m * s m) + (z + c m - 1) * s m + 1
  -- The deterministic residual bound turns quadratic-form errors into `c * r → 0`.
  have hcr : Tendsto (fun m ↦ (c m : ℂ) * r m) atTop (𝓝 0) := by
    have hbound := (hω.add (tendsto_one_div_add_atTop_nhds_zero_nat.div_const |z.im|)).const_mul
      (‖z‖ / |z.im|)
    rw [zero_div, zero_add, mul_zero] at hbound
    refine squeeze_zero_norm (fun m ↦ ?_) hbound
    -- The quadratic-form errors of the columns, whose sup norm `hω` controls.
    let E (k : Fin (m + 1)) := ((m + 1 : ℕ) : ℂ)⁻¹ *
      (star ((X m ω).col k) ⬝ᵥ (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹ *ᵥ
        (X m ω).col k - (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹.trace)
    have h := norm_mul_quadratic_resolventTransform_spectralMeasure_sampleCovariance_le
      (X m ω) hz.ne' (ε := ‖E‖) fun k ↦ by
        rw [Fintype.card_fin]
        exact norm_le_pi_norm E k
    have hcm : ((c m : ℝ) : ℂ) = (Fintype.card (Fin (p m)) : ℂ) / Fintype.card (Fin (m + 1)) := by
      simp [c]
    calc
      _ = _ := by simp only [r, s, hcm]
      _ ≤ _ := h
      _ = _ := by simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_div, E, col_apply']
  have hdiv := hcr.div ((Complex.continuous_ofReal.tendsto _).comp hc')
    (by exact_mod_cast hy.ne' : ((y : ℝ) : ℂ) ≠ 0)
  rw [zero_div] at hdiv
  refine hdiv.congr fun m ↦ ?_
  have hcm : (c m : ℂ) ≠ 0 := by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, NNReal.coe_eq_zero]
    exact div_ne_zero (by exact_mod_cast NeZero.ne (p m)) (by positivity)
  exact mul_div_cancel_left₀ _ hcm

/-- **Marchenko–Pastur law, almost surely.** Let `x` be an array, indexed by `ℕ × ℕ`, of independent
complex entries with common law `ν` of mean zero and unit second absolute moment, let `p(n) ≥ 1`
with `p(n) / n → y > 0`, and let `Xₙ` be the top-left `p(n) × n` corner of the array. Then almost
surely the empirical spectral measures of the sample covariances `Xₙ Xₙᴴ / n` converge weakly to
the Marchenko–Pastur law `MP_y`. -/
theorem marchenkoPastur_ae {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ}
    (hx : ∀ ij, HasLaw (x ij) ν P) (hindep : iIndepFun x P)
    (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1)
    {p : ℕ → ℕ} [∀ n, NeZero (p n)] {y : ℝ≥0} (hy : 0 < y)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).sampleCovariance.spectralMeasure
        (isHermitian_sampleCovariance _)) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have : IsProbabilityMeasure ν := (hx (0, 0)).isProbabilityMeasure_iff.1 ‹_›
  -- Work with the corners of size `p (m + 1) × (m + 1)`, which have a nonempty column type.
  have hp' : Tendsto (fun m : ℕ ↦ (p (m + 1) : ℝ) / (m + 1)) atTop (𝓝 y) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (tendsto_add_atTop_iff_nat 1).2 hp
  have hdim : ∀ᶠ m : ℕ in atTop, (y / 2 : ℝ) * m ≤ Fintype.card (Fin (p (m + 1))) := by
    filter_upwards [hp'.eventually (lt_mem_nhds (half_lt_self (by exact_mod_cast hy)))] with m hm
    rw [Fintype.card_fin]
    have := (lt_div_iff₀ (by positivity)).1 hm
    nlinarith [NNReal.coe_nonneg y]
  have hind (m : ℕ) : iIndepFun (fun ij : Fin (p (m + 1)) × Fin (m + 1) ↦
      fun ω ↦ x (ij.1, ij.2) ω) P :=
    hindep.precomp (g := fun ij : Fin (p (m + 1)) × Fin (m + 1) ↦ ((ij.1 : ℕ), (ij.2 : ℕ)))
      fun a b h ↦ by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  have h := ae_tendsto_spectralMeasure_sampleCovariance_of_bounded_entries
    (X := fun m ω ↦ Matrix.of fun (i : Fin (p (m + 1))) (j : Fin (m + 1)) ↦ x (i, j) ω)
    (μ := (marchenkoPastur y).toProbabilityMeasure) hind (fun _ _ _ ↦ hx _) hmean hvar
    (by positivity) hdim ?_
  · filter_upwards [h] with ω hω
    exact (tendsto_add_atTop_iff_nat 1).1 hω
  -- Bounded centred entries of unit variance are sub-Gaussian, so the first theorem applies.
  intro Y hY ρ hYind hYlaw ⟨B, hB⟩ hρmean hρunit
  apply tendsto_expectedCovarianceSpectralMeasure_of_ae_tendsto hY
  refine ae_tendsto_spectralMeasure_sampleCovariance_marchenkoPastur (K := B.toNNReal ^ 2)
    hYind (fun m i j ↦ ?_) (fun m i j ↦ ?_) hy hp'
  · have hl := hYlaw m i j
    refine hasSubgaussianMGF_re_star_mul_of_norm_le hl.aemeasurable ?_ (hl.integral_eq.trans hρmean)
    exact (hl.ae_iff (p := fun x ↦ ‖x‖ ≤ B.toNNReal)
      (measurableSet_setOfPred.1 (measurableSet_le measurable_norm measurable_const))).2
      (hB.mono fun _ h ↦ h.trans (Real.le_coe_toNNReal B))
  · exact ((hYlaw m i j).integral_comp (by fun_prop)).trans hρunit

end TauCeti.Probability
