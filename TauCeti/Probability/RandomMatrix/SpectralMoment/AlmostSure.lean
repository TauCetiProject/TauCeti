/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SpectralMoment.Second
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost-sure convergence of second Wigner spectral moments

The summable second-moment fluctuation bound gives almost-sure convergence to the mean.
For unit off-diagonal second absolute moments and a common diagonal second moment, the
mean tends to one, so the second empirical spectral moment tends almost surely to one.
Only pairwise independence of squared coordinate norms is needed. In particular, no
independence between matrices of different sizes is required.

The fourth-moment assumptions below are expressed as square-integrability of squared
coordinate norms, together with a uniform variance bound. These assumptions suffice for
this moment argument, without asserting the finite-second-moment semicircle law.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §2.1.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Second spectral moment fluctuations tend almost surely to zero under the summable
variance bound. Pairwise independence is imposed within each finite coordinate family. -/
theorem ae_tendsto_second_spectralMoment_sub_mean {V : ℝ}
    (hindep : ∀ n, Pairwise fun i j ↦
      IndepFun (wignerCoordinateSquare ξ η (n + 1) i)
        (wignerCoordinateSquare ξ η (n + 1) j) P)
    (hmem : ∀ n i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ n i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) := by
  let X : ℕ → Ω → ℝ := fun n ω ↦
    (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
    ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P
  have hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, inv_pow] using
      (summable_nat_add_iff 1).2
        ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))
  have hbc (k : ℕ) : ∀ᵐ ω ∂P,
      ∀ᶠ n in atTop, |X n ω| < (k + 1 : ℝ)⁻¹ := by
    have hbound (n : ℕ) : P {ω | (k + 1 : ℝ)⁻¹ ≤ |X n ω|} ≤
        ENNReal.ofReal ((8 * V / (n + 1 : ℝ) ^ 2) / ((k + 1 : ℝ)⁻¹) ^ 2) :=
      measure_second_spectralMoment_sub_mean_ge (ξ := ξ) (η := η) (P := P) n
        (hindep n) (hmem n) (hvar n) (inv_pos.mpr (by positivity))
    have hsum : Summable (fun n : ℕ ↦
        (8 * V / (n + 1 : ℝ) ^ 2) / ((k + 1 : ℝ)⁻¹) ^ 2) := by
      have ht := Summable.mul_right ((((k + 1 : ℝ)⁻¹) ^ 2)⁻¹)
        (Summable.mul_left (8 * V) hs)
      simpa only [div_eq_mul_inv, inv_pow, mul_assoc] using ht
    have hfinite : (∑' n, P {ω | (k + 1 : ℝ)⁻¹ ≤ |X n ω|}) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum hbound)
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfinite
  -- Intersect the full-measure events for a countable sequence of tolerances tending to zero.
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn.trans (by simpa only [one_div] using hk)

/-- With unit off-diagonal second absolute moments and constant diagonal second moment,
the second empirical spectral moment tends almost surely to one. Square-integrable squared
norms with uniformly bounded variances and pairwise independence of those squares suffice;
neither centering nor identical distribution of the entries is required. -/
theorem ae_tendsto_second_spectralMoment {V σ2 : ℝ}
    (hindep : ∀ n, Pairwise fun i j ↦
      IndepFun (wignerCoordinateSquare ξ η (n + 1) i)
        (wignerCoordinateSquare ξ η (n + 1) j) P)
    (hmem : ∀ n i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ n i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hη : ∀ i, ∫ ω, η i ω ^ 2 ∂P = σ2) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) atTop (𝓝 1) := by
  have hmean (n : ℕ) :
      (∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) =
        1 + (σ2 - 1) * (n + 1 : ℝ)⁻¹ := by
    have hξi : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P := fun ij ↦
      Integrable.of_integral_ne_zero (by rw [hξ ij]; exact one_ne_zero)
    have hηi (i : ℕ) : Integrable (fun ω ↦ η i ω ^ 2) P := by
      exact ((hmem i (.inl ⟨i, Nat.lt_succ_self i⟩)).integrable (by norm_num)).congr
        (ae_of_all P (fun ω ↦ wignerCoordinateSquare_inl (i + 1) ⟨i, Nat.lt_succ_self i⟩ ω))
    have h := integral_re_trace_wignerMatrix_mul_self hξi hξ hηi hη (n + 1)
    have heq (ω : Ω) :
        (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
        (((n + 1 : ℕ) : ℂ)⁻¹ *
          (wignerMatrix ξ η (n + 1) ω * wignerMatrix ξ η (n + 1) ω).trace).re := by
      rw [Matrix.integral_pow_spectralMeasure]
      simp only [pow_two, Fintype.card_fin, RCLike.re_to_complex]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simp_rw [heq]
    rw [h]
    push_cast
    field_simp
    ring
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hm : Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ 2
      ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) atTop (𝓝 1) := by
    simp_rw [hmean]
    simpa using tendsto_const_nhds.add (hinv.const_mul (σ2 - 1))
  filter_upwards [ae_tendsto_second_spectralMoment_sub_mean hindep hmem hvar] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hm

end TauCeti.Probability
