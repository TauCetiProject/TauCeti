/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Probability.RandomMatrix.Wigner.Truncation.OperatorNorm
import TauCeti.Probability.RandomMatrix.Wigner.SemicircleLaw
import TauCeti.Probability.RandomMatrix.Diagonal
import TauCeti.Probability.RandomMatrix.SpectralMoment.Extremes
import TauCeti.Probability.RandomMatrix.TraceWord
import TauCeti.Analysis.Matrix.SpectralMeasure.Extremes

/-!
# Reduction of Wigner edge limits to a growing trace bound

The zero-diagonal semicircle law forces eigenvalues arbitrarily close to both edges from
inside. A growing trace bound on centered truncated corners controls the operator norm
from above. This upper bound transfers to the original matrices by the operator-norm
truncation result. The diagonal perturbation also transfers the lower edge estimates,
so the diagonal entries can be dependent.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.12.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix ProbabilityTheory
open scoped Topology ENNReal NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

local notation "e₀" => (⟨(0, 1), by decide⟩ : StrictUpper)

/-- To prove both Wigner edge limits under a finite fourth moment, it suffices to bound the
expected real trace of the `2*k`-th powers of the zero-diagonal centered truncations at radius
`(n+1)^a`, with `a > 1/4`, by a polynomial in the sequence index times `4^k`. At each threshold
`r > 2`, the order may depend on `r` and `n`, with `k n ≥ B * log (n + 1)` eventually and
`2 * B * log (r/2) > d+1` for the polynomial exponent `d`. -/
theorem ae_tendsto_extreme_eigenvalues₀_wignerMatrix_of_integral_re_trace_pow_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) (ξ e₀) P P)
    (hξ : MemLp (ξ e₀) 4 P) (hmean : ∫ ω, ξ e₀ ω ∂P = 0)
    (hvar : ∫ ω, ‖ξ e₀ ω‖ ^ 2 ∂P = 1)
    (hd : ∀ i, IdentDistrib (η i) (η 0) P P) (hη : MemLp (η 0) 2 P)
    {a : ℝ} (ha : 1 / 4 < a)
    (htrace : ∀ r > (2 : ℝ), ∃ (B C d : ℝ) (k : ℕ → ℕ), d + 1 < 2 * B * Real.log (r / 2) ∧
      (∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop, (∫ ω, ((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        (fun _ _ ↦ 0) (n + 1) ω ^ (2 * k n)).trace).re ∂P) ≤
        C * (n + 1 : ℝ) ^ d * (2 : ℝ) ^ (2 * k n))) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ ⊥)
        atTop (𝓝 2) ∧
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ ⊤)
        atTop (𝓝 (-2)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let R (n : ℕ) : ℝ≥0 := ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩
  let B (n : ℕ) (ω : Ω) := wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P (R n))
    (fun _ _ ↦ 0) (n + 1) ω
  let Z (n : ℕ) (ω : Ω) := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  have hB n ω : (B n ω).IsHermitian := wignerMatrix_isHermitian _ _ _ _
  have hZ n ω : (Z n ω).IsHermitian := wignerMatrix_isHermitian _ _ _ _
  have hnorm : ∀ᵐ ω ∂P, ∀ r > (2 : ℝ), ∀ᶠ n in atTop, ‖B n ω‖ < r := by
    apply ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_le
      (.of_forall fun n ↦ .of_forall (hB n)) (by norm_num)
    intro r hr
    obtain ⟨b, C, d, k, hb, hk, htrace'⟩ := htrace r hr
    refine ⟨b, C, d, k, hb, hk, .of_forall fun n ↦ ?_, ?_⟩
    · have hi : Integrable (fun ω ↦ ((B n ω) ^ (2 * k n)).trace) P :=
        integrable_trace_pow_wignerMatrix (fun ij _ ↦
          (hid ij).aestronglyMeasurable_fst.memLp_centeredTruncation _) (fun _ _ ↦ memLp_const 0)
      exact hi.re
    · simpa only [B, R, RCLike.re_to_complex] using htrace'
  have happrox : ∀ᵐ ω ∂P, Tendsto (fun n ↦ ‖Z n ω - B n ω‖) atTop (𝓝 0) := by
    simpa only [B, Z, R] using ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_centeredTruncation
      (η := fun _ _ ↦ 0) (fun _ ↦
        (hind.precomp Subtype.val_injective).wignerMatrix_row_apply_of_ne)
      hid hξ hmean (fun _ ↦ IdentDistrib.refl aemeasurable_const)
      (memLp_const 0) ha
  have hweak := ae_tendsto_spectralMeasure_wignerMatrix_zero_of_memLp
    hind hid (hξ.mono_exponent (by norm_num)) hmean 1 (by simpa using hvar)
  have hdiag := ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_zero (ξ := ξ) hd hη
  filter_upwards [hnorm, happrox, hweak, hdiag] with ω hn hdiff hw hdω
  have hZnorm r (hr : 2 < r) : ∀ᶠ n in atTop, ‖Z n ω‖ < r := by
    have hgap : 0 < (r - 2) / 2 := by linarith
    filter_upwards [hn ((r + 2) / 2) (by linarith), hdiff.eventually_lt_const hgap] with n hBn hδ
    have htri : ‖Z n ω‖ ≤ ‖Z n ω - B n ω‖ + ‖B n ω‖ := by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (Z n ω) (B n ω) 0
    exact htri.trans_lt ((add_lt_add hδ hBn).trans_eq (by ring))
  have hmax := hw.eigenvalues₀_bot_of_eventually_lt
    (hA := fun n ↦ hZ n ω) (c := 2) (by simp [support_semicircleReal]) (fun r hr ↦
      (hZnorm r hr).mono fun n hn ↦ (Real.le_norm_self _).trans_lt
        (((hZ n ω).norm_eigenvalues₀_le_l2_opNorm ⊥).trans_lt hn))
  have hmin := hw.eigenvalues₀_top_of_eventually_gt
    (hA := fun n ↦ hZ n ω) (c := -2) (by simp [support_semicircleReal]) (fun r hr ↦
      (hZnorm (-r) (by linarith)).mono fun n hn ↦ by
        have h := ((hZ n ω).norm_eigenvalues₀_le_l2_opNorm ⊤).trans_lt hn
        simpa only [neg_neg, Real.norm_eq_abs] using (neg_lt_neg h).trans_le (neg_abs_le _))
  exact ⟨hmax.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
      (fun n ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hdω,
    hmin.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
      (fun n ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hdω⟩

end TauCeti.Probability
