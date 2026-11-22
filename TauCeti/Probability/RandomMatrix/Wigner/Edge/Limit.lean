/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Probability.RandomMatrix.Wigner.Truncation.OperatorNorm
import TauCeti.Probability.RandomMatrix.Wigner.SemicircleLaw
import TauCeti.Probability.RandomMatrix.Wigner.Diagonal.OperatorNorm
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

open Filter MeasureTheory Matrix TauCeti TauCeti.Probability
open scoped Topology ENNReal NNReal Matrix.Norms.L2Operator

namespace ProbabilityTheory.iIndepFun

variable {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
  {P : Measure Ω} {Q : Measure Ω'} {S : Measure Ω''}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {X : Ω' → ℂ} {Y : Ω'' → ℝ}

local notation "e₀" => (⟨(0, 1), by decide⟩ : StrictUpper)

/-- Let the upper entries be independent with a common centered law of unit second moment and
finite fourth moment, and let the diagonal entries, possibly dependent, share a law of finite
second moment. Then the largest and smallest eigenvalues of the normalized corners converge
almost surely to `2` and `-2`, provided the following trace bound holds. The expected real trace
of the `2*k`-th powers of the zero-diagonal centered truncations at radius `(n+1)^a`, with
`a > 1/4`, is bounded by a polynomial in the sequence index times `t^(2*k)`. At each threshold
`r > 2`, the scale `0 < t < r` and the orders `k n` may depend on `r`. The orders satisfy
`k n ≥ B * log (n + 1)` eventually and `2 * B * log (r/t) > d+1` for polynomial exponent `d`. -/
theorem ae_tendsto_extreme_eigenvalues₀_wignerMatrix_of_integral_re_trace_pow_two_mul_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P Q)
    (hξ : MemLp X 4 Q) (hmean : ∫ ω, X ω ∂Q = 0) (hvar : ∫ ω, ‖X ω‖ ^ 2 ∂Q = 1)
    (hd : ∀ i, IdentDistrib (η i) Y P S) (hη : MemLp Y 2 S)
    {a : ℝ} (ha : 1 / 4 < a)
    (htrace : ∀ r > (2 : ℝ), ∃ (t B C d : ℝ) (k : ℕ → ℕ), 0 < t ∧ t < r ∧
      d + 1 < 2 * B * Real.log (r / t) ∧
      (∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop, (∫ ω, ((wignerMatrix (fun ij ↦
        TauCeti.Probability.centeredTruncation (ξ ij) P
          ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        (fun _ _ ↦ 0) (n + 1) ω ^ (2 * k n)).trace).re ∂P) ≤
        C * (n + 1 : ℝ) ^ d * t ^ (2 * k n))) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ ⊥)
        atTop (𝓝 2) ∧
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ ⊤)
        atTop (𝓝 (-2)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let B (n : ℕ) (ω : Ω) :=
    wignerMatrix (fun ij ↦ TauCeti.Probability.centeredTruncation (ξ ij) P
      ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
      (fun _ _ ↦ 0) (n + 1) ω
  let Z (n : ℕ) (ω : Ω) := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  have hZ n ω : (Z n ω).IsHermitian := wignerMatrix_isHermitian _ _ _ _
  have hnorm : ∀ᵐ ω ∂P, ∀ r > (2 : ℝ), ∀ᶠ n in atTop, ‖B n ω‖ < r := by
    apply ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_two_mul_le (A := B)
      (.of_forall fun n ↦ .of_forall fun ω ↦ wignerMatrix_isHermitian _ _ ω (n + 1))
    intro r hr
    obtain ⟨t, b, C, d, k, ht, htr, hb, hk, htrace'⟩ := htrace r hr
    refine ⟨t, b, C, d, k, ht, htr, hb, hk, .of_forall fun n ↦ ?_, ?_⟩
    · have hi : Integrable (fun ω ↦ ((B n ω) ^ (2 * k n)).trace) P :=
        integrable_trace_pow_wignerMatrix (fun ij _ ↦
          (hid ij).aestronglyMeasurable_fst.memLp_centeredTruncation _) (fun _ _ ↦ memLp_const 0)
      exact hi.re
    · simpa only [B, RCLike.re_to_complex] using htrace'
  have happrox : ∀ᵐ ω ∂P, Tendsto (fun n ↦ ‖Z n ω - B n ω‖) atTop (𝓝 0) := by
    simpa only [B, Z] using
      ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_centeredTruncation
        (η := fun _ _ ↦ 0) (fun _ ↦
          (hind.precomp Subtype.val_injective).wignerMatrix_row_apply_of_ne)
        hid hξ hmean ha
  have hweak := ae_tendsto_spectralMeasure_wignerMatrix_zero_of_memLp hind
    (fun ij ↦ (hid ij).trans (hid e₀).symm)
    (((hid e₀).symm.memLp_snd hξ).mono_exponent (by norm_num))
    ((hid e₀).integral_eq.trans hmean) 1 (by
      simpa only [Function.comp_apply, NNReal.coe_one] using
        ((hid e₀).comp (measurable_norm.pow_const 2)).integral_eq.trans hvar)
  have hdiag := ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_zero (ξ := ξ) hd hη
  filter_upwards [hnorm, happrox, hweak, hdiag] with ω hn hdiff hw hdω
  -- The norm bounds pass from the truncations to the zero-diagonal corners.
  have hZnorm r (hr : 2 < r) : ∀ᶠ n in atTop, ‖Z n ω‖ < r := by
    have hgap : 0 < (r - 2) / 2 := by linarith
    filter_upwards [hn ((r + 2) / 2) (by linarith), hdiff.eventually_lt_const hgap] with n hBn hδ
    exact (norm_le_norm_sub_add (Z n ω) (B n ω)).trans_lt
      ((add_lt_add hδ hBn).trans_eq (by ring))
  obtain ⟨hmax, hmin⟩ := hw.eigenvalues₀_bot_and_top_of_eventually_l2_opNorm_lt
    (hA := fun n ↦ hZ n ω) (by simp [support_semicircleReal]) (by simp [support_semicircleReal])
    hZnorm
  -- The diagonal perturbation has vanishing operator norm.
  exact ⟨hmax.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
      (fun n ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hdω,
    hmin.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
      (fun n ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hdω⟩

end ProbabilityTheory.iIndepFun
