/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Probability.RandomMatrix.Wigner.Edge.Truncation
import TauCeti.Probability.RandomMatrix.Wigner.SemicircleLaw
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

omit [MeasurableSpace Ω] in
private theorem tendsto_wigner_eigenvalues₀_of_tendsto_norm_sub_zero (ω : Ω)
    (i : (n : ℕ) → Fin (Fintype.card (Fin (n + 1)))) {c : ℝ}
    (hd : Tendsto (fun n : ℕ ↦ ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω‖) atTop (𝓝 0))
    (h : Tendsto (fun n : ℕ ↦
      (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)).eigenvalues₀ (i n)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ (i n))
      atTop (𝓝 c) := by
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  have hdist := tendsto_iff_dist_tendsto_zero.1 h
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    (by simpa only [add_zero] using hd.add hdist)
  refine (dist_triangle _ ((wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)).eigenvalues₀
    (i n)) _).trans (add_le_add_left ?_ _)
  rw [Real.dist_eq]
  exact (wignerMatrix_isHermitian ξ η ω (n + 1)).abs_eigenvalues₀_sub_le_norm
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) (i n)

/-- To prove both Wigner edge limits under the fourth-moment hypothesis, it suffices
to prove an eventual polynomial-times-`4^k` bound on the expected trace of the
`2*k`-th powers of the zero-diagonal centered truncations at radius `n^a`. The order
`k` may depend on `n` and must grow faster than `log n`. -/
theorem ae_tendsto_extreme_eigenvalues₀_wignerMatrix_of_integral_trace_pow_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) (ξ e₀) P P)
    (hξ : MemLp (ξ e₀) 4 P) (hmean : ∫ ω, ξ e₀ ω ∂P = 0)
    (hvar : ∫ ω, ‖ξ e₀ ω‖ ^ 2 ∂P = 1)
    (hd : ∀ i, IdentDistrib (η i) (η 0) P P) (hη : MemLp (η 0) 2 P)
    {a : ℝ} (ha : 5 / 12 < a) {k : ℕ → ℕ}
    (hk : ∀ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ))
    {C d : ℝ} (htrace : ∀ᶠ n : ℕ in atTop,
      (∫ ω, ((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        (fun _ _ ↦ 0) (n + 1) ω ^ (2 * k n)).trace).re ∂P) ≤
      C * (n + 1 : ℝ) ^ d * (2 : ℝ) ^ (2 * k n)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ 0)
        atTop (𝓝 2) ∧
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀
        ((Fin.last n).cast (Fintype.card_fin _).symm))
        atTop (𝓝 (-2)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let R (n : ℕ) : ℝ≥0 := ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩
  let B (n : ℕ) (ω : Ω) := wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P (R n))
    (fun _ _ ↦ 0) (n + 1) ω
  let Z (n : ℕ) (ω : Ω) := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  have hB n ω : (B n ω).IsHermitian := wignerMatrix_isHermitian _ _ _ _
  have hZ n ω : (Z n ω).IsHermitian := wignerMatrix_isHermitian _ _ _ _
  have hint (n : ℕ) : Integrable (fun ω ↦ RCLike.re ((B n ω) ^ (2 * k n)).trace) P := by
    have hi : Integrable (fun ω ↦ ((B n ω) ^ (2 * k n)).trace) P :=
      integrable_trace_pow_wignerMatrix (fun ij _ ↦
        (hid ij).aestronglyMeasurable_fst.memLp_centeredTruncation _) (fun _ _ ↦ memLp_const 0)
    exact Complex.reCLM.integrable_comp hi
  have hnorm := ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_le hB hk
    (.of_forall hint) (by norm_num : (0 : ℝ) < 2) htrace
  have happrox := ae_tendsto_norm_wignerMatrix_sub_centeredTruncation (η := fun _ _ ↦ 0)
    hind hid hξ hmean (fun _ ↦ IdentDistrib.refl aemeasurable_const) (memLp_const 0) ha
  have hweak := ae_tendsto_spectralMeasure_wignerMatrix_zero_of_memLp
    hind hid (hξ.mono_exponent (by norm_num)) hmean 1 (by simpa using hvar)
  have hdiag := ae_tendsto_norm_wignerMatrix_sub_zero_diagonal (ξ := ξ) hd hη
  filter_upwards [hnorm, happrox, hweak, hdiag] with ω hn hdiff hw hdω
  have hZnorm r (hr : 2 < r) : ∀ᶠ n in atTop, ‖Z n ω‖ < r := by
    have hclose := hdiff.eventually_lt_const (show 0 < (r - 2) / 2 by linarith)
    filter_upwards [hn ((r + 2) / 2) (by linarith), hclose] with n hBn hδ
    have hδ' : ‖Z n ω - B n ω‖ < (r - 2) / 2 := hδ
    have htri : ‖Z n ω‖ ≤ ‖Z n ω - B n ω‖ + ‖B n ω‖ := by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (Z n ω) (B n ω) 0
    exact htri.trans_lt ((add_lt_add hδ' hBn).trans_eq (by ring))
  obtain ⟨htop, hbottom⟩ := tendsto_extreme_eigenvalues₀_of_tendsto_spectralMeasure
    (A := fun n ↦ Z n ω) (hA := fun n ↦ hZ n ω) hw
    (c := 2) (by simp [support_semicircleReal]) (by simp [support_semicircleReal]) hZnorm
  have heq (n : ℕ) : (Fin.last n).cast (Fintype.card_fin (n + 1)).symm =
      (Fin.last (Fintype.card (Fin (n + 1)) - 1)).cast (Nat.sub_add_cancel Fintype.card_pos) := by
    apply Fin.ext
    simp
  exact ⟨tendsto_wigner_eigenvalues₀_of_tendsto_norm_sub_zero ω (fun _ ↦ 0) hdω htop,
    tendsto_wigner_eigenvalues₀_of_tendsto_norm_sub_zero ω
      (fun n ↦ (Fin.last n).cast (Fintype.card_fin _).symm) hdω
      (by simpa only [heq] using hbottom)⟩

end TauCeti.Probability
