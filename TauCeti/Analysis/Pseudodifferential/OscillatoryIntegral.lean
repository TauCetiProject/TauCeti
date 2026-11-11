/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import TauCeti.Analysis.Pseudodifferential.Quantization
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Oscillatory integrals with the phase `-⟪y, ξ⟫`

For an amplitude `b : E × E → W` of a position `y` and an angular frequency `ξ`, the oscillatory
integral

`∫∫ exp(-i ⟪y, ξ⟫) b(y, ξ) dy dξ`

need not converge absolutely: a symbol of order `m ≥ 0` does not decay in `ξ`. It is defined by
regularization: the integrand is multiplied by `χ(εξ)` for a compactly supported continuous
cutoff `χ` with `χ(0) = 1`, which makes it absolutely integrable on `E × E` when `b` is a.e.
strongly measurable with integrable position slices of polynomially bounded `L¹` norm, and one
lets `ε → 0`.

The limit exists, and is independent of the cutoff, as soon as the position derivatives of the
amplitude have polynomial growth in the frequency: if `b` is a.e. strongly measurable on
`E × E`, `y ↦ b(y, ξ)` is `C^N` with integrable derivatives, and both `∫ ‖b(y, ξ)‖ dy` and
`∫ ‖D_y^N b(y, ξ)‖ dy` are at most `C ⟨ξ⟩ ^ m`, where `⟨ξ⟩ ^ s = (1 + ‖ξ‖²) ^ (s / 2)` and
`N > m + dim E`. Integrating by parts `N` times in the position,
`‖ξ‖ ^ N ‖∫ exp(-i ⟪y, ξ⟫) b(y, ξ) dy‖ ≤ ∫ ‖D_y^N b(y, ξ)‖ dy`, so the position integral is
`O(⟨ξ⟩ ^ (m - N))` and hence integrable in the frequency. The limit of the regularized integrals
is therefore the iterated integral with the position integral inside,
`TauCeti.oscillatoryIntegral`.

The left Kohn–Nirenberg quantization of a coefficient `a(x, ξ)` on a Schwartz function `u` is
`(2π)⁻ⁿ` times the oscillatory integral of `b(y, ξ) = exp(i ⟪x, ξ⟫) a(x, ξ) u(y)`, so its formal
double integral `(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) u(y) dy dξ` is the limit of its
regularizations.

## Main results

* `TauCeti.norm_integral_exp_smul_le`: integration by parts in the position bounds the position
  integral by `2 ^ (N + 1) C ⟨ξ⟩ ^ (m - N)`.
* `TauCeti.integrable_integral_exp_smul`: the position integral is integrable in the frequency.
* `TauCeti.norm_oscillatoryIntegral_le`: the bound
  `‖∫∫ exp(-i ⟪y, ξ⟫) b(y, ξ) dy dξ‖ ≤ 2 ^ (N + 1) C ∫ ⟨ξ⟩ ^ (m - N) dξ`.
* `TauCeti.integrable_cutoff_smul`: for `ε ≠ 0` the regularized integrand
  `χ(εξ) exp(-i ⟪y, ξ⟫) b(y, ξ)` is integrable on `E × E`.
* `TauCeti.tendsto_integral_cutoff_smul_oscillatoryIntegral`: the regularized double integrals
  `∫∫ χ(εξ) exp(-i ⟪y, ξ⟫) b(y, ξ) dy dξ` tend to the oscillatory integral as `ε → 0`, for every
  cutoff `χ`.
* `TauCeti.quantizeSchwartzValue_eq_smul_oscillatoryIntegral` and
  `TauCeti.tendsto_integral_cutoff_smul_quantizeSchwartzValue`: the Kohn–Nirenberg quantization
  of a coefficient with polynomial growth is the regularized limit of its double integral.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.1)–(1.4).
-/

public section

open MeasureTheory Filter Real Module
open scoped RealInnerProductSpace Topology SchwartzMap ContDiff FourierTransform

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The oscillatory integral `∫∫ exp(-i ⟪y, ξ⟫) b(y, ξ) dy dξ` of an amplitude `b(y, ξ)`, as the
iterated Bochner integral with the position integral inside. It is the oscillatory integral only
for amplitudes whose position slices `y ↦ b(y, ξ)` are integrable; otherwise the inner Bochner
integral is `0`. If `b` is a.e. strongly measurable on `E × E`, the slices are `C^N` with
integrable derivatives up to order `N`, and both `∫ ‖b(y, ξ)‖ dy` and `∫ ‖D_y^N b(y, ξ)‖ dy`
are at most `C ⟨ξ⟩ ^ m` with `N > m + dim E`, the position integral is integrable in the
frequency (`integrable_integral_exp_smul`) and this is the limit of the regularized double
integrals (`tendsto_integral_cutoff_smul_oscillatoryIntegral`). -/
def oscillatoryIntegral (b : E × E → W) : W :=
  ∫ ξ, ∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b (y, ξ)

/-- Unfolding `oscillatoryIntegral` into the iterated integral. -/
theorem oscillatoryIntegral_def (b : E × E → W) :
    oscillatoryIntegral b = ∫ ξ, ∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b (y, ξ) :=
  (rfl)

/-- The oscillatory integral is homogeneous in the amplitude. -/
@[simp]
theorem oscillatoryIntegral_smul (c : ℂ) (b : E × E → W) :
    oscillatoryIntegral (c • b) = c • oscillatoryIntegral b := by
  simp only [oscillatoryIntegral_def, Pi.smul_apply, smul_comm _ c, integral_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma norm_exp_neg_inner_mul_I (y ξ : E) : ‖Complex.exp (-(⟪y, ξ⟫ * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The oscillatory integral is additive on amplitudes whose position slices are integrable and
whose position integrals are integrable in the frequency. -/
theorem oscillatoryIntegral_add {b b' : E × E → W} (hb : ∀ ξ, Integrable fun y ↦ b (y, ξ))
    (hb' : ∀ ξ, Integrable fun y ↦ b' (y, ξ))
    (hF : Integrable fun ξ ↦ ∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b (y, ξ))
    (hF' : Integrable fun ξ ↦ ∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b' (y, ξ)) :
    oscillatoryIntegral (b + b') = oscillatoryIntegral b + oscillatoryIntegral b' := by
  simp only [oscillatoryIntegral_def, Pi.add_apply, smul_add]
  rw [← integral_add hF hF']
  congr 1 with ξ
  exact integral_add (integrable_exp_neg_inner_smul (hb ξ) ξ)
    (integrable_exp_neg_inner_smul (hb' ξ) ξ)

section Amplitude

variable {b : E × E → W} {m C : ℝ} {N : ℕ}

/-- **Integration by parts in the position.** The position integral of an amplitude whose `C^N`
position slices satisfy `∫ ‖b(y, ξ)‖ dy ≤ C ⟨ξ⟩ ^ m` and `∫ ‖D_y^N b(y, ξ)‖ dy ≤ C ⟨ξ⟩ ^ m` is
bounded by `2 ^ (N + 1) C ⟨ξ⟩ ^ (m - N)`. -/
theorem norm_integral_exp_smul_le (hdiff : ∀ ξ, ContDiff ℝ N fun y ↦ b (y, ξ))
    (hint : ∀ ξ, ∀ k ≤ N, Integrable (iteratedFDeriv ℝ k fun y ↦ b (y, ξ)))
    (h₀ : ∀ ξ, ∫ y, ‖b (y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hN : ∀ ξ, ∫ y, ‖iteratedFDeriv ℝ N (fun y ↦ b (y, ξ)) y‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (ξ : E) :
    ‖∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b (y, ξ)‖ ≤
      2 ^ (N + 1) * C * (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  set w := 1 + ‖ξ‖ ^ 2
  have hw : 0 < w := by positivity
  rw [integral_exp_smul_eq_fourier]
  set F := 𝓕 (fun y ↦ b (y, ξ)) ((2 * π)⁻¹ • ξ)
  have hA : ‖F‖ ≤ C * w ^ (m / 2) := (Real.norm_fourier_le_integral_norm _ _).trans (h₀ ξ)
  have hB : ‖ξ‖ ^ N * ‖F‖ ≤ C * w ^ (m / 2) := by
    have h := pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv (hdiff ξ) (hint ξ)
      ((2 * π)⁻¹ • ξ)
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul] at h
    exact h.trans (hN ξ)
  have hsplit : w ^ ((m - N) / 2) * w ^ ((N : ℝ) / 2) = w ^ (m / 2) := by
    rw [← Real.rpow_add hw]
    ring_nf
  have hpow : 0 < w ^ ((N : ℝ) / 2) := Real.rpow_pos_of_pos hw _
  refine le_of_mul_le_mul_right ?_ hpow
  rw [mul_assoc (2 ^ (N + 1) * C), hsplit]
  calc ‖F‖ * w ^ ((N : ℝ) / 2) ≤ ‖F‖ * (2 ^ N * (1 + ‖ξ‖ ^ N)) :=
        mul_le_mul_of_nonneg_left (one_add_norm_sq_rpow_le_two_pow_mul_one_add_norm_pow ξ N)
          (norm_nonneg _)
    _ = 2 ^ N * (‖F‖ + ‖ξ‖ ^ N * ‖F‖) := by ring
    _ ≤ 2 ^ N * (C * w ^ (m / 2) + C * w ^ (m / 2)) := by gcongr
    _ = 2 ^ (N + 1) * C * w ^ (m / 2) := by ring

/-- The frequency weight `⟨ξ⟩ ^ (m - N)` is integrable when `N > m + dim E`. -/
private lemma integrable_one_add_norm_sq_rpow_sub (hNm : m + finrank ℝ E < N) :
    Integrable fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  have hr : (finrank ℝ E : ℝ) < N - m := by linarith
  simpa only [show -((N : ℝ) - m) / 2 = (m - N) / 2 by ring] using
    integrable_rpow_neg_one_add_norm_sq (E := E) (μ := volume) hr

/-- The integrand of the position integral is a.e. strongly measurable on the product. -/
private lemma aestronglyMeasurable_exp_smul (hb : AEStronglyMeasurable b) :
    AEStronglyMeasurable (fun p : E × E ↦ Complex.exp (-(⟪p.1, p.2⟫ * Complex.I)) • b p) :=
  (by fun_prop : Continuous fun p : E × E ↦ Complex.exp (-(⟪p.1, p.2⟫ * Complex.I))
    ).aestronglyMeasurable.smul hb

/-- **The position integral is integrable.** If `b` is a.e. strongly measurable, its position
slices `y ↦ b(y, ξ)` are `C^N` with integrable derivatives, and `∫ ‖b(y, ξ)‖ dy` and
`∫ ‖D_y^N b(y, ξ)‖ dy` are at most `C ⟨ξ⟩ ^ m` with `N > m + dim E`, then
`ξ ↦ ∫ exp(-i ⟪y, ξ⟫) b(y, ξ) dy` is integrable. -/
theorem integrable_integral_exp_smul (hb : AEStronglyMeasurable b)
    (hdiff : ∀ ξ, ContDiff ℝ N fun y ↦ b (y, ξ))
    (hint : ∀ ξ, ∀ k ≤ N, Integrable (iteratedFDeriv ℝ k fun y ↦ b (y, ξ)))
    (h₀ : ∀ ξ, ∫ y, ‖b (y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hN : ∀ ξ, ∫ y, ‖iteratedFDeriv ℝ N (fun y ↦ b (y, ξ)) y‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hNm : m + finrank ℝ E < N) :
    Integrable fun ξ ↦ ∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b (y, ξ) := by
  exact ((integrable_one_add_norm_sq_rpow_sub hNm).const_mul (2 ^ (N + 1) * C)).mono'
    (aestronglyMeasurable_exp_smul hb).prod_swap.integral_prod_right'
    (ae_of_all _ (norm_integral_exp_smul_le hdiff hint h₀ hN))

/-- **Bound on the oscillatory integral.** Under the hypotheses of
`integrable_integral_exp_smul`,
`‖∫∫ exp(-i ⟪y, ξ⟫) b(y, ξ) dy dξ‖ ≤ 2 ^ (N + 1) C ∫ ⟨ξ⟩ ^ (m - N) dξ`. -/
theorem norm_oscillatoryIntegral_le (hdiff : ∀ ξ, ContDiff ℝ N fun y ↦ b (y, ξ))
    (hint : ∀ ξ, ∀ k ≤ N, Integrable (iteratedFDeriv ℝ k fun y ↦ b (y, ξ)))
    (h₀ : ∀ ξ, ∫ y, ‖b (y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hN : ∀ ξ, ∫ y, ‖iteratedFDeriv ℝ N (fun y ↦ b (y, ξ)) y‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hNm : m + finrank ℝ E < N) :
    ‖oscillatoryIntegral b‖ ≤ 2 ^ (N + 1) * C * ∫ ξ : E, (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  rw [oscillatoryIntegral_def, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((integrable_one_add_norm_sq_rpow_sub hNm).const_mul _)
    (ae_of_all _ (norm_integral_exp_smul_le hdiff hint h₀ hN))

variable {χ : E → ℂ}

/-- **The regularized integrand is integrable.** If `b` is a.e. strongly measurable, its position
slices `y ↦ b(y, ξ)` are integrable with `∫ ‖b(y, ξ)‖ dy ≤ C ⟨ξ⟩ ^ m`, and `χ` is continuous
and compactly supported, then for `ε ≠ 0` the regularized integrand
`χ(εξ) exp(-i ⟪y, ξ⟫) b(y, ξ)` is integrable on `E × E`. -/
theorem integrable_cutoff_smul (hb : AEStronglyMeasurable b)
    (hint₀ : ∀ ξ, Integrable fun y ↦ b (y, ξ))
    (h₀ : ∀ ξ, ∫ y, ‖b (y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hχ : Continuous χ) (hχs : HasCompactSupport χ) {ε : ℝ} (hε : ε ≠ 0) :
    Integrable fun p : E × E ↦
      χ (ε • p.2) • Complex.exp (-(⟪p.1, p.2⟫ * Complex.I)) • b p := by
  have hχε : Continuous fun ξ : E ↦ χ (ε • ξ) := hχ.comp (continuous_const_smul ε)
  have hmeas : AEStronglyMeasurable fun p : E × E ↦
      χ (ε • p.2) • Complex.exp (-(⟪p.1, p.2⟫ * Complex.I)) • b p :=
    (hχε.comp continuous_snd).aestronglyMeasurable.smul (aestronglyMeasurable_exp_smul hb)
  have hnorm : ∀ y ξ : E,
      ‖χ (ε • ξ) • Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b (y, ξ)‖ = ‖χ (ε • ξ)‖ * ‖b (y, ξ)‖ := by
    intro y ξ
    rw [norm_smul, norm_smul, norm_exp_neg_inner_mul_I, one_mul]
  rw [Measure.volume_eq_prod, integrable_prod_iff' hmeas]
  refine ⟨ae_of_all _ fun ξ ↦ ?_, ?_⟩
  · exact (integrable_exp_neg_inner_smul (hint₀ ξ) ξ).smul (χ (ε • ξ))
  · have hbound : Integrable fun ξ : E ↦ ‖χ (ε • ξ)‖ * (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
      Continuous.integrable_of_hasCompactSupport (hχε.norm.mul (continuous_const.mul
        ((continuous_const.add (continuous_norm.pow 2)).rpow_const
          fun ξ ↦ Or.inl (by positivity : (1 : ℝ) + ‖ξ‖ ^ 2 ≠ 0))))
        (hχs.comp_smul hε).norm.mul_right
    refine hbound.mono' hmeas.norm.prod_swap.integral_prod_right' (ae_of_all _ fun ξ ↦ ?_)
    simp only [hnorm, integral_const_mul]
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
      (integral_nonneg fun _ ↦ norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (h₀ ξ) (norm_nonneg _)

/-- **Oscillatory integrals as regularized limits.** Let `b` be an amplitude as in
`integrable_integral_exp_smul`, and let `χ` be a continuous compactly supported cutoff with
`χ 0 = 1`. Then the absolutely convergent double integrals
`∫∫ χ(εξ) exp(-i ⟪y, ξ⟫) b(y, ξ) dy dξ` tend to the oscillatory integral of `b` as `ε → 0`;
in particular the limit does not depend on the cutoff. -/
theorem tendsto_integral_cutoff_smul_oscillatoryIntegral (hb : AEStronglyMeasurable b)
    (hdiff : ∀ ξ, ContDiff ℝ N fun y ↦ b (y, ξ))
    (hint : ∀ ξ, ∀ k ≤ N, Integrable (iteratedFDeriv ℝ k fun y ↦ b (y, ξ)))
    (h₀ : ∀ ξ, ∫ y, ‖b (y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hN : ∀ ξ, ∫ y, ‖iteratedFDeriv ℝ N (fun y ↦ b (y, ξ)) y‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hNm : m + finrank ℝ E < N) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) :
    Tendsto (fun ε : ℝ ↦ ∫ p : E × E,
        χ (ε • p.2) • Complex.exp (-(⟪p.1, p.2⟫ * Complex.I)) • b p)
      (𝓝[≠] 0) (𝓝 (oscillatoryIntegral b)) := by
  set F := fun ξ ↦ ∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • b (y, ξ)
  have hF : Integrable F := integrable_integral_exp_smul hb hdiff hint h₀ hN hNm
  have hint₀ : ∀ ξ, Integrable fun y ↦ b (y, ξ) := fun ξ ↦
    (integrable_norm_iff (hdiff ξ).continuous.aestronglyMeasurable).mp
      (by simpa only [norm_iteratedFDeriv_zero] using (hint ξ 0 (Nat.zero_le _)).norm)
  obtain ⟨M, hM⟩ := hχ.bounded_above_of_compact_support hχs
  -- Fubini: for `ε ≠ 0` the regularized double integral is `∫ χ(εξ) F(ξ) dξ`.
  have hfub : ∀ ε : ℝ, ε ≠ 0 → ∫ p : E × E,
      χ (ε • p.2) • Complex.exp (-(⟪p.1, p.2⟫ * Complex.I)) • b p = ∫ ξ, χ (ε • ξ) • F ξ := by
    intro ε hε
    rw [Measure.volume_eq_prod, integral_prod_symm _
      (Measure.volume_eq_prod E E ▸ integrable_cutoff_smul hb hint₀ h₀ hχ hχs hε)]
    simp only [F, integral_smul]
  -- Dominated convergence: `ε ↦ ∫ χ(εξ) F(ξ) dξ` is continuous at `0`.
  have hcont : Tendsto (fun ε : ℝ ↦ ∫ ξ, χ (ε • ξ) • F ξ) (𝓝 0) (𝓝 (∫ ξ, χ ((0 : ℝ) • ξ) • F ξ)) :=
    tendsto_integral_filter_of_dominated_convergence (fun ξ ↦ M * ‖F ξ‖)
      (Eventually.of_forall fun ε ↦
        ((hχ.comp (continuous_const_smul ε)).aestronglyMeasurable.smul hF.aestronglyMeasurable))
      (Eventually.of_forall fun ε ↦ ae_of_all _ fun ξ ↦ by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
      (hF.norm.const_mul M)
      (ae_of_all _ fun ξ ↦ ((hχ.comp (continuous_id.smul continuous_const)).tendsto 0).smul_const _)
  simp only [zero_smul, hχ0, one_smul] at hcont
  exact (hcont.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun ε hε ↦ (hfub ε hε).symm)

end Amplitude

section Quantization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The left Kohn–Nirenberg quantization of a coefficient `a` on a Schwartz function `u` at `x` is
`(2π)⁻ⁿ` times the oscillatory integral of the amplitude
`b(y, ξ) = exp(i ⟪x, ξ⟫) a(x, ξ) u(y)`, with `n = finrank ℝ E`. -/
theorem quantizeSchwartzValue_eq_smul_oscillatoryIntegral [CompleteSpace V]
    (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a u x = ((2 * π) ^ finrank ℝ E)⁻¹ •
      oscillatoryIntegral fun p : E × E ↦ Complex.exp (⟪x, p.2⟫ * Complex.I) • a (x, p.2) (u p.1)
    := by
  by_cases hW : CompleteSpace W
  swap
  · simp only [quantizeSchwartzValue_def, oscillatoryIntegral_def,
      integral_of_not_completeSpace hW, smul_zero]
  rw [quantizeSchwartzValue_eq_smul_integral, oscillatoryIntegral_def]
  congr 2 with ξ
  rw [← (a (x, ξ)).integral_comp_comm (integrable_exp_neg_inner_smul u.integrable ξ),
    ← integral_smul]
  congr 1 with y
  rw [map_smul, smul_comm]

/-- **The Kohn–Nirenberg quantization as a regularized double integral.** If `ξ ↦ a(x, ξ)` is
a.e. strongly measurable and `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m`, then for every continuous compactly
supported cutoff `χ` with `χ 0 = 1`,

`(2π)⁻ⁿ ∫∫ χ(εξ) exp(i ⟪x - y, ξ⟫) a(x, ξ) u(y) dy dξ → Op(a) u (x)` as `ε → 0`,

where `n = finrank ℝ E`. -/
theorem tendsto_integral_cutoff_smul_quantizeSchwartzValue [CompleteSpace V]
    {a : E × E → V →L[ℂ] W} {x : E} {C m : ℝ} (hmeas : AEStronglyMeasurable fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (u : 𝓢(E, V)) {χ : E → ℂ}
    (hχ : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : χ 0 = 1) :
    Tendsto (fun ε : ℝ ↦ ((2 * π) ^ finrank ℝ E)⁻¹ • ∫ p : E × E,
        χ (ε • p.2) • Complex.exp (⟪x - p.1, p.2⟫ * Complex.I) • a (x, p.2) (u p.1))
      (𝓝[≠] 0) (𝓝 (quantizeSchwartzValue a u x)) := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  -- The amplitude is `b(y, ξ) = L ξ (u y)` with `L ξ = exp(i ⟪x, ξ⟫) a(x, ξ)`.
  set L : E → V →L[ℝ] W := fun ξ ↦
    (Complex.exp (⟪x, ξ⟫ * Complex.I) • a (x, ξ)).restrictScalars ℝ
  have hL : ∀ ξ, ‖L ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := fun ξ ↦ by
    rw [ContinuousLinearMap.norm_restrictScalars, norm_smul, Complex.norm_exp_ofReal_mul_I,
      one_mul]
    exact hC ξ
  set N := ⌊m⌋₊ + finrank ℝ E + 1
  set K := (∫ y, ‖u y‖) + ∫ y, ‖iteratedFDeriv ℝ N u y‖
  have hK₀ : ∫ y, ‖u y‖ ≤ K :=
    le_add_of_nonneg_right (integral_nonneg fun _ ↦ norm_nonneg _)
  have hKN : ∫ y, ‖iteratedFDeriv ℝ N u y‖ ≤ K :=
    le_add_of_nonneg_left (integral_nonneg fun _ ↦ norm_nonneg _)
  have hbound : ∀ ξ, ∀ k, ∫ y, ‖iteratedFDeriv ℝ k u y‖ ≤ K →
      ∫ y, ‖iteratedFDeriv ℝ k (fun y ↦ L ξ (u y)) y‖ ≤ C * K * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
    fun ξ k hk ↦ (u.integral_norm_iteratedFDeriv_comp_left_le (L ξ) k).trans <| by
      rw [mul_right_comm]
      exact mul_le_mul (hL ξ) hk (integral_nonneg fun _ ↦ norm_nonneg _) (by positivity)
  have hmeas' : AEStronglyMeasurable fun p : E × E ↦ L p.2 (u p.1) := by
    have h : AEStronglyMeasurable fun p : E × E ↦
        Complex.exp (⟪x, p.2⟫ * Complex.I) • a (x, p.2) (u p.1) :=
      (by fun_prop : Continuous fun p : E × E ↦ Complex.exp (⟪x, p.2⟫ * Complex.I)
        ).aestronglyMeasurable.smul (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hmeas.comp_snd.prodMk (u.continuous.comp continuous_fst).aestronglyMeasurable))
    refine h.congr (ae_of_all _ fun p ↦ ?_)
    simp only [L, ContinuousLinearMap.coe_restrictScalars', smul_apply]
  have key := tendsto_integral_cutoff_smul_oscillatoryIntegral (b := fun p ↦ L p.2 (u p.1))
    (N := N) hmeas'
    (fun ξ ↦ ((L ξ).contDiff.comp (u.smooth ⊤)).of_le (mod_cast le_top))
    (fun ξ k _ ↦ u.integrable_iteratedFDeriv_comp_left (L ξ) k)
    (fun ξ ↦ by simpa only [norm_iteratedFDeriv_zero] using hbound ξ 0 (by simpa using hK₀))
    (fun ξ ↦ hbound ξ N hKN)
    (by simp only [N]; push_cast; linarith [Nat.lt_floor_add_one m]) hχ hχs hχ0
  rw [quantizeSchwartzValue_eq_smul_oscillatoryIntegral]
  refine (key.const_smul ((2 * π) ^ finrank ℝ E)⁻¹).congr fun ε ↦ ?_
  congr 2 with p
  rw [ContinuousLinearMap.coe_restrictScalars', smul_apply,
    smul_smul (Complex.exp (-(⟪p.1, p.2⟫ * Complex.I))), ← Complex.exp_add, inner_sub_left]
  congr 3
  push_cast
  ring

end Quantization

end TauCeti
