/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Non-stationary phase in a direction

Let `f` be a smooth compactly supported complex function on a finite-dimensional real normed
space and `Φ` a smooth real phase. If the derivative `∂_w Φ` of the phase in a direction `w` stays
away from zero on the support of `f`, comparable to a large parameter `r`, and its own derivatives
are `O(r)` there, then the oscillatory integral decays faster than every power of `r`:

`‖∫ f(y) 𝐞(Φ(y)) dy‖ ≤ C r^(-M)`,

with `C` depending only on `f`, `M` and the comparability constant, not on `Φ`, `w` or `r`
(`TauCeti.exists_norm_integral_mul_fourierChar_le`). This is the principle of non-stationary
phase, in the form used to transport the wave front set along changes of variables, where the
phase is `⟪y, η⟫ - ⟪κ(y), ξ⟫` for a diffeomorphism `κ` and its derivative in a suitable direction
is comparable to the frequencies.

The proof integrates by parts `M` times in the direction `w`. Since
`∂_w 𝐞(Φ) = 2πi (∂_w Φ) 𝐞(Φ)`, each step trades the amplitude `h` for `∂_w (h v)`, where
`v = r / ∂_w Φ` on the support of `f`, at the price of a factor `(2πr)⁻¹`. The function `v` is
`g ∘ (∂_w Φ / r)` for a fixed smooth function `g` equal to `t ↦ t⁻¹` on `[1, ∞)`, so the bounds on
the derivatives of `∂_w Φ / r` give bounds on those of `v` that do not depend on `r`
(`norm_iteratedFDeriv_comp_le`), and the Leibniz rule bounds the derivatives of the successive
amplitudes.

## Main results

* `TauCeti.exists_norm_integral_mul_fourierChar_le`: the non-stationary phase estimate.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §2.1.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff FourierTransform Nat Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth function equal to `t ↦ t⁻¹` on `[1, ∞)`. Its denominator
`1 / 2 + s (2 t - 1) (t - 1 / 2)`, with `s` the smooth transition, is at least `1 / 2`
everywhere. -/
private def smoothRecip (t : ℝ) : ℝ :=
  (1 / 2 + Real.smoothTransition (2 * t - 1) * (t - 1 / 2))⁻¹

private theorem smoothRecip_denom_pos (t : ℝ) :
    0 < 1 / 2 + Real.smoothTransition (2 * t - 1) * (t - 1 / 2) := by
  rcases le_or_gt (1 / 2) t with ht | ht
  · have := mul_nonneg (Real.smoothTransition.nonneg (2 * t - 1)) (sub_nonneg.2 ht)
    linarith
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num

private theorem contDiff_smoothRecip : ContDiff ℝ ∞ smoothRecip :=
  (contDiff_const.add ((Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
      (contDiff_id.sub contDiff_const))).inv fun t ↦ (smoothRecip_denom_pos t).ne'

private theorem smoothRecip_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothRecip t = t⁻¹ := by
  rw [smoothRecip, Real.smoothTransition.one_of_one_le (by linarith)]
  ring_nf

/-- The amplitudes produced by integrating by parts against `𝐞(Φ)` in the direction `w`, with the
multiplier `v`: `h₀ = f` and `h_(k+1) = ∂_w (h_k v)`. -/
private def ibpAmplitude (f v : E → ℂ) (w : E) : ℕ → E → ℂ
  | 0 => f
  | k + 1 => fun y ↦ fderiv ℝ (fun z ↦ ibpAmplitude f v w k z * v z) y w

private theorem contDiff_ibpAmplitude {f v : E → ℂ} (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (w : E) (k : ℕ) : ContDiff ℝ ∞ (ibpAmplitude f v w k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact ((ih.mul hv).fderiv_right (by simp)).clm_apply contDiff_const

private theorem tsupport_ibpAmplitude_subset (f v : E → ℂ) (w : E) (k : ℕ) :
    tsupport (ibpAmplitude f v w k) ⊆ tsupport f := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    refine ((tsupport_comp_subset (g := fun L : E →L[ℝ] ℂ ↦ L w) (by simp) _).trans
      (tsupport_fderiv_subset ℝ)).trans ((tsupport_mul_subset_left).trans ih)

/-- One integration by parts: if `v ∂_w Φ = r` on the support of `f`, then
`∫ h_k 𝐞(Φ) = -(2πir)⁻¹ ∫ h_(k+1) 𝐞(Φ)`. -/
private theorem integral_ibpAmplitude_mul_fourierChar [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] {f v : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v) {Φ : E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {w : E} {r : ℝ} (hr : r ≠ 0)
    (hvΦ : ∀ y ∈ tsupport f, v y * (fderiv ℝ Φ y w : ℂ) = r) (k : ℕ) :
    ∫ y, ibpAmplitude f v w k y * 𝐞 (Φ y) ∂μ =
      -(2 * π * Complex.I * r)⁻¹ * ∫ y, ibpAmplitude f v w (k + 1) y * 𝐞 (Φ y) ∂μ := by
  set h := ibpAmplitude f v w k
  have hh : ContDiff ℝ ∞ h := contDiff_ibpAmplitude hf hv w k
  have hhs : tsupport h ⊆ tsupport f := tsupport_ibpAmplitude_subset f v w k
  have hhv : HasCompactSupport fun z ↦ h z * v z :=
    (hfc.mono' ((subset_tsupport h).trans hhs)).mul_right
  -- The derivative of the phase factor `𝐞 ∘ Φ`.
  have hG (y : E) : fderiv ℝ (fun z ↦ (𝐞 (Φ z) : ℂ)) y w =
      (2 * π * Complex.I * 𝐞 (Φ y)) * (fderiv ℝ Φ y w : ℂ) := by
    have h1 := (Real.hasDerivAt_fourierChar (Φ y)).hasFDerivAt.comp y
      ((hΦ.differentiable (by simp)) y).hasFDerivAt
    rw [show (fun z ↦ (𝐞 (Φ z) : ℂ)) = (fun t : ℝ ↦ (𝐞 t : ℂ)) ∘ Φ from rfl, h1.fderiv]
    simp [mul_comm]
  have hGc : ContDiff ℝ ∞ fun z ↦ (𝐞 (Φ z) : ℂ) := by
    simp_rw [Real.fourierChar_apply]
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul hΦ)).mul contDiff_const)
  have hibp := integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport (μ := μ)
    (ContinuousLinearMap.mul ℝ ℂ) (f := fun z ↦ (𝐞 (Φ z) : ℂ)) (g := fun z ↦ h z * v z)
    (fun x _ ↦ hGc.contDiffAt.of_le (by simp)) ((hh.mul hv).of_le (by simp)) hhv w
  simp only [ContinuousLinearMap.mul_apply', hG] at hibp
  -- On the support of `f`, `∂_w (𝐞 ∘ Φ) (h v) = 2πir h 𝐞(Φ)`; off it both sides vanish.
  have hpt (y : E) : (2 * π * Complex.I * 𝐞 (Φ y)) * (fderiv ℝ Φ y w : ℂ) * (h y * v y) =
      (2 * π * Complex.I * r) * (h y * 𝐞 (Φ y)) := by
    by_cases hy : y ∈ tsupport f
    · rw [← hvΦ y hy]
      ring
    · have : h y = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hy (hhs h')
      simp [this]
  have hL : ∫ y, (𝐞 (Φ y) : ℂ) * ibpAmplitude f v w (k + 1) y ∂μ =
      -((2 * π * Complex.I * r) * ∫ y, h y * 𝐞 (Φ y) ∂μ) := by
    rw [← integral_const_mul]
    exact hibp.trans (congrArg _ (integral_congr_ae (ae_of_all _ hpt)))
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [show (∫ y, ibpAmplitude f v w (k + 1) y * 𝐞 (Φ y) ∂μ) =
      ∫ y, (𝐞 (Φ y) : ℂ) * ibpAmplitude f v w (k + 1) y ∂μ by simp_rw [mul_comm], hL]
  field_simp

/-- Iterating the integration by parts `k` times. -/
private theorem integral_mul_fourierChar_eq_pow_mul [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] {f v : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v) {Φ : E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {w : E} {r : ℝ} (hr : r ≠ 0)
    (hvΦ : ∀ y ∈ tsupport f, v y * (fderiv ℝ Φ y w : ℂ) = r) (k : ℕ) :
    ∫ y, f y * 𝐞 (Φ y) ∂μ =
      (-(2 * π * Complex.I * r)⁻¹) ^ k * ∫ y, ibpAmplitude f v w k y * 𝐞 (Φ y) ∂μ := by
  induction k with
  | zero => simp [ibpAmplitude]
  | succ k ih =>
    rw [ih, integral_ibpAmplitude_mul_fourierChar hf hfc hv hΦ hr hvΦ k]
    ring

/-- The derivatives of the amplitudes `h_k` of order at most `M - k` are bounded on the support
of `f` by `(2 ^ M C_v) ^ k C_f`, if those of `f` and `v` of order at most `M` are bounded by `C_f`
and `C_v` there and `‖w‖ ≤ 1`. -/
private theorem norm_iteratedFDeriv_ibpAmplitude_le {f v : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hv : ContDiff ℝ ∞ v) {w : E} (hw : ‖w‖ ≤ 1) {M : ℕ} {Cf Cv : ℝ} (hCf : 0 ≤ Cf)
    (hCv : 0 ≤ Cv) (hfb : ∀ j ≤ M, ∀ y ∈ tsupport f, ‖iteratedFDeriv ℝ j f y‖ ≤ Cf)
    (hvb : ∀ j ≤ M, ∀ y ∈ tsupport f, ‖iteratedFDeriv ℝ j v y‖ ≤ Cv) (k : ℕ) :
    ∀ j, j + k ≤ M → ∀ y ∈ tsupport f,
      ‖iteratedFDeriv ℝ j (ibpAmplitude f v w k) y‖ ≤ (2 ^ M * Cv) ^ k * Cf := by
  induction k with
  | zero =>
    intro j hj y hy
    rw [pow_zero, one_mul]
    exact hfb j (by omega) y hy
  | succ k ih =>
    intro j hj y hy
    set h := ibpAmplitude f v w k
    have hh : ContDiff ℝ ∞ h := contDiff_ibpAmplitude hf hv w k
    have hF : ContDiff ℝ ∞ fun z ↦ h z * v z := hh.mul hv
    -- `h_(k+1)` is the derivative of `h v` evaluated at `w`.
    have hcomp : ibpAmplitude f v w (k + 1) =
        (ContinuousLinearMap.apply ℝ ℂ w) ∘ fderiv ℝ fun z ↦ h z * v z := rfl
    have happ : ‖ContinuousLinearMap.apply ℝ ℂ w‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
        simpa using (L.le_opNorm w).trans (mul_le_of_le_one_right (norm_nonneg _) hw)
    calc ‖iteratedFDeriv ℝ j (ibpAmplitude f v w (k + 1)) y‖
        ≤ ‖ContinuousLinearMap.apply ℝ ℂ w‖ *
            ‖iteratedFDeriv ℝ j (fderiv ℝ fun z ↦ h z * v z) y‖ := by
          rw [hcomp]
          exact (ContinuousLinearMap.apply ℝ ℂ w).norm_iteratedFDeriv_comp_left
            (hF.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)
      _ ≤ ‖iteratedFDeriv ℝ (j + 1) (fun z ↦ h z * v z) y‖ := by
          rw [norm_iteratedFDeriv_fderiv]
          exact mul_le_of_le_one_left (norm_nonneg _) happ
      _ ≤ ∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ) *
            ‖iteratedFDeriv ℝ i h y‖ * ‖iteratedFDeriv ℝ (j + 1 - i) v y‖ :=
          norm_iteratedFDeriv_mul_le hh hv y (by simp)
      _ ≤ ∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ) *
            ((2 ^ M * Cv) ^ k * Cf) * Cv := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' : i ≤ j + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          gcongr
          · exact ih i (by omega) y hy
          · exact hvb _ (by omega) y hy
      _ = 2 ^ (j + 1) * ((2 ^ M * Cv) ^ k * Cf) * Cv := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose (j + 1)
      _ ≤ 2 ^ M * ((2 ^ M * Cv) ^ k * Cf) * Cv := by
          gcongr
          · exact one_le_two
          · omega
      _ = (2 ^ M * Cv) ^ (k + 1) * Cf := by ring

/-- The derivatives of order at most `M` of `v = g ∘ a`, with `g` the smooth reciprocal, are
bounded by `M! C_g D ^ M` at a point where `a ∈ [1, D]` and the derivatives of `a` of orders
`1, …, M` are bounded by the powers of `D ≥ 1`, if those of `g` are bounded by `C_g` on `[1, D]`. -/
private theorem norm_iteratedFDeriv_ofReal_smoothRecip_comp_le {a : E → ℝ} (ha : ContDiff ℝ ∞ a)
    {M : ℕ} {D Cg : ℝ} (hD : 1 ≤ D) (hCg : 0 ≤ Cg)
    (hg : ∀ i ≤ M, ∀ t ∈ Icc 1 D, ‖iteratedFDeriv ℝ i smoothRecip t‖ ≤ Cg) {y : E}
    (hy : a y ∈ Icc 1 D) (hDa : ∀ i, 1 ≤ i → i ≤ M → ‖iteratedFDeriv ℝ i a y‖ ≤ D ^ i) {j : ℕ}
    (hj : j ≤ M) :
    ‖iteratedFDeriv ℝ j (fun z ↦ (smoothRecip (a z) : ℂ)) y‖ ≤ M ! * Cg * D ^ M := by
  have hcomp : (fun z ↦ (smoothRecip (a z) : ℂ)) = Complex.ofRealLI ∘ (smoothRecip ∘ a) := rfl
  rw [hcomp, LinearIsometry.norm_iteratedFDeriv_comp_left _
    ((contDiff_smoothRecip.comp ha).contDiffAt) (by simp)]
  calc ‖iteratedFDeriv ℝ j (smoothRecip ∘ a) y‖ ≤ j ! * Cg * D ^ j :=
        norm_iteratedFDeriv_comp_le contDiff_smoothRecip ha (by simp) y
          (fun i hi ↦ hg i (by omega) _ hy) fun i hi1 hij ↦ hDa i hi1 (by omega)
    _ ≤ M ! * Cg * D ^ M := mul_le_mul (mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.factorial_le hj) hCg) (pow_le_pow_right₀ hD hj) (by positivity)
        (by positivity)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- **Non-stationary phase in a direction.** Let `f` be a smooth compactly supported function and
`M : ℕ`, `D : ℝ`. There is a constant `C` such that for every smooth real phase `Φ`, every
direction `w` with `‖w‖ ≤ 1` and every `r > 0`, if the derivative `∂_w Φ` lies in `[r, D r]` on the
support of `f` and its derivatives of orders `1, …, M` are bounded by `D r` there, then
`‖∫ f(y) 𝐞(Φ(y)) dμ‖ ≤ C / r ^ M`. -/
theorem exists_norm_integral_mul_fourierChar_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (M : ℕ) (D : ℝ) :
    ∃ C, ∀ Φ : E → ℝ, ContDiff ℝ ∞ Φ → ∀ w : E, ‖w‖ ≤ 1 → ∀ r : ℝ, 0 < r →
      (∀ y ∈ tsupport f, r ≤ fderiv ℝ Φ y w ∧ fderiv ℝ Φ y w ≤ D * r) →
      (∀ y ∈ tsupport f, ∀ i, 1 ≤ i → i ≤ M →
        ‖iteratedFDeriv ℝ i (fun z ↦ fderiv ℝ Φ z w) y‖ ≤ D * r) →
      ‖∫ y, f y * 𝐞 (Φ y) ∂μ‖ ≤ C / r ^ M := by
  set D' := max D 1
  have hD' : 1 ≤ D' := le_max_right _ _
  -- Bounds for the derivatives of the reciprocal on `[1, D']` and of `f` on its support.
  obtain ⟨Cg, hCg, hgb⟩ := ((contDiff_smoothRecip.of_le (m := (M : WithTop ℕ∞))
    (by simp)).contDiffOn (s := univ)).exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_univ
      (isCompact_Icc (a := 1) (b := D')) (subset_univ _)
  obtain ⟨Cf, hCf, hfb⟩ := ((hf.of_le (m := (M : WithTop ℕ∞)) (by simp)).contDiffOn
    (s := univ)).exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_univ hfc.isCompact
      (subset_univ _)
  set Cv := (M ! : ℝ) * Cg * D' ^ M
  have hCv : 0 ≤ Cv := by positivity
  refine ⟨(2 ^ M * Cv) ^ M * Cf * μ.real (tsupport f) / (2 * π) ^ M,
    fun Φ hΦ w hw r hr hΦr hΦd ↦ ?_⟩
  -- The normalized derivative `a = ∂_w Φ / r` and the multiplier `v = 1 / a` on the support.
  set a : E → ℝ := fun z ↦ r⁻¹ * fderiv ℝ Φ z w
  have hda : ContDiff ℝ ∞ fun z ↦ fderiv ℝ Φ z w :=
    (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul hda
  set v : E → ℂ := fun z ↦ (smoothRecip (a z) : ℂ)
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp (contDiff_smoothRecip.comp ha)
  have haI {y : E} (hy : y ∈ tsupport f) : a y ∈ Icc 1 D' := by
    obtain ⟨h1, h2⟩ := hΦr y hy
    constructor
    · rw [show a y = r⁻¹ * fderiv ℝ Φ y w from rfl, le_inv_mul_iff₀ hr]
      linarith
    · rw [show a y = r⁻¹ * fderiv ℝ Φ y w from rfl, inv_mul_le_iff₀ hr]
      nlinarith [le_max_left D 1]
  have hvΦ : ∀ y ∈ tsupport f, v y * (fderiv ℝ Φ y w : ℂ) = r := by
    intro y hy
    have h1 : 1 ≤ a y := (haI hy).1
    have hpos : 0 < fderiv ℝ Φ y w := hr.trans_le (hΦr y hy).1
    have hne : ((fderiv ℝ Φ y w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    simp only [v, smoothRecip_of_one_le h1, a]
    push_cast
    field_simp
  -- The derivatives of `v` of order at most `M` are bounded by `Cv` on the support of `f`.
  have hvb : ∀ j ≤ M, ∀ y ∈ tsupport f, ‖iteratedFDeriv ℝ j v y‖ ≤ Cv := by
    intro j hj y hy
    refine norm_iteratedFDeriv_ofReal_smoothRecip_comp_le ha hD' hCg hgb (haI hy)
      (fun i hi1 hiM ↦ ?_) hj
    have heq : a = r⁻¹ • fun z ↦ fderiv ℝ Φ z w := rfl
    rw [heq, iteratedFDeriv_const_smul_apply (hda.of_le (m := i) (by simp)).contDiffAt, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_le_iff₀ hr]
    calc ‖iteratedFDeriv ℝ i (fun z ↦ fderiv ℝ Φ z w) y‖ ≤ D * r := hΦd y hy i hi1 hiM
      _ ≤ r * D' := by rw [mul_comm]; gcongr; exact le_max_left _ _
      _ ≤ r * D' ^ i := by gcongr; exact le_self_pow₀ hD' (by omega)
  -- Integrate by parts `M` times and bound the last amplitude on the support of `f`.
  have hamp := norm_iteratedFDeriv_ibpAmplitude_le hf hv hw hCf hCv hfb hvb M 0 (by omega)
  rw [integral_mul_fourierChar_eq_pow_mul hf hfc hv hΦ hr.ne' hvΦ M, norm_mul, norm_pow,
    norm_neg, norm_inv]
  have hnorm : ‖(2 * π * Complex.I * r : ℂ)‖ = 2 * π * r := by
    simp [abs_of_pos hr, abs_of_pos Real.pi_pos]
  rw [hnorm]
  have hint : ‖∫ y, ibpAmplitude f v w M y * 𝐞 (Φ y) ∂μ‖ ≤
      (2 ^ M * Cv) ^ M * Cf * μ.real (tsupport f) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport f) fun y hy ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h' ↦ hy (tsupport_ibpAmplitude_subset f v w M h'),
        zero_mul]]
    refine norm_setIntegral_le_of_norm_le_const hfc.isCompact.measure_lt_top fun y hy ↦ ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    simpa using hamp y hy
  calc (2 * π * r)⁻¹ ^ M * ‖∫ y, ibpAmplitude f v w M y * 𝐞 (Φ y) ∂μ‖
      ≤ (2 * π * r)⁻¹ ^ M * ((2 ^ M * Cv) ^ M * Cf * μ.real (tsupport f)) := by
        gcongr
    _ = (2 ^ M * Cv) ^ M * Cf * μ.real (tsupport f) / (2 * π) ^ M / r ^ M := by
        rw [inv_pow, mul_pow]
        field_simp

end TauCeti
