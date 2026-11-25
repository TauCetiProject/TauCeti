/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Fourier.FourierChar.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.InnerProductSpace.Calculus

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

As a consequence, on a finite-dimensional real inner product space the Fourier transform at `m`
of a cutoff `ψ` with the nonlinear phase `⟪y, Bᵀ ξ⟫ - ⟪σ y, ξ⟫` decays faster than every power of
`‖m‖`, uniformly in `ξ`, once `Dσ` stays within `ε` of `B` on the support of `ψ` and
`2 ε ‖ξ‖ ≤ ‖m‖` (`TauCeti.exists_norm_pow_mul_norm_fourier_mul_fourierChar_le`): the phase of
the Fourier integral then has derivative at least `‖m‖ / 2` in the direction `-m / ‖m‖`.

A variant allows the directional derivative to change sign: for a family of phases `Φᵢ`,
directions `‖wᵢ‖ ≤ 1` and scales `τᵢ > 0` with `|DΦᵢ(x) wᵢ| ≥ τᵢ` on the support of `ψ` and every
derivative of `Φᵢ` of positive order `O(τᵢ)` there, `‖∫ ψ 𝐞(Φᵢ)‖ ≤ C_N τᵢ^(-N)` uniformly in `i`
(`TauCeti.exists_norm_integral_mul_fourierChar_le_of_le_abs`). Here the integration by parts is
against the reciprocal `(DΦᵢ · wᵢ)⁻¹` itself, whose derivatives are `O(τᵢ⁻¹)`
(`TauCeti.exists_norm_iteratedFDeriv_inv_le_div`). It applies to the phases `⟪f x, ζ⟫ - ⟪x, ξ⟫`
of a change of variables `f` in a Fourier integral: if `(Df(x))†` stays within `c / 2` of a linear
map `B` on the support of `ψ`, the oscillatory integral decays faster than every power of
`‖ξ‖ + ‖ζ‖` on the frequencies with `c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖`
(`TauCeti.exists_norm_integral_mul_fourierChar_inner_sub_le`).

## Main results

* `TauCeti.exists_norm_integral_mul_fourierChar_le`: the non-stationary phase estimate.
* `TauCeti.exists_norm_pow_mul_norm_fourier_mul_fourierChar_le`: rapid decay of the Fourier
  transform of a cutoff with a nonlinear phase close to a linear one.
* `TauCeti.exists_norm_integral_mul_fourierChar_le_of_le_abs`: the estimate uniformly over a family
  of phases whose directional derivatives have size at least `τᵢ`, of either sign.
* `TauCeti.exists_norm_integral_mul_fourierChar_inner_sub_le`: rapid decay in `‖ξ‖ + ‖ζ‖` of the
  oscillatory integrals with phases `⟪f x, ζ⟫ - ⟪x, ξ⟫`, away from their stationary frequencies.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §2.1.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProduct Nat Real RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth function equal to `t ↦ t⁻¹` on `[1, ∞)`: the reciprocal of the smooth lower clamp
at level `1 / 2`. -/
private def smoothRecip (t : ℝ) : ℝ :=
  (smoothLowerClamp (1 / 2) t)⁻¹

private theorem contDiff_smoothRecip : ContDiff ℝ ∞ smoothRecip :=
  (contDiff_smoothLowerClamp _).inv fun t ↦
    ((le_smoothLowerClamp (by norm_num) t).trans_lt' (by norm_num)).ne'

private theorem smoothRecip_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothRecip t = t⁻¹ := by
  rw [smoothRecip, smoothLowerClamp_of_two_mul_le (by norm_num) (by linarith)]

/-- The amplitudes produced by integrating by parts against `𝐞(Φ)` in the direction `w`, with the
multiplier `v`: `h₀ = f` and `h_(k+1) = ∂_w (h_k v)`. -/
private def ibpAmplitude (f v : E → ℂ) (w : E) : ℕ → E → ℂ
  | 0 => f
  | k + 1 => fun y ↦ fderiv ℝ (fun z ↦ ibpAmplitude f v w k z * v z) y w

private theorem ibpAmplitude_succ (f v : E → ℂ) (w : E) (k : ℕ) (y : E) :
    ibpAmplitude f v w (k + 1) y = fderiv ℝ (fun z ↦ ibpAmplitude f v w k z * v z) y w := by
  rw [ibpAmplitude]

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
    rw [((hΦ.differentiable (by simp)) y).hasFDerivAt.fourierChar.fderiv]
    simp [mul_comm]
  have hGc : ContDiff ℝ ∞ fun z ↦ (𝐞 (Φ z) : ℂ) := hΦ.fourierChar
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
        (ContinuousLinearMap.apply ℝ ℂ w) ∘ fderiv ℝ fun z ↦ h z * v z := by
      funext y
      simp [h, ibpAmplitude_succ]
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
  have hcomp : (fun z ↦ (smoothRecip (a z) : ℂ)) = Complex.ofRealLI ∘ (smoothRecip ∘ a) :=
    funext fun _ ↦ by simp [Complex.ofRealLI_apply]
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
    · simp only [a]
      rw [le_inv_mul_iff₀ hr]
      linarith
    · simp only [a]
      rw [inv_mul_le_iff₀ hr]
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
    have heq : a = r⁻¹ • fun z ↦ fderiv ℝ Φ z w := by
      funext z
      simp [a, smul_eq_mul]
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

/-! ### Fourier transforms of cutoffs with a nonlinear phase -/

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The derivatives of positive order of `z ↦ a - ⟪ξ, Dσ(z) w⟫` are bounded by
`‖ξ‖ ‖D^(i+1) σ‖ ‖w‖`. -/
private theorem norm_iteratedFDeriv_const_sub_inner_fderiv_le {σ : V → V} (hσ : ContDiff ℝ ∞ σ)
    (a : ℝ) (ξ w : V) {i : ℕ} (hi : i ≠ 0) (y : V) :
    ‖iteratedFDeriv ℝ i (fun z ↦ a - ⟪ξ, fderiv ℝ σ z w⟫) y‖ ≤
      ‖ξ‖ * (‖iteratedFDeriv ℝ (i + 1) σ y‖ * ‖w‖) := by
  have hσw : ContDiff ℝ ∞ fun z ↦ fderiv ℝ σ z w :=
    (hσ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have heq : (fun z ↦ a - ⟪ξ, fderiv ℝ σ z w⟫) =
      (fun _ ↦ a) - (innerSL ℝ ξ) ∘ fun z ↦ fderiv ℝ σ z w := by
    ext z
    simp
  rw [heq, iteratedFDeriv_sub_apply contDiff_const.contDiffAt
    (((innerSL ℝ ξ).contDiff.comp hσw).contDiffAt.of_le (by simp)),
    iteratedFDeriv_const_of_ne hi, Pi.zero_apply, zero_sub, norm_neg]
  calc ‖iteratedFDeriv ℝ i ((innerSL ℝ ξ) ∘ fun z ↦ fderiv ℝ σ z w) y‖
      ≤ ‖innerSL ℝ ξ‖ * ‖iteratedFDeriv ℝ i (fun z ↦ fderiv ℝ σ z w) y‖ :=
        (innerSL ℝ ξ).norm_iteratedFDeriv_comp_left hσw.contDiffAt (by simp)
    _ ≤ ‖ξ‖ * (‖iteratedFDeriv ℝ (i + 1) σ y‖ * ‖w‖) := by
        gcongr
        · exact (innerSL_apply_norm ℝ ξ).le
        · exact hσ.norm_iteratedFDeriv_fderiv_apply_le (by simp) w y

/-- The phase `y ↦ ⟪Bᵀ ξ - m, y⟫ - ⟪ξ, σ y⟫` has derivative `‖m‖ + ⟪ξ, (B - Dσ(y)) w⟫` in the
direction `w = -m / ‖m‖`. -/
private theorem fderiv_phase_apply_neg_smul [FiniteDimensional ℝ V] {σ : V → V}
    (hσ : ContDiff ℝ ∞ σ) (B : V →L[ℝ] V) (ξ : V) {m : V} (hm : m ≠ 0) (y : V) :
    fderiv ℝ (fun y ↦ innerSL ℝ ((B†) ξ - m) y - innerSL ℝ ξ (σ y)) y (-(‖m‖⁻¹ • m)) =
      ‖m‖ + ⟪ξ, (B - fderiv ℝ σ y) (-(‖m‖⁻¹ • m))⟫ := by
  have h : HasFDerivAt (fun y ↦ innerSL ℝ ((B†) ξ - m) y - innerSL ℝ ξ (σ y))
      (innerSL ℝ ((B†) ξ - m) - (innerSL ℝ ξ).comp (fderiv ℝ σ y)) y :=
    ((innerSL ℝ ((B†) ξ - m)).hasFDerivAt (x := y)).sub
      ((innerSL ℝ ξ).hasFDerivAt.comp y ((hσ.differentiable (by simp)) y).hasFDerivAt)
  have hm0 : ‖m‖ ≠ 0 := norm_ne_zero_iff.2 hm
  rw [h.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left, map_neg, map_smul, inner_neg_right,
    inner_smul_right, real_inner_self_eq_norm_sq, inner_sub_right]
  have hmm : ‖m‖⁻¹ * ‖m‖ ^ 2 = ‖m‖ := by field_simp
  linear_combination hmm

/-- The Fourier transform at `m` of `y ↦ ψ(y) 𝐞(⟪y, Bᵀ ξ⟫ - ⟪σ y, ξ⟫)` is the oscillatory integral
of `ψ` against the phase `y ↦ ⟪Bᵀ ξ - m, y⟫ - ⟪ξ, σ y⟫`. -/
private theorem fourier_mul_fourierChar_eq_integral [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (ψ : V → ℂ) (σ : V → V) (B : V →L[ℝ] V) (ξ m : V) :
    𝓕 (fun y ↦ ψ y * 𝐞 (⟪y, (B†) ξ⟫ - ⟪σ y, ξ⟫)) m =
      ∫ y, ψ y * 𝐞 (innerSL ℝ ((B†) ξ - m) y - innerSL ℝ ξ (σ y)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [Circle.smul_def, smul_eq_mul, innerSL_apply_apply]
  rw [mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_sub_left,
    real_inner_comm ((B†) ξ) y, real_inner_comm m y, real_inner_comm ξ (σ y)]
  congr 3
  ring

/-- **Decay of the Fourier transform of a cutoff with a nonlinear phase.** Let `ψ` be smooth with
compact support and `σ` smooth with `‖Dσ(y) - B‖ ≤ ε` on the support of `ψ`. Then the Fourier
transform at `m` of `y ↦ ψ(y) 𝐞(⟪y, Bᵀ ξ⟫ - ⟪σ y, ξ⟫)` decays faster than every power of `‖m‖`,
uniformly in `ξ`, at the frequencies `m ≠ 0` with `2 ε ‖ξ‖ ≤ ‖m‖`. The phase of the Fourier
integral has derivative at least `‖m‖ / 2` in the direction `-m / ‖m‖`. -/
theorem exists_norm_pow_mul_norm_fourier_mul_fourierChar_le [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {ψ : V → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {σ : V → V} (hσ : ContDiff ℝ ∞ σ) (B : V →L[ℝ] V) {ε : ℝ} (hε : 0 < ε)
    (hσB : ∀ y ∈ tsupport ψ, ‖fderiv ℝ σ y - B‖ ≤ ε) (M : ℕ) :
    ∃ C, ∀ ξ m : V, m ≠ 0 → 2 * ε * ‖ξ‖ ≤ ‖m‖ →
      ‖m‖ ^ M * ‖𝓕 (fun y ↦ ψ y * 𝐞 (⟪y, (B†) ξ⟫ - ⟪σ y, ξ⟫)) m‖ ≤ C := by
  -- The derivatives of `σ` of order at most `M + 1` are bounded on the support of `ψ`.
  obtain ⟨Cσ, hCσ, hσb⟩ := ((hσ.of_le (m := ((M + 1 : ℕ) : WithTop ℕ∞)) (by simp)).contDiffOn
    (s := univ)).exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_univ hψc.isCompact
    (subset_univ _)
  obtain ⟨C, hC⟩ := exists_norm_integral_mul_fourierChar_le (volume : Measure V) hψ hψc M
    (max 3 (Cσ / ε))
  refine ⟨C * 2 ^ M, fun ξ m hm hξm ↦ ?_⟩
  have hm' : 0 < ‖m‖ := norm_pos_iff.2 hm
  set w : V := -(‖m‖⁻¹ • m)
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hm'.ne']
  -- The phase and its derivative in the direction `w`.
  set Φ : V → ℝ := fun y ↦ innerSL ℝ ((B†) ξ - m) y - innerSL ℝ ξ (σ y)
  have hΦ : ContDiff ℝ ∞ Φ :=
    (innerSL ℝ ((B†) ξ - m)).contDiff.sub ((innerSL ℝ ξ).contDiff.comp hσ)
  have hΦd (y : V) : fderiv ℝ Φ y w = ‖m‖ + ⟪ξ, (B - fderiv ℝ σ y) w⟫ :=
    fderiv_phase_apply_neg_smul hσ B ξ hm y
  -- `∂_w Φ` lies in `[‖m‖ / 2, 3 ‖m‖ / 2]` and its derivatives are `O(‖ξ‖) = O(‖m‖)`.
  have hsmall {y : V} (hy : y ∈ tsupport ψ) : |⟪ξ, (B - fderiv ℝ σ y) w⟫| ≤ ‖m‖ / 2 := by
    calc |⟪ξ, (B - fderiv ℝ σ y) w⟫| ≤ ‖ξ‖ * (‖B - fderiv ℝ σ y‖ * ‖w‖) :=
          (abs_real_inner_le_norm _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ‖ξ‖ * ε := by rw [hw, mul_one, norm_sub_rev]; gcongr; exact hσB y hy
      _ ≤ ‖m‖ / 2 := by nlinarith
  have hrange : ∀ y ∈ tsupport ψ, ‖m‖ / 2 ≤ fderiv ℝ Φ y w ∧
      fderiv ℝ Φ y w ≤ max 3 (Cσ / ε) * (‖m‖ / 2) := by
    intro y hy
    have h := abs_le.1 (hsmall hy)
    rw [hΦd]
    exact ⟨by linarith, by nlinarith [le_max_left 3 (Cσ / ε)]⟩
  have hderiv : ∀ y ∈ tsupport ψ, ∀ i, 1 ≤ i → i ≤ M →
      ‖iteratedFDeriv ℝ i (fun z ↦ fderiv ℝ Φ z w) y‖ ≤ max 3 (Cσ / ε) * (‖m‖ / 2) := by
    intro y hy i hi1 hiM
    have heq : (fun z ↦ fderiv ℝ Φ z w) = fun z ↦ (‖m‖ + ⟪ξ, B w⟫) - ⟪ξ, fderiv ℝ σ z w⟫ :=
      funext fun z ↦ by rw [hΦd, sub_apply, inner_sub_right]; ring
    rw [heq]
    calc _ ≤ ‖ξ‖ * (‖iteratedFDeriv ℝ (i + 1) σ y‖ * ‖w‖) :=
          norm_iteratedFDeriv_const_sub_inner_fderiv_le hσ _ ξ w (by omega) y
      _ ≤ ‖ξ‖ * Cσ := by
          rw [hw, mul_one]
          exact mul_le_mul_of_nonneg_left (hσb (i + 1) (by omega) y hy) (norm_nonneg _)
      _ ≤ Cσ / ε * (‖m‖ / 2) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hε]
          nlinarith
      _ ≤ max 3 (Cσ / ε) * (‖m‖ / 2) := by gcongr; exact le_max_right _ _
  have h := hC Φ hΦ w hw.le (‖m‖ / 2) (by positivity) hrange hderiv
  rw [fourier_mul_fourierChar_eq_integral]
  calc ‖m‖ ^ M * ‖∫ y, ψ y * 𝐞 (Φ y)‖ ≤ ‖m‖ ^ M * (C / (‖m‖ / 2) ^ M) := by gcongr
    _ = C * 2 ^ M := by
        rw [div_pow]
        field_simp

end InnerProductSpace

end TauCeti

namespace TauCeti

open Filter Complex Real

section AbsLowerBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace NonstationaryPhase

/-- The reciprocal of the derivative of the phase in the direction `w`, times an amplitude `u`
supported where that derivative does not vanish, is smooth. -/
private theorem contDiff_inv_fderiv_apply_mul {u : E → ℂ} (hu : ContDiff ℝ ∞ u) {Φ : E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {w : E} (ha : ∀ x ∈ tsupport u, fderiv ℝ Φ x w ≠ 0) :
    ContDiff ℝ ∞ fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)⁻¹ * u z := by
  have hac := hΦ.ofReal_fderiv_apply (m := ∞) (by simp) w
  exact (ContinuousLinearMap.mul ℝ ℂ).contDiff_of_tsupport_subset_right
    (hac.contDiffOn.inv fun z hz ↦ hz) hu.contDiffOn
    (isOpen_ne_fun hac.continuous continuous_const) fun x hx ↦ by simpa using ha x hx

/-- The amplitudes produced by integrating `k` times by parts in the direction `w` against the
phase `𝐞 (Φ x)`, starting from `ψ`. -/
private noncomputable def amplitude (Φ : E → ℝ) (w : E) (ψ : E → ℂ) : ℕ → E → ℂ
  | 0 => ψ
  | k + 1 => fun x ↦ fderiv ℝ (fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)⁻¹ * amplitude Φ w ψ k z) x w

private theorem contDiff_amplitude {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) {Φ : E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {w : E} (ha : ∀ x ∈ tsupport ψ, fderiv ℝ Φ x w ≠ 0) (k : ℕ) :
    ContDiff ℝ ∞ (amplitude Φ w ψ k) ∧ tsupport (amplitude Φ w ψ k) ⊆ tsupport ψ := by
  induction k with
  | zero => exact ⟨hψ, subset_rfl⟩
  | succ k ih =>
    have hf := contDiff_inv_fderiv_apply_mul ih.1 hΦ fun x hx ↦ ha x (ih.2 hx)
    refine ⟨(hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, ?_⟩
    refine (tsupport_comp_subset (g := fun L : E →L[ℝ] ℂ ↦ L w) (by simp) _).trans ?_
    exact (tsupport_fderiv_subset ℝ).trans ((tsupport_mul_subset_right).trans ih.2)

variable {ι : Type*} {ψ : E → ℂ} {Φ : ι → E → ℝ} {w : ι → E} {τ : ι → ℝ}

/-- Uniform bounds on the derivatives of the reciprocal of the phase derivative `DΦᵢ(x) wᵢ`: if it
has size at least `τᵢ` on `K` and the derivatives of `Φᵢ` of positive order are `O(τᵢ)` on `K`, then
the derivatives of its reciprocal are `O(τᵢ⁻¹)` on `K`. -/
private theorem exists_norm_iteratedFDeriv_inv_fderiv_apply_le {K : Set E}
    (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i)) (hw : ∀ i, ‖w i‖ ≤ 1) (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ K, τ i ≤ |fderiv ℝ (Φ i) x (w i)|)
    (hhigh : ∀ k : ℕ, ∃ C, ∀ i, ∀ x ∈ K, ‖iteratedFDeriv ℝ (k + 1) (Φ i) x‖ ≤ C * τ i) (n : ℕ) :
    ∃ Q, 0 ≤ Q ∧ ∀ i, ∀ j ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun z ↦ ((fderiv ℝ (Φ i) z (w i) : ℝ) : ℂ)⁻¹) x‖ ≤ Q / τ i := by
  choose C hC using hhigh
  set A := ∑ j ∈ Finset.range (n + 1), |C j|
  obtain ⟨Q, hQ0, hQ⟩ := exists_norm_iteratedFDeriv_inv_le_div (E := E) (𝕜 := ℂ) n A one_pos
  refine ⟨Q, hQ0, fun i j hj x hx ↦ hQ _ (τ i) x (hτ i) ?_ (fun j' hj' ↦ ?_) ?_ j hj⟩
  · exact ((hΦ i).ofReal_fderiv_apply (m := ∞) (by simp) (w i)).of_le (by exact_mod_cast le_top)
  · have hCτ : 0 ≤ C j' * τ i := (norm_nonneg _).trans (hC j' i x hx)
    calc _ ≤ ‖iteratedFDeriv ℝ (j' + 1) (Φ i) x‖ * ‖w i‖ :=
          (hΦ i).norm_iteratedFDeriv_ofReal_fderiv_apply_le (by exact_mod_cast le_top) _ x
      _ ≤ C j' * τ i * 1 := mul_le_mul (hC j' i x hx) (hw i) (norm_nonneg _) hCτ
      _ ≤ |C j'| * τ i := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (hτ i).le
      _ ≤ A * τ i := by
          refine mul_le_mul_of_nonneg_right ?_ (hτ i).le
          exact Finset.single_le_sum (f := fun j ↦ |C j|) (fun _ _ ↦ abs_nonneg _)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hj'))
  · rw [one_mul, norm_real, Real.norm_eq_abs]
    exact hlow i x hx

/-- The phase derivative does not vanish where it is bounded below by a positive `τᵢ`. -/
private theorem fderiv_apply_ne_zero_of_le_abs (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ tsupport ψ, τ i ≤ |fderiv ℝ (Φ i) x (w i)|) (i : ι) :
    ∀ x ∈ tsupport ψ, fderiv ℝ (Φ i) x (w i) ≠ 0 := fun x hx h ↦ by
  have h' := hlow i x hx
  rw [h, abs_zero] at h'
  exact (hτ i).not_ge h'

/-- Uniform bounds on the amplitudes: the derivatives of the `k`-th amplitude are `O(τᵢ⁻ᵏ)`. -/
private theorem exists_norm_iteratedFDeriv_amplitude_le (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ)
    (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i)) (hw : ∀ i, ‖w i‖ ≤ 1) (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ tsupport ψ, τ i ≤ |fderiv ℝ (Φ i) x (w i)|)
    (hhigh : ∀ k : ℕ, ∃ C, ∀ i, ∀ x ∈ tsupport ψ,
      ‖iteratedFDeriv ℝ (k + 1) (Φ i) x‖ ≤ C * τ i) (k n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ j ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ j (amplitude (Φ i) (w i) ψ k) y‖ ≤ C / τ i ^ k := by
  induction k generalizing n with
  | zero =>
    obtain ⟨C, hC0, hC⟩ :=
      hψc.exists_bound_iteratedFDeriv_of_contDiff
        (hψ.of_le (m := (n : WithTop ℕ∞)) (by exact_mod_cast le_top))
    exact ⟨C, hC0, fun i j hj y ↦ by simpa [amplitude] using hC j hj y⟩
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih (n + 1)
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_norm_iteratedFDeriv_inv_fderiv_apply_le hΦ hw hτ hlow hhigh (n + 1)
    refine ⟨2 ^ (n + 1) * Q * C, by positivity, fun i j hj y ↦ ?_⟩
    have ha := fderiv_apply_ne_zero_of_le_abs hτ hlow i
    obtain ⟨hk, hks⟩ := contDiff_amplitude hψ (hΦ i) ha k
    have hac := (hΦ i).ofReal_fderiv_apply (m := ∞) (by simp) (w i)
    have hs : IsOpen {z | ((fderiv ℝ (Φ i) z (w i) : ℝ) : ℂ) ≠ 0} :=
      isOpen_ne_fun hac.continuous continuous_const
    have hm : minSmoothness ℝ (j + 1) ≤ (∞ : WithTop ℕ∞) := by simp
    have hτi := hτ i
    calc ‖iteratedFDeriv ℝ j (amplitude (Φ i) (w i) ψ (k + 1)) y‖
        ≤ ‖iteratedFDeriv ℝ (j + 1) (fun z ↦ ((fderiv ℝ (Φ i) z (w i) : ℝ) : ℂ)⁻¹ *
            amplitude (Φ i) (w i) ψ k z) y‖ * ‖w i‖ :=
          ContDiff.norm_iteratedFDeriv_fderiv_apply_le
            (contDiff_inv_fderiv_apply_mul hk (hΦ i) fun x hx ↦ ha x (hks hx)) hm (w i) y
      _ ≤ 2 ^ (j + 1) * (Q / τ i) * (C / τ i ^ k) * 1 := by
          refine mul_le_mul ?_ (hw i) (norm_nonneg _) (by positivity)
          exact norm_iteratedFDeriv_mul_le_of_tsupport_subset hs (fun x hx ↦ by simpa using ha x hx)
            (hac.contDiffOn.inv fun z hz ↦ hz) hk hks (by exact_mod_cast le_top) (by positivity)
            (fun i' hi' x hx ↦ hQ i i' (by omega) x hx) (fun i' hi' x ↦ hC i i' (by omega) x) y
      _ = 2 ^ (j + 1) * Q * C / τ i ^ (k + 1) := by
          field_simp
          ring
      _ ≤ 2 ^ (n + 1) * Q * C / τ i ^ (k + 1) := by
          gcongr
          exact one_le_two

end NonstationaryPhase

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

namespace NonstationaryPhase

/-- **One integration by parts in a direction `w`.** If the derivative `DΦ(x) w` of the phase does
not vanish on the support of the amplitude `u`, then
`∫ u 𝐞(Φ) = -(2πi)⁻¹ ∫ D((DΦ · w)⁻¹ u) w 𝐞(Φ)`. -/
private theorem integral_mul_fourierChar_eq {u : E → ℂ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : E}
    (ha : ∀ x ∈ tsupport u, fderiv ℝ Φ x w ≠ 0) :
    ∫ x, u x * 𝐞 (Φ x) ∂μ =
      -(2 * π * I)⁻¹ * ∫ x, fderiv ℝ (fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)⁻¹ * u z) x w *
        𝐞 (Φ x) ∂μ := by
  set a : E → ℂ := fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)
  set f : E → ℂ := fun z ↦ (a z)⁻¹ * u z
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hf : ContDiff ℝ ∞ f := contDiff_inv_fderiv_apply_mul hu hΦ ha
  have hfs : tsupport f ⊆ tsupport u :=
    tsupport_mul_subset_right (f := fun z ↦ (a z)⁻¹) (g := u)
  have hfc : HasCompactSupport f := IsCompact.of_isClosed_subset huc (isClosed_tsupport f) hfs
  have hcont : Continuous fun y ↦ (𝐞 (Φ y) : ℂ) := by fun_prop
  -- On the support of `u`, `f * D(𝐞 Φ) w = 2πi u 𝐞(Φ)`.
  have hkey (x : E) : f x * fderiv ℝ (fun y ↦ (𝐞 (Φ y) : ℂ)) x w =
      2 * π * I * (u x * 𝐞 (Φ x)) := by
    rw [fderiv_fourierChar_comp_apply (hΦd x)]
    by_cases hx : x ∈ tsupport u
    · have hax : a x ≠ 0 := by simpa [a] using ha x hx
      simp only [f]
      field_simp
      simp [a, mul_comm]
    · simp [f, image_eq_zero_of_notMem_tsupport hx]
  have hsupp : Function.support (fun x ↦ fderiv ℝ f x w * 𝐞 (Φ x)) ⊆ tsupport f := fun x hx ↦ by
    by_contra h
    simp [fderiv_of_notMem_tsupport ℝ h] at hx
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := f)
    (g := fun y ↦ (𝐞 (Φ y) : ℂ)) (v := w)
    ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hcont)
      |>.integrable_of_hasCompactSupport (hfc.mono' hsupp))
    (by
      simp_rw [hkey]
      exact (continuous_const.mul (hu.continuous.mul hcont)).integrable_of_hasCompactSupport
        huc.mul_right.mul_left)
    (((hf.continuous).mul hcont).integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ ↦ hf.differentiable (by simp) x)
    (fun x _ ↦ (hΦd x).hasFDerivAt.fourierChar.differentiableAt)
  simp_rw [hkey, integral_const_mul] at hibp
  have hc : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero]
  rw [neg_mul, ← mul_neg, ← hibp, inv_mul_cancel_left₀ hc]

/-- Integrating `k` times by parts: `∫ ψ 𝐞(Φ) = (-(2πi)⁻¹)ᵏ ∫ uₖ 𝐞(Φ)` for the `k`-th amplitude
`uₖ`, as long as `DΦ(x) w` does not vanish on the support of `ψ`. -/
private theorem integral_mul_fourierChar_eq_pow_mul_amplitude {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : E}
    (ha : ∀ x ∈ tsupport ψ, fderiv ℝ Φ x w ≠ 0) (k : ℕ) :
    ∫ x, ψ x * 𝐞 (Φ x) ∂μ =
      (-(2 * π * I)⁻¹) ^ k * ∫ x, amplitude Φ w ψ k x * 𝐞 (Φ x) ∂μ := by
  induction k with
  | zero => simp [amplitude]
  | succ k ih =>
    obtain ⟨hk, hks⟩ := contDiff_amplitude hψ hΦ ha k
    rw [ih, integral_mul_fourierChar_eq hk
      (IsCompact.of_isClosed_subset hψc (isClosed_tsupport _) hks) hΦ fun x hx ↦ ha x (hks hx),
      pow_succ, mul_assoc ((-(2 * π * I)⁻¹) ^ k)]
    simp only [amplitude]

end NonstationaryPhase

open NonstationaryPhase in
/-- **Non-stationary phase.** Let `ψ` be a smooth compactly supported amplitude on a
finite-dimensional real normed space, and let `Φᵢ` be a family of smooth real phases, `wᵢ`
directions with `‖wᵢ‖ ≤ 1` and `τᵢ > 0` scales such that on the support of `ψ` the derivative of
`Φᵢ` in the direction `wᵢ` has size at least `τᵢ`, `|DΦᵢ(x) wᵢ| ≥ τᵢ`, while every derivative of
`Φᵢ` of positive order is `O(τᵢ)`, uniformly in `i`. Then the oscillatory integrals decay faster
than every power of `τᵢ`, uniformly in `i`:

`‖∫ ψ(x) 𝐞(Φᵢ(x)) dx‖ ≤ C_N τᵢ^(-N)`.

Only derivatives in the single direction `wᵢ` are integrated by parts, so no lower bound on the
full gradient is needed beyond its component along `wᵢ`. -/
theorem exists_norm_integral_mul_fourierChar_le_of_le_abs {ι : Type*} {ψ : E → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {Φ : ι → E → ℝ}
    (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i)) {w : ι → E} (hw : ∀ i, ‖w i‖ ≤ 1) {τ : ι → ℝ} (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ tsupport ψ, τ i ≤ |fderiv ℝ (Φ i) x (w i)|)
    (hhigh : ∀ k : ℕ, ∃ C, ∀ i, ∀ x ∈ tsupport ψ, ‖iteratedFDeriv ℝ (k + 1) (Φ i) x‖ ≤ C * τ i)
    (N : ℕ) : ∃ C, ∀ i, ‖∫ x, ψ x * 𝐞 (Φ i x) ∂μ‖ ≤ C / τ i ^ N := by
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_amplitude_le hψ hψc hΦ hw hτ hlow hhigh N 0
  refine ⟨(2 * π)⁻¹ ^ N * (C * μ.real (tsupport ψ)), fun i ↦ ?_⟩
  have ha := fderiv_apply_ne_zero_of_le_abs hτ hlow i
  obtain ⟨-, hNs⟩ := contDiff_amplitude hψ (hΦ i) ha N
  -- The `N`-th amplitude is `O(τᵢ⁻ᴺ)` and vanishes off the support of `ψ`.
  have hint : ‖∫ x, amplitude (Φ i) (w i) ψ N x * 𝐞 (Φ i x) ∂μ‖ ≤
      C / τ i ^ N * μ.real (tsupport ψ) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hNs h), zero_mul]]
    refine norm_setIntegral_le_of_norm_le_const hψc.measure_lt_top fun x _ ↦ ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    simpa using hC i 0 le_rfl x
  have h2π : ‖-(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    simp [abs_of_pos pi_pos]
  rw [integral_mul_fourierChar_eq_pow_mul_amplitude hψ hψc (hΦ i) ha N, norm_mul, norm_pow, h2π]
  calc (2 * π)⁻¹ ^ N * ‖∫ x, amplitude (Φ i) (w i) ψ N x * 𝐞 (Φ i x) ∂μ‖
      ≤ (2 * π)⁻¹ ^ N * (C / τ i ^ N * μ.real (tsupport ψ)) := by gcongr
    _ = (2 * π)⁻¹ ^ N * (C * μ.real (tsupport ψ)) / τ i ^ N := by ring

end AbsLowerBound

section ChangeOfVariables

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

namespace NonstationaryPhase

/-- Where `(Df(x))†` is within `c / 2` of `B` and `c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖`, the derivative of
the phase in the direction of `B ζ - ξ` is at least `c / 2 (‖ξ‖ + ‖ζ‖)`. -/
private theorem le_inner_adjoint_sub {A : E →L[ℝ] F} {B : F →L[ℝ] E} {c : ℝ}
    (hAB : ‖A† - B‖ ≤ c / 2) {ξ : E} {ζ : F} (hξζ : c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖) :
    c / 2 * (‖ξ‖ + ‖ζ‖) ≤ ⟪‖B ζ - ξ‖⁻¹ • (B ζ - ξ), (A†) ζ - ξ⟫ := by
  set d := ‖B ζ - ξ‖ with hd_def
  have hsplit : (A†) ζ - ξ = (B ζ - ξ) + (A† - B) ζ := by
    simp only [sub_apply]
    abel
  have h1 : ⟪d⁻¹ • (B ζ - ξ), B ζ - ξ⟫ = d := by
    rcases eq_or_ne d 0 with hd | hd
    · simp [hd, norm_eq_zero.1 hd]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, ← hd_def]
      field_simp
  have h2 : -(c / 2 * ‖ζ‖) ≤ ⟪d⁻¹ • (B ζ - ξ), (A† - B) ζ⟫ := by
    have hw : ‖d⁻¹ • (B ζ - ξ)‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_le_one
    refine neg_le_of_abs_le ((abs_real_inner_le_norm _ _).trans ?_)
    calc ‖d⁻¹ • (B ζ - ξ)‖ * ‖(A† - B) ζ‖ ≤ 1 * (c / 2 * ‖ζ‖) :=
          mul_le_mul hw (((A† - B).le_opNorm ζ).trans (by gcongr)) (norm_nonneg _) zero_le_one
      _ = c / 2 * ‖ζ‖ := one_mul _
  have hc : 0 ≤ c := by linarith [(norm_nonneg _).trans hAB]
  rw [hsplit, inner_add_right, h1]
  nlinarith [mul_nonneg hc (norm_nonneg ξ)]

end NonstationaryPhase

variable [MeasurableSpace E] [BorelSpace E]

namespace NonstationaryPhase

/-- The non-stationary phase estimate for the phases `⟪f x, ζ⟫ - ⟪x, ξ⟫` on the frequencies with
`c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖` and `1 ≤ ‖ξ‖ + ‖ζ‖`, integrating by parts in the direction of
`B ζ - ξ`. -/
private theorem exists_norm_integral_mul_fourierChar_inner_sub_le_div {f : E → F}
    (hf : ContDiff ℝ ∞ f) {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {B : F →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hfB : ∀ x ∈ tsupport ψ, ‖(fderiv ℝ f x)† - B‖ ≤ c / 2) (N : ℕ) :
    ∃ C, ∀ (ξ : E) (ζ : F), c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖ → 1 ≤ ‖ξ‖ + ‖ζ‖ →
      ‖∫ x, ψ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ ≤ C / (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N := by
  set S := {p : E × F // c * (‖p.1‖ + ‖p.2‖) ≤ ‖B p.2 - p.1‖ ∧ 1 ≤ ‖p.1‖ + ‖p.2‖}
  have hsum (p : S) : 0 < ‖p.val.1‖ + ‖p.val.2‖ := one_pos.trans_le p.property.2
  have hf' : Differentiable ℝ f := hf.differentiable (by simp)
  have hM (k : ℕ) : ∃ M, 0 ≤ M ∧ ∀ x ∈ tsupport ψ, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (m := k + 1) (by exact_mod_cast le_top)).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun x hx ↦ (hM x hx).trans (le_max_left _ _)⟩
  choose M hM0 hM using hM
  obtain ⟨C₁, hC₁⟩ :=
    exists_norm_integral_mul_fourierChar_le_of_le_abs (μ := (volume : Measure E)) hψ hψc
    (Φ := fun (p : S) y ↦ ⟪f y, p.val.2⟫ - ⟪y, p.val.1⟫)
    (fun p ↦ (hf.inner ℝ contDiff_const).sub (contDiff_id.inner ℝ contDiff_const))
    (w := fun p ↦ ‖B p.val.2 - p.val.1‖⁻¹ • (B p.val.2 - p.val.1))
    (fun p ↦ by rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_le_one)
    (τ := fun p ↦ c / 2 * (‖p.val.1‖ + ‖p.val.2‖)) (fun p ↦ by have := hsum p; positivity)
    (fun p x hx ↦ by
      rw [fderiv_inner_sub_inner_apply (hf' x)]
      exact (le_inner_adjoint_sub (hfB x hx) p.property.1).trans (le_abs_self _))
    (fun k ↦ ⟨2 / c * (M k + 1), fun p x hx ↦ by
      refine (norm_iteratedFDeriv_succ_inner_sub_inner_le
        (hf.contDiffAt.of_le (by exact_mod_cast le_top)) _ _).trans ?_
      have h := hM k x hx
      have := hM0 k
      rw [show 2 / c * (M k + 1) * (c / 2 * (‖p.val.1‖ + ‖p.val.2‖)) =
        (M k + 1) * (‖p.val.1‖ + ‖p.val.2‖) by field_simp]
      nlinarith [norm_nonneg p.val.1, norm_nonneg p.val.2, norm_nonneg (iteratedFDeriv ℝ
          (k + 1) f x)]⟩)
    N
  exact ⟨C₁, fun ξ ζ hξζ h1 ↦ hC₁ ⟨(ξ, ζ), hξζ, h1⟩⟩

end NonstationaryPhase

open NonstationaryPhase in
/-- **Non-stationary phase for changes of variables in a Fourier integral.** Let `f` be smooth, `ψ`
a smooth compactly supported amplitude, and `B` a linear map within `c / 2` of the transposes
`(Df(x))†` of the derivatives of `f` on the support of `ψ`, for some `c > 0`. Then the oscillatory
integral with phase `⟪f x, ζ⟫ - ⟪x, ξ⟫` decays faster than every power of `‖ξ‖ + ‖ζ‖` on the
frequencies `(ξ, ζ)` with `c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖`, where its gradient `(Df(x))† ζ - ξ` stays
away from zero:

`‖∫ ψ(x) 𝐞(⟪f x, ζ⟫ - ⟪x, ξ⟫) dx‖ ≤ C_N (1 + ‖ξ‖ + ‖ζ‖)^(-N)`. -/
theorem exists_norm_integral_mul_fourierChar_inner_sub_le {f : E → F} (hf : ContDiff ℝ ∞ f)
    {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {B : F →L[ℝ] E} {c : ℝ}
    (hc : 0 < c) (hfB : ∀ x ∈ tsupport ψ, ‖(fderiv ℝ f x)† - B‖ ≤ c / 2) (N : ℕ) :
    ∃ C, ∀ (ξ : E) (ζ : F), c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖ →
      ‖∫ x, ψ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ ≤ C / (1 + ‖ξ‖ + ‖ζ‖) ^ N := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_integral_mul_fourierChar_inner_sub_le_div hf hψ hψc hc hfB N
  refine ⟨max (C₁ * (4 / c) ^ N) ((∫ x, ‖ψ x‖) * 2 ^ N), fun ξ ζ hξζ ↦ ?_⟩
  rw [le_div_iff₀ (by positivity)]
  by_cases h1 : 1 ≤ ‖ξ‖ + ‖ζ‖
  · -- Away from the origin, `1 + ‖ξ‖ + ‖ζ‖ ≤ 2 (‖ξ‖ + ‖ζ‖)`.
    have h := hC₁ ξ ζ hξζ h1
    have hτ : 0 < c / 2 * (‖ξ‖ + ‖ζ‖) := by positivity
    have hle : (1 + ‖ξ‖ + ‖ζ‖) ^ N ≤ (4 / c) ^ N * (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N := by
      rw [← mul_pow]
      gcongr
      have h2 : 4 / c * (c / 2 * (‖ξ‖ + ‖ζ‖)) = 2 * (‖ξ‖ + ‖ζ‖) := by
        field_simp
        ring
      rw [h2]
      linarith
    calc ‖∫ x, ψ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ * (1 + ‖ξ‖ + ‖ζ‖) ^ N
        ≤ C₁ / (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N * ((4 / c) ^ N * (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N) :=
          mul_le_mul h hle (by positivity) ((norm_nonneg _).trans h)
      _ = C₁ * (4 / c) ^ N := by
          rw [mul_left_comm, div_mul_cancel₀ _ (pow_ne_zero N hτ.ne'), mul_comm]
      _ ≤ _ := le_max_left _ _
  · -- Near the origin, `‖∫ ψ 𝐞(…)‖ ≤ ∫ ‖ψ‖` and `1 + ‖ξ‖ + ‖ζ‖ ≤ 2`.
    have htriv : ‖∫ x, ψ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ ≤ ∫ x, ‖ψ x‖ :=
      (norm_integral_le_integral_norm _).trans_eq (by simp)
    calc ‖∫ x, ψ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ * (1 + ‖ξ‖ + ‖ζ‖) ^ N
        ≤ (∫ x, ‖ψ x‖) * 2 ^ N := by
          gcongr
          linarith
      _ ≤ _ := le_max_right _ _

end ChangeOfVariables

end TauCeti
