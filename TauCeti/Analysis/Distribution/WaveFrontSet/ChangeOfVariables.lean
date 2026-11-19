/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Algebra.Module.ZLattice.Dual
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TestFunction.ChangeOfVariables
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Fourier.NonstationaryPhase.Directional
import TauCeti.Analysis.Normed.Module.Cone

/-!
# The wave front set under smooth changes of variables

Let `e` be a smooth change of variables of a finite-dimensional real inner product space `E`: a
smooth open partial homeomorphism with smooth inverse. A complex distribution `T` on an open set
`Ω` pulls back along `e` to the distribution `e^* T` on an open subset `U` of the source of `e`
mapped into `Ω` (`Distribution.compCLMOfOpenPartialHomeomorph`). This file proves that the wave
front set transforms as a subset of the cotangent bundle: covectors pull back by the transpose of
the derivative,

`(x, ξ) ∈ WF(e^* T) ↔ (e x, (De⁻¹(e x))ᵀ ξ) ∈ WF(T)` for `x ∈ U`,

when `e` identifies `U` with `Ω` (`Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`).
Equivalently `WF(e^* T) = {(x, De(x)ᵀ η) | x ∈ U, (e x, η) ∈ WF(T)}`. This is the invariance of
the wave front set under diffeomorphisms (Hörmander I, Theorem 8.2.4), which makes it a
well-defined closed conic subset of the cotangent bundle of a manifold. For linear `e` it is
`Distribution.waveFrontSet_compCLMOfContinuousLinearEquiv`.

## The argument

Let `T` be microlocally smooth at `(y₀, η₀)` with `y₀ = e x₀` and `η₀ = Bᵀ ξ₀`, where
`B = De⁻¹(y₀)`. For a cutoff `φ` supported near `x₀`, the localized Fourier transform of `e^* T`
at `ξ` pairs `T` with `ψ(y) 𝐞(-⟪e⁻¹ y, ξ⟫)`, where `ψ` is the pushforward of `φ`. Factoring out the
linear part of the phase, this is the localized Fourier transform of `T` at `η = Bᵀ ξ` with the
cutoff `G_ξ(y) = ψ(y) 𝐞(⟪y, Bᵀ ξ⟫ - ⟪e⁻¹ y, ξ⟫)`, which depends on `ξ`. Expanding `G_ξ` in a
Fourier series on a box (`Distribution.hasSum_localFourier_ofSupportedIn`) gives

`T (G_ξ e_η) = ∑ m, a_m(ξ) T (χ e_(η - m))`,  `a_m(ξ) = (covolume)⁻¹ 𝓕 G_ξ (m)`.

The terms with `‖m‖ ≤ c ‖η‖` evaluate `T (χ e_ζ)` in the cone around `η₀` where it decays
rapidly, and `|a_m(ξ)|` is bounded. For the others, the phase of `𝓕 G_ξ (m)` has derivative
`‖m‖ + ⟪(B - De⁻¹(y)) w, ξ⟫` in the direction `w = -m / ‖m‖`, which is at least `‖m‖ / 2` once
`De⁻¹` stays close to `B` on the support of `ψ`, so `𝓕 G_ξ (m)` decays faster than every power of
`‖m‖` by non-stationary phase (`TauCeti.exists_norm_integral_mul_fourierChar_le`).

## Main results

* `Distribution.IsMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph`: if `T` is microlocally
  smooth at `(e x, (De⁻¹(e x))ᵀ ξ)`, then `e^* T` is microlocally smooth at `(x, ξ)`.
* `Distribution.isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff`: the converse, when
  `e` identifies `U` with `Ω`.
* `Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`: the wave front set of `e^* T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 and Theorem 7.7.1.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Fourier coefficients of a cutoff with a nonlinear phase -/

omit [FiniteDimensional ℝ E] in
/-- The derivatives of positive order of `z ↦ a - ⟪ξ, Dσ(z) w⟫` are bounded by
`‖ξ‖ ‖D^(i+1) σ‖ ‖w‖`. -/
private theorem norm_iteratedFDeriv_const_sub_inner_fderiv_le {σ : E → E} (hσ : ContDiff ℝ ∞ σ)
    (a : ℝ) (ξ w : E) {i : ℕ} (hi : i ≠ 0) (y : E) :
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

/-- **Decay of the Fourier transform of a cutoff with a nonlinear phase.** Let `ψ` be smooth with
compact support and `σ` smooth with `‖Dσ(y) - B‖ ≤ ε` on the support of `ψ`. Then the Fourier
transform at `m` of `y ↦ ψ(y) 𝐞(⟪y, Bᵀ ξ⟫ - ⟪σ y, ξ⟫)` decays faster than every power of `‖m‖`,
uniformly in `ξ`, at the frequencies `m ≠ 0` with `2 ε ‖ξ‖ ≤ ‖m‖`. The phase of the Fourier
integral has derivative at least `‖m‖ / 2` in the direction `-m / ‖m‖`. -/
private theorem exists_norm_pow_mul_norm_fourier_le [MeasurableSpace E] [BorelSpace E]
    {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {σ : E → E}
    (hσ : ContDiff ℝ ∞ σ) (B : E →L[ℝ] E) {ε : ℝ} (hε : 0 < ε)
    (hσB : ∀ y ∈ tsupport ψ, ‖fderiv ℝ σ y - B‖ ≤ ε) (M : ℕ) :
    ∃ C, ∀ ξ m : E, m ≠ 0 → 2 * ε * ‖ξ‖ ≤ ‖m‖ →
      ‖m‖ ^ M * ‖𝓕 (fun y ↦ ψ y * 𝐞 (⟪y, (B†) ξ⟫ - ⟪σ y, ξ⟫)) m‖ ≤ C := by
  -- The derivatives of `σ` of order at most `M + 1` are bounded on the support of `ψ`.
  obtain ⟨Cσ, hCσ, hσb⟩ := ((hσ.of_le (m := ((M + 1 : ℕ) : WithTop ℕ∞)) (by simp)).contDiffOn
    (s := univ)).exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_univ hψc.isCompact
    (subset_univ _)
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_integral_mul_fourierChar_le (volume : Measure E) hψ hψc M
    (max 3 (Cσ / ε))
  refine ⟨C * 2 ^ M, fun ξ m hm hξm ↦ ?_⟩
  have hm' : 0 < ‖m‖ := norm_pos_iff.2 hm
  set w : E := -(‖m‖⁻¹ • m)
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hm'.ne']
  -- The phase, its derivative in the direction `w`, and the Fourier integral.
  set Φ : E → ℝ := fun y ↦ innerSL ℝ ((B†) ξ - m) y - innerSL ℝ ξ (σ y)
  have hΦ : ContDiff ℝ ∞ Φ :=
    (innerSL ℝ ((B†) ξ - m)).contDiff.sub ((innerSL ℝ ξ).contDiff.comp hσ)
  have hΦd (y : E) : fderiv ℝ Φ y w = ‖m‖ + ⟪ξ, (B - fderiv ℝ σ y) w⟫ := by
    have h : HasFDerivAt Φ (innerSL ℝ ((B†) ξ - m) - (innerSL ℝ ξ).comp (fderiv ℝ σ y)) y :=
      ((innerSL ℝ ((B†) ξ - m)).hasFDerivAt (x := y)).sub
        ((innerSL ℝ ξ).hasFDerivAt.comp y ((hσ.differentiable (by simp)) y).hasFDerivAt)
    have hm0 : ‖m‖ ≠ 0 := hm'.ne'
    rw [h.fderiv]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left, w, map_neg, map_smul, inner_neg_right,
      inner_smul_right, real_inner_self_eq_norm_sq, inner_sub_right]
    have hmm : ‖m‖⁻¹ * ‖m‖ ^ 2 = ‖m‖ := by field_simp
    linear_combination hmm
  have hFourier : 𝓕 (fun y ↦ ψ y * 𝐞 (⟪y, (B†) ξ⟫ - ⟪σ y, ξ⟫)) m = ∫ y, ψ y * 𝐞 (Φ y) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only [Circle.smul_def, smul_eq_mul, Φ, innerSL_apply_apply]
    rw [mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_sub_left,
      real_inner_comm ((B†) ξ) y, real_inner_comm m y, real_inner_comm ξ (σ y)]
    ring_nf
  -- `∂_w Φ` lies in `[‖m‖ / 2, 3 ‖m‖ / 2]` and its derivatives are `O(‖ξ‖) = O(‖m‖)`.
  have hsmall {y : E} (hy : y ∈ tsupport ψ) : |⟪ξ, (B - fderiv ℝ σ y) w⟫| ≤ ‖m‖ / 2 := by
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
    have heq : (fun z ↦ fderiv ℝ Φ z w) = fun z ↦ (‖m‖ + ⟪ξ, B w⟫) - ⟪ξ, fderiv ℝ σ z w⟫ := by
      ext z
      simp only [hΦd, sub_apply, inner_sub_right]
      ring
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
  rw [hFourier]
  calc ‖m‖ ^ M * ‖∫ y, ψ y * 𝐞 (Φ y)‖ ≤ ‖m‖ ^ M * (C / (‖m‖ / 2) ^ M) := by gcongr
    _ = C * 2 ^ M := by
        rw [div_pow]
        field_simp

/-! ### Discrete convolutions with coefficients depending on the frequency -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A term `a F (η - v)` of a discrete convolution with a small shift `‖v‖ ≤ c ‖η‖`, `c ≤ 1 / 2`:
the shifted frequency stays in a set `Γ` on which `(1 + ‖ζ‖) ^ (N + q) ‖F ζ‖ ≤ C₁`. -/
private theorem norm_mul_mul_le_of_norm_le {F : E → ℂ} {Γ : Set E} {N q : ℕ} {C₁ : ℝ}
    (hdecay : ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ (N + q) * ‖F ζ‖ ≤ C₁) {c : ℝ} (hc1 : c ≤ 1 / 2) {η v : E}
    (hη : closedBall η (c * ‖η‖) ⊆ Γ) (hv : ‖v‖ ≤ c * ‖η‖) {a : ℂ} {A₀ : ℝ} (ha : ‖a‖ ≤ A₀) :
    ‖a‖ * ‖F (η - v)‖ * (1 + ‖η‖) ^ N ≤ A₀ * (2 ^ (N + q) * C₁) / (1 + ‖v‖) ^ q := by
  have hmem : η - v ∈ Γ := hη (by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hv)
  have hη2 : 1 + ‖η‖ ≤ 2 * (1 + ‖η - v‖) := by
    have := norm_sub_norm_le η v
    nlinarith [norm_nonneg η]
  have hvη : 1 + ‖v‖ ≤ 1 + ‖η‖ := by nlinarith [norm_nonneg η]
  have hF : (1 + ‖η‖) ^ (N + q) * ‖F (η - v)‖ ≤ 2 ^ (N + q) * C₁ :=
    calc (1 + ‖η‖) ^ (N + q) * ‖F (η - v)‖ ≤ (2 * (1 + ‖η - v‖)) ^ (N + q) * ‖F (η - v)‖ := by
          gcongr
      _ = 2 ^ (N + q) * ((1 + ‖η - v‖) ^ (N + q) * ‖F (η - v)‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ (N + q) * C₁ := by gcongr; exact hdecay _ hmem
  rw [le_div_iff₀ (by positivity)]
  calc ‖a‖ * ‖F (η - v)‖ * (1 + ‖η‖) ^ N * (1 + ‖v‖) ^ q
      ≤ ‖a‖ * ‖F (η - v)‖ * (1 + ‖η‖) ^ N * (1 + ‖η‖) ^ q := by gcongr
    _ ≤ A₀ * ‖F (η - v)‖ * (1 + ‖η‖) ^ N * (1 + ‖η‖) ^ q := by gcongr
    _ = A₀ * ((1 + ‖η‖) ^ (N + q) * ‖F (η - v)‖) := by rw [pow_add]; ring
    _ ≤ A₀ * (2 ^ (N + q) * C₁) := by gcongr; exact (norm_nonneg a).trans ha

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A term `a F (η - v)` of a discrete convolution with a large shift `‖v‖ > c ‖η‖`, `c ≤ 1 / 2`,
for `F` of polynomial growth `(1 + ‖ζ‖) ^ k` and a coefficient with
`‖v‖ ^ (N + 2 k + q) ‖a‖ ≤ A₁`. -/
private theorem norm_mul_mul_le_of_lt_norm {F : E → ℂ} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {N q : ℕ} {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    {η v : E} (hv : c * ‖η‖ < ‖v‖) {a : ℂ} {A₀ A₁ : ℝ} (ha₀ : ‖a‖ ≤ A₀)
    (ha₁ : ‖v‖ ^ (N + 2 * k + q) * ‖a‖ ≤ A₁) :
    ‖a‖ * ‖F (η - v)‖ * (1 + ‖η‖) ^ N ≤
      C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁)) * ((1 + ‖v‖) ^ q)⁻¹ := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  have hle : 1 + ‖η‖ ≤ c⁻¹ * (1 + ‖v‖) := by
    rw [le_inv_mul_iff₀ hc]
    nlinarith [norm_nonneg η]
  have hFle : ‖F (η - v)‖ ≤ C₀ * ((1 + ‖η‖) ^ k * (1 + ‖v‖) ^ k) := by
    refine (hF _).trans ?_
    rw [← mul_pow]
    gcongr
    nlinarith [norm_sub_le η v, norm_nonneg η, norm_nonneg v]
  -- `(1 + ‖v‖) ^ (N + 2 k + q) ‖a‖ ≤ 2 ^ (N + 2 k + q) (A₀ + A₁)`.
  have hav : (1 + ‖v‖) ^ (N + 2 * k + q) * ‖a‖ ≤ 2 ^ (N + 2 * k + q) * (A₀ + A₁) :=
    calc (1 + ‖v‖) ^ (N + 2 * k + q) * ‖a‖
        ≤ 2 ^ (N + 2 * k + q - 1) * (1 ^ (N + 2 * k + q) + ‖v‖ ^ (N + 2 * k + q)) * ‖a‖ := by
          gcongr; exact add_pow_le zero_le_one (norm_nonneg _) _
      _ = 2 ^ (N + 2 * k + q - 1) * (‖a‖ + ‖v‖ ^ (N + 2 * k + q) * ‖a‖) := by ring
      _ ≤ 2 ^ (N + 2 * k + q) * (A₀ + A₁) := mul_le_mul
          (pow_le_pow_right₀ one_le_two (by omega)) (add_le_add ha₀ ha₁) (by positivity)
          (by positivity)
  calc ‖a‖ * ‖F (η - v)‖ * (1 + ‖η‖) ^ N
      ≤ ‖a‖ * (C₀ * ((1 + ‖η‖) ^ k * (1 + ‖v‖) ^ k)) * (1 + ‖η‖) ^ N := by gcongr
    _ = C₀ * ((1 + ‖η‖) ^ (N + k) * ((1 + ‖v‖) ^ k * ‖a‖)) := by ring
    _ ≤ C₀ * ((c⁻¹ * (1 + ‖v‖)) ^ (N + k) * ((1 + ‖v‖) ^ k * ‖a‖)) := by gcongr
    _ = C₀ * c⁻¹ ^ (N + k) * ((1 + ‖v‖) ^ (N + 2 * k + q) * ‖a‖) * ((1 + ‖v‖) ^ q)⁻¹ := by
        rw [mul_pow]
        field_simp
        ring
    _ ≤ C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁)) * ((1 + ‖v‖) ^ q)⁻¹ := by
        gcongr

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Decay of a discrete convolution, region by region.** Let `F` grow at most like
`(1 + ‖ζ‖) ^ k` and satisfy `(1 + ‖ζ‖) ^ (N + q) ‖F ζ‖ ≤ C₁` on a set `Γ` containing the closed
ball of radius `c ‖η‖` about `η`, with `0 < c ≤ 1 / 2`. If the coefficients `a i` are bounded by
`A₀`, and those with `‖v i‖ > c ‖η‖` satisfy `‖v i‖ ^ (N + 2 k + q) ‖a i‖ ≤ A₁`, then the sum
`s = ∑ i, a i F (η - v i)` has `(1 + ‖η‖) ^ N ‖s‖` bounded by a constant depending only on these
data, times `∑ i, (1 + ‖v i‖) ^ (-q)`. -/
private theorem one_add_norm_pow_mul_norm_le_of_hasSum {ι : Type*} (v : ι → E) {q : ℕ}
    (hv : Summable fun i ↦ ((1 + ‖v i‖) ^ q)⁻¹) {F : E → ℂ} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ : Set E} {N : ℕ} {C₁ : ℝ}
    (hdecay : ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ (N + q) * ‖F ζ‖ ≤ C₁) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    {η : E} (hη : closedBall η (c * ‖η‖) ⊆ Γ) {a : ι → ℂ} {A₀ A₁ : ℝ} (hA₀ : 0 ≤ A₀)
    (hA₁ : 0 ≤ A₁) (ha₀ : ∀ i, ‖a i‖ ≤ A₀)
    (ha₁ : ∀ i, c * ‖η‖ < ‖v i‖ → ‖v i‖ ^ (N + 2 * k + q) * ‖a i‖ ≤ A₁) {s : ℂ}
    (hs : HasSum (fun i ↦ a i * F (η - v i)) s) :
    (1 + ‖η‖) ^ N * ‖s‖ ≤ (A₀ * 2 ^ (N + q) * C₁ +
      C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁))) * ∑' i, ((1 + ‖v i‖) ^ q)⁻¹ := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  have hC₁ : 0 ≤ C₁ := (by positivity : 0 ≤ (1 + ‖η‖) ^ (N + q) * ‖F η‖).trans
    (hdecay η (hη (mem_closedBall_self (by positivity))))
  have hp : 0 < (1 + ‖η‖) ^ N := by positivity
  -- Each term is bounded by the constant times `(1 + ‖v i‖) ^ (-q) / (1 + ‖η‖) ^ N`.
  have hterm (i : ι) : ‖a i * F (η - v i)‖ ≤ (A₀ * 2 ^ (N + q) * C₁ +
      C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁))) * ((1 + ‖v i‖) ^ q)⁻¹ /
        (1 + ‖η‖) ^ N := by
    rw [le_div_iff₀ hp, norm_mul, add_mul]
    by_cases hvi : ‖v i‖ ≤ c * ‖η‖
    · refine (norm_mul_mul_le_of_norm_le hdecay hc1 hη hvi (ha₀ i)).trans ?_
      have h2 : 0 ≤ C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁)) *
          ((1 + ‖v i‖) ^ q)⁻¹ := by positivity
      rw [div_eq_mul_inv]
      linarith [show A₀ * (2 ^ (N + q) * C₁) * ((1 + ‖v i‖) ^ q)⁻¹ =
        A₀ * 2 ^ (N + q) * C₁ * ((1 + ‖v i‖) ^ q)⁻¹ by ring]
    · push Not at hvi
      exact (norm_mul_mul_le_of_lt_norm hF hc hc1 hvi (ha₀ i) (ha₁ i hvi)).trans
        (le_add_of_nonneg_left (by positivity))
  have hbound := hs.norm_le_of_bounded ((hv.hasSum.mul_left _).div_const _) hterm
  rw [le_div_iff₀ hp] at hbound
  linarith

/-! ### The wave front set of a pullback -/

variable {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- On the source of `e`, the transposes of `De(x)` and `De⁻¹(e x)` are inverse:
`De(x)ᵀ (De⁻¹(e x)ᵀ ξ) = ξ`. -/
private theorem adjoint_fderiv_apply_adjoint_fderiv_symm_apply
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : E} (hx : x ∈ e.source) (ξ : E) :
    ((fderiv ℝ e x)†) (((fderiv ℝ e.symm (e x))†) ξ) = ξ := by
  have hd : DifferentiableAt ℝ e x :=
    (he.differentiableOn (by simp)).differentiableAt (e.open_source.mem_nhds hx)
  have hds : DifferentiableAt ℝ e.symm (e x) :=
    (he'.differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds (e.map_source hx))
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    e.fderiv_symm_comp_fderiv_of_mem_source hx hd hds, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply]

/-- The localized Fourier transform of the pullback `e^* T` with cutoff `φ` at `ζ` is that of `T`
at `Bᵀ ζ` with the cutoff `G = (e_* φ) 𝐞(⟪·, Bᵀ ζ⟫ - ⟪σ ·, ζ⟫)`, for any `σ` agreeing with `e⁻¹` on
the support of the pushforward `e_* φ`. -/
private theorem localFourier_compCLMOfOpenPartialHomeomorph_eq (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(U, ℂ))
    {σ : E → E} (hσ : ∀ y ∈ e.target, φ (e.symm y) ≠ 0 → σ y = e.symm y) {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) (G : 𝓓_{K}(E, ℂ)) (B : E →L[ℝ] E) (ζ : E)
    (hG : ∀ y, G y = pushforwardCLM e he he' hU hUΩ φ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).localFourier φ ζ =
      T.localFourier (ofSupportedIn hKΩ G) ((B†) ζ) := by
  rw [localFourier_def, complexPairing_compCLMOfOpenPartialHomeomorph]
  refine (localFourier_eq _ _ fun y ↦ ?_).symm
  by_cases hy : y ∈ e.target
  · rw [pushforwardCLM_apply_of_mem _ hy]
    by_cases hφy : φ (e.symm y) = 0
    · simp [bilinLeftCLM_apply, hG, pushforwardCLM_apply_of_mem _ hy, hφy]
    · simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', coe_ofSupportedIn, hG,
        pushforwardCLM_apply_of_mem _ hy, hσ y hy hφy, TauCeti.fourierAtom_eq_fourierChar,
        real_smul, real_inner_comm ζ]
      rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      ring_nf
  · simp [pushforwardCLM_apply_of_notMem _ hy, hG]

omit [FiniteDimensional ℝ E] in
/-- **Decay of the localized Fourier transforms with phase-modulated cutoffs.** Let `T` have
localized Fourier transforms decaying rapidly on a cone `Γ` for all cutoffs supported in `W`, and
let `Γ'` have conic neighbourhoods of relative size `c ≤ 1 / 2` inside `Γ`. Let `ψ` be supported
in a set `K₁` on which a smooth function `χ` supported in a box `K ⊆ W ∩ Ω` equals one, the box
meeting none of its nonzero translates by a lattice `L`. If `‖ζ‖ ≤ a ‖Bᵀ ζ‖` and `Dσ` stays within
`c / (2 a)` of `B` on the support of `ψ`, then `T` with the cutoffs
`G ζ = ψ 𝐞(⟪·, Bᵀ ζ⟫ - ⟪σ ·, ζ⟫)` has localized Fourier transform at `Bᵀ ζ` decaying rapidly in
`Bᵀ ζ ∈ Γ'`. The Fourier series of `G ζ` on the box is split into the frequencies `m` small
compared with `Bᵀ ζ`, which stay in `Γ`, and the large ones, where `𝓕 (G ζ)` decays by
non-stationary phase. -/
private theorem exists_one_add_norm_pow_mul_norm_localFourier_le [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] {T : 𝓓'(Ω, ℂ)} {W Γ Γ' : Set E}
    (hdecay : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ W →
      ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) (hKW : (K : Set E) ⊆ W) {K₁ : Set E}
    {χ : 𝓓_{K}(E, ℂ)} (hχ : ∀ y ∈ K₁, χ y = 1) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hL : ∀ y ∈ K, ∀ ℓ : L, y + ℓ ∈ K → ℓ = 0) {ψ : 𝓓(Ω, ℂ)}
    (hψK₁ : tsupport ψ ⊆ K₁) {σ : E → E} (hσ : ContDiff ℝ ∞ σ) (B : E →L[ℝ] E) {a : ℝ}
    (ha : 0 < a) (hB : ∀ ζ, ‖ζ‖ ≤ a * ‖(B†) ζ‖)
    (hσB : ∀ y ∈ tsupport (ψ : E → ℂ), ‖fderiv ℝ σ y - B‖ ≤ c / (2 * a))
    (G : E → 𝓓_{K}(E, ℂ)) (hG : ∀ ζ y, G ζ y = ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫)) (N : ℕ) :
    ∃ C, ∀ ζ, (B†) ζ ∈ Γ' →
      (1 + ‖(B†) ζ‖) ^ N * ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖ ≤ C := by
  -- The Fourier series of `G ζ` in the modulations of `χ`, and the growth and decay of the
  -- localized Fourier transform `F` of `T` with cutoff `χ`.
  have hχG (ζ : E) : EqOn χ 1 (support (G ζ)) := fun y hy ↦ by
    refine hχ y (hψK₁ (subset_tsupport _ fun h0 ↦ hy ?_))
    rw [hG, h0, zero_mul]
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T (ofSupportedIn hKΩ χ)
  set q := Module.finrank ℝ E + 1
  have hq : Summable fun m : ZLattice.dual L ↦ ((1 + ‖(m : E)‖) ^ q)⁻¹ :=
    ZLattice.summable_one_add_norm_pow_inv _ (by rw [ZLattice.rank ℝ]; omega)
  obtain ⟨C₁, hC₁⟩ := hdecay (ofSupportedIn hKΩ χ)
    (fun y hy ↦ hKW (χ.tsupport_subset (by simpa using hy))) (N + q)
  -- The Fourier coefficients of `G ζ` are bounded, and decay at large frequencies.
  set κ := ‖((ZLattice.covolume L : ℂ))⁻¹‖
  set A₀ := κ * ∫ y, ‖ψ y‖
  have ha₀ (ζ m : E) : ‖(ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (G ζ : E → ℂ) m‖ ≤ A₀ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((Real.norm_fourier_le_integral_norm _ _).trans_eq
      (integral_congr_ae (ae_of_all _ fun y ↦ ?_))) (norm_nonneg _)
    simp [hG]
  obtain ⟨C₂, hC₂⟩ := exists_norm_pow_mul_norm_fourier_le ψ.contDiff ψ.hasCompactSupport hσ B
    (by positivity) hσB (N + 2 * k + q)
  refine ⟨_, fun ζ hζ ↦ one_add_norm_pow_mul_norm_le_of_hasSum (fun m : ZLattice.dual L ↦ (m : E))
    hq hF hC₁ hc hc1 (hΓ' _ hζ) (A₀ := A₀) (A₁ := κ * max C₂ 0) (by positivity) (by positivity)
    (fun m ↦ ha₀ ζ m) (fun m hm ↦ ?_)
    (by simpa only [smul_eq_mul] using hasSum_localFourier_ofSupportedIn T hKΩ L hL (hχG ζ) _)⟩
  -- Frequencies `m` with `‖m‖ > c ‖Bᵀ ζ‖ ≥ (c / a) ‖ζ‖` are non-stationary.
  have hm0 : (m : E) ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at hm; exact (lt_irrefl _ (hm.trans_le' (by positivity)))
  have hεm : 2 * (c / (2 * a)) * ‖ζ‖ ≤ ‖(m : E)‖ := by
    have : 2 * (c / (2 * a)) * ‖ζ‖ ≤ c * ‖(B†) ζ‖ := by
      rw [show 2 * (c / (2 * a)) = c / a by field_simp, div_mul_eq_mul_div,
        div_le_iff₀ ha]
      nlinarith [hB ζ]
    linarith
  have hGf : (G ζ : E → ℂ) = fun y ↦ ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫) := funext (hG ζ)
  rw [norm_mul, mul_left_comm, hGf]
  exact mul_le_mul_of_nonneg_left ((hC₂ ζ m hm0 hεm).trans (le_max_left _ _)) (norm_nonneg _)

/-- **The wave front set of a pullback along a change of variables.** If `T` is microlocally
smooth at `(e x, (De⁻¹(e x))ᵀ ξ)`, then its pullback `e^* T` is microlocally smooth at `(x, ξ)`
(Hörmander I, Theorem 8.2.4). -/
theorem IsMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hx : x ∈ U) (h : T.IsMicrolocallySmoothAt (e x) (((fderiv ℝ e.symm (e x))†) ξ)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySmoothAt x ξ := by
  borelize E
  set B : E →L[ℝ] E := fderiv ℝ e.symm (e x)
  set a := ‖fderiv ℝ e x‖ + 1
  have hxs : x ∈ e.source := hU hx
  have hy₀ : e x ∈ e.target := e.map_source hxs
  -- Frequencies are comparable through the transposes: `‖ζ‖ ≤ (‖De(x)‖ + 1) ‖Bᵀ ζ‖`.
  have hB (ζ : E) : ‖ζ‖ ≤ a * ‖(B†) ζ‖ :=
    calc ‖ζ‖ = ‖((fderiv ℝ e x)†) ((B†) ζ)‖ := by
          rw [adjoint_fderiv_apply_adjoint_fderiv_symm_apply he he' hxs]
      _ ≤ ‖(fderiv ℝ e x)†‖ * ‖(B†) ζ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ a * ‖(B†) ζ‖ := by rw [LinearIsometryEquiv.norm_map]; gcongr; linarith
  -- The decay of `T` near `(e x, Bᵀ ξ)`, uniform over the cutoffs supported in `W`, on the cone
  -- `Γ`; the smaller cone `Γ'` has conic neighbourhoods of relative size `c'` inside `Γ`.
  obtain ⟨W, hW, Γ, hΓo, hΓξ, hΓc, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨Γ', hΓ'o, hΓ'ξ, hΓ'c, c, hc, hΓ'⟩ := hΓo.exists_cone_closedBall_subset hΓc hΓξ
  set c' := min c (1 / 2)
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hΓ'' : ∀ η ∈ Γ', closedBall η (c' * ‖η‖) ⊆ Γ := fun η hη ↦
    (closedBall_subset_closedBall (by gcongr; exact min_le_left _ _)).trans (hΓ' η hη)
  -- A box `K ⊆ W ∩ Ω` around `e x`, a lattice, and a cutoff `χ` equal to one on `K₁ ∋ e x`.
  obtain ⟨K, K₁, hKW, hK₁, hK₁K, ⟨χ, hχ⟩, L, _, _, hL⟩ :=
    exists_compacts_cutoff_lattice (hUΩ hx) hW
  have hKΩ : (K : Set E) ⊆ Ω := hKW.trans inter_subset_right
  -- A smooth `σ` equal to `e⁻¹` near `e x`; near `e x`, `Dσ` stays within `c' / (2 a)` of `B`.
  obtain ⟨σ, hσ, -, hσe⟩ :=
    he'.exists_contDiff_eventuallyEq_of_finiteDimensional (e.open_target.mem_nhds hy₀)
  have hε : 0 < c' / (2 * a) := by positivity
  set S : Set E := K₁ ∩ {y | σ y = e.symm y} ∩ {y | ‖fderiv ℝ σ y - B‖ < c' / (2 * a)}
  have hS : S ∈ 𝓝 (e x) := by
    have hσc := ((hσ.continuous_fderiv (by simp)).continuousAt (x := e x)).eventually
      (Metric.ball_mem_nhds _ hε)
    rw [hσe.fderiv_eq] at hσc
    exact inter_mem (inter_mem hK₁ hσe) (hσc.mono fun y hy ↦ by simpa [dist_eq_norm] using hy)
  -- A cutoff `φ` at `x` whose pushforward `ψ` is supported in `S`.
  obtain ⟨φ, hφs, hφx⟩ := exists_tsupport_subset_apply_eq (Ω := U)
    (inter_mem (U.isOpen.mem_nhds hx) ((e.continuousAt hxs).preimage_mem_nhds hS))
    inter_subset_left (1 : ℂ)
  set ψ : 𝓓(Ω, ℂ) := pushforwardCLM e he he' hU hUΩ φ
  have hψS : tsupport ψ ⊆ S :=
    (tsupport_pushforwardCLM_subset φ).trans (image_subset_iff.2 (hφs.trans inter_subset_right))
  -- The cutoffs `G ζ = ψ 𝐞(⟪·, Bᵀ ζ⟫ - ⟪σ ·, ζ⟫)`, supported in `K`.
  have hGc (ζ : E) : ContDiff ℝ ∞ fun y ↦ ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫) := by
    refine ψ.contDiff.mul ?_
    simp_rw [Real.fourierChar_apply]
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
      ((contDiff_id.inner ℝ contDiff_const).sub (hσ.inner ℝ contDiff_const)))).mul
        contDiff_const)
  have hGs (ζ : E) : support (fun y ↦ ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫)) ⊆ K := fun y hy ↦
    hK₁K (hψS (subset_tsupport _ (left_ne_zero_of_mul hy))).1.1
  let G (ζ : E) : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset (hGc ζ) (hGs ζ)
  have hG (ζ y : E) : G ζ y = ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫) :=
    ContDiffMapSupportedIn.coe_of_support_subset _ _ y
  -- On the support of `φ ∘ e⁻¹`, `σ = e⁻¹`.
  have hσφ : ∀ y ∈ e.target, φ (e.symm y) ≠ 0 → σ y = e.symm y := fun y hy hφy ↦ by
    simpa [e.right_inv hy] using ((hφs (subset_tsupport _ hφy)).2).1.2
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], (B†) ⁻¹' Γ',
    hΓ'o.preimage (B†).continuous, hΓ'ξ,
    fun t ht ζ hζ ↦ by simpa [map_smul] using hΓ'c t ht _ hζ, fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_localFourier_le hdecay hc'
    (min_le_right _ _) hΓ'' hKΩ (fun y hy ↦ (hKW hy).1) hχ L hL (fun y hy ↦ (hψS hy).1.1) hσ B
    (by positivity) hB (fun y hy ↦ (hψS hy).2.le) G hG N
  refine ⟨a ^ N * C, fun ζ hζ ↦ ?_⟩
  rw [localFourier_compCLMOfOpenPartialHomeomorph_eq T φ hσφ hKΩ (G ζ) B ζ (hG ζ)]
  calc (1 + ‖ζ‖) ^ N * ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖
      ≤ (a * (1 + ‖(B†) ζ‖)) ^ N * ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖ := by
        gcongr
        nlinarith [hB ζ, norm_nonneg ((B†) ζ), norm_nonneg (fderiv ℝ e x)]
    _ = a ^ N * ((1 + ‖(B†) ζ‖) ^ N *
          ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖) := by rw [mul_pow]; ring
    _ ≤ a ^ N * C := mul_le_mul_of_nonneg_left (hC ζ hζ) (by positivity)

/-- **The wave front set under a change of variables, pointwise.** When `e` identifies `U` with
`Ω`, the pullback `e^* T` is microlocally smooth at `(x, ξ)` exactly when `T` is microlocally
smooth at `(e x, (De⁻¹(e x))ᵀ ξ)`. -/
theorem isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hx : x ∈ U) (hΩ : (Ω : Set E) ⊆ e.target) (hΩU : MapsTo e.symm Ω U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySmoothAt x ξ ↔
      T.IsMicrolocallySmoothAt (e x) (((fderiv ℝ e.symm (e x))†) ξ) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compCLMOfOpenPartialHomeomorph hx⟩
  -- Pull `e^* T` back along `e⁻¹`, which gives back `T`.
  have hxs : x ∈ e.source := hU hx
  have h' : (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySmoothAt
      (e.symm (e x)) (((fderiv ℝ e.symm.symm (e.symm (e x)))†)
        (((fderiv ℝ e.symm (e x))†) ξ)) := by
    simpa only [OpenPartialHomeomorph.symm_symm, e.left_inv hxs,
      adjoint_fderiv_apply_adjoint_fderiv_symm_apply he he' hxs] using h
  have h₂ := h'.compCLMOfOpenPartialHomeomorph (e := e.symm) (he := he') (he' := he)
    (hU := hΩ) (hUΩ := hΩU) (hUΩ hx)
  convert h₂ using 1
  exact (compCLMOfOpenPartialHomeomorph_symm_apply_apply T).symm

/-- **The wave front set under a change of variables** (Hörmander I, Theorem 8.2.4). When `e`
identifies `U` with `Ω`, the wave front set of the pullback `e^* T` consists of the `(x, ξ)` with
`x ∈ U` and `(e x, (De⁻¹(e x))ᵀ ξ) ∈ WF(T)`: covectors pull back by the transpose of the
derivative. -/
theorem waveFrontSet_compCLMOfOpenPartialHomeomorph (T : 𝓓'(Ω, ℂ))
    (hΩ : (Ω : Set E) ⊆ e.target) (hΩU : MapsTo e.symm Ω U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).waveFrontSet =
      {p : E × E | p.1 ∈ U ∧ (e p.1, ((fderiv ℝ e.symm (e p.1))†) p.2) ∈ T.waveFrontSet} := by
  ext ⟨x, ξ⟩
  simp only [mem_ofPred_eq, mem_waveFrontSet_iff]
  constructor
  · rintro ⟨hx, hξ, h⟩
    refine ⟨hx, hUΩ hx, fun h0 ↦ hξ ?_, fun h' ↦ h ?_⟩
    · rw [← adjoint_fderiv_apply_adjoint_fderiv_symm_apply he he' (hU hx) ξ, h0, map_zero]
    · exact (isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff hx hΩ hΩU).2 h'
  · rintro ⟨hx, -, hξ, h⟩
    exact ⟨hx, fun h0 ↦ hξ (by rw [h0, map_zero]), fun h' ↦
      h ((isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff hx hΩ hΩU).1 h')⟩

end Distribution
