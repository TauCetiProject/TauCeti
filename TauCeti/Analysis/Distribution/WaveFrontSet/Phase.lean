/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Fourier.NonstationaryPhase.Parametric
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Decay of a distribution against a nonlinear phase

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`. By definition, `T` is microlocally smooth at `(x₀, ξ₀)` when the pairings of `T` with
the cutoff linear phases `ψ(x) 𝐞(-⟪x, t ξ⟫)` decay rapidly as `t → ∞`, for `ξ` near `ξ₀` and
`ψ` supported near `x₀`. This file proves the same decay for nonlinear phases: if `Φ` is a smooth
real phase whose gradient at `x₀` is `ξ₀ ≠ 0`, then

`T (ψ 𝐞(-t Φ)) = O(t ^ (-N))` as `t → ∞`, for every `N`,

for all `ψ` supported near `x₀`
(`Distribution.IsMicrolocallySmoothAt.exists_nhds_forall_pow_mul_norm_complexPairing_le`). The
phase may depend smoothly on a parameter `p`, and the estimate is uniform for `p` near a given
`p₀`. This is the estimate behind the behaviour of wave front sets under smooth changes of
coordinates and under pullback and pushforward along smooth maps, where the localized Fourier
transform of the transformed distribution pairs `T` with the phase `x ↦ ⟪κ x, ξ⟫` for a smooth
map `κ`.

The proof expands the test function `g = ψ 𝐞(-t Φ)` in a Fourier series on a compact set `K`
around the support of `ψ`, as in the proof that microlocal smoothness does not depend on the
cutoff:

`T g = ∑ m, (covolume L)⁻¹ 𝓕 g (m) T (χ e_(-m))`,

summed over the dual of a lattice `L` none of whose nonzero translates of `K` meet `K`, with a
cutoff `χ` equal to one on the support of `g` (`Distribution.hasSum_fourier_mul_localFourier`).
The Fourier coefficient
`𝓕 g (m) = ∫ ψ(x) 𝐞(-(t Φ(x) + ⟪x, m⟫)) dx` is an oscillatory integral whose phase has
gradient `-(t ∇Φ(x) + m)`. When `‖t ∇Φ(x) + m‖ ≥ δ (t + ‖m‖)` on the support of `ψ`, it is
`O((t + ‖m‖) ^ (-N))` by non-stationary phase
(`TauCeti.exists_forall_abs_pow_mul_norm_integral_mul_fourierChar_le`), which beats the polynomial
growth of `T (χ e_(-m))`. Otherwise `-m` lies within `δ (t + ‖m‖)` of `t ∇Φ(x)` for some `x` near
`x₀`; for small `δ` this puts `-m` in a cone around `ξ₀` where `T (χ e_(-m))` decays rapidly, and
`‖m‖` is comparable to `t`.

## Main results

* `Distribution.IsMicrolocallySmoothAt.exists_nhds_forall_pow_mul_norm_complexPairing_le`: rapid
  decay of `T (ψ 𝐞(-t Φ(p, ·)))` in `t`, uniformly for `p` near `p₀`, when `T` is microlocally
  smooth at `(x₀, ∇Φ(p₀, ·)(x₀))`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1 (non-stationary phase) and the proof of Theorem 8.2.4 (the wave
  front set of a pullback).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

omit [FiniteDimensional ℝ E] in
/-- **The stationary region.** If `ξ` is within `‖ξ₀‖ / 2` of `ξ₀` and `-m` is within
`δ (t + ‖m‖)` of `t ξ` for a small enough `δ`, then `-m` is within `c ‖t ξ‖` of `t ξ`, and `‖m‖`
is comparable to `t`. -/
private theorem neg_mem_closedBall_and_le_of_norm_add_lt {ξ₀ ξ m : E} {t c δ : ℝ} (ht : 0 < t)
    (hξ : ‖ξ - ξ₀‖ ≤ ‖ξ₀‖ / 2) (hδ₁ : δ ≤ 1 / 2) (hδ₂ : 8 * δ * (1 + 2 * ‖ξ₀‖) ≤ min c 1 * ‖ξ₀‖)
    (h : ‖t • ξ + m‖ < δ * (t + ‖m‖)) :
    -m ∈ closedBall (t • ξ) (c * ‖t • ξ‖) ∧ t * ‖ξ₀‖ ≤ 4 * ‖m‖ := by
  have hξu : ‖ξ‖ ≤ 2 * ‖ξ₀‖ := by
    linarith [norm_le_norm_add_norm_sub' ξ ξ₀, norm_nonneg ξ₀]
  have hξl : ‖ξ₀‖ ≤ 2 * ‖ξ‖ := by
    linarith [norm_le_norm_add_norm_sub' ξ₀ ξ, norm_sub_rev ξ₀ ξ]
  have htξ : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hm : ‖m‖ ≤ ‖t • ξ + m‖ + t * ‖ξ‖ := by
    have := norm_sub_le (t • ξ + m) (t • ξ)
    rwa [add_sub_cancel_left, htξ] at this
  have hδ : 0 < δ := by
    by_contra hδ
    have : δ * (t + ‖m‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hδ) (by positivity)
    linarith [norm_nonneg (t • ξ + m)]
  have hmin : 0 < min c 1 := by
    by_contra hneg
    nlinarith [norm_nonneg ξ₀, not_lt.1 hneg]
  have hc : 0 < c := hmin.trans_le (min_le_left c 1)
  -- `t + ‖m‖ ≤ 2 t (1 + 2 ‖ξ₀‖)`, hence `‖t ξ + m‖ < min c 1 t ‖ξ₀‖ / 4`.
  have hμ : t + ‖m‖ ≤ 2 * t * (1 + 2 * ‖ξ₀‖) := by
    nlinarith [mul_le_mul_of_nonneg_right hδ₁ (by positivity : (0 : ℝ) ≤ t + ‖m‖),
      mul_le_mul_of_nonneg_left hξu ht.le]
  have hkey : ‖t • ξ + m‖ < min c 1 * (t * ‖ξ₀‖) / 4 := by
    calc ‖t • ξ + m‖ < δ * (t + ‖m‖) := h
      _ ≤ δ * (2 * t * (1 + 2 * ‖ξ₀‖)) := by gcongr
      _ = t * (8 * δ * (1 + 2 * ‖ξ₀‖)) / 4 := by ring
      _ ≤ t * (min c 1 * ‖ξ₀‖) / 4 := by gcongr
      _ = min c 1 * (t * ‖ξ₀‖) / 4 := by ring
  have htξ₀ : t * ‖ξ₀‖ ≤ 2 * (t * ‖ξ‖) := by nlinarith [mul_le_mul_of_nonneg_left hξl ht.le]
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, htξ, show -m - t • ξ = -(t • ξ + m) by abel, norm_neg]
    calc ‖t • ξ + m‖ ≤ min c 1 * (t * ‖ξ₀‖) / 4 := hkey.le
      _ ≤ c * (2 * (t * ‖ξ‖)) / 4 := by gcongr; exact min_le_left c 1
      _ ≤ c * (t * ‖ξ‖) := by nlinarith [mul_nonneg hc.le (mul_nonneg ht.le (norm_nonneg ξ))]
  · have := norm_le_norm_add_norm_sub' (t • ξ) (-m)
    rw [htξ, norm_neg, sub_neg_eq_add] at this
    nlinarith [mul_le_mul_of_nonneg_right (min_le_right c 1)
      (mul_nonneg ht.le (norm_nonneg ξ₀))]

/-- The bound on a term of the Fourier series in the non-stationary region: the coefficient
`F₀` decays like `μ ^ (-(N + k + r))`, `μ = t + n`, while the localized Fourier transform `L₀`
grows like `(1 + n) ^ k`. -/
private theorem pow_mul_mul_le_of_nonstationary {t n F₀ L₀ C₀ C : ℝ} {N k r : ℕ} (ht : 1 ≤ t)
    (hn : 0 ≤ n) (hF₀ : 0 ≤ F₀) (hC₀ : 0 ≤ C₀) (hF : (t + n) ^ (N + k + r) * F₀ ≤ C)
    (hL : L₀ ≤ C₀ * (1 + n) ^ k) :
    t ^ N * (F₀ * L₀) ≤ C₀ * C * ((1 + n) ^ r)⁻¹ := by
  rw [le_mul_inv_iff₀ (by positivity)]
  calc t ^ N * (F₀ * L₀) * (1 + n) ^ r ≤ t ^ N * (F₀ * (C₀ * (1 + n) ^ k)) * (1 + n) ^ r := by
        gcongr
    _ = C₀ * (t ^ N * (1 + n) ^ k * (1 + n) ^ r * F₀) := by ring
    _ ≤ C₀ * ((t + n) ^ N * (t + n) ^ k * (t + n) ^ r * F₀) := by
        gcongr; linarith
    _ = C₀ * ((t + n) ^ (N + k + r) * F₀) := by ring
    _ ≤ C₀ * C := by gcongr

/-- The bound on a term of the Fourier series in the stationary region: there `t ≤ 4 n / a`, the
coefficient `F₀` is bounded, and the localized Fourier transform `L₀` decays like
`(1 + n) ^ (-(N + r))`. -/
private theorem pow_mul_mul_le_of_stationary {t n a F₀ L₀ A C : ℝ} {N r : ℕ} (ht : 0 < t)
    (hn : 0 ≤ n) (ha : 0 < a) (hF₀ : 0 ≤ F₀) (hL₀ : 0 ≤ L₀) (htn : t * a ≤ 4 * n) (hF : F₀ ≤ A)
    (hL : (1 + n) ^ (N + r) * L₀ ≤ C) :
    t ^ N * (F₀ * L₀) ≤ A * C * (4 / a) ^ N * ((1 + n) ^ r)⁻¹ := by
  have hA : 0 ≤ A := hF₀.trans hF
  have ht' : t ≤ 4 / a * (1 + n) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    linarith
  rw [le_mul_inv_iff₀ (by positivity)]
  calc t ^ N * (F₀ * L₀) * (1 + n) ^ r ≤ (4 / a * (1 + n)) ^ N * (A * L₀) * (1 + n) ^ r := by
        gcongr
    _ = A * (4 / a) ^ N * ((1 + n) ^ (N + r) * L₀) := by rw [mul_pow, pow_add]; ring
    _ ≤ A * (4 / a) ^ N * C := by gcongr
    _ = A * C * (4 / a) ^ N := by ring

section Phase

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The phase `θ((s, w, p), x) = -(s Φ(p, x) + ⟪w, x⟫)` of the Fourier coefficients
`𝓕 (ψ 𝐞(-t Φ(p, ·))) (m)`, normalized by `s = t / (t + ‖m‖)` and `w = m / (t + ‖m‖)`. -/
private def coeffPhase (Φ : F × E → ℝ) (z : (ℝ × E × F) × E) : ℝ :=
  -(z.1.1 * Φ (z.1.2.2, z.2) + ⟪z.1.2.1, z.2⟫)

omit [FiniteDimensional ℝ E] in
private theorem contDiff_coeffPhase {Φ : F × E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (coeffPhase Φ) :=
  ((contDiff_fst.fst.mul (hΦ.comp (contDiff_fst.snd.snd.prodMk contDiff_snd))).add
    (contDiff_fst.snd.fst.inner ℝ contDiff_snd)).neg

/-- The phase `coeffPhase Φ` has no critical point in `x` where `s ∇Φ(p, x) + w ≠ 0`. -/
private theorem fderiv_coeffPhase_ne_zero {Φ : F × E → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {q : ℝ × E × F} {x : E} (hq : q.1 • gradient (fun y ↦ Φ (q.2.2, y)) x + q.2.1 ≠ 0) :
    fderiv ℝ (fun y ↦ coeffPhase Φ (q, y)) x ≠ 0 := by
  have hΦx : HasFDerivAt (fun y ↦ Φ (q.2.2, y)) (fderiv ℝ (fun y ↦ Φ (q.2.2, y)) x) x :=
    ((hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x).hasFDerivAt
  have h : HasFDerivAt (fun y ↦ coeffPhase Φ (q, y))
      (-(q.1 • fderiv ℝ (fun y ↦ Φ (q.2.2, y)) x + innerSL ℝ q.2.1)) x :=
    ((hΦx.const_mul q.1).add (innerSL ℝ q.2.1).hasFDerivAt).neg
  rw [h.fderiv]
  intro h0
  -- Evaluating the derivative at `v = s ∇Φ(p, x) + w` gives `-‖v‖ ^ 2`.
  have h1 := congrArg (fun L : E →L[ℝ] ℝ ↦
    L (q.1 • gradient (fun y ↦ Φ (q.2.2, y)) x + q.2.1)) h0
  simp only [neg_apply, add_apply, smul_apply, innerSL_apply_apply, ← toDual_gradient,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul, zero_apply, neg_eq_zero] at h1
  rw [← real_inner_smul_left, ← inner_add_left, real_inner_self_eq_norm_sq] at h1
  exact hq (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

variable [MeasurableSpace E] [BorelSpace E]

/-- **Non-stationary Fourier coefficients.** For `p` in a compact set `V`, the Fourier transform of
`ψ 𝐞(-t Φ(p, ·))` at `m` is `O((t + ‖m‖) ^ (-N))` in the non-stationary region where
`‖t ∇Φ(p, x) + m‖ ≥ δ (t + ‖m‖)` on the support of `ψ`. -/
private theorem exists_forall_pow_mul_norm_fourier_le (ψ : 𝓓(Ω, ℂ)) {Φ : F × E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {V : Set F} (hV : IsCompact V) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ C, ∀ p ∈ V, ∀ t : ℝ, 0 ≤ t → ∀ m : E, 0 < t + ‖m‖ →
      (∀ x ∈ tsupport ψ, δ * (t + ‖m‖) ≤ ‖t • gradient (fun y ↦ Φ (p, y)) x + m‖) →
      (t + ‖m‖) ^ N * ‖𝓕 (fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ)) m‖ ≤ C := by
  set G : F × E → E := fun q ↦ gradient (fun y ↦ Φ (q.1, y)) q.2
  have hGc : Continuous G :=
    TauCeti.continuous_gradient_slice_right (f := fun p y ↦ Φ (p, y)) (hΦ.of_le (by simp))
  -- The compact set of normalized parameters `(s, w, p)` of the non-stationary region.
  let Q : Set (ℝ × E × F) := Prod.fst ⁻¹' Icc 0 1 ∩ (fun q ↦ q.2.1) ⁻¹' closedBall 0 1 ∩
    (fun q ↦ q.2.2) ⁻¹' V ∩ ⋂ x ∈ tsupport ψ, {q | δ ≤ ‖q.1 • G (q.2.2, x) + q.2.1‖}
  have hQ : IsCompact Q := by
    refine (isCompact_Icc.prod ((isCompact_closedBall 0 1).prod hV)).of_isClosed_subset ?_
      fun q hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.1.2⟩
    refine (((isClosed_Icc.preimage continuous_fst).inter
      (isClosed_closedBall.preimage continuous_snd.fst)).inter
      (hV.isClosed.preimage continuous_snd.snd)).inter
      (isClosed_biInter fun x _ ↦ isClosed_le continuous_const ?_)
    exact ((continuous_fst.smul (hGc.comp (continuous_snd.snd.prodMk continuous_const))).add
      continuous_snd.fst).norm
  obtain ⟨C, hC⟩ := TauCeti.exists_forall_abs_pow_mul_norm_integral_mul_fourierChar_le
    (μ := MeasureTheory.volume) ψ.contDiff ψ.hasCompactSupport (contDiff_coeffPhase hΦ) hQ
    (fun q hq x hx ↦ fderiv_coeffPhase_ne_zero hΦ (norm_pos_iff.1 (hδ.trans_le
      (mem_iInter₂.1 hq.2 x hx)))) N
  refine ⟨C, fun p hp t ht m hμ hns ↦ ?_⟩
  set μ := t + ‖m‖
  -- The normalized parameter of `(t, m, p)` lies in `Q`.
  have hq : ((t / μ, μ⁻¹ • m, p) : ℝ × E × F) ∈ Q := by
    refine ⟨⟨⟨⟨div_nonneg ht hμ.le, (div_le_one hμ).2 (le_add_of_nonneg_right (norm_nonneg m))⟩,
      ?_⟩, hp⟩, mem_iInter₂.2 fun x hx ↦ ?_⟩
    · rw [mem_preimage, mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hμ.le]
      exact inv_mul_le_one_of_le₀ (le_add_of_nonneg_left ht) hμ.le
    · have h : (t / μ) • G (p, x) + μ⁻¹ • m = μ⁻¹ • (t • G (p, x) + m) := by
        rw [smul_add, smul_smul, div_eq_inv_mul]
      rw [mem_ofPred_eq, h, norm_smul, norm_inv, Real.norm_of_nonneg hμ.le, le_inv_mul_iff₀ hμ,
        mul_comm]
      exact hns x hx
  -- The Fourier coefficient is the oscillatory integral with phase `μ θ`.
  have hF : 𝓕 (fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ)) m =
      ∫ x, ψ x * 𝐞 (μ * coeffPhase Φ ((t / μ, μ⁻¹ • m, p), x)) := by
    rw [Real.fourier_eq]
    congr 1
    ext x
    have harg : μ * coeffPhase Φ ((t / μ, μ⁻¹ • m, p), x) = -⟪x, m⟫ + -(t * Φ (p, x)) := by
      simp only [coeffPhase, real_inner_smul_left, real_inner_comm m x]
      field_simp
      ring
    rw [harg, AddChar.map_add_eq_mul, Circle.coe_mul, Circle.smul_def, smul_eq_mul]
    ring
  have h := hC _ hq μ
  rwa [abs_of_pos hμ, ← hF] at h

end Phase

section Decay

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The bound on the terms of the Fourier series of the pairing of `T` with `ψ 𝐞(-t Φ(p, ·))`: in
the non-stationary region by the decay `hCA` of the Fourier coefficient against the polynomial
growth `hC₀` of `T (χ e_(-m))`, and in the stationary region, where `-m` lies in the cone `Γ`, by
the decay `hCΓ` of `T (χ e_(-m))` there. -/
private theorem pow_mul_norm_fourier_mul_norm_localFourier_le [MeasurableSpace E] [BorelSpace E]
    {T : 𝓓'(Ω, ℂ)} {χ ψ : 𝓓(Ω, ℂ)} {Φ : F × E → ℝ} {p : F} {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0)
    {Γ Γ' : Set E} (hΓ'c : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') {c : ℝ}
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    (hG : ∀ x ∈ tsupport ψ, gradient (fun y ↦ Φ (p, y)) x ∈ Γ' ∧
      ‖gradient (fun y ↦ Φ (p, y)) x - ξ₀‖ ≤ ‖ξ₀‖ / 2)
    {δ : ℝ} (hδ₁ : δ ≤ 1 / 2) (hδ₂ : 8 * δ * (1 + 2 * ‖ξ₀‖) ≤ min c 1 * ‖ξ₀‖)
    {N k r : ℕ} {C₀ CA CΓ : ℝ} (hC₀0 : 0 ≤ C₀)
    (hC₀ : ∀ η, ‖T.localFourier χ η‖ ≤ C₀ * (1 + ‖η‖) ^ k)
    (hCΓ : ∀ η ∈ Γ, (1 + ‖η‖) ^ (N + r) * ‖T.localFourier χ η‖ ≤ CΓ) {t : ℝ} (ht : 1 ≤ t)
    (hCA : ∀ m : E, (∀ x ∈ tsupport ψ, δ * (t + ‖m‖) ≤ ‖t • gradient (fun y ↦ Φ (p, y)) x + m‖) →
      (t + ‖m‖) ^ (N + k + r) * ‖𝓕 (fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ)) m‖ ≤ CA)
    (m : E) :
    t ^ N * (‖𝓕 (fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ)) m‖ * ‖T.localFourier χ (-m)‖) ≤
      (max (C₀ * CA) 0 + max ((∫ x, ‖ψ x‖) * CΓ * (4 / ‖ξ₀‖) ^ N) 0) * ((1 + ‖m‖) ^ r)⁻¹ := by
  have hn : 0 ≤ ‖m‖ := norm_nonneg _
  have hinv : 0 ≤ ((1 + ‖m‖) ^ r)⁻¹ := by positivity
  by_cases hns : ∀ x ∈ tsupport ψ, δ * (t + ‖m‖) ≤ ‖t • gradient (fun y ↦ Φ (p, y)) x + m‖
  · -- Non-stationary: the Fourier coefficient decays faster than `T (χ e_(-m))` grows.
    have hL := hC₀ (-m)
    rw [norm_neg] at hL
    exact (pow_mul_mul_le_of_nonstationary ht hn (norm_nonneg _) hC₀0 (hCA m hns) hL).trans
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans
        (le_add_of_nonneg_right (le_max_right _ _))) hinv)
  · -- Stationary: `-m` lies in the cone `Γ`, where `T (χ e_(-m))` decays, and `t ≲ ‖m‖`.
    push Not at hns
    obtain ⟨x, hx, hlt⟩ := hns
    obtain ⟨hΓ'x, hdist⟩ := hG x hx
    obtain ⟨hball, htm⟩ := neg_mem_closedBall_and_le_of_norm_add_lt (by linarith) hdist hδ₁ hδ₂ hlt
    have hL := hCΓ _ (hΓ' _ (hΓ'c t (by linarith) _ hΓ'x) hball)
    rw [norm_neg] at hL
    have hF : ‖𝓕 (fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ)) m‖ ≤ ∫ x, ‖ψ x‖ := by
      refine (Real.norm_fourier_le_integral_norm _ _).trans (le_of_eq ?_)
      congr 1
      ext x
      simp
    exact (pow_mul_mul_le_of_stationary (by linarith) hn (norm_pos_iff.2 hξ₀) (norm_nonneg _)
      (norm_nonneg _) htm hF hL).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans
        (le_add_of_nonneg_left (le_max_right _ _))) hinv)

/-- The decay estimate, for a cutoff `ψ` over whose support, for `p ∈ V`, the gradient of `Φ(p, ·)`
stays in a cone `Γ'` and within `‖ξ₀‖ / 2` of `ξ₀`, where `Γ'` has conic neighbourhoods inside a
cone `Γ` on which `T` decays rapidly for a cutoff `χ` equal to one on the support of `ψ`. -/
private theorem exists_forall_pow_mul_norm_complexPairing_le_of_forall {T : 𝓓'(Ω, ℂ)}
    {Φ : F × E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0) {Γ Γ' : Set E} {χ ψ : 𝓓(Ω, ℂ)}
    (hdec : ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier χ η‖ ≤ C)
    (hχψ : ∀ x ∈ tsupport ψ, χ x = 1) (hΓ'c : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') {c : ℝ}
    (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {V : Set F} (hV : IsCompact V)
    (hG : ∀ p ∈ V, ∀ x ∈ tsupport ψ, gradient (fun y ↦ Φ (p, y)) x ∈ Γ' ∧
      ‖gradient (fun y ↦ Φ (p, y)) x - ξ₀‖ ≤ ‖ξ₀‖ / 2) (N : ℕ) :
    ∃ C, ∀ p ∈ V, ∀ t : ℝ, 1 ≤ t → ∀ f : 𝓓(Ω, ℂ), (∀ x, f x = ψ x * 𝐞 (-(t * Φ (p, x)))) →
      t ^ N * ‖T.complexPairing f‖ ≤ C := by
  borelize E
  -- A lattice `L` none of whose nonzero translates of `tsupport χ` meet it.
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  -- The constants: polynomial growth and conic decay of `T (χ e_η)`, the non-stationary bound,
  -- and the bound `‖𝓕 g‖ ≤ ∫ ‖ψ‖`.
  obtain ⟨C₀, k₀, hC₀⟩ := exists_norm_localFourier_le T χ
  have hC₀0 : 0 ≤ C₀ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC₀ 0)) (by positivity)
  set r₀ := Module.finrank ℤ (ZLattice.dual L) + 1
  have hsum := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (Nat.lt_succ_self _)
  obtain ⟨CΓ, hCΓ⟩ := hdec (N + r₀)
  set δ : ℝ := min (1 / 2) (min c 1 * ‖ξ₀‖ / (8 * (1 + 2 * ‖ξ₀‖)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₂ : 8 * δ * (1 + 2 * ‖ξ₀‖) ≤ min c 1 * ‖ξ₀‖ := by
    linarith [(le_div_iff₀ (by positivity)).1
      (min_le_right (1 / 2 : ℝ) (min c 1 * ‖ξ₀‖ / (8 * (1 + 2 * ‖ξ₀‖))))]
  obtain ⟨CA, hCA⟩ := exists_forall_pow_mul_norm_fourier_le ψ hΦ hV hδ (N + k₀ + r₀)
  set A₀ := ∫ x, ‖ψ x‖
  set κ : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set B := ‖κ‖ * (max (C₀ * CA) 0 + max (A₀ * CΓ * (4 / ‖ξ₀‖) ^ N) 0)
  refine ⟨B * ∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ r₀)⁻¹, fun p hp t ht f hf ↦ ?_⟩
  have hfψ : (f : E → ℂ) = fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ) := funext hf
  have hsuppf : support f ⊆ tsupport ψ := fun x hx ↦
    subset_tsupport _ fun h ↦ hx (by simp [hf, h])
  -- Expand `T f` in the Fourier series of `f` along `L`.
  have hT := hasSum_fourier_mul_localFourier T χ L hL (φ := f) fun x hx ↦ hχψ x (hsuppf hx)
  -- Each term of the Fourier series is `O(t ^ (-N) (1 + ‖m‖) ^ (-r₀))`.
  have hterm (m : ZLattice.dual L) :
      ‖(t ^ N : ℂ) * (κ * 𝓕 (f : E → ℂ) m * T.localFourier χ (-m))‖ ≤
        B * ((1 + ‖(m : E)‖) ^ r₀)⁻¹ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ t), hfψ]
    calc t ^ N * (‖κ‖ * ‖𝓕 (fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ)) m‖ *
          ‖T.localFourier χ (-m)‖)
        = ‖κ‖ * (t ^ N * (‖𝓕 (fun x ↦ ψ x * (𝐞 (-(t * Φ (p, x))) : ℂ)) m‖ *
          ‖T.localFourier χ (-m)‖)) := by ring
      _ ≤ ‖κ‖ * ((max (C₀ * CA) 0 + max (A₀ * CΓ * (4 / ‖ξ₀‖) ^ N) 0) *
          ((1 + ‖(m : E)‖) ^ r₀)⁻¹) :=
        mul_le_mul_of_nonneg_left (pow_mul_norm_fourier_mul_norm_localFourier_le hξ₀ hΓ'c hΓ'
          (hG p hp) (min_le_left _ _) hδ₂ hC₀0 hC₀ hCΓ ht
          (fun m' hns ↦ hCA p hp t (by linarith) m' (by positivity) hns) m) (norm_nonneg _)
      _ = B * ((1 + ‖(m : E)‖) ^ r₀)⁻¹ := by ring
  calc t ^ N * ‖T.complexPairing f‖ = ‖(t ^ N : ℂ) * T.complexPairing f‖ := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    _ ≤ ∑' m : ZLattice.dual L, B * ((1 + ‖(m : E)‖) ^ r₀)⁻¹ :=
        (hT.mul_left _).norm_le_of_bounded (hsum.mul_left B).hasSum hterm
    _ = B * ∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ r₀)⁻¹ := tsum_mul_left

/-- **Decay along a nonlinear phase.** Let `Φ(p, x)` be a smooth real phase depending on a
parameter `p` in a finite-dimensional space, and suppose that `T` is microlocally smooth at
`(x₀, ξ₀)`, where `ξ₀ = ∇Φ(p₀, ·)(x₀) ≠ 0`. Then there are neighbourhoods `V` of `p₀` and `U` of
`x₀` such that for every test function `ψ` supported in `U`, the pairing of `T` with
`ψ 𝐞(-t Φ(p, ·))` decays faster than every power of `t` as `t → ∞`, uniformly for `p ∈ V`. For
the linear phase `Φ(p, x) = ⟪x, ξ₀⟫` this is the rapid decay of the localized Fourier transform of
`T` along the ray of `ξ₀`. -/
theorem IsMicrolocallySmoothAt.exists_nhds_forall_pow_mul_norm_complexPairing_le
    [FiniteDimensional ℝ F] {T : 𝓓'(Ω, ℂ)} {Φ : F × E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {p₀ : F} {x₀ : E}
    (h₀ : gradient (fun x ↦ Φ (p₀, x)) x₀ ≠ 0)
    (hT : T.IsMicrolocallySmoothAt x₀ (gradient (fun x ↦ Φ (p₀, x)) x₀)) :
    ∃ V ∈ 𝓝 p₀, ∃ U ∈ 𝓝 x₀, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → ∀ N : ℕ, ∃ C, ∀ p ∈ V,
      ∀ t : ℝ, 1 ≤ t → ∀ f : 𝓓(Ω, ℂ), (∀ x, f x = ψ x * 𝐞 (-(t * Φ (p, x)))) →
        t ^ N * ‖T.complexPairing f‖ ≤ C := by
  set ξ₀ := gradient (fun x ↦ Φ (p₀, x)) x₀
  obtain ⟨U₁, hU₁, Γ, hΓo, hξΓ, hΓc, hdec⟩ := hT.exists_nhds_cone
  obtain ⟨Γ', hΓ'o, hξΓ', hΓ'c, c, hc, hΓ'⟩ := hΓo.exists_cone_closedBall_subset hΓc hξΓ
  -- Near `(p₀, x₀)` the gradient stays in `Γ'` and within `‖ξ₀‖ / 2` of `ξ₀`.
  have hGc : Continuous fun q : F × E ↦ gradient (fun y ↦ Φ (q.1, y)) q.2 :=
    TauCeti.continuous_gradient_slice_right (f := fun p y ↦ Φ (p, y)) (hΦ.of_le (by simp))
  have hW : {q : F × E | gradient (fun y ↦ Φ (q.1, y)) q.2 ∈ Γ' ∧
      dist (gradient (fun y ↦ Φ (q.1, y)) q.2) ξ₀ < ‖ξ₀‖ / 2} ∈ 𝓝 (p₀, x₀) :=
    ((hΓ'o.preimage hGc).inter (isOpen_lt (hGc.dist continuous_const) continuous_const)).mem_nhds
      ⟨hξΓ', (dist_self ξ₀).trans_lt (half_pos (norm_pos_iff.2 h₀))⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  obtain ⟨ε', hε', hε'U⟩ := Metric.mem_nhds_iff.1 hU₁
  have hr : 0 < min ε ε' := lt_min hε hε'
  refine ⟨closedBall p₀ (min ε ε' / 2), closedBall_mem_nhds _ (half_pos hr),
    ball x₀ (min ε ε' / 2), ball_mem_nhds _ (half_pos hr), fun ψ hψ N ↦ ?_⟩
  -- A cutoff `χ` equal to one near the support of `ψ`, supported in `U₁ ∩ Ω`.
  set U := ball x₀ (min ε ε' / 2)
  have hUU₁ : U ⊆ U₁ := (ball_subset_ball (by linarith [min_le_right ε ε'])).trans hε'U
  obtain ⟨χr, hχr, -, hχ1, hχc, hχU⟩ := ψ.hasCompactSupport.isCompact.exists_contDiff_cutoff
    (isOpen_ball.inter Ω.isOpen) (subset_inter hψ ψ.tsupport_subset)
  have hχs : tsupport (fun x ↦ (χr x : ℂ)) ⊆ U ∩ Ω :=
    (tsupport_comp_subset ofReal_zero χr).trans hχU
  have hχrc : ContDiff ℝ ∞ fun x ↦ (χr x : ℂ) := ofRealCLM.contDiff.comp hχr
  let χ : 𝓓(Ω, ℂ) := ⟨fun x ↦ (χr x : ℂ), hχrc, hχc.comp_left ofReal_zero,
    hχs.trans inter_subset_right⟩
  have hχψ (x : E) (hx : x ∈ tsupport ψ) : χ x = 1 := by
    simpa [χ, TestFunction.coe_mk] using interior_subset (hχ1 hx)
  refine exists_forall_pow_mul_norm_complexPairing_le_of_forall hΦ h₀
    (hdec χ ((hχs.trans inter_subset_left).trans hUU₁)) hχψ hΓ'c hc hΓ' (isCompact_closedBall _ _)
    (fun p hp x hx ↦ ?_) N
  replace hx : x ∈ U := hψ hx
  have hq : (p, x) ∈ ball (p₀, x₀) ε := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.1 hp).trans_lt (by linarith [min_le_left ε ε']),
      (mem_ball.1 hx).trans (by linarith [min_le_left ε ε'])⟩
  obtain ⟨h1, h2⟩ := hεW hq
  rw [← dist_eq_norm]
  exact ⟨h1, h2.le⟩

end Decay


end Distribution
