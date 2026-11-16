/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Non-stationary phase for compact families of phases

Let `u` be a smooth compactly supported amplitude on a finite-dimensional real space `E` and
`G(θ, x)` a smooth real phase depending on a parameter `θ`. If for every `θ` in a compact set `P`
the phase `x ↦ G(θ, x)` has no critical point on the support of `u`, then the oscillatory integrals

`∫ e(s G(θ, x)) u(x) dx`, with `e(t) = exp(2πi t)`,

decay faster than every power of the frequency `s`, uniformly for `θ ∈ P`:
`|s| ^ N ‖∫ e(s G(θ, x)) u(x) dx‖ ≤ C_N` for all `θ ∈ P` and all real `s`
(`TauCeti.exists_abs_pow_mul_norm_integral_fourierChar_smul_le`).

This is the uniform form of the principle of non-stationary phase used for families of phases
that are linear in a large frequency. For instance the localized Fourier transform of a
distribution pushed forward along a smooth map `Φ` is a superposition of integrals with phases
`⟪x, m⟫ + ⟪Φ x, η⟫`; normalizing `(m, η)` to the unit sphere gives a compact family, and the
estimate controls these integrals away from the stationary points `m = -(DΦ x)ᵀ η`.

## Proof

Fix a basis `(bⱼ)` of `E` and write `∂ⱼG` for the partial derivatives of `G` in `x` along it. The
sum of squares `S = ∑ⱼ (∂ⱼG)²` is bounded below by some `c > 0` on `P × supp u`, by compactness.
With a smooth function `φ` equal to the identity on `[c, ∞)` and bounded below by `c / 2`, the
smooth coefficients `aⱼ = ∂ⱼG / φ(S)` satisfy `∑ⱼ aⱼ ∂ⱼG = 1` on `P × supp u`, so that

`2πi s e(sG) u = ∑ⱼ aⱼ u ∂ⱼ(e(sG))` there.

Integrating by parts moves the derivatives onto the amplitude: with the transposed operator
`ᵗL w = ∑ⱼ ∂ⱼ(aⱼ w)`, `2πi s ∫ e(sG) w = -∫ e(sG) ᵗL w`. Iterating `N` times, the integral is
`(2πi s)⁻ᴺ` times the integral of `(ᵗL)ᴺ u`, a function jointly continuous in `(θ, x)` and
supported in `supp u`, hence bounded on the compact set `P × supp u`. Working with a whole
compact family of phases at once, rather than with explicit bounds on the derivatives of one phase,
keeps the constants uniform without any bookkeeping of derivatives.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §2.
-/

public section

open MeasureTheory Set Function Complex
open scoped FourierTransform ContDiff Real

namespace TauCeti

namespace ParametricNonstationaryPhase

variable {Θ E : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The transposed operator `ᵗL w = ∑ⱼ ∂ⱼ(aⱼ w)`, the derivatives taken in the second variable
along the vectors `b j`. -/
private noncomputable def transposeOp {ι : Type*} [Fintype ι] (a : ι → Θ × E → ℝ) (b : ι → E)
    (w : Θ × E → ℂ) : Θ × E → ℂ :=
  fun p ↦ ∑ j, fderiv ℝ (fun q ↦ w q * (a j q : ℂ)) p (0, b j)

variable {ι : Type*} [Fintype ι] {a : ι → Θ × E → ℝ} {b : ι → E}

private theorem contDiff_transposeOp (ha : ∀ j, ContDiff ℝ ∞ (a j)) {w : Θ × E → ℂ}
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (transposeOp a b w) :=
  ContDiff.sum fun j _ ↦
    ((hw.mul (ofRealCLM.contDiff.comp (ha j))).fderiv_right le_rfl).clm_apply contDiff_const

/-- The iterates `(ᵗL)ⁿ w` of a smooth `w` are smooth. -/
private theorem contDiff_iterate_transposeOp (ha : ∀ j, ContDiff ℝ ∞ (a j)) {w : Θ × E → ℂ}
    (hw : ContDiff ℝ ∞ w) (n : ℕ) : ContDiff ℝ ∞ ((transposeOp a b)^[n] w) := by
  induction n with
  | zero => exact hw
  | succ n ih => rw [iterate_succ_apply']; exact contDiff_transposeOp ha ih

/-- `ᵗL` preserves the vanishing outside a closed set `K` of the second variable. -/
private theorem transposeOp_eq_zero {K : Set E} (hK : IsClosed K) {w : Θ × E → ℂ}
    (hw : ∀ p : Θ × E, p.2 ∉ K → w p = 0) (p : Θ × E) (hp : p.2 ∉ K) :
    transposeOp a b w p = 0 := by
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hopen : IsOpen {q : Θ × E | q.2 ∉ K} := hK.isOpen_compl.preimage continuous_snd
  have hev : (fun q ↦ w q * (a j q : ℂ)) =ᶠ[nhds p] fun _ ↦ 0 :=
    Filter.eventually_of_mem (hopen.mem_nhds hp) fun q hq ↦ by simp [hw q hq]
  simp [hev.fderiv_eq]

/-- The iterates `(ᵗL)ⁿ w` vanish outside `K` when `w` does. -/
private theorem iterate_transposeOp_eq_zero {K : Set E} (hK : IsClosed K) {w : Θ × E → ℂ}
    (hw : ∀ p : Θ × E, p.2 ∉ K → w p = 0) (n : ℕ) (p : Θ × E) (hp : p.2 ∉ K) :
    (transposeOp a b)^[n] w p = 0 := by
  induction n generalizing p with
  | zero => exact hw p hp
  | succ n ih => rw [iterate_succ_apply']; exact transposeOp_eq_zero hK ih p hp

/-- The phase factor `x ↦ e(s G(θ, x))` is smooth. -/
private theorem contDiff_fourierChar_mul {G : Θ × E → ℝ} (hG : ContDiff ℝ ∞ G) (θ : Θ) (s : ℝ) :
    ContDiff ℝ ∞ fun x ↦ (𝐞 (s * G (θ, x)) : ℂ) :=
  Real.contDiff_fourierChar.comp (contDiff_const.mul (hG.comp (contDiff_const.prodMk contDiff_id)))

/-- The derivative of the phase factor `x ↦ e(s G(θ, x))` along `v` is
`2πi s ∂_v G(θ, x) e(s G(θ, x))`. -/
private theorem fderiv_fourierChar_mul_apply {G : Θ × E → ℝ} (hG : ContDiff ℝ ∞ G) (θ : Θ)
    (s : ℝ) (x v : E) :
    fderiv ℝ (fun x ↦ (𝐞 (s * G (θ, x)) : ℂ)) x v =
      2 * π * I * s * (fderiv ℝ G (θ, x) (0, v) : ℂ) * 𝐞 (s * G (θ, x)) := by
  have h1 : HasFDerivAt (fun x ↦ s * G (θ, x)) (s • fderiv ℝ (fun x ↦ G (θ, x)) x) x :=
    (((hG.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
      |>.hasFDerivAt).const_mul s
  have h2 : HasFDerivAt (fun x ↦ (𝐞 (s * G (θ, x)) : ℂ)) _ x :=
    (Real.hasDerivAt_fourierChar (s * G (θ, x))).hasFDerivAt.comp
      (g := fun t : ℝ ↦ (𝐞 t : ℂ)) x h1
  rw [h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, fderiv_slice_right (hG.differentiable (by simp)).differentiableAt]
  simp only [smul_eq_mul, real_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  push_cast
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **One integration by parts.** If `∑ⱼ aⱼ ∂ⱼG = 1` at `θ` on a compact set `K` outside which `w`
vanishes, then `2πis ∫ e(sG(θ, ·)) w(θ, ·) = -∫ e(sG(θ, ·)) ᵗL w(θ, ·)`. -/
private theorem mul_integral_eq_neg_integral_transposeOp {G : Θ × E → ℝ} (hG : ContDiff ℝ ∞ G)
    (ha : ∀ j, ContDiff ℝ ∞ (a j)) {K : Set E} (hK : IsCompact K) {θ : Θ}
    (hθ : ∀ x ∈ K, ∑ j, a j (θ, x) * fderiv ℝ G (θ, x) (0, b j) = 1) {w : Θ × E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hwK : ∀ p : Θ × E, p.2 ∉ K → w p = 0) (s : ℝ) :
    (2 * π * I * s) * ∫ x, 𝐞 (s * G (θ, x)) • w (θ, x) ∂μ =
      -∫ x, 𝐞 (s * G (θ, x)) • transposeOp a b w (θ, x) ∂μ := by
  set e : E → ℂ := fun x ↦ 𝐞 (s * G (θ, x))
  set f : ι → E → ℂ := fun j x ↦ w (θ, x) * (a j (θ, x) : ℂ)
  have he : ContDiff ℝ ∞ e := contDiff_fourierChar_mul hG θ s
  have hde (x : E) (v : E) :
      fderiv ℝ e x v = 2 * π * I * s * (fderiv ℝ G (θ, x) (0, v) : ℂ) * e x :=
    fderiv_fourierChar_mul_apply hG θ s x v
  have hfj (j : ι) : ContDiff ℝ ∞ (f j) :=
    ((hw.mul (ofRealCLM.contDiff.comp (ha j))).comp (contDiff_const.prodMk contDiff_id))
  have hfK (j : ι) : HasCompactSupport (f j) :=
    HasCompactSupport.intro hK fun x hx ↦ by simp [f, hwK (θ, x) hx]
  -- The derivative of the amplitudes `aⱼ w` in the second variable.
  have hdf (j : ι) (x : E) (v : E) :
      fderiv ℝ (f j) x v = fderiv ℝ (fun q ↦ w q * (a j q : ℂ)) (θ, x) (0, v) := by
    simpa [f] using congrArg (· v) (fderiv_slice_right
      ((hw.mul (ofRealCLM.contDiff.comp (ha j))).differentiable (by simp)).differentiableAt)
  -- Pointwise, `2πis e w = ∑ⱼ aⱼ w ∂ⱼ e`.
  have hpt (x : E) : 2 * π * I * s * (𝐞 (s * G (θ, x)) • w (θ, x)) =
      ∑ j, f j x * fderiv ℝ e x (b j) := by
    by_cases hx : x ∈ K
    · simp_rw [hde, f, Circle.smul_def, smul_eq_mul]
      have h := congrArg (fun r : ℝ ↦ (r : ℂ)) (hθ x hx)
      push_cast at h
      calc 2 * π * I * s * (e x * w (θ, x))
          = 2 * π * I * s * e x * w (θ, x) * ∑ j, (a j (θ, x) : ℂ) *
              (fderiv ℝ G (θ, x) (0, b j) : ℂ) := by rw [h]; ring
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
    · simp [f, hwK (θ, x) hx]
  have hint1 (j : ι) : Integrable (fun x ↦ f j x * fderiv ℝ e x (b j)) μ :=
    ((hfj j).continuous.mul ((he.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport (hfK j).mul_right
  have hint2 (j : ι) : Integrable (fun x ↦ fderiv ℝ (f j) x (b j) * e x) μ :=
    ((((hfj j).continuous_fderiv (by simp)).clm_apply continuous_const).mul
      he.continuous).integrable_of_hasCompactSupport ((hfK j).fderiv_apply (𝕜 := ℝ) _).mul_right
  have hint3 (j : ι) : Integrable (fun x ↦ f j x * e x) μ :=
    ((hfj j).continuous.mul he.continuous).integrable_of_hasCompactSupport (hfK j).mul_right
  calc (2 * π * I * s) * ∫ x, 𝐞 (s * G (θ, x)) • w (θ, x) ∂μ
      = ∫ x, ∑ j, f j x * fderiv ℝ e x (b j) ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ j, ∫ x, f j x * fderiv ℝ e x (b j) ∂μ := integral_finsetSum _ fun j _ ↦ hint1 j
    _ = ∑ j, -∫ x, fderiv ℝ (f j) x (b j) * e x ∂μ := Finset.sum_congr rfl fun j _ ↦
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint2 j) (hint1 j) (hint3 j)
          (fun x _ ↦ ((hfj j).differentiable (by simp)).differentiableAt)
          fun x _ ↦ (he.differentiable (by simp)).differentiableAt
    _ = -∫ x, 𝐞 (s * G (θ, x)) • transposeOp a b w (θ, x) ∂μ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ ↦ hint2 j]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        simp only [transposeOp, Circle.smul_def, smul_eq_mul, Finset.mul_sum, hdf]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **`N` integrations by parts.** -/
private theorem pow_mul_integral_eq {G : Θ × E → ℝ} (hG : ContDiff ℝ ∞ G)
    (ha : ∀ j, ContDiff ℝ ∞ (a j)) {K : Set E} (hK : IsCompact K) {θ : Θ}
    (hθ : ∀ x ∈ K, ∑ j, a j (θ, x) * fderiv ℝ G (θ, x) (0, b j) = 1) {w : Θ × E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hwK : ∀ p : Θ × E, p.2 ∉ K → w p = 0) (s : ℝ) (N : ℕ) :
    (2 * π * I * s) ^ N * ∫ x, 𝐞 (s * G (θ, x)) • w (θ, x) ∂μ =
      (-1) ^ N * ∫ x, 𝐞 (s * G (θ, x)) • (transposeOp a b)^[N] w (θ, x) ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h := mul_integral_eq_neg_integral_transposeOp (μ := μ) hG ha hK hθ
      (contDiff_iterate_transposeOp (b := b) ha hw N)
      (iterate_transposeOp_eq_zero hK.isClosed hwK N) s
    rw [iterate_succ_apply']
    linear_combination (2 * π * I * s) * ih + (-1) ^ N * h

end ParametricNonstationaryPhase

open ParametricNonstationaryPhase

variable {Θ E : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] in
/-- If the phases `x ↦ G (θ, x)`, `θ ∈ P`, have no critical point on a compact set `K`, there are
smooth coefficients `aⱼ` on `Θ × E` with `∑ⱼ aⱼ ∂ⱼG = 1` on `P × K`, the derivatives `∂ⱼ` taken
in the second variable along a basis of `E`. -/
private theorem exists_sum_mul_fderiv_eq_one {G : Θ × E → ℝ} (hG : ContDiff ℝ ∞ G) {P : Set Θ}
    (hP : IsCompact P) {K : Set E} (hK : IsCompact K)
    (hcrit : ∀ θ ∈ P, ∀ x ∈ K, fderiv ℝ (fun x ↦ G (θ, x)) x ≠ 0) :
    ∃ a : Fin (Module.finrank ℝ E) → Θ × E → ℝ, (∀ j, ContDiff ℝ ∞ (a j)) ∧
      ∀ θ ∈ P, ∀ x ∈ K, ∑ j, a j (θ, x) * fderiv ℝ G (θ, x) (0, Module.finBasis ℝ E j) = 1 := by
  set b := Module.finBasis ℝ E
  -- The partial derivatives of `G` in the second variable, and their sum of squares.
  set D : Fin (Module.finrank ℝ E) → Θ × E → ℝ := fun j p ↦ fderiv ℝ G p (0, b j)
  have hD (j) : ContDiff ℝ ∞ (D j) := (hG.fderiv_right le_rfl).clm_apply contDiff_const
  set S : Θ × E → ℝ := fun p ↦ ∑ j, D j p ^ 2
  have hS : ContDiff ℝ ∞ S := ContDiff.sum fun j _ ↦ (hD j).pow 2
  -- `S` is positive, hence bounded below by some `c > 0`, on `P × K`.
  have hSpos : ∀ p ∈ P ×ˢ K, 0 < S p := by
    rintro ⟨θ, x⟩ ⟨hθ, hx⟩
    by_contra! h
    refine hcrit θ hθ x hx (ContinuousLinearMap.coe_injective (b.ext fun j ↦ ?_))
    have h0 : ∀ j ∈ Finset.univ, D j (θ, x) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _).1 (le_antisymm h
        (Finset.sum_nonneg fun j _ ↦ sq_nonneg _))
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (h0 j (Finset.mem_univ j))
    simpa [fderiv_slice_right (hG.differentiable (by simp)).differentiableAt] using this
  obtain ⟨c, hc, hcS⟩ : ∃ c > 0, ∀ p ∈ P ×ˢ K, c ≤ S p := by
    rcases (P ×ˢ K).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := (hP.prod hK).exists_isMinOn h hS.continuous.continuousOn
      exact ⟨S p₀, hSpos p₀ hp₀, fun p hp ↦ hmin hp⟩
  -- The smooth coefficients `aⱼ = ∂ⱼG / φ(S)`, with `φ(S) = S` on `P × K`.
  obtain ⟨φ, hφ, hφpos, hφS⟩ := exists_contDiff_eq_self_of_le hc
  refine ⟨fun j p ↦ D j p / φ (S p), fun j ↦ (hD j).div (hφ.comp hS) fun p ↦
    (lt_of_lt_of_le (by linarith) (hφpos _)).ne', fun θ hθ x hx ↦ ?_⟩
  simp only [← Finset.sum_div, div_mul_eq_mul_div]
  rw [hφS _ (hcS _ ⟨hθ, hx⟩), div_eq_one_iff_eq (hSpos _ ⟨hθ, hx⟩).ne']
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Non-stationary phase for a compact family of phases** (Hörmander I, Theorem 7.7.1). Let `u`
be a smooth compactly supported amplitude and `G` a smooth phase on `Θ × E`. If for every `θ` in
a compact set `P` the phase `x ↦ G (θ, x)` has no critical point on the support of `u`, then the
oscillatory integrals `∫ e(s G(θ, x)) u(x) dx` decay faster than every power of `s`, uniformly
for `θ ∈ P`: for every `N` there is `C` with `|s| ^ N ‖∫ e(s G(θ, x)) u(x) dx‖ ≤ C` for all
`θ ∈ P` and all real `s`. -/
theorem exists_abs_pow_mul_norm_integral_fourierChar_smul_le {G : Θ × E → ℝ}
    (hG : ContDiff ℝ ∞ G) {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (hu' : HasCompactSupport u)
    {P : Set Θ} (hP : IsCompact P)
    (hcrit : ∀ θ ∈ P, ∀ x ∈ tsupport u, fderiv ℝ (fun x ↦ G (θ, x)) x ≠ 0) (N : ℕ) :
    ∃ C, ∀ θ ∈ P, ∀ s : ℝ, |s| ^ N * ‖∫ x, 𝐞 (s * G (θ, x)) • u x ∂μ‖ ≤ C := by
  set K := tsupport u
  have hK : IsCompact K := hu'.isCompact
  obtain ⟨a, ha, hθ⟩ := exists_sum_mul_fderiv_eq_one hG hP hK hcrit
  -- After `N` integrations by parts the amplitude is bounded by `M` on `P × K`.
  set w : Θ × E → ℂ := fun p ↦ u p.2
  have hw : ContDiff ℝ ∞ w := hu.comp contDiff_snd
  have hwK : ∀ p : Θ × E, p.2 ∉ K → w p = 0 := fun p hp ↦
    image_eq_zero_of_notMem_tsupport (f := u) hp
  set b : Fin (Module.finrank ℝ E) → E := fun j ↦ Module.finBasis ℝ E j
  set W := (transposeOp a b)^[N] w
  have hWK : ∀ p : Θ × E, p.2 ∉ K → W p = 0 := iterate_transposeOp_eq_zero hK.isClosed hwK N
  obtain ⟨M, hM⟩ := (hP.prod hK).exists_bound_of_continuousOn
    (contDiff_iterate_transposeOp ha hw N).continuous.continuousOn
  refine ⟨M * μ.real K / (2 * π) ^ N, fun θ hθP s ↦ ?_⟩
  have hint : ‖∫ x, 𝐞 (s * G (θ, x)) • W (θ, x) ∂μ‖ ≤ M * μ.real K := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [hWK (θ, x) hx]]
    exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun x hx ↦ by
      simpa [Circle.smul_def] using hM (θ, x) ⟨hθP, hx⟩
  have hnorm : (2 * π) ^ N * |s| ^ N * ‖∫ x, 𝐞 (s * G (θ, x)) • u x ∂μ‖ =
      ‖∫ x, 𝐞 (s * G (θ, x)) • W (θ, x) ∂μ‖ := by
    have h := congrArg norm (pow_mul_integral_eq (μ := μ) hG ha hK (hθ θ hθP) hw hwK s N)
    simpa only [norm_mul, norm_pow, Complex.norm_ofNat, norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_I, one_pow, mul_one, norm_neg, norm_one, one_mul, mul_pow]
      using h
  rw [le_div_iff₀ (by positivity)]
  calc |s| ^ N * ‖∫ x, 𝐞 (s * G (θ, x)) • u x ∂μ‖ * (2 * π) ^ N
      = ‖∫ x, 𝐞 (s * G (θ, x)) • W (θ, x) ∂μ‖ := by rw [← hnorm]; ring
    _ ≤ M * μ.real K := hint

end TauCeti
