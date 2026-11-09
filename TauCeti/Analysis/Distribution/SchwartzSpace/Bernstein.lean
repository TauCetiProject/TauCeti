/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Sobolev.Dilation
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Bernstein's inequalities

Let `E` be a finite-dimensional real inner product space of dimension `d`, and let `f` be a
Schwartz function on `E` whose Fourier transform vanishes outside the closed ball of radius
`R > 0`. **Bernstein's inequality** bounds every derivative of `f` in `L^q` by `f` in `Lᵖ`: for
`1 ≤ p ≤ q ≤ ∞` and every order `k` there is `C`, independent of `R` and `f`, with

`‖Dᵏ f‖_q ≤ C R ^ (k + d (1/p - 1/q)) ‖f‖_p`

(`SchwartzMap.exists_eLpNorm_iteratedFDeriv_le_of_support_fourier_subset`). The case `k = 0`,
`‖f‖_q ≤ C R ^ (d (1/p - 1/q)) ‖f‖_p`, is `SchwartzMap.exists_eLpNorm_le_of_support_fourier_subset`.
Here `1/p` stands for `p.toReal⁻¹`, which is `0` at `p = ∞`.

If instead the Fourier transform of `f` vanishes outside the annulus `R ≤ ‖ξ‖ ≤ θ R`, the
derivatives of `f` also control `f` itself: for `1 ≤ p ≤ ∞` there is `C`, depending on `θ` but not
on `R` or `f`, with

`‖f‖_p ≤ C R ^ (-k) ‖Dᵏ f‖_p`

(`SchwartzMap.exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_support_fourier_subset`).

These are the basic estimates of Littlewood–Paley theory: a dyadic block whose frequencies have
size `2 ^ j` behaves like a function at the single scale `2 ^ (-j)`, so that each derivative costs
exactly a factor `2 ^ j`, and passing from `Lᵖ` to `L^q` costs `2 ^ (j d (1/p - 1/q))`. They give
the Bernstein embeddings between Besov spaces and identify Besov norms of positive regularity
through derivatives.

## Implementation notes

Both inequalities are proved at frequency scale `R = 1` and transported to every `R` by the
dilation `f ↦ f (R⁻¹ • ·)`, which rescales frequencies by `R⁻¹` and `Lᵖ` norms by `R ^ (d/p)`.
At scale `1`, a Schwartz symbol `σ` equal to `1` on the unit ball reproduces `f`, so that
`∂^m f = (∂^m 𝓕⁻ σ) ⋆ f` for every tuple of directions `m`, and convolution with the Schwartz
kernel `∂^m 𝓕⁻ σ` maps `Lᵖ` to `L^q` (`SchwartzMap.exists_eLpNorm_convolution_le`). On the
annulus, the symbols `⟪bᵢ, ξ⟫ / (2πi ‖ξ‖²)`, cut off by a Littlewood–Paley partition, invert the
partial derivatives: `f = ∑ᵢ T_{σᵢ} (∂_{bᵢ} f)`. In both cases the full derivative `Dᵏ f` is
compared with its entries on an orthonormal basis.

## Main declarations

* `SchwartzMap.exists_eLpNorm_iteratedFDeriv_le_of_support_fourier_subset`: Bernstein's
  inequality for frequencies in a ball.
* `SchwartzMap.exists_eLpNorm_le_of_support_fourier_subset`: its case `k = 0`, comparing
  `Lᵖ` and `L^q` norms.
* `SchwartzMap.exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_support_fourier_subset`: the reverse
  Bernstein inequality for frequencies in an annulus.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.1.
-/

public section

namespace SchwartzMap

open MeasureTheory ContinuousLinearMap Module Metric LineDeriv
open scoped ENNReal NNReal FourierTransform Convolution Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Dilations -/

/-- The dilation `f ↦ f (R⁻¹ • ·)` of Schwartz functions, which rescales frequencies by `R⁻¹`. -/
private noncomputable def dilate (R : ℝ) (hR : 0 < R) : 𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  compCLMOfContinuousLinearEquiv ℝ
    (LinearEquiv.smulOfNeZero ℝ E R⁻¹ (inv_ne_zero hR.ne')).toContinuousLinearEquiv

omit [MeasurableSpace E] [BorelSpace E] in
private theorem coe_dilate {R : ℝ} (hR : 0 < R) (f : 𝓢(E, F)) :
    ⇑(dilate R hR f) = fun x => f (R⁻¹ • x) :=
  rfl

/-- The frequencies of the dilation `f (R⁻¹ • ·)` are those of `f`, scaled by `R⁻¹`. -/
private theorem support_fourier_dilate {R : ℝ} (hR : 0 < R) (f : 𝓢(E, F)) :
    Function.support ⇑(𝓕 (dilate R hR f) : 𝓢(E, F)) =
      R⁻¹ • Function.support ⇑(𝓕 f : 𝓢(E, F)) := by
  rw [fourier_coe, fourier_coe, coe_dilate,
    TauCeti.support_fourier_comp_smul _ (inv_ne_zero hR.ne')]

private theorem eLpNorm_dilate {R : ℝ} (hR : 0 < R) (f : 𝓢(E, F)) (p : ℝ≥0∞) :
    eLpNorm (dilate R hR f) p = ENNReal.ofReal (R ^ (finrank ℝ E / p.toReal)) * eLpNorm f p := by
  rw [coe_dilate, Measure.eLpNorm_comp_inv_smul volume _ hR.ne' p, abs_of_pos hR]

private theorem eLpNorm_iteratedFDeriv_dilate {R : ℝ} (hR : 0 < R) (f : 𝓢(E, F)) (k : ℕ)
    (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ k (dilate R hR f)) p =
      ENNReal.ofReal (R⁻¹ ^ k * R ^ (finrank ℝ E / p.toReal)) *
        eLpNorm (iteratedFDeriv ℝ k f) p := by
  rw [coe_dilate, Measure.eLpNorm_iteratedFDeriv_comp_inv_smul volume (f.smooth k) hR.ne' p,
    abs_of_pos hR, Real.rpow_sub hR, Real.rpow_natCast, inv_pow, div_eq_inv_mul]

variable [CompleteSpace F]

/-! ### Bernstein's inequality on a ball -/

/-- A Schwartz symbol whose Fourier multiplier fixes every Schwartz function with frequencies in
the closed unit ball. -/
private theorem exists_fourierMultiplierCLM_eq_self :
    ∃ σ : 𝓢(E, ℂ), ∀ f : 𝓢(E, F), Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ closedBall 0 1 →
      fourierMultiplierCLM F σ f = f := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport fun ξ => (φ ξ : ℂ) :=
    φ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ (⊤ : ℕ∞) fun ξ => (φ ξ : ℂ) := Complex.ofRealCLM.contDiff.comp φ.contDiff
  refine ⟨hc.toSchwartzMap hs, fun f hf => ?_⟩
  have h : smulLeftCLM F (hc.toSchwartzMap hs : E → ℂ) (𝓕 f) = 𝓕 f := by
    ext ξ
    rw [smulLeftCLM_apply_apply (hc.toSchwartzMap hs).hasTemperateGrowth]
    by_cases hξ : 𝓕 f ξ = 0
    · simp [hξ]
    · have : φ ξ = 1 := φ.one_of_mem_closedBall (by simpa using hf hξ)
      simp [this]
  rw [fourierMultiplierCLM_apply, h, FourierTransform.fourierInv_fourier_eq]

/-- Bernstein's inequality for one iterated line derivative, at frequency scale `1`. -/
private theorem exists_eLpNorm_iteratedLineDerivOp_le_of_support_fourier_subset_closedBall_one
    {n : ℕ} (m : Fin n → E) {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F), Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ closedBall 0 1 →
      eLpNorm ⇑(∂^{m} f : 𝓢(E, F)) q ≤ C * eLpNorm f p := by
  obtain ⟨σ, hσ⟩ := exists_fourierMultiplierCLM_eq_self (E := E) (F := F)
  obtain ⟨C, hC⟩ := exists_eLpNorm_convolution_le (F := F) (∂^{m} (𝓕⁻ σ)) hp hpq
  refine ⟨C, fun f hf => ?_⟩
  have h : ⇑(∂^{m} f : 𝓢(E, F)) = ⇑(∂^{m} (𝓕⁻ σ) : 𝓢(E, ℂ)) ⋆[lsmul ℂ ℂ] f := by
    conv_lhs => rw [← hσ f hf]
    rw [fourierMultiplierCLM_eq_convolution, iteratedLineDerivOp_convolution_lsmul]
    exact funext (convolution_apply _ _ _)
  rw [h]
  exact hC f f.continuous.aestronglyMeasurable

/-- Bernstein's inequality for the iterated derivative, at frequency scale `1`. -/
private theorem exists_eLpNorm_iteratedFDeriv_le_of_support_fourier_subset_closedBall_one
    (k : ℕ) {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F), Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ closedBall 0 1 →
      eLpNorm (iteratedFDeriv ℝ k f) q ≤ C * eLpNorm f p := by
  let b := stdOrthonormalBasis ℝ E
  choose C hC using fun r : Fin k → Fin (finrank ℝ E) =>
    exists_eLpNorm_iteratedLineDerivOp_le_of_support_fourier_subset_closedBall_one (F := F)
      (fun j => b (r j)) hp hpq
  refine ⟨∑ r : Fin k → Fin (finrank ℝ E), C r, fun f hf => ?_⟩
  have hq : 1 ≤ q := hp.trans hpq
  let g : (Fin k → Fin (finrank ℝ E)) → E → ℝ := fun r x => ‖∂^{fun j => b (r j)} f x‖
  have h1 : eLpNorm (iteratedFDeriv ℝ k f) q ≤ eLpNorm (∑ r, g r) q := by
    refine eLpNorm_mono_real ((f.smooth k).continuous_iteratedFDeriv
      (by exact_mod_cast le_rfl)).aestronglyMeasurable fun x => ?_
    refine ((iteratedFDeriv ℝ k f x).opNorm_le_sum_norm_apply_orthonormalBasis
      fun _ => b).trans_eq ?_
    rw [Finset.sum_apply]
    -- The two sums run over `Finset.univ` for different `DecidableEq` instances on `Fin k`.
    refine Finset.sum_congr ?_ fun r _ => by simp only [g, iteratedLineDerivOp_eq_iteratedFDeriv]
    congr
    exact Subsingleton.elim _ _
  have h2 : eLpNorm (∑ r, g r) q ≤ ∑ r, eLpNorm (g r) q := eLpNorm_sum_le hq
  have h3 (r : Fin k → Fin (finrank ℝ E)) : eLpNorm (g r) q ≤ C r * eLpNorm f p :=
    (eLpNorm_norm _ (∂^{fun j => b (r j)} f).continuous.aestronglyMeasurable).le.trans
      (hC r f hf)
  calc eLpNorm (iteratedFDeriv ℝ k f) q ≤ ∑ r, (C r : ℝ≥0∞) * eLpNorm f p :=
        h1.trans (h2.trans (Finset.sum_le_sum fun r _ => h3 r))
    _ = ((∑ r, C r : ℝ≥0) : ℝ≥0∞) * eLpNorm f p := by push_cast; rw [Finset.sum_mul]

/-- **Bernstein's inequality.** For `1 ≤ p ≤ q ≤ ∞` and `k : ℕ` there is `C` such that every
Schwartz function `f` whose Fourier transform vanishes outside the closed ball of radius `R > 0`
satisfies `‖Dᵏ f‖_q ≤ C R ^ (k + d (1/p - 1/q)) ‖f‖_p`, where `d` is the dimension of `E` and
`1/p` stands for `p.toReal⁻¹`. -/
theorem exists_eLpNorm_iteratedFDeriv_le_of_support_fourier_subset (k : ℕ) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ≥0, ∀ {R : ℝ}, 0 < R → ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ closedBall 0 R →
      eLpNorm (iteratedFDeriv ℝ k f) q ≤
        C * ENNReal.ofReal (R ^ ((k : ℝ) + finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹))) *
          eLpNorm f p := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_le_of_support_fourier_subset_closedBall_one (E := E) (F := F) k
      hp hpq
  refine ⟨C, fun {R} hR f hf => ?_⟩
  -- The dilation `f (R⁻¹ • ·)` has its frequencies in the closed unit ball.
  have hgsupp : Function.support ⇑(𝓕 (dilate R hR f) : 𝓢(E, F)) ⊆ closedBall 0 1 := by
    rw [support_fourier_dilate]
    rintro _ ⟨ξ, hξ, rfl⟩
    have h := mem_closedBall_zero_iff.1 (hf hξ)
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
    exact inv_mul_le_one_of_le₀ h hR.le
  have hmain := hC _ hgsupp
  rw [eLpNorm_iteratedFDeriv_dilate, eLpNorm_dilate] at hmain
  set a : ℝ := R⁻¹ ^ k * R ^ (finrank ℝ E / q.toReal) with ha_def
  have ha : 0 < a := by positivity
  have hexp : a⁻¹ * R ^ (finrank ℝ E / p.toReal) =
      R ^ ((k : ℝ) + finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) := by
    have hsplit : (k : ℝ) + finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹) =
        k + finrank ℝ E / p.toReal - finrank ℝ E / q.toReal := by ring
    rw [hsplit, ha_def, Real.rpow_sub hR, Real.rpow_add hR, Real.rpow_natCast, inv_pow]
    field_simp
  calc eLpNorm (iteratedFDeriv ℝ k f) q
      = ENNReal.ofReal a⁻¹ * (ENNReal.ofReal a * eLpNorm (iteratedFDeriv ℝ k f) q) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal a⁻¹ * (C * (ENNReal.ofReal (R ^ (finrank ℝ E / p.toReal)) *
          eLpNorm f p)) := by gcongr
    _ = C * ENNReal.ofReal (R ^ ((k : ℝ) + finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹))) *
          eLpNorm f p := by
        rw [← hexp, ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]
        ring

/-- **Bernstein's inequality** at order `0`: for `1 ≤ p ≤ q ≤ ∞` there is `C` such that every
Schwartz function `f` whose Fourier transform vanishes outside the closed ball of radius `R > 0`
satisfies `‖f‖_q ≤ C R ^ (d (1/p - 1/q)) ‖f‖_p`, where `d` is the dimension of `E` and `1/p`
stands for `p.toReal⁻¹`. -/
theorem exists_eLpNorm_le_of_support_fourier_subset {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ≥0, ∀ {R : ℝ}, 0 < R → ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ closedBall 0 R →
      eLpNorm f q ≤
        C * ENNReal.ofReal (R ^ (finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹))) * eLpNorm f p := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_iteratedFDeriv_le_of_support_fourier_subset (E := E) (F := F)
    0 hp hpq
  refine ⟨C, fun hR f hf => ?_⟩
  have h := hC hR f hf
  rwa [Nat.cast_zero, zero_add, eLpNorm_congr_norm_ae
    (f.smooth 0).continuous_iteratedFDeriv'.aestronglyMeasurable f.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => norm_iteratedFDeriv_zero)] at h

/-! ### The reverse Bernstein inequality on an annulus -/

/-- A Schwartz function with frequencies in the annulus `1 ≤ ‖ξ‖ ≤ θ` is a sum of Fourier
multipliers with Schwartz symbols applied to its partial derivatives: on the annulus, the
symbols agree with `⟪bᵢ, ξ⟫ / (2πi ‖ξ‖²)`, and `∑ᵢ ⟪bᵢ, ξ⟫ ⟪ξ, bᵢ⟫ / ‖ξ‖² = 1`. -/
private theorem exists_eq_sum_fourierMultiplierCLM_lineDerivOp (θ : ℝ) :
    ∃ σ : Fin (finrank ℝ E) → 𝓢(E, ℂ), ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        f = ∑ i, fourierMultiplierCLM F (σ i) (∂_{stdOrthonormalBasis ℝ E i} f) := by
  let b := stdOrthonormalBasis ℝ E
  let m (i : Fin (finrank ℝ E)) (ξ : E) : ℂ :=
    (2 * Real.pi * Complex.I)⁻¹ * ((inner ℝ (b i) ξ / ‖ξ‖ ^ 2 : ℝ) : ℂ)
  have hm (i : Fin (finrank ℝ E)) : ContDiffOn ℝ (⊤ : ℕ∞) (m i) {0}ᶜ := by
    refine contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn ?_)
    exact (innerSL ℝ (b i)).contDiff.contDiffOn.div (contDiff_norm_sq ℝ).contDiffOn
      fun ξ hξ => pow_ne_zero 2 (norm_ne_zero_iff.2 hξ)
  choose σ hσ using fun i => exists_eqOn_annulus_of_contDiffOn (hm i) θ
  refine ⟨σ, fun f hf => ?_⟩
  have hv (v : E) : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  have key : 𝓕 f = 𝓕 (∑ i, fourierMultiplierCLM F (σ i) (∂_{b i} f)) := by
    rw [FourierTransform.fourier_sum]
    ext ξ
    simp only [sum_apply, fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
      smulLeftCLM_apply_apply (σ _).hasTemperateGrowth, fourier_lineDerivOp_eq, smul_apply,
      smulLeftCLM_apply_apply (hv _)]
    by_cases h0 : (𝓕 f : 𝓢(E, F)) ξ = 0
    · simp [h0]
    · have hξ := hf h0
      have hξ0 : ‖ξ‖ ≠ 0 := by linarith [hξ.1]
      simp_rw [hσ _ hξ]
      have hterm (i : Fin (finrank ℝ E)) :
          m i ξ • (2 * (Real.pi : ℂ) * Complex.I) • inner ℝ ξ (b i) • (𝓕 f : 𝓢(E, F)) ξ =
            ((inner ℝ (b i) ξ ^ 2 / ‖ξ‖ ^ 2 : ℝ) : ℂ) • (𝓕 f : 𝓢(E, F)) ξ := by
        rw [← Complex.coe_smul, smul_smul, smul_smul]
        congr 1
        simp only [m, real_inner_comm ξ (b i)]
        push_cast
        field_simp
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul, ← Complex.ofReal_sum,
        ← Finset.sum_div, b.sum_sq_inner_right, div_self (pow_ne_zero 2 hξ0), Complex.ofReal_one,
        one_smul]
  simpa using congrArg 𝓕⁻ key

/-- The reverse Bernstein inequality for the first partial derivatives, at frequency scale `1`. -/
private theorem exists_eLpNorm_le_sum_eLpNorm_lineDerivOp (θ : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        eLpNorm f p ≤ C * ∑ i, eLpNorm ⇑(∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E, F)) p := by
  obtain ⟨σ, hσ⟩ := exists_eq_sum_fourierMultiplierCLM_lineDerivOp (E := E) (F := F) θ
  -- Each multiplier is bounded on `Lᵖ` by the `L¹` norm of its Schwartz kernel `𝓕⁻ σᵢ`.
  have hfin (i : Fin (finrank ℝ E)) : eLpNorm (𝓕⁻ (σ i : E → ℂ)) 1 ≠ ∞ := by
    rw [← fourierInv_coe]
    exact ((𝓕⁻ (σ i) : 𝓢(E, ℂ)).memLp 1).eLpNorm_ne_top
  let C (i : Fin (finrank ℝ E)) : ℝ≥0 := (eLpNorm (𝓕⁻ (σ i : E → ℂ)) 1).toNNReal
  refine ⟨∑ i, C i, fun f hf => ?_⟩
  set b := stdOrthonormalBasis ℝ E
  have h (i : Fin (finrank ℝ E)) :
      eLpNorm ⇑(fourierMultiplierCLM F (σ i) (∂_{b i} f)) p ≤
        C i * eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p := by
    rw [ENNReal.coe_toNNReal (hfin i)]
    exact eLpNorm_fourierMultiplierCLM_le _ _ hp
  let g (i : Fin (finrank ℝ E)) : E → F := ⇑(fourierMultiplierCLM F (σ i) (∂_{b i} f))
  have h1 : eLpNorm f p = eLpNorm (∑ i, g i) p := by
    conv_lhs => rw [hσ f hf]
    congr 1
    ext x
    simp [g, sum_apply]
  have h2 : eLpNorm (∑ i, g i) p ≤ ∑ i, eLpNorm (g i) p := eLpNorm_sum_le hp
  have h3 (i : Fin (finrank ℝ E)) : eLpNorm (g i) p ≤
      (∑ j, (C j : ℝ≥0∞)) * eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p := by
    refine (h i).trans ?_
    gcongr
    exact Finset.single_le_sum (f := fun j => (C j : ℝ≥0∞)) (fun _ _ => zero_le)
      (Finset.mem_univ i)
  calc eLpNorm f p ≤ ∑ i, (∑ j, (C j : ℝ≥0∞)) * eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p :=
        h1.trans_le (h2.trans (Finset.sum_le_sum fun i _ => h3 i))
    _ = ((∑ i, C i : ℝ≥0) : ℝ≥0∞) * ∑ i, eLpNorm ⇑(∂_{b i} f : 𝓢(E, F)) p := by
        push_cast
        rw [Finset.mul_sum]

/-- The reverse Bernstein inequality for the iterated partial derivatives of order `k`, at
frequency scale `1`. -/
private theorem exists_eLpNorm_le_sum_eLpNorm_iteratedLineDerivOp (θ : ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        eLpNorm f p ≤ C * ∑ r : Fin k → Fin (finrank ℝ E),
          eLpNorm ⇑(∂^{fun j => stdOrthonormalBasis ℝ E (r j)} f : 𝓢(E, F)) p := by
  set b := stdOrthonormalBasis ℝ E
  induction k with
  | zero =>
    refine ⟨1, fun f _ => ?_⟩
    simp [iteratedLineDerivOp_fin_zero]
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_le_sum_eLpNorm_lineDerivOp (E := E) (F := F) θ hp
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * C₁, fun f hf => ?_⟩
    -- Reindex the pairs `(i, r)` as the tuples `Fin.cons i r`.
    have hre : ∑ r : Fin k → Fin (finrank ℝ E), ∑ i,
          eLpNorm ⇑(∂_{b i} (∂^{fun j => b (r j)} f) : 𝓢(E, F)) p =
        ∑ r : Fin (k + 1) → Fin (finrank ℝ E), eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p := by
      rw [← (Fin.consEquiv fun _ => Fin (finrank ℝ E)).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
      -- The tuple `Fin.cons i r` has head `i` and tail `r`.
      rw [iteratedLineDerivOp_succ_left]
      rfl
    calc eLpNorm f p
        ≤ C * ∑ r : Fin k → Fin (finrank ℝ E), eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p :=
          hC f hf
      _ ≤ C * ∑ r : Fin k → Fin (finrank ℝ E),
            C₁ * ∑ i, eLpNorm ⇑(∂_{b i} (∂^{fun j => b (r j)} f) : 𝓢(E, F)) p := by
          gcongr with r
          exact hC₁ _ ((support_fourier_iteratedLineDerivOp_subset f _).trans hf)
      _ = ((C * C₁ : ℝ≥0) : ℝ≥0∞) * ∑ r : Fin (k + 1) → Fin (finrank ℝ E),
            eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p := by
          rw [← hre, ← Finset.mul_sum, ENNReal.coe_mul, mul_assoc]

/-- The reverse Bernstein inequality for the iterated derivative, at frequency scale `1`. -/
private theorem exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_one_le_norm (θ : ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} →
        eLpNorm f p ≤ C * eLpNorm (iteratedFDeriv ℝ k f) p := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_sum_eLpNorm_iteratedLineDerivOp (E := E) (F := F) θ hp k
  refine ⟨C * Fintype.card (Fin k → Fin (finrank ℝ E)), fun f hf => ?_⟩
  set b := stdOrthonormalBasis ℝ E
  -- Each partial derivative along basis vectors is bounded by the full derivative.
  have h (r : Fin k → Fin (finrank ℝ E)) :
      eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p ≤ eLpNorm (iteratedFDeriv ℝ k f) p := by
    refine eLpNorm_mono (∂^{fun j => b (r j)} f).continuous.aestronglyMeasurable fun x => ?_
    rw [iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ k f x).le_opNorm _).trans_eq ?_
    simp [b.orthonormal.1]
  calc eLpNorm f p ≤ C * ∑ r : Fin k → Fin (finrank ℝ E),
        eLpNorm ⇑(∂^{fun j => b (r j)} f : 𝓢(E, F)) p := hC f hf
    _ ≤ C * ∑ _r : Fin k → Fin (finrank ℝ E), eLpNorm (iteratedFDeriv ℝ k f) p := by
        gcongr with r
        exact h r
    _ = ((C * Fintype.card (Fin k → Fin (finrank ℝ E)) : ℝ≥0) : ℝ≥0∞) *
          eLpNorm (iteratedFDeriv ℝ k f) p := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

/-- **The reverse Bernstein inequality.** For `1 ≤ p ≤ ∞`, `k : ℕ` and `θ : ℝ` there is `C` such
that every Schwartz function `f` whose Fourier transform vanishes outside the annulus
`R ≤ ‖ξ‖ ≤ θ R`, for some `R > 0`, satisfies `‖f‖_p ≤ C R ^ (-k) ‖Dᵏ f‖_p`. -/
theorem exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_support_fourier_subset (k : ℕ) (θ : ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ {R : ℝ}, 0 < R → ∀ f : 𝓢(E, F),
      Function.support ⇑(𝓕 f : 𝓢(E, F)) ⊆ {ξ | R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ * R} →
        eLpNorm f p ≤ C * ENNReal.ofReal (R⁻¹ ^ k) * eLpNorm (iteratedFDeriv ℝ k f) p := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_one_le_norm (E := E) (F := F) θ hp k
  refine ⟨C, fun {R} hR f hf => ?_⟩
  -- The dilation `f (R⁻¹ • ·)` has its frequencies in the annulus `1 ≤ ‖ξ‖ ≤ θ`.
  have hgsupp : Function.support ⇑(𝓕 (dilate R hR f) : 𝓢(E, F)) ⊆
      {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ θ} := by
    rw [support_fourier_dilate]
    rintro _ ⟨ξ, hξ, rfl⟩
    obtain ⟨h1, h2⟩ := hf hξ
    refine ⟨?_, ?_⟩ <;> rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
    exacts [(le_inv_mul_iff₀ hR).2 (by linarith), (inv_mul_le_iff₀ hR).2 (by linarith)]
  have hmain := hC _ hgsupp
  rw [eLpNorm_iteratedFDeriv_dilate, eLpNorm_dilate, ENNReal.ofReal_mul (by positivity)] at hmain
  have h0 : ENNReal.ofReal (R ^ (finrank ℝ E / p.toReal)) ≠ 0 := by
    simpa using Real.rpow_pos_of_pos hR _
  refine (ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top).1 ?_
  exact hmain.trans_eq (by ring)

end SchwartzMap
