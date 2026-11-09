/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv

/-!
# Pseudodifferential kernels are smooth off the diagonal

The left quantization of a symbol `a ∈ S^m_{1,0}` on `ℝⁿ` is formally the integral operator with
kernel `K_a(x, y) = ∫ exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ) dζ`. For `m < -n` this integral converges
absolutely (`TauCeti.quantizationKernel`); in general it does not, and `K_a` is only a distribution.
Away from the diagonal it is nevertheless a smooth function, by repeated integration by parts in the
frequency: multiplying the kernel by `-‖x - y‖²` replaces `a` by its frequency Laplacian `Δ_ξ a`,
a symbol of order `m - 2`, so `K_a(x, y) = (-‖x - y‖²)⁻ᴺ K_{Δ_ξ^N a}(x, y)` where the right side
converges absolutely as soon as `m - 2N < -n`, and is `C^k` as soon as `m - 2N + k < -n`.

## Main results

* `TauCeti.contDiff_quantizationKernel_of_bound` and `TauCeti.Symbol.contDiff_quantizationKernel`:
  the kernel of a coefficient of order `m` is `C^k` when `m + k < -n`; each derivative of the
  integrand in `(x, y)` costs one power of the frequency.
* `TauCeti.Symbol.quantizationKernel_frequencyLaplacian`: for `m < -n`, the kernel of `Δ_ξ a` is
  `-‖x - y‖² K_a(x, y)`; `TauCeti.Symbol.quantizationKernel_iteratedFrequencyLaplacian` iterates
  this.
* `TauCeti.Symbol.quantizeSchwartzValue_frequencyDeriv`,
  `TauCeti.Symbol.quantizeSchwartzValue_iteratedFrequencyLaplacian`: the same identities for the
  operators, for symbols of every order: `Op(∂_{ξ_j} a) w (x) = -i Op(a) ((x - ·)_j w) (x)` and
  `Op(Δ_ξ^N a) w (x) = Op(a) ((-‖x - ·‖²)^N w) (x)` on Schwartz functions `w`.
* `TauCeti.Symbol.offDiagonalKernel`: the kernel `K_a(x, y)` of a symbol of any order for `x ≠ y`,
  with the formula `TauCeti.Symbol.offDiagonalKernel_eq` for every admissible `N`; it agrees with
  `TauCeti.quantizationKernel` when `m < -n`
  (`TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel`).
* `TauCeti.Symbol.contDiffOn_offDiagonalKernel`: **the kernel is smooth off the diagonal.**
* `TauCeti.Symbol.norm_offDiagonalKernel_le`: `‖K_a(x, y)‖ ≤ C_{x,N} ‖x - y‖⁻²ᴺ` for every `N`
  with `m - 2N < -n`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`: **kernel representation**,
  `Op(a) u (x) = ∫ K_a(x, y) u(y) dy` for compactly supported Schwartz `u` vanishing near `x`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ContDiff
open MeasureTheory Real Module

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The phase `(x, y) ↦ 2πi ⟪ζ, x - y⟫` of the kernel integrand at the frequency `ζ`, a real-linear
map to `ℂ` of norm at most `2 ‖2πζ‖`. -/
private def kernelPhase (ζ : E) : E × E →L[ℝ] ℂ :=
  ((2 * π : ℂ) * Complex.I) • (Complex.ofRealCLM ∘L (innerSL ℝ ζ) ∘L
    (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem kernelPhase_apply (ζ : E) (p : E × E) :
    kernelPhase ζ p = ((2 * π * ⟪ζ, p.1 - p.2⟫ : ℝ) : ℂ) * Complex.I := by
  simp [kernelPhase, inner_sub_right]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem exp_kernelPhase (ζ : E) (p : E × E) :
    Complex.exp (kernelPhase ζ p) = 𝐞 ⟪ζ, p.1 - p.2⟫ := by
  rw [kernelPhase_apply, Real.fourierChar_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_kernelPhase_le (ζ : E) : ‖kernelPhase ζ‖ ≤ 2 * ‖(2 * π) • ζ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p ↦ ?_
  rw [kernelPhase_apply, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos two_pi_pos, norm_smul, Real.norm_of_nonneg two_pi_pos.le]
  have hp : ‖p.1 - p.2‖ ≤ 2 * ‖p‖ := (norm_sub_le _ _).trans (by
    linarith [norm_fst_le p, norm_snd_le p])
  calc 2 * π * |⟪ζ, p.1 - p.2⟫| ≤ 2 * π * (‖ζ‖ * ‖p.1 - p.2‖) := by
        gcongr; exact abs_real_inner_le_norm _ _
    _ ≤ 2 * π * (‖ζ‖ * (2 * ‖p‖)) := by gcongr
    _ = 2 * (2 * π * ‖ζ‖) * ‖p‖ := by ring

/-- **Smoothness of the kernel.** Let `a` be a `C^k` coefficient whose position derivatives of
order at most `k` satisfy `‖D_x^i a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m`, uniformly for `x` in each compact set
`K`, with `m + k < -n`. Then the kernel `(x, y) ↦ K_a(x, y)` is `C^k`: each derivative of the
integrand `exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ)` in `(x, y)` costs at most one power of `⟨2πζ⟩`. -/
theorem contDiff_quantizationKernel_of_bound {a : E × E → V →L[ℂ] W} {k : ℕ} {m : ℝ}
    (ha : ContDiff ℝ k a) (hm : m + k < -finrank ℝ E)
    (hC : ∀ K : Set E, IsCompact K → ∃ C, ∀ i ≤ k, ∀ x ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun y ↦ a (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    ContDiff ℝ k (Function.uncurry (quantizationKernel a)) := by
  -- Near each point `p₀`, Mathlib's `hasFTaylorSeriesUpToOn_integral_of_le_bound` differentiates
  -- under the integral sign `k` times. Its hypotheses are measurability of the derivatives of the
  -- integrand in the frequency, the Leibniz bound `C (1 + 2 ‖2πζ‖) ^ i ⟨2πζ⟩ ^ m` on the `i`-th
  -- derivative for positions near `p₀`, and integrability of these bounds since `m + k < -n`.
  -- The integrand `F p ζ` as a jointly `C^k` function of the kernel variables `p = (x, y)` and the
  -- frequency `ζ`.
  obtain ⟨F, hF⟩ : ∃ F : E × E → E → V →L[ℂ] W,
      F = fun p ζ ↦ Complex.exp (kernelPhase ζ p) • a (p.1, (2 * π) • ζ) := ⟨_, rfl⟩
  have hK : Function.uncurry (quantizationKernel a) = fun p ↦ ∫ ζ, F p ζ := by
    funext p
    simp only [Function.uncurry_def, quantizationKernel_def, hF, exp_kernelPhase, Circle.smul_def]
  have hΦ : ContDiff ℝ k fun q : (E × E) × E ↦ F q.1 q.2 := by
    have hphase : ContDiff ℝ k fun q : (E × E) × E ↦ (2 * π * ⟪q.2, q.1.1 - q.1.2⟫ : ℝ) :=
      contDiff_const.mul (contDiff_snd.inner ℝ
        ((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst)))
    simp only [hF, kernelPhase_apply]
    exact ((Complex.ofRealCLM.contDiff.comp hphase).mul contDiff_const).cexp.smul
      (ha.comp ((contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.const_smul _)))
  have hslice (ζ : E) : ContDiff ℝ k fun p ↦ F p ζ :=
    hΦ.comp (contDiff_id.prodMk contDiff_const)
  rw [hK, contDiff_iff_contDiffAt]
  intro p₀
  obtain ⟨C, hC⟩ := hC _ (isCompact_closedBall p₀.1 1)
  have hs : IsOpen (Prod.fst ⁻¹' Metric.ball p₀.1 1 : Set (E × E)) :=
    Metric.isOpen_ball.preimage continuous_fst
  -- The derivatives of the slice `p ↦ F p ζ` are those of the jointly smooth integrand.
  have hslice_deriv (ζ : E) (i : ℕ) (hi : i ≤ k) (p : E × E) :
      iteratedFDeriv ℝ i (F · ζ) p = (iteratedFDeriv ℝ i (fun q : (E × E) × E ↦ F q.1 q.2)
        (p, ζ)).compContinuousLinearMap fun _ ↦ ContinuousLinearMap.inl ℝ (E × E) E := by
    have h : (F · ζ) = (fun q : (E × E) × E ↦ F (q + (0, ζ)).1 (q + (0, ζ)).2) ∘
        ContinuousLinearMap.inl ℝ (E × E) E := by
      funext p
      simp
    have hg : ContDiff ℝ k fun q : (E × E) × E ↦ F (q + (0, ζ)).1 (q + (0, ζ)).2 :=
      hΦ.comp (contDiff_id.add contDiff_const)
    have hshift := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun q : (E × E) × E ↦ F q.1 q.2)
      i (0, ζ) (ContinuousLinearMap.inl ℝ (E × E) E p)
    rw [h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (mod_cast hi), hshift]
    simp
  -- The bound on the derivatives of the slices, for positions in `closedBall p₀.1 1`.
  have hbound (ζ : E) (p : E × E) (hp : p.1 ∈ Metric.closedBall p₀.1 1) (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (F · ζ) p‖ ≤
        C * (1 + 2 * ‖(2 * π) • ζ‖) ^ i * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) := by
    set ξ := (2 * π) • ζ
    have he : ContDiff ℝ i fun p ↦ Complex.exp (kernelPhase ζ p) :=
      (kernelPhase ζ).contDiff.cexp
    have hg : ContDiff ℝ i fun y : E ↦ a (y, ξ) :=
      (ha.of_le (mod_cast hi)).comp (contDiff_id.prodMk contDiff_const)
    have hF' : (F · ζ) = fun p ↦ Complex.exp (kernelPhase ζ p) • a (p.1, ξ) := by
      rw [hF]
    -- The `j`-th derivative of the phase factor is at most `(2 ‖ξ‖) ^ j`.
    have he_le (j : ℕ) : ‖iteratedFDeriv ℝ j (fun p ↦ Complex.exp (kernelPhase ζ p)) p‖ ≤
        (2 * ‖ξ‖) ^ j := by
      refine ((kernelPhase ζ).norm_iteratedFDeriv_cexp_comp_le j p).trans ?_
      rw [exp_kernelPhase, Circle.norm_coe, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_kernelPhase_le ζ) j
    -- The `r`-th derivative of the coefficient factor is at most `C ⟨ξ⟩ ^ m`.
    have hg_le (r : ℕ) (hr : r ≤ i) : ‖iteratedFDeriv ℝ r (fun p : E × E ↦ a (p.1, ξ)) p‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
      have hcomp := (ContinuousLinearMap.fst ℝ E E).iteratedFDeriv_comp_right hg p
        (i := r) (mod_cast hr)
      simp only [Function.comp_def, ContinuousLinearMap.coe_fst'] at hcomp
      rw [hcomp]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      refine (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
        (ContinuousLinearMap.norm_fst_le ℝ E E))).trans ?_
      exact hC r (hr.trans hi) p.1 hp ξ
    rw [hF']
    refine (norm_iteratedFDeriv_smul_le he (hg.comp contDiff_fst) p le_rfl).trans ?_
    calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (fun p ↦ Complex.exp (kernelPhase ζ p)) p‖ *
          ‖iteratedFDeriv ℝ (i - j) (fun p : E × E ↦ a (p.1, ξ)) p‖
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 * ‖ξ‖) ^ j *
          (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          gcongr with j hj
          · exact he_le j
          · exact hg_le (i - j) (Nat.sub_le i j)
      _ = C * (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
          rw [← Finset.sum_mul, show 1 + 2 * ‖ξ‖ = 2 * ‖ξ‖ + 1 by ring, add_pow]
          simp only [one_pow, mul_one]
          rw [Finset.sum_congr rfl fun j _ ↦ mul_comm ((i.choose j : ℝ)) ((2 * ‖ξ‖) ^ j)]
          ring
  have hT := hasFTaylorSeriesUpToOn_integral_of_le_bound (μ := volume) (F := F)
    (s := Prod.fst ⁻¹' Metric.ball p₀.1 1) (n := (k : ℕ∞))
    (p := fun p ζ ↦ ftaylorSeries ℝ (F · ζ) p)
    (bound := fun i ζ ↦ C * (1 + 2 * ‖(2 * π) • ζ‖) ^ i * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2))
    hs (fun p _ i hi ↦ ?_) (ae_of_all _ fun ζ p hp i hi ↦ ?_) (fun i hi ↦ ?_)
    (ae_of_all _ fun ζ ↦ (contDiff_iff_ftaylorSeries.1 (hslice ζ)).hasFTaylorSeriesUpToOn _)
  · exact hT.contDiffOn.contDiffAt (hs.mem_nhds (Metric.mem_ball_self one_pos))
  · -- measurability: the derivatives of the slices are continuous in the frequency
    have hi' : i ≤ k := by exact_mod_cast hi
    -- Instance synthesis does not find the pseudo-metrizable structure of these multilinear maps
    -- on the product `E × E`, although their topology is the one of their norm.
    have : TopologicalSpace.PseudoMetrizableSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ E × E) (V →L[ℂ] W)) :=
      @PseudoEMetricSpace.pseudoMetrizableSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ E × E) (V →L[ℂ] W)) _
    simp only [ftaylorSeries, hslice_deriv _ i hi' p]
    exact ((ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
      ((hΦ.continuous_iteratedFDeriv (mod_cast hi')).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact hbound ζ p (Metric.ball_subset_closedBall hp) i (by exact_mod_cast hi)
  · -- integrability: `(1 + 2 ‖ξ‖) ^ i ⟨ξ⟩ ^ m ≤ 3 ^ i ⟨ξ⟩ ^ (m + i)` with `m + i < -n`
    have hi' : (i : ℝ) ≤ k := by exact_mod_cast hi
    have hint := (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure E))
      (r := -(m + i)) (by linarith)).const_mul (|C| * 3 ^ i)
    refine (Integrable.mono' (f := fun ξ : E ↦ C * (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
      hint ?_ (ae_of_all _ fun ξ ↦ ?_)).comp_smul two_pi_pos.ne'
    · have hcont : Continuous fun ξ : E ↦ C * (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
        Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun ξ ↦
          Or.inl (by positivity))
      exact hcont.aestronglyMeasurable
    · have hw : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
      have hsqrt : 1 + 2 * ‖ξ‖ ≤ 3 * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        have h1 : 1 ≤ √(1 + ‖ξ‖ ^ 2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖ξ‖])
        have h2 : ‖ξ‖ ≤ √(1 + ‖ξ‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
        linarith
      have hpow : (1 + 2 * ‖ξ‖) ^ i ≤ 3 ^ i * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) := by
        rw [div_eq_mul_one_div (i : ℝ), mul_comm (i : ℝ), Real.rpow_mul hw.le, Real.rpow_natCast,
          ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hsqrt i
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity), neg_neg, mul_assoc, mul_assoc |C|]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
      calc (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2)
          ≤ 3 ^ i * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by gcongr
        _ = 3 ^ i * (1 + ‖ξ‖ ^ 2) ^ ((m + i) / 2) := by
          rw [mul_assoc, ← Real.rpow_add hw]
          ring_nf

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- **Smoothness of the kernel of a symbol.** The kernel of a symbol of order `m` is `C^k` as soon
as `m + k < -n`. -/
theorem contDiff_quantizationKernel (b : Symbol n V W m) (k : ℕ) (hk : m + k < -n) :
    ContDiff ℝ k (Function.uncurry (quantizationKernel b.coefficient)) := by
  refine contDiff_quantizationKernel_of_bound (b.contDiff_coefficient.of_le (mod_cast le_top))
    (by simpa using hk) fun K hK ↦ ?_
  choose C hC0 hC using fun α : List (Fin n) ↦ b.exists_bound K hK α []
  refine ⟨∑ i ∈ Finset.range (k + 1), ∑ r : Fin i → Fin n, C (List.ofFn r),
    fun i hi x hx ξ ↦ ?_⟩
  have hslice : ContDiff ℝ i fun y ↦ b.coefficient (y, ξ) :=
    (b.contDiff_coefficient_slice ξ).of_le (mod_cast le_top)
  refine (norm_iteratedFDeriv_le_sum_coordinateDeriv hslice x).trans ?_
  calc ∑ r : Fin i → Fin n, ‖coordinateDeriv (List.ofFn r) (fun y ↦ b.coefficient (y, ξ)) x‖
      ≤ ∑ r : Fin i → Fin n, C (List.ofFn r) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
        Finset.sum_le_sum fun r _ ↦ by simpa [mixedDeriv_def] using hC (List.ofFn r) x hx ξ
    _ = (∑ r : Fin i → Fin n, C (List.ofFn r)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (k + 1), ∑ r : Fin i → Fin n, C (List.ofFn r)) *
        (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        gcongr
        exact Finset.single_le_sum (f := fun i ↦ ∑ r : Fin i → Fin n, C (List.ofFn r))
          (fun i _ ↦ Finset.sum_nonneg fun r _ ↦ hC0 _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-! ### The frequency Laplacian and multiplication by `‖x - y‖²` -/

/-- **Kernel of the frequency Laplacian.** For a symbol of order `m < -n`, the kernel of `Δ_ξ a` is
`-‖x - y‖² K_a(x, y)`. -/
theorem quantizationKernel_frequencyLaplacian (a : Symbol n V W m) (hm : m < -n)
    (x y : CoordinateSpace n) :
    quantizationKernel (frequencyLaplacian a).coefficient x y =
      (-‖x - y‖ ^ 2) • quantizationKernel a.coefficient x y := by
  rw [coefficient_frequencyLaplacian_eq_sum,
    quantizationKernel_sum _ fun j _ ↦ integrable_coefficient _ (by linarith) x]
  simp only [quantizationKernel_frequencyDeriv _ (by linarith : m - 1 < -n),
    quantizationKernel_frequencyDeriv _ hm, smul_smul, ← Finset.sum_smul]
  rw [← Complex.coe_smul, EuclideanSpace.real_norm_sq_eq]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination ((x - y) j : ℂ) ^ 2 * Complex.I_sq

/-- **Kernel of the iterated frequency Laplacian.** For a symbol of order `m < -n`, the kernel of
`Δ_ξ^N a` is `(-‖x - y‖²)^N K_a(x, y)`. -/
theorem quantizationKernel_iteratedFrequencyLaplacian (a : Symbol n V W m) (hm : m < -n) (N : ℕ)
    (x y : CoordinateSpace n) :
    quantizationKernel (iteratedFrequencyLaplacian N a).coefficient x y =
      (-‖x - y‖ ^ 2) ^ N • quantizationKernel a.coefficient x y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [coefficient_iteratedFrequencyLaplacian_succ,
      quantizationKernel_frequencyLaplacian _ (by linarith), ih, smul_smul, ← pow_succ']

/-! ### Multiplication of the input by the displacement -/

/-- **Frequency derivatives and multiplication by the displacement.** For a symbol `a` and a
Schwartz function `w`, `Op(∂_{ξ_j} a) w (x) = -i Op(a) ((x - ·)_j w) (x)`. This is the operator form
of `TauCeti.Symbol.quantizationKernel_frequencyDeriv`, valid for symbols of every order: on the
Fourier side, multiplying `w` by `(x - y)_j` differentiates `𝓕 w`, and an integration by parts in
the frequency moves this derivative onto `exp(2πi ⟪ζ, x⟫) a(x, 2πζ)`. -/
theorem quantizeSchwartzValue_frequencyDeriv (a : Symbol n V W m) (j : Fin n)
    (w : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (frequencyDeriv j a).coefficient w x =
      -Complex.I • quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (x - y) j) w) x := by
  set v : CoordinateSpace n := EuclideanSpace.single j 1
  set c : ℂ := 2 * π * Complex.I * x j
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le {x} isCompact_singleton
  obtain ⟨C', hC'⟩ := (frequencyDeriv j a).exists_norm_coefficient_le {x} isCompact_singleton
  have hI := integrable_quantizeSchwartzValue_integrand
    (a.continuous_coefficient_slice x).aestronglyMeasurable (hC x rfl)
  have hI' := integrable_quantizeSchwartzValue_integrand
    ((frequencyDeriv j a).continuous_coefficient_slice x).aestronglyMeasurable (hC' x rfl)
  -- `w₁ y = ⟪y, v⟫ w y = y_j w y`, whose Fourier transform is `(-2πi)⁻¹ ∂_v 𝓕 w`.
  have htg : (fun y : CoordinateSpace n ↦ ⟪y, v⟫).HasTemperateGrowth := by fun_prop
  set w₁ := SchwartzMap.smulLeftCLM V (⟪·, v⟫) w
  have hw₁ : ∂_{v} (𝓕 w) = -(2 * π * Complex.I) • 𝓕 w₁ := by
    rw [SchwartzMap.lineDerivOp_fourier_eq, FourierTransform.fourier_smul]
  have hM : SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (x - y) j) w =
      (x j : ℂ) • w + (-1 : ℂ) • w₁ := by
    have htg' : (fun y : CoordinateSpace n ↦ (x - y) j).HasTemperateGrowth := by
      convert (Function.HasTemperateGrowth.const (x j)).sub
        (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).hasTemperateGrowth using 1
      funext y
      simp
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply htg', add_apply, smul_apply,
      smul_apply, SchwartzMap.smulLeftCLM_apply_apply htg]
    simp [v, add_smul, neg_smul, Complex.coe_smul, EuclideanSpace.inner_single_right,
      sub_eq_add_neg]
  -- The character `ζ ↦ 𝐞 ⟪ζ, x⟫` has line derivative `c 𝐞 ⟪ζ, x⟫` along `v`.
  have hf (ζ : CoordinateSpace n) :
      HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) (c * 𝐞 ⟪ζ, x⟫) ζ v := by
    convert (Real.differentiable_fourierChar_neg_bilinear_left (innerSL ℝ) (-x)
      ζ).hasFDerivAt.hasLineDerivAt v using 1
    · simp only [innerSL_apply_apply ℝ, inner_neg_right, neg_neg]
    · rw [Real.fderiv_fourierChar_neg_bilinear_left_apply]
      simp only [innerSL_apply_apply ℝ, inner_neg_right, neg_neg, Complex.ofReal_neg, c, v,
        EuclideanSpace.inner_single_left, map_one, one_mul]
      ring
  -- The amplitude `ζ ↦ a(x, 2πζ) (𝓕 w ζ)` has the product-rule line derivative.
  have hg (ζ : CoordinateSpace n) : HasLineDerivAt ℝ
      (fun ζ ↦ a.coefficient (x, (2 * π) • ζ) (𝓕 w ζ))
      ((2 * π) • (frequencyDeriv j a).coefficient (x, (2 * π) • ζ) (𝓕 w ζ) +
        a.coefficient (x, (2 * π) • ζ) (∂_{v} (𝓕 w) ζ)) ζ v := by
    have hda : HasLineDerivAt ℝ (fun ξ ↦ a.coefficient (x, ξ))
        ((frequencyDeriv j a).coefficient (x, (2 * π) • ζ)) ((2 * π) • ζ) v := by
      rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]
      exact ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).differentiable
        (by simp) _).hasFDerivAt.hasLineDerivAt _
    have hA : HasLineDerivAt ℝ (fun ζ ↦ a.coefficient (x, (2 * π) • ζ))
        ((2 * π) • (frequencyDeriv j a).coefficient (x, (2 * π) • ζ)) ζ v := by
      simpa only [HasLineDerivAt, smul_add, smul_comm (2 * π) _ v] using hda.smul (2 * π)
    have hB : HasLineDerivAt ℝ (fun ζ ↦ 𝓕 w ζ) (∂_{v} (𝓕 w) ζ) ζ v := by
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact ((𝓕 w).differentiableAt).hasFDerivAt.hasLineDerivAt v
    unfold HasLineDerivAt at hA hB ⊢
    have h := ((ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).hasFDerivAt.comp_hasDerivAt _
      hA).clm_apply hB
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars', smul_apply, zero_smul,
      add_zero] using h
  -- Integrate by parts: `∫ 𝐞 ⟪ζ, x⟫ g'(ζ) = -c ∫ 𝐞 ⟪ζ, x⟫ g(ζ)`.
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (f := fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) (f' := fun ζ ↦ c * 𝐞 ⟪ζ, x⟫)
    (g := fun ζ ↦ a.coefficient (x, (2 * π) • ζ) (𝓕 w ζ))
    (g' := fun ζ ↦ (2 * π) • (frequencyDeriv j a).coefficient (x, (2 * π) • ζ) (𝓕 w ζ) +
        a.coefficient (x, (2 * π) • ζ) (∂_{v} (𝓕 w) ζ))
    (((hI (𝓕 w)).smul c).congr (ae_of_all _ fun ζ ↦ by
      simp only [Pi.smul_apply, ContinuousLinearMap.lsmul_apply, Circle.smul_def, smul_smul]))
    ((((hI' (𝓕 w)).smul (2 * π)).add (hI (∂_{v} (𝓕 w)))).congr (ae_of_all _ fun ζ ↦ by
      simp only [Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.lsmul_apply, Circle.smul_def,
        smul_add, smul_comm (2 * π : ℝ) ((𝐞 ⟪ζ, x⟫ : ℂ))]))
    ((hI (𝓕 w)).congr (ae_of_all _ fun ζ ↦ by
      simp only [ContinuousLinearMap.lsmul_apply, Circle.smul_def]))
    (fun ζ _ ↦ hf ζ) (fun ζ _ ↦ hg ζ)
  simp only [ContinuousLinearMap.lsmul_apply] at hparts
  -- Identify the three integrals with quantizations.
  have hL : ∫ ζ, (𝐞 ⟪ζ, x⟫ : ℂ) •
      ((2 * π) • (frequencyDeriv j a).coefficient (x, (2 * π) • ζ) (𝓕 w ζ) +
        a.coefficient (x, (2 * π) • ζ) (∂_{v} (𝓕 w) ζ)) =
      (2 * π) • quantizeSchwartzValue (frequencyDeriv j a).coefficient w x +
        (-(2 * π * Complex.I)) • quantizeSchwartzValue a.coefficient w₁ x := by
    have h₁ : Integrable fun ζ ↦ (2 * π) •
        (𝐞 ⟪ζ, x⟫ • (frequencyDeriv j a).coefficient (x, (2 * π) • ζ) (𝓕 w ζ)) :=
      (hI' (𝓕 w)).smul (2 * π)
    have h₂ : Integrable fun ζ ↦ (-(2 * π * Complex.I)) •
        (𝐞 ⟪ζ, x⟫ • a.coefficient (x, (2 * π) • ζ) (𝓕 w₁ ζ)) :=
      (hI (𝓕 w₁)).smul _
    rw [quantizeSchwartzValue_def, quantizeSchwartzValue_def, ← integral_smul, ← integral_smul,
      ← integral_add h₁ h₂]
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    simp only [hw₁, smul_apply, map_smul, Circle.smul_def, smul_add,
      smul_comm (2 * π : ℝ) ((𝐞 ⟪ζ, x⟫ : ℂ)), smul_comm (-(2 * π * Complex.I)) ((𝐞 ⟪ζ, x⟫ : ℂ))]
  have hR : ∫ ζ, (c * 𝐞 ⟪ζ, x⟫) • a.coefficient (x, (2 * π) • ζ) (𝓕 w ζ) =
      c • quantizeSchwartzValue a.coefficient w x := by
    rw [quantizeSchwartzValue_def, ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    simp only [Circle.smul_def, smul_smul]
  rw [hL, hR] at hparts
  rw [hM, quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable
    (hC x rfl), quantizeSchwartzValue_smul_right, quantizeSchwartzValue_smul_right]
  -- `hparts : 2π Op(∂_j a) w - 2πi Op(a) w₁ = -2πi x_j Op(a) w`; solve for `Op(∂_j a) w`.
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos.ne'
  apply smul_right_injective W h2π
  simp only [← Complex.coe_smul] at hparts
  push_cast at hparts
  simp only [c] at hparts
  linear_combination (norm := module) hparts

/-- The multiplier `y ↦ -‖x - y‖²` has temperate growth. -/
private theorem hasTemperateGrowth_neg_norm_sub_sq (x : CoordinateSpace n) :
    (fun y : CoordinateSpace n ↦ -‖x - y‖ ^ 2).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.comp (Function.hasTemperateGrowth_norm_sq (CoordinateSpace n))
    ((Function.HasTemperateGrowth.const x).sub Function.HasTemperateGrowth.id')).neg

/-- The multiplier `y ↦ (-‖x - y‖²)^N` has temperate growth. -/
private theorem hasTemperateGrowth_neg_norm_sub_sq_pow (x : CoordinateSpace n) (N : ℕ) :
    (fun y : CoordinateSpace n ↦ (-‖x - y‖ ^ 2) ^ N).HasTemperateGrowth :=
  (hasTemperateGrowth_neg_norm_sub_sq x).pow N

/-- **The frequency Laplacian and multiplication by `-‖x - ·‖²`.** For a symbol `a` and a Schwartz
function `w`, `Op(Δ_ξ a) w (x) = Op(a) (-‖x - ·‖² w) (x)`. -/
theorem quantizeSchwartzValue_frequencyLaplacian (a : Symbol n V W m)
    (w : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (frequencyLaplacian a).coefficient w x =
      quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ -‖x - y‖ ^ 2) w) x := by
  -- `u ↦ Op(a) u (x)` as a linear map, to distribute it over a finite sum of inputs.
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le {x} isCompact_singleton
  let L : 𝓢(CoordinateSpace n, V) →ₗ[ℂ] W :=
    { toFun := fun u ↦ quantizeSchwartzValue a.coefficient u x
      map_add' := quantizeSchwartzValue_add_right
        (a.continuous_coefficient_slice x).aestronglyMeasurable (hC x rfl)
      map_smul' := fun c u ↦ quantizeSchwartzValue_smul_right c u }
  have htg (j : Fin n) : (fun y : CoordinateSpace n ↦ (x - y) j).HasTemperateGrowth := by
    convert (Function.HasTemperateGrowth.const (x j)).sub
      (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).hasTemperateGrowth using 1
    funext y
    simp
  -- The multiplier `-‖x - y‖²` is `-∑ⱼ (x - y)_j²`.
  have hsum : SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ -‖x - y‖ ^ 2) w =
      ∑ j, (-1 : ℂ) • SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (x - y) j)
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (x - y) j) w) := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_neg_norm_sub_sq x),
      EuclideanSpace.real_norm_sq_eq, sum_apply, neg_smul, Finset.sum_smul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_apply, neg_one_smul, SchwartzMap.smulLeftCLM_apply_apply (htg j),
      SchwartzMap.smulLeftCLM_apply_apply (htg j), smul_smul, sq]
  have hq : ∀ j, quantizeSchwartzValue (frequencyDeriv j (frequencyDeriv j a)).coefficient w x =
      L ((-1 : ℂ) • SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (x - y) j)
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (x - y) j) w)) := fun j ↦ by
    rw [quantizeSchwartzValue_frequencyDeriv, quantizeSchwartzValue_frequencyDeriv, smul_smul,
      map_smul]
    congr 1
    simp
  have hI (j : Fin n) : Integrable fun ζ ↦ 𝐞 ⟪ζ, x⟫ •
      (frequencyDeriv j (frequencyDeriv j a)).coefficient (x, (2 * π) • ζ) (𝓕 w ζ) := by
    obtain ⟨C', hC'⟩ := (frequencyDeriv j (frequencyDeriv j a)).exists_norm_coefficient_le {x}
      isCompact_singleton
    exact integrable_quantizeSchwartzValue_integrand
      ((frequencyDeriv j (frequencyDeriv j a)).continuous_coefficient_slice x).aestronglyMeasurable
      (hC' x rfl) _
  calc quantizeSchwartzValue (frequencyLaplacian a).coefficient w x
      = ∑ j, quantizeSchwartzValue (frequencyDeriv j (frequencyDeriv j a)).coefficient w x := by
        simp only [quantizeSchwartzValue_def, coefficient_frequencyLaplacian_eq_sum,
          Finset.sum_apply, sum_apply, Finset.smul_sum]
        exact integral_finsetSum _ fun j _ ↦ hI j
    _ = L (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ -‖x - y‖ ^ 2) w) := by
        rw [hsum, map_sum]
        exact Finset.sum_congr rfl fun j _ ↦ hq j

/-- **Iterated frequency Laplacians and multiplication by `(-‖x - ·‖²)^N`.** For a symbol `a` and a
Schwartz function `w`, `Op(Δ_ξ^N a) w (x) = Op(a) ((-‖x - ·‖²)^N w) (x)`. -/
theorem quantizeSchwartzValue_iteratedFrequencyLaplacian (a : Symbol n V W m) (N : ℕ)
    (w : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (iteratedFrequencyLaplacian N a).coefficient w x =
      quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (-‖x - y‖ ^ 2) ^ N) w) x := by
  induction N generalizing w with
  | zero => simp
  | succ N ih =>
    rw [coefficient_iteratedFrequencyLaplacian_succ, quantizeSchwartzValue_frequencyLaplacian, ih,
      SchwartzMap.smulLeftCLM_smulLeftCLM_apply (hasTemperateGrowth_neg_norm_sub_sq_pow x N)
        (hasTemperateGrowth_neg_norm_sub_sq x),
      show ((fun y : CoordinateSpace n ↦ (-‖x - y‖ ^ 2) ^ N) * fun y ↦ -‖x - y‖ ^ 2) =
        fun y ↦ (-‖x - y‖ ^ 2) ^ (N + 1) from funext fun y ↦ (pow_succ _ _).symm]

/-! ### The kernel off the diagonal -/

/-- `N = ⌊(m + n) / 2⌋ + 1` frequency Laplacians bring the order `m` below `-n`. -/
private theorem sub_two_mul_floor_add_one_lt (n : ℕ) (m : ℝ) :
    m - 2 * ((⌊(m + n) / 2⌋₊ + 1 : ℕ) : ℝ) < -n := by
  have := Nat.lt_floor_add_one ((m + n) / 2)
  push_cast
  linarith

/-- The kernel `K_a(x, y)` of the quantization of a symbol `a` of order `m`, off the diagonal
`x = y`. For any `N` with `m - 2N < -n`, the symbol `Δ_ξ^N a` has an absolutely convergent kernel,
and `K_a(x, y) = (-‖x - y‖²)⁻ᴺ K_{Δ_ξ^N a}(x, y)` (`TauCeti.Symbol.offDiagonalKernel_eq`); when
`m < -n` this is the kernel `TauCeti.quantizationKernel` itself
(`TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel`), and for every order it represents
`Op(a)` away from the diagonal
(`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`). The definition uses
`N = ⌊(m + n) / 2⌋ + 1`. On the diagonal the kernel of a general symbol is singular, and the value
`0` given by this formula there is a convention. -/
def offDiagonalKernel (a : Symbol n V W m) (x y : CoordinateSpace n) : V →L[ℂ] W :=
  ((-‖x - y‖ ^ 2) ^ (⌊(m + n) / 2⌋₊ + 1))⁻¹ •
    quantizationKernel (iteratedFrequencyLaplacian (⌊(m + n) / 2⌋₊ + 1) a).coefficient x y

theorem offDiagonalKernel_def (a : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel a x y = ((-‖x - y‖ ^ 2) ^ (⌊(m + n) / 2⌋₊ + 1))⁻¹ •
      quantizationKernel (iteratedFrequencyLaplacian (⌊(m + n) / 2⌋₊ + 1) a).coefficient x y :=
  (rfl)

/-- Applying `M` more frequency Laplacians does not change the kernel formula off the diagonal. -/
private theorem inv_smul_quantizationKernel_iteratedFrequencyLaplacian_add (a : Symbol n V W m)
    {N : ℕ} (hN : m - 2 * N < -n) (M : ℕ) {x y : CoordinateSpace n} (hxy : x ≠ y) :
    ((-‖x - y‖ ^ 2) ^ (N + M))⁻¹ •
        quantizationKernel (iteratedFrequencyLaplacian (N + M) a).coefficient x y =
      ((-‖x - y‖ ^ 2) ^ N)⁻¹ •
        quantizationKernel (iteratedFrequencyLaplacian N a).coefficient x y := by
  have hr : -‖x - y‖ ^ 2 ≠ 0 :=
    neg_ne_zero.2 (pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)))
  rw [coefficient_iteratedFrequencyLaplacian_add,
    quantizationKernel_iteratedFrequencyLaplacian _ hN, smul_smul, pow_add, mul_inv,
    mul_assoc, inv_mul_cancel₀ (pow_ne_zero M hr), mul_one]

/-- **Kernel formula off the diagonal.** For every `N` with `m - 2N < -n` and `x ≠ y`, the kernel
of `a` is `(-‖x - y‖²)⁻ᴺ K_{Δ_ξ^N a}(x, y)`. -/
theorem offDiagonalKernel_eq (a : Symbol n V W m) {N : ℕ} (hN : m - 2 * N < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = ((-‖x - y‖ ^ 2) ^ N)⁻¹ •
      quantizationKernel (iteratedFrequencyLaplacian N a).coefficient x y := by
  rw [offDiagonalKernel_def, ← inv_smul_quantizationKernel_iteratedFrequencyLaplacian_add a
      (sub_two_mul_floor_add_one_lt n m) N hxy,
    ← inv_smul_quantizationKernel_iteratedFrequencyLaplacian_add a hN
      (⌊(m + n) / 2⌋₊ + 1) hxy, add_comm]

/-- For a symbol of order `m < -n`, the kernel off the diagonal is the absolutely convergent
kernel `K_a(x, y) = ∫ exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ) dζ`. -/
theorem offDiagonalKernel_eq_quantizationKernel (a : Symbol n V W m) (hm : m < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = quantizationKernel a.coefficient x y := by
  rw [offDiagonalKernel_eq a (N := 0) (by simpa using hm) hxy]
  simp

/-- **Pseudodifferential kernels are smooth off the diagonal.** The kernel of a symbol of any order
is smooth on `{(x, y) | x ≠ y}`. -/
theorem contDiffOn_offDiagonalKernel (a : Symbol n V W m) :
    ContDiffOn ℝ ∞ (Function.uncurry (offDiagonalKernel a)) {p | p.1 ≠ p.2} := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  -- Use `N` Laplacians, with `m - 2N + k < -n`, so that the kernel of `Δ_ξ^N a` is `C^k`.
  have hN := sub_two_mul_floor_add_one_lt n (m + k)
  set N := ⌊(m + k + n) / 2⌋₊ + 1
  have h₁ : ContDiffOn ℝ k (fun p : CoordinateSpace n × CoordinateSpace n ↦
      ((-‖p.1 - p.2‖ ^ 2) ^ N)⁻¹) {p | p.1 ≠ p.2} :=
    (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).neg.pow N).contDiffOn.inv
      fun p hp ↦ pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero 2
        (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))))
  have h₂ := ((iteratedFrequencyLaplacian N a).contDiff_quantizationKernel k
    (by linarith)).contDiffOn (s := {p | p.1 ≠ p.2})
  exact (h₁.smul h₂).congr fun p hp ↦ offDiagonalKernel_eq a (by linarith) hp

/-- **Decay off the diagonal.** For every `N` with `m - 2N < -n` and `x ≠ y`,
`‖K_a(x, y)‖ ≤ ‖x - y‖⁻²ᴺ (2π)⁻ⁿ ∫ ‖Δ_ξ^N a(x, ξ)‖ dξ`. In particular, for fixed `x` the kernel
decays faster than every power of `‖x - y‖`. -/
theorem norm_offDiagonalKernel_le (a : Symbol n V W m) {N : ℕ} (hN : m - 2 * N < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    ‖offDiagonalKernel a x y‖ ≤ (‖x - y‖ ^ (2 * N))⁻¹ *
      (((2 * π) ^ n)⁻¹ * ∫ ξ, ‖(iteratedFrequencyLaplacian N a).coefficient (x, ξ)‖) := by
  rw [offDiagonalKernel_eq a hN hxy, norm_smul, norm_inv, norm_pow, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), ← pow_mul]
  gcongr
  simpa using norm_quantizationKernel_le (iteratedFrequencyLaplacian N a).coefficient x y

/-- **Kernel representation off the diagonal.** For a symbol `a` of any order, a compactly
supported Schwartz function `u` and a point `x` outside the support of `u`,
`Op(a) u (x) = ∫ K_a(x, y) u(y) dy`. Thus `offDiagonalKernel a` is the distribution kernel of
`Op(a)` away from the diagonal. -/
theorem quantizeSchwartzValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u)
    {x : CoordinateSpace n} (hx : x ∉ tsupport u) :
    quantizeSchwartzValue a.coefficient u x = ∫ y, offDiagonalKernel a x y (u y) := by
  have hN := sub_two_mul_floor_add_one_lt n m
  set N := ⌊(m + n) / 2⌋₊ + 1
  have hux : ∀ y, y ∉ tsupport u → u y = 0 := fun y hy ↦ image_eq_zero_of_notMem_tsupport hy
  -- `w = (-‖x - ·‖²)⁻ᴺ u` is smooth, since `u` vanishes near `x`, and compactly supported.
  set g : CoordinateSpace n → ℝ := fun y ↦ ((-‖x - y‖ ^ 2) ^ N)⁻¹
  have hg : ContDiffOn ℝ ∞ g {y | y ≠ x} :=
    (((contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)).neg.pow N).contDiffOn.inv
      fun y hy ↦ pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero 2
        (norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hy)))))
  have hw_smooth : ContDiff ℝ ∞ fun y ↦ g y • u y := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ tsupport u
    · have hyx : y ≠ x := fun h ↦ hx (h ▸ hy)
      exact (hg.contDiffAt ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hyx)).smul
        (u.smooth ⊤).contDiffAt
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hy] with z hz
      rw [hux z hz, smul_zero]
  set w := (hu.smul_left (f := g)).toSchwartzMap hw_smooth
  have hw (y : CoordinateSpace n) : w y = g y • u y :=
    HasCompactSupport.toSchwartzMap_toFun _ _ y
  -- `(-‖x - ·‖²)ᴺ w = u`.
  have hwu : SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (-‖x - y‖ ^ 2) ^ N) w = u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_neg_norm_sub_sq_pow x N), hw,
      smul_smul]
    by_cases hy : y = x
    · rw [hy, hux x hx, smul_zero]
    · rw [mul_inv_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero 2
        (norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hy)))))), one_smul]
  conv_lhs => rw [← hwu]
  rw [← quantizeSchwartzValue_iteratedFrequencyLaplacian,
    quantizeSchwartzValue_eq_integral_quantizationKernel
      ((iteratedFrequencyLaplacian N a).integrable_coefficient hN x)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  by_cases hy : y = x
  · simp only [hw, hy, hux x hx, smul_zero, map_zero]
  · dsimp only
    rw [offDiagonalKernel_eq a hN (Ne.symm hy), hw, smul_apply,
      ContinuousLinearMap.map_smul_of_tower]

/-- The kernel off the diagonal is additive in the symbol. -/
@[simp]
theorem offDiagonalKernel_add (a b : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (a + b) x y = offDiagonalKernel a x y + offDiagonalKernel b x y := by
  have h := sub_two_mul_floor_add_one_lt n m
  simp only [offDiagonalKernel_def, map_add, coefficient_add, ← smul_add]
  rw [quantizationKernel_add (integrable_coefficient _ h x) (integrable_coefficient _ h x)]

/-- The kernel off the diagonal is homogeneous in the symbol. -/
@[simp]
theorem offDiagonalKernel_smul (c : ℂ) (a : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (c • a) x y = c • offDiagonalKernel a x y := by
  simp only [offDiagonalKernel_def, map_smul, coefficient_smul, quantizationKernel_smul]
  exact smul_comm _ _ _

end Symbol

end TauCeti
