/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# The Bernstein inequalities

Let `f ∈ Lᵖ(E)`, `1 ≤ p ≤ ∞`, on a finite-dimensional real inner product space `E`, and suppose
that the Fourier transform of `f` (as a tempered distribution) vanishes outside the closed ball of
radius `R > 0`. Then the derivatives of `f` lie in `Lᵖ` and cost exactly one factor `R` each:

`‖∂ₘ f‖_p ≤ C R ‖m‖ ‖f‖_p`, and `‖∂_{m₁} ⋯ ∂_{mₙ} f‖_p ≤ (C R)ⁿ ‖m₁‖ ⋯ ‖mₙ‖ ‖f‖_p`,

with `C` depending only on `E`, not on `p`, `R`, `f` or `n`. Conversely, if the Fourier transform
of `f` vanishes outside the closed annulus `a R ≤ ‖ξ‖ ≤ c R` with `a > 0`, then the first
derivatives are at least of size `R ‖f‖_p`: for an orthonormal basis `(bᵢ)` of `E`,

`‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖∂_{bᵢ} f‖_p`,

with `C` depending only on `E`, `a` and `c`. These are the estimates by which the Littlewood–Paley
blocks `Δⱼ f` (`TemperedDistribution.isVanishingOn_fourier_littlewoodPaleyBlock`) trade
derivatives for powers of `2^j` in the dyadic description of Besov and Hölder spaces.

The frequency localization is the vanishing of `𝓕 f` on the complement of the ball or annulus, in
the sense of `Distribution.IsVanishingOn`.

## Implementation notes

The proofs are by the reproducing property of a frequency cutoff. Fix a smooth bump `θ` equal to
`1` on the ball of radius `2`. The Fourier multiplier with symbol `θ (R⁻¹ •)` fixes `f`
(`TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`), so `∂ₘ f` is the Fourier
multiplier with symbol `2πi ⟪ξ, m⟫ θ (R⁻¹ • ξ)`. This symbol is the dilate by `R` of the Schwartz
symbol `2πi ⟪η, R m⟫ θ η`, whose kernel is `∂_{R m} 𝓕⁻ θ`; a dilation does not change the `L¹` norm
of the kernel, which is therefore at most `R ‖m‖ ‖∇ 𝓕⁻ θ‖₁`, and Young's inequality
(`TemperedDistribution.exists_fourierMultiplierCLM_eq_and_norm_le`) gives the bound. For the
reverse inequality the cutoff `θ` equals `1` near the annulus and vanishes near `0`, and
`θ (R⁻¹ • ξ) = ∑ᵢ 2πi ⟪ξ, bᵢ⟫ σᵢ(ξ)` with the Schwartz symbols
`σᵢ(ξ) = ⟪ξ, bᵢ⟫ θ (R⁻¹ • ξ) / (2πi ‖ξ‖²)`, so `f = ∑ᵢ T_{σᵢ} ∂_{bᵢ} f`.

## Main results

* `TemperedDistribution.exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn`: the Bernstein
  inequality `‖∂ₘ f‖_p ≤ C R ‖m‖ ‖f‖_p`.
* `TemperedDistribution.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn`: its iterate
  for derivatives of every order.
* `TemperedDistribution.exists_norm_le_sum_norm_of_lineDerivOp_eq`: the reverse Bernstein
  inequality `‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖∂_{bᵢ} f‖_p` for frequencies in an annulus.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.1.
-/

public section

open Filter Metric Set Topology MeasureTheory
open FourierTransform LineDeriv
open Distribution (IsVanishingOn)
open scoped SchwartzMap ENNReal Real RealInnerProductSpace ContDiff

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A smooth compactly supported real function, as a complex Schwartz function. -/
private noncomputable def ofRealSchwartz {θ : E → ℝ} (h₁ : HasCompactSupport θ)
    (h₂ : ContDiff ℝ ∞ θ) : 𝓢(E, ℂ) :=
  (h₁.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp h₂)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem ofRealSchwartz_apply {θ : E → ℝ} (h₁ : HasCompactSupport θ)
    (h₂ : ContDiff ℝ ∞ θ) (ξ : E) : ofRealSchwartz h₁ h₂ ξ = θ ξ :=
  rfl

/-- The derivative symbol `ξ ↦ 2πi ⟪ξ, m⟫ θ ξ`, defined as the Fourier transform of the derivative
`∂ₘ 𝓕⁻ θ` of the kernel of `θ`. -/
private noncomputable def derivSymbol (θ : 𝓢(E, ℂ)) (m : E) : 𝓢(E, ℂ) :=
  𝓕 (∂_{m} (𝓕⁻ θ))

private theorem derivSymbol_apply (θ : 𝓢(E, ℂ)) (m ξ : E) :
    derivSymbol θ m ξ = 2 * π * Complex.I * ⟪ξ, m⟫ * θ ξ := by
  have : (inner ℝ · m : E → ℝ).HasTemperateGrowth := by fun_prop
  simp [derivSymbol, SchwartzMap.lineDerivOp_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply this, mul_assoc]

/-- The kernel `∂ₘ 𝓕⁻ θ` of the derivative symbol has `L¹` norm at most `‖∇ 𝓕⁻ θ‖₁ ‖m‖`. -/
private theorem integral_norm_fourierInv_derivSymbol_le (θ : 𝓢(E, ℂ)) (m : E) :
    ∫ x, ‖𝓕⁻ (derivSymbol θ m : E → ℂ) x‖ ≤
      (∫ x, ‖fderiv ℝ ⇑(𝓕⁻ θ : 𝓢(E, ℂ)) x‖) * ‖m‖ := by
  have h : 𝓕⁻ (derivSymbol θ m : E → ℂ) = ∂_{m} (𝓕⁻ θ) := by
    rw [← SchwartzMap.fourierInv_coe, derivSymbol, FourierTransform.fourierInv_fourier_eq]
  rw [h]
  refine (integral_mono (SchwartzMap.integrable _).norm
    ((SchwartzMap.fderivCLM ℝ E ℂ (𝓕⁻ θ)).integrable.norm.mul_const _) fun x ↦ ?_).trans_eq
    (integral_mul_const _ _)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact (fderiv ℝ ⇑(𝓕⁻ θ : 𝓢(E, ℂ)) x).le_opNorm m

/-- The dilate `ξ ↦ σ (R⁻¹ • ξ)` of a Schwartz function. -/
private noncomputable def dilate {R : ℝ} (hR : R ≠ 0) (σ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 R⁻¹ (inv_ne_zero hR))) σ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem dilate_apply {R : ℝ} (hR : R ≠ 0) (σ : 𝓢(E, ℂ)) (ξ : E) :
    dilate hR σ ξ = σ (R⁻¹ • ξ) := by
  simp [dilate, Units.smul_def]

/-- Dilating a symbol does not change the `L¹` norm of its kernel. -/
private theorem integral_norm_fourierInv_dilate {R : ℝ} (hR : R ≠ 0) (σ : 𝓢(E, ℂ)) :
    ∫ x, ‖𝓕⁻ (dilate hR σ : E → ℂ) x‖ = ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖ := by
  rw [show (dilate hR σ : E → ℂ) = fun ξ ↦ σ (R⁻¹ • ξ) from funext (dilate_apply hR σ)]
  exact TauCeti.integral_norm_fourierInv_comp_smul _ (inv_ne_zero hR)

/-- **Bernstein's inequality.** There is `C`, depending only on `E`, such that whenever the
Fourier transform of `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, vanishes outside the closed ball of radius `R > 0`,
every derivative `∂ₘ f` is an `Lᵖ` function with `‖∂ₘ f‖_p ≤ C R ‖m‖ ‖f‖_p`. -/
theorem exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : E,
      ∃ g : Lp F p (volume : Measure E), ∂_{m} (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * R * ‖m‖ * ‖f‖ := by
  set θ : ContDiffBump (0 : E) := ⟨2, 3, two_pos, by norm_num⟩
  set θS := ofRealSchwartz θ.hasCompactSupport θ.contDiff
  refine ⟨∫ x, ‖fderiv ℝ ⇑(𝓕⁻ θS : 𝓢(E, ℂ)) x‖, fun {p} _ {R} hR f hf m ↦ ?_⟩
  set θR := dilate hR.ne' θS
  set σ := dilate hR.ne' (derivSymbol θS (R • m))
  -- The cutoff `θ (R⁻¹ •)` equals `1` on the ball of radius `2R`, a neighbourhood of the
  -- frequency support, so it reproduces `∂ₘ f`; and `2πi ⟪ξ, m⟫ θ (R⁻¹ • ξ)` is `σ`.
  have hθR : ∀ᶠ ξ in 𝓝ˢ (closedBall (0 : E) R)ᶜᶜ, θR ξ = 1 := by
    rw [compl_compl]
    filter_upwards [isOpen_ball.mem_nhdsSet.2
      (closedBall_subset_ball (by linarith : R < 2 * R))] with ξ hξ
    have : R⁻¹ • ξ ∈ closedBall (0 : E) 2 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
        inv_mul_le_iff₀ hR]
      exact (mem_ball_zero_iff.1 hξ).le.trans_eq (mul_comm _ _)
    simp [θR, dilate_apply, θS, ofRealSchwartz_apply, θ.one_of_mem_closedBall this]
  have hσ : ∂_{m} (f : 𝓢'(E, F)) = fourierMultiplierCLM F σ f := by
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    rw [← fourierMultiplierCLM_eq_self_of_isVanishingOn θR.hasTemperateGrowth
      (isVanishingOn_fourier_lineDerivOp hf m) hθR,
      fourierMultiplierCLM_lineDerivOp θR.hasTemperateGrowth]
    congr 2
    funext ξ
    simp only [σ, θR, dilate_apply, derivSymbol_apply, real_inner_smul_left,
      real_inner_smul_right, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    push_cast
    field_simp
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ f
  refine ⟨g, hσ.trans hg, hgf.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg f))⟩
  rw [integral_norm_fourierInv_dilate]
  refine (integral_norm_fourierInv_derivSymbol_le θS (R • m)).trans_eq ?_
  rw [norm_smul, Real.norm_of_nonneg hR.le, mul_assoc]

/-- **Bernstein's inequality for derivatives of every order.** There is `C`, depending only on
`E`, such that whenever the Fourier transform of `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, vanishes outside the
closed ball of radius `R > 0`, every iterated derivative `∂_{m₀} ⋯ ∂_{m_{n-1}} f` is an `Lᵖ`
function of norm at most `(C R)ⁿ ‖m₀‖ ⋯ ‖m_{n-1}‖ ‖f‖_p`. -/
theorem exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ {n : ℕ} (m : Fin n → E),
      ∃ g : Lp F p (volume : Measure E), ∂^{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ (C * R) ^ n * (∏ i, ‖m i‖) * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn (E := E) (F := F)
  refine ⟨max C 0, fun {p} _ {R} hR f hf n m ↦ ?_⟩
  induction n with
  | zero => exact ⟨f, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨g, hg, hgf⟩ := ih (Fin.tail m)
    obtain ⟨h, hh, hhg⟩ := hC hR g (hg ▸ isVanishingOn_fourier_iteratedLineDerivOp hf _) (m 0)
    refine ⟨h, by rw [iteratedLineDerivOp_succ_left, hg, hh], ?_⟩
    calc ‖h‖ ≤ max C 0 * R * ‖m 0‖ * ‖g‖ := by
          refine hhg.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg g))
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * R * ‖m 0‖ * ((max C 0 * R) ^ n * (∏ i, ‖Fin.tail m i‖) * ‖f‖) := by
          gcongr
      _ = (max C 0 * R) ^ (n + 1) * (∏ i, ‖m i‖) * ‖f‖ := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail]
          ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth compactly supported cutoff `θ` equal to `1` on the shell `a / 2 ≤ ‖η‖ ≤ c + 1` and
vanishing near `0`, so that `θ η / ‖η‖²` is smooth as well. -/
private theorem exists_annulus_cutoff {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∃ θ : E → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ θ 0 = 0 ∧
      ContDiff ℝ ∞ (fun η ↦ θ η / ‖η‖ ^ 2) ∧ ∀ η : E, a / 2 ≤ ‖η‖ → ‖η‖ ≤ c + 1 → θ η = 1 := by
  set c' := max c a + 1
  have hc' : 0 < c' := by positivity
  set θ₁ : ContDiffBump (0 : E) := ⟨c', c' + 1, hc', by linarith⟩
  set θ₂ : ContDiffBump (0 : E) := ⟨a / 3, a / 2, by positivity, by linarith⟩
  have hθ : ContDiff ℝ ∞ fun η ↦ θ₁ η - θ₂ η := θ₁.contDiff.sub θ₂.contDiff
  have h0 (η : E) (hη : η ∈ ball (0 : E) (a / 3)) : θ₁ η - θ₂ η = 0 := by
    have h₁ : η ∈ closedBall (0 : E) c' :=
      closedBall_subset_closedBall (by linarith [le_max_right c a]) (ball_subset_closedBall hη)
    simp [θ₁.one_of_mem_closedBall h₁, θ₂.one_of_mem_closedBall (ball_subset_closedBall hη)]
  refine ⟨fun η ↦ θ₁ η - θ₂ η, hθ, θ₁.hasCompactSupport.sub θ₂.hasCompactSupport,
    h0 0 (mem_ball_self (by positivity)), contDiff_iff_contDiffAt.2 fun η ↦ ?_,
    fun η h₂ h₁ ↦ ?_⟩
  · -- Near `0` the quotient vanishes identically; elsewhere `‖η‖² ≠ 0`.
    rcases eq_or_ne η 0 with rfl | hη
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds (0 : E) (by positivity : 0 < a / 3)] with x hx
      simp [h0 x hx]
    · exact hθ.contDiffAt.div (contDiff_norm_sq ℝ).contDiffAt
        (pow_ne_zero _ (norm_ne_zero_iff.2 hη))
  · have h₁' : η ∈ closedBall (0 : E) c' :=
      mem_closedBall_zero_iff.2 (h₁.trans (by linarith [le_max_left c a]))
    simp [θ₁.one_of_mem_closedBall h₁', θ₂.zero_of_le_dist (by rwa [dist_zero_right])]

/-- **The reverse Bernstein identity.** Let the symbols `σᵢ` satisfy
`∑ᵢ 2πi ⟪ξ, vᵢ⟫ σᵢ(ξ) = θ ξ`, where the multiplier with symbol `θ` fixes `f`. Then
`f = ∑ᵢ T_{σᵢ} ∂_{vᵢ} f`, so `‖f‖_p ≤ ∑ᵢ ‖𝓕⁻ σᵢ‖₁ ‖∂_{vᵢ} f‖_p`. -/
private theorem norm_le_sum_of_sum_mul_eq {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (v : ι → E) (θ : 𝓢(E, ℂ)) (σ : ι → 𝓢(E, ℂ))
    (hθ : ∀ ξ, ∑ i, 2 * π * Complex.I * (⟪ξ, v i⟫ * σ i ξ) = θ ξ)
    (f : Lp F p (volume : Measure E)) (hf : fourierMultiplierCLM F θ (f : 𝓢'(E, F)) = f)
    (g : ι → Lp F p (volume : Measure E)) (hg : ∀ i, ∂_{v i} (f : 𝓢'(E, F)) = g i) :
    ‖f‖ ≤ ∑ i, (∫ x, ‖𝓕⁻ (σ i : E → ℂ) x‖) * ‖g i‖ := by
  set G : ι → E → ℂ := fun i ↦ (2 * π * Complex.I) • ((fun ξ ↦ ((⟪ξ, v i⟫ : ℝ) : ℂ)) * ⇑(σ i))
  have hG (i : ι) : (G i).HasTemperateGrowth := by
    have := (σ i).hasTemperateGrowth
    simp only [G]
    fun_prop
  choose h hh hhg using fun i ↦ exists_fourierMultiplierCLM_eq_and_norm_le (σ i) (g i)
  have hfh : f = ∑ i, h i := by
    refine LinearMap.ker_eq_bot.1 (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F)
      (μ := (volume : Measure E)) (p := p)) ?_
    simp only [ContinuousLinearMap.coe_coe, map_sum, Lp.toTemperedDistributionCLM_apply]
    calc (f : 𝓢'(E, F)) = fourierMultiplierCLM F (fun ξ ↦ ∑ i, G i ξ) f := by
          simp only [G, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hθ, hf]
      _ = ∑ i, (h i : 𝓢'(E, F)) := by
          rw [fourierMultiplierCLM_sum F fun i _ ↦ hG i, sum_apply]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← hh i, ← hg i, fourierMultiplierCLM_lineDerivOp (σ i).hasTemperateGrowth]
  calc ‖f‖ = ‖∑ i, h i‖ := congrArg norm hfh
    _ ≤ ∑ i, ‖h i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (∫ x, ‖𝓕⁻ (σ i : E → ℂ) x‖) * ‖g i‖ := Finset.sum_le_sum fun i _ ↦ hhg i

omit [CompleteSpace F] in
/-- The symbols of the reverse Bernstein inequality: if `q η = -θ η / (4π² ‖η‖²)` with `θ 0 = 0`,
then `∑ᵢ 2πi ⟪ξ, bᵢ⟫ σᵢ(ξ) = θ (R⁻¹ • ξ)` for the dilated derivative symbols
`σᵢ(ξ) = 2πi ⟪R⁻¹ • ξ, R⁻¹ • bᵢ⟫ q (R⁻¹ • ξ)`. -/
private theorem sum_mul_derivSymbol_dilate {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {θ : E → ℝ} (hθ0 : θ 0 = 0) {q : 𝓢(E, ℂ)}
    (hq : ∀ η, q η = -(4 * (π : ℂ) ^ 2)⁻¹ * ((θ η / ‖η‖ ^ 2 : ℝ) : ℂ)) {R : ℝ} (hR : 0 < R)
    (ξ : E) :
    ∑ i, 2 * π * Complex.I * (⟪ξ, b i⟫ * dilate hR.ne' (derivSymbol q (R⁻¹ • b i)) ξ) =
      θ (R⁻¹ • ξ) := by
  have hsum : ∑ i, ((⟪ξ, b i⟫ : ℝ) : ℂ) ^ 2 = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast b.sum_sq_inner_left ξ
  have hterm (i : ι) :
      2 * π * Complex.I * (⟪ξ, b i⟫ * dilate hR.ne' (derivSymbol q (R⁻¹ • b i)) ξ) =
        (2 * π * Complex.I) ^ 2 * ((R : ℂ)⁻¹) ^ 2 * q (R⁻¹ • ξ) * ((⟪ξ, b i⟫ : ℝ) : ℂ) ^ 2 := by
    simp only [dilate_apply, derivSymbol_apply, real_inner_smul_left, real_inner_smul_right]
    push_cast
    ring
  simp_rw [hterm, ← Finset.mul_sum, hsum, hq]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hθ0]
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hξ' : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hξ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- **The reverse Bernstein inequality.** Let `(bᵢ)` be an orthonormal basis of `E` and `0 < a`.
There is `C`, depending only on `E`, `a` and `c`, such that whenever the Fourier transform of
`f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, vanishes outside the closed annulus `a R ≤ ‖ξ‖ ≤ c R`, `R > 0`, and the
derivatives `∂_{bᵢ} f` are the `Lᵖ` functions `gᵢ`, then `‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖gᵢ‖_p`. -/
theorem exists_norm_le_sum_norm_of_lineDerivOp_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) {ξ | a * R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ c * R}ᶜ →
      ∀ g : ι → Lp F p (volume : Measure E), (∀ i, ∂_{b i} (f : 𝓢'(E, F)) = g i) →
      ‖f‖ ≤ C * R⁻¹ * ∑ i, ‖g i‖ := by
  obtain ⟨θ, hθ, hθc, hθ0, hq, hθ1⟩ := exists_annulus_cutoff (E := E) ha c
  set θS := ofRealSchwartz hθc hθ
  have hqc : HasCompactSupport fun η ↦ θ η / ‖η‖ ^ 2 :=
    hθc.mono fun η hη h ↦ hη (by simp [h])
  set qS : 𝓢(E, ℂ) := (-(4 * (π : ℂ) ^ 2)⁻¹) • ofRealSchwartz hqc hq
  set C := ∫ x, ‖fderiv ℝ ⇑(𝓕⁻ qS : 𝓢(E, ℂ)) x‖
  refine ⟨C, fun {p} _ {R} hR f hf g hg ↦ ?_⟩
  set θR := dilate hR.ne' θS
  set σ : ι → 𝓢(E, ℂ) := fun i ↦ dilate hR.ne' (derivSymbol qS (R⁻¹ • b i))
  -- `f` is reproduced by `θ (R⁻¹ •)`, which is `1` near the annulus `a R ≤ ‖ξ‖ ≤ c R`.
  have hrep : fourierMultiplierCLM F θR (f : 𝓢'(E, F)) = f := by
    refine fourierMultiplierCLM_eq_self_of_isVanishingOn θR.hasTemperateGrowth hf ?_
    rw [compl_compl]
    have hU : IsOpen ({ξ : E | a / 2 * R < ‖ξ‖} ∩ ball 0 ((c + 1) * R)) :=
      (isOpen_lt continuous_const continuous_norm).inter isOpen_ball
    have hsub : {ξ : E | a * R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ c * R} ⊆
        {ξ | a / 2 * R < ‖ξ‖} ∩ ball 0 ((c + 1) * R) :=
      fun ξ hξ ↦ ⟨by simp only [mem_ofPred_eq]; linarith [hξ.1, mul_pos ha hR],
        mem_ball_zero_iff.2 <| hξ.2.trans_lt (mul_lt_mul_of_pos_right (by linarith) hR)⟩
    filter_upwards [hU.mem_nhdsSet.2 hsub] with ξ hξ
    have hn : ‖R⁻¹ • ξ‖ = R⁻¹ * ‖ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
    have h₁ : ‖R⁻¹ • ξ‖ ≤ c + 1 := by
      rw [hn, inv_mul_le_iff₀ hR]
      exact (mem_ball_zero_iff.1 hξ.2).le.trans_eq (mul_comm _ _)
    have h₂ : a / 2 ≤ ‖R⁻¹ • ξ‖ := by
      rw [hn, le_inv_mul_iff₀ hR]
      exact (mul_comm _ _).trans_le hξ.1.le
    simp [θR, dilate_apply, θS, ofRealSchwartz_apply, hθ1 _ h₂ h₁]
  have hsymb (ξ : E) : ∑ i, 2 * π * Complex.I * (⟪ξ, b i⟫ * σ i ξ) = θR ξ := by
    rw [sum_mul_derivSymbol_dilate b hθ0 (fun η ↦ ?_) hR ξ]
    · simp [θR, dilate_apply, θS, ofRealSchwartz_apply]
    · simp [qS, ofRealSchwartz_apply]
  refine (norm_le_sum_of_sum_mul_eq (fun i ↦ b i) θR σ hsymb f hrep g hg).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [integral_norm_fourierInv_dilate]
  refine (integral_norm_fourierInv_derivSymbol_le qS _).trans_eq ?_
  rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]

end TemperedDistribution
