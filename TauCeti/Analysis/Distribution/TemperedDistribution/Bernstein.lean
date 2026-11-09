/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.SchwartzSpace.Dilation
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The Bernstein inequalities

Let `f ∈ Lᵖ(E)`, `1 ≤ p ≤ ∞`, on a finite-dimensional real inner product space `E`, and suppose
that the Fourier transform of `f` (as a tempered distribution) vanishes outside the closed ball of
radius `R > 0`. Then the derivatives of `f` lie in `Lᵖ` and cost exactly one factor `R` each:

`‖∂ₘ f‖_p ≤ C R ‖m‖ ‖f‖_p`, and `‖∂_{m₁} ⋯ ∂_{mₙ} f‖_p ≤ (C R)ⁿ ‖m₁‖ ⋯ ‖mₙ‖ ‖f‖_p`,

with `C` depending only on `E` and the target space `F`, not on `p`, `R`, `f` or `n`. Conversely,
if the Fourier transform of `f` vanishes outside the closed annulus `a R ≤ ‖ξ‖ ≤ c R` with `a > 0`,
then the first derivatives are at least of size `R ‖f‖_p`: for an orthonormal basis `(bᵢ)` of `E`,

`‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖∂_{bᵢ} f‖_p`,

with `C` depending only on `E`, `F`, `a` and `c`, not on the basis. These are the estimates by
which the Littlewood–Paley blocks `Δⱼ f`
(`TemperedDistribution.isVanishingOn_fourier_littlewoodPaleyBlock`) trade derivatives for powers
of `2^j` in the dyadic description of Besov and Hölder spaces.

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

/-- **Bernstein's inequality.** There is `C ≥ 0`, depending only on `E` and `F`, such that
whenever the Fourier transform of `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, vanishes outside the closed ball of
radius `R > 0`, every derivative `∂ₘ f` is an `Lᵖ` function with `‖∂ₘ f‖_p ≤ C R ‖m‖ ‖f‖_p`. -/
theorem exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : E,
      ∃ g : Lp F p (volume : Measure E), ∂_{m} (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * R * ‖m‖ * ‖f‖ := by
  set θ : ContDiffBump (0 : E) := ⟨2, 3, two_pos, by norm_num⟩
  set θS : 𝓢(E, ℂ) :=
    (θ.hasCompactSupport.toSchwartzMap θ.contDiff).postcompCLM Complex.ofRealCLM
  refine ⟨∫ x, ‖fderiv ℝ ⇑(𝓕⁻ θS : 𝓢(E, ℂ)) x‖, integral_nonneg fun _ ↦ norm_nonneg _,
    fun {p} _ {R} hR f hf m ↦ ?_⟩
  set θR := SchwartzMap.dilate hR.ne' θS
  -- The symbol `2πi ⟪ξ, m⟫ θ (R⁻¹ • ξ)`, the dilate of the symbol of `∂_{R m} 𝓕⁻ θ`.
  set σ := SchwartzMap.dilate hR.ne' (𝓕 (∂_{R • m} (𝓕⁻ θS)))
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
    simp [θR, θS, θ.one_of_mem_closedBall this]
  have hσ : ∂_{m} (f : 𝓢'(E, F)) = fourierMultiplierCLM F σ f := by
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    rw [← fourierMultiplierCLM_eq_self_of_isVanishingOn θR.hasTemperateGrowth
      (isVanishingOn_fourier_lineDerivOp hf m) hθR,
      fourierMultiplierCLM_lineDerivOp θR.hasTemperateGrowth]
    congr 2
    funext ξ
    simp only [σ, θR, SchwartzMap.dilate_apply, SchwartzMap.fourier_lineDerivOp_apply,
      FourierTransform.fourier_fourierInv_eq, real_inner_smul_left, real_inner_smul_right,
      Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    push_cast
    field_simp
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ f
  refine ⟨g, hσ.trans hg, hgf.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg f))⟩
  rw [SchwartzMap.integral_norm_fourierInv_dilate, ← SchwartzMap.fourierInv_coe,
    FourierTransform.fourierInv_fourier_eq]
  refine (SchwartzMap.integral_norm_lineDerivOp_le _ (R • m)).trans_eq ?_
  rw [norm_smul, Real.norm_of_nonneg hR.le, mul_assoc]

/-- **Bernstein's inequality for derivatives of every order.** There is `C ≥ 0`, depending only on
`E` and `F`, such that whenever the Fourier transform of `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, vanishes outside the
closed ball of radius `R > 0`, every iterated derivative `∂_{m₀} ⋯ ∂_{m_{n-1}} f` is an `Lᵖ`
function of norm at most `(C R)ⁿ ‖m₀‖ ⋯ ‖m_{n-1}‖ ‖f‖_p`. -/
theorem exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ {n : ℕ} (m : Fin n → E),
      ∃ g : Lp F p (volume : Measure E), ∂^{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ (C * R) ^ n * (∏ i, ‖m i‖) * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn (E := E) (F := F)
  refine ⟨C, hC0, fun {p} _ {R} hR f hf n m ↦ ?_⟩
  induction n with
  | zero => exact ⟨f, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨g, hg, hgf⟩ := ih (Fin.tail m)
    obtain ⟨h, hh, hhg⟩ := hC hR g (hg ▸ isVanishingOn_fourier_iteratedLineDerivOp hf _) (m 0)
    refine ⟨h, by rw [iteratedLineDerivOp_succ_left, hg, hh], ?_⟩
    calc ‖h‖ ≤ C * R * ‖m 0‖ * ‖g‖ := hhg
      _ ≤ C * R * ‖m 0‖ * ((C * R) ^ n * (∏ i, ‖Fin.tail m i‖) * ‖f‖) := by
          gcongr
      _ = (C * R) ^ (n + 1) * (∏ i, ‖m i‖) * ‖f‖ := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail]
          ring

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
private theorem sum_mul_dilate_fourier_lineDerivOp_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {θ : E → ℝ} (hθ0 : θ 0 = 0) {q : 𝓢(E, ℂ)}
    (hq : ∀ η, q η = -(4 * (π : ℂ) ^ 2)⁻¹ * ((θ η / ‖η‖ ^ 2 : ℝ) : ℂ)) {R : ℝ} (hR : 0 < R)
    (ξ : E) :
    ∑ i, 2 * π * Complex.I *
        (⟪ξ, b i⟫ * SchwartzMap.dilate hR.ne' (𝓕 (∂_{R⁻¹ • b i} (𝓕⁻ q))) ξ) = θ (R⁻¹ • ξ) := by
  have hsum : ∑ i, ((⟪ξ, b i⟫ : ℝ) : ℂ) ^ 2 = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast b.sum_sq_inner_left ξ
  have hterm (i : ι) :
      2 * π * Complex.I * (⟪ξ, b i⟫ * SchwartzMap.dilate hR.ne' (𝓕 (∂_{R⁻¹ • b i} (𝓕⁻ q))) ξ) =
        (2 * π * Complex.I) ^ 2 * ((R : ℂ)⁻¹) ^ 2 * q (R⁻¹ • ξ) * ((⟪ξ, b i⟫ : ℝ) : ℂ) ^ 2 := by
    simp only [SchwartzMap.dilate_apply, SchwartzMap.fourier_lineDerivOp_apply,
      FourierTransform.fourier_fourierInv_eq, real_inner_smul_left, real_inner_smul_right,
      smul_eq_mul]
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
  simp only [mul_pow, Complex.I_sq]
  field_simp
  ring

/-- **The reverse Bernstein inequality.** Let `0 < a`. There is `C ≥ 0`, depending only on `E`,
`F`, `a` and `c`, such that for every orthonormal basis `(bᵢ)` of `E`, whenever the Fourier
transform of `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, vanishes outside the closed annulus `a R ≤ ‖ξ‖ ≤ c R`, `R > 0`,
and the derivatives `∂_{bᵢ} f` are the `Lᵖ` functions `gᵢ`, then `‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖gᵢ‖_p`. -/
theorem exists_norm_le_sum_norm_of_lineDerivOp_eq {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {p : ℝ≥0∞}
      [Fact (1 ≤ p)] {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) {ξ | a * R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ c * R}ᶜ →
      ∀ g : ι → Lp F p (volume : Measure E), (∀ i, ∂_{b i} (f : 𝓢'(E, F)) = g i) →
      ‖f‖ ≤ C * R⁻¹ * ∑ i, ‖g i‖ := by
  obtain ⟨θ, hθ, hθc, hθ0, hθ1⟩ :=
    TauCeti.exists_contDiff_annulus_cutoff (E := E) (by positivity : 0 < a / 2) (c + 1)
  -- Since `θ` vanishes near `0`, the quotient `θ η / ‖η‖²` is smooth.
  have hq : ContDiff ℝ ∞ (fun η ↦ θ η / ‖η‖ ^ 2) := contDiff_iff_contDiffAt.2 fun η ↦ by
    rcases eq_or_ne η 0 with rfl | hη
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hθ0] with x hx
      simp [hx]
    · exact hθ.contDiffAt.div (contDiff_norm_sq ℝ).contDiffAt
        (pow_ne_zero _ (norm_ne_zero_iff.2 hη))
  have hqc : HasCompactSupport fun η ↦ θ η / ‖η‖ ^ 2 :=
    hθc.mono fun η hη h ↦ hη (by simp [h])
  set θS : 𝓢(E, ℂ) := (hθc.toSchwartzMap hθ).postcompCLM Complex.ofRealCLM
  set qS : 𝓢(E, ℂ) :=
    (-(4 * (π : ℂ) ^ 2)⁻¹) • (hqc.toSchwartzMap hq).postcompCLM Complex.ofRealCLM
  set C := ∫ x, ‖fderiv ℝ ⇑(𝓕⁻ qS : 𝓢(E, ℂ)) x‖
  refine ⟨C, integral_nonneg fun _ ↦ norm_nonneg _, fun {ι} _ b {p} _ {R} hR f hf g hg ↦ ?_⟩
  set θR := SchwartzMap.dilate hR.ne' θS
  set σ : ι → 𝓢(E, ℂ) := fun i ↦ SchwartzMap.dilate hR.ne' (𝓕 (∂_{R⁻¹ • b i} (𝓕⁻ qS)))
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
    simp [θR, θS, hθ1 _ h₂ h₁]
  have hsymb (ξ : E) : ∑ i, 2 * π * Complex.I * (⟪ξ, b i⟫ * σ i ξ) = θR ξ := by
    rw [sum_mul_dilate_fourier_lineDerivOp_eq b hθ0.self_of_nhds (fun η ↦ ?_) hR ξ]
    · simp [θR, θS]
    · simp [qS]
  refine (norm_le_sum_of_sum_mul_eq (fun i ↦ b i) θR σ hsymb f hrep g hg).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [SchwartzMap.integral_norm_fourierInv_dilate, ← SchwartzMap.fourierInv_coe,
    FourierTransform.fourierInv_fourier_eq]
  refine (SchwartzMap.integral_norm_lineDerivOp_le _ _).trans_eq ?_
  rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]

end TemperedDistribution
