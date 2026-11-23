/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# The retarded Strichartz estimate for the wave equation with Besov forcing

On a nontrivial real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`,
`j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`) as symbols. The solution of the wave equation `∂ₜ²u - Δu = F`
with zero data at `t = -∞` is the retarded Duhamel integral

`u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`

(`TauCeti.waveSinPropagator`). Let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`,
with `2 < q < ∞`, and let `(q₁, r₁)` be wave-admissible with `2 < q₁ ≤ ∞`, with Hölder conjugates
`p₁` and `r₁'`. Put `γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. This file proves
the **retarded Strichartz estimate** for every integrable forcing term `F : ℝ → L²(E)`:

`‖u‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`

(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`), with `C`
independent of `F`. The right-hand side is a dyadic `ℓ¹` sum over the blocks of `F`, each measured
along the second pair. For the energy pair `(q₁, r₁) = (∞, 2)` it is
`∑ⱼ 2^{j(γ - 1)} ‖Pⱼ F‖_{L¹_t L²_x}`. The integral `u(t)` is a Bochner integral, which exists for
instance when `F` vanishes outside a bounded interval of times, since `‖D⁻¹ sin(τD)‖ ≤ |τ|`;
where it does not exist it is `0`, and the estimate is stated for this value.

## The argument

The frequency-localized estimate
(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le`)
controls the retarded integral of `Pⱼ Pⱼ G` by `2^{j(γ + γ₁ - 1)} ‖G‖_{L^{p₁}_t L^{r₁'}_x}` for
every integrable `G`, with the square `Pⱼ Pⱼ` of a block rather than the block itself. It is summed
over the blocks as follows.

* **Reassembling a block from squared blocks.** The function `Ψ = ∑ⱼ ψⱼ²` is positive and smooth
  on `E \ {0}`, and invariant under `ξ ↦ 2 ξ`. Let `Qₗ` be the multiplier whose symbol is a
  Schwartz function equal to `1 / Ψ` on the support of `ψₗ`, the dilate by `2^l` of a fixed one.
  Its kernel is the `L¹`-normalised dilate of a fixed Schwartz function, so `Qₗ` is bounded on
  `L^{r₁'}` uniformly in `l`. Since only the `ψⱼ` with `|j - l| < L` meet the support of `ψₗ`,
  `Pₗ = ∑_{|j - l| < L} Pⱼ Pⱼ Qₗ Pₗ`.
* **Summation.** At each time, `‖u(t)‖_r ≤ ∑ₗ ‖Pₗ u(t)‖_r`
  (`ContDiffBump.eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM`), and `Pₗ u(t)` is the
  sum over `|j - l| < L` of the retarded integrals of `Pⱼ Pⱼ (Qₗ Pₗ F)`. Minkowski's inequality in
  `L^q_t`, the frequency-localized estimate and the bound for `Qₗ` give
  `‖u‖_{L^q_t L^r_x} ≤ C ∑ₗ ∑_{|j - l| < L} 2^{j(γ + γ₁ - 1)} ‖Pₗ F‖_{L^{p₁}_t L^{r₁'}_x}`, and
  `2^{j(γ + γ₁ - 1)}` is comparable to `2^{l(γ + γ₁ - 1)}` for `|j - l| < L`.

## Main declarations

* `ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`: the
  retarded Strichartz estimate for the wave equation with forcing in the dyadic `ℓ¹` class.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap Topology
open MeasureTheory TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (φ : ContDiffBump (0 : E))

/-! ### The sum of the squares of the cutoffs -/

/-- The sum `Ψ ξ = ∑ⱼ ψⱼ ξ²` of the squares of the Littlewood–Paley cutoffs. -/
private def sumSq (ξ : E) : ℝ :=
  ∑' j : ℤ, φ.littlewoodPaley j ξ ^ 2

/-- If only the cutoffs indexed by `s` can be nonzero at `ξ`, then `Ψ ξ` is a finite sum. -/
private theorem sumSq_eq_sum {s : Finset ℤ} {ξ : E} (h : ∀ j ∉ s, φ.littlewoodPaley j ξ = 0) :
    φ.sumSq ξ = ∑ j ∈ s, φ.littlewoodPaley j ξ ^ 2 :=
  tsum_eq_sum fun j hj ↦ by rw [h j hj, sq, zero_mul]

/-- Near a point `ξ₀ ≠ 0`, only finitely many cutoffs are nonzero. -/
private theorem exists_finset_eventually_littlewoodPaley_eq_zero {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0) :
    ∃ s : Finset ℤ, ∀ᶠ ξ in 𝓝 ξ₀, ∀ j ∉ s, φ.littlewoodPaley j ξ = 0 := by
  set c := ‖ξ₀‖
  have hc : 0 < c := norm_pos_iff.2 hξ₀
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (2 * φ.rOut / c) one_lt_two
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (4 * c / φ.rIn) one_lt_two
  rw [div_lt_iff₀ hc] at ha
  rw [div_lt_iff₀ φ.rIn_pos] at hb
  refine ⟨Finset.Ioo (-(a : ℤ)) (b + 1), ?_⟩
  have hU : ∀ᶠ ξ in 𝓝 ξ₀, ‖ξ‖ ∈ Set.Ioo (c / 2) (2 * c) :=
    continuous_norm.continuousAt (x := ξ₀) (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hU] with ξ hξ j hj
  rw [Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hj
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  rcases hj with hj | hj
  · -- Low indices: `2^j φ.rOut ≤ c / 2 < ‖ξ‖`.
    refine φ.littlewoodPaley_eq_zero_of_le_norm (le_trans ?_ hξ.1.le)
    have h1 : (2 : ℝ) ^ j ≤ (2 ^ a)⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ one_le_two hj
    calc 2 ^ j * φ.rOut ≤ (2 ^ a)⁻¹ * φ.rOut := mul_le_mul_of_nonneg_right h1 φ.rOut_pos.le
      _ ≤ c / 2 := by rw [inv_mul_le_iff₀ h2a]; linarith
  · -- High indices: `‖ξ‖ < 2 c ≤ 2^{j - 1} φ.rIn`.
    refine φ.littlewoodPaley_eq_zero_of_norm_le (le_trans hξ.2.le ?_)
    have h1 : (2 : ℝ) ^ b ≤ 2 ^ (j - 1) := by
      rw [← zpow_natCast]
      exact zpow_le_zpow_right₀ one_le_two (by omega)
    nlinarith [mul_le_mul_of_nonneg_right h1 φ.rIn_pos.le]

/-- `Ψ` is positive away from the origin, where the cutoffs sum to `1`. -/
private theorem sumSq_pos {ξ : E} (hξ : ξ ≠ 0) : 0 < φ.sumSq ξ := by
  obtain ⟨s, hs⟩ := φ.exists_finset_eventually_littlewoodPaley_eq_zero hξ
  have hs := hs.self_of_nhds
  obtain ⟨j, hj⟩ : ∃ j, φ.littlewoodPaley j ξ ≠ 0 := by
    by_contra! h
    have h0 : HasSum (fun j ↦ φ.littlewoodPaley j ξ) 0 := by
      simp only [h]
      exact hasSum_zero
    exact one_ne_zero ((φ.hasSum_littlewoodPaley hξ).unique h0)
  have hjs : j ∈ s := by
    by_contra h
    exact hj (hs j h)
  rw [φ.sumSq_eq_sum hs]
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ ↦ sq_nonneg _) hjs)

/-- `Ψ` is smooth away from the origin, where it is locally a finite sum. -/
private theorem contDiffAt_sumSq {n : ℕ∞} {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0) :
    ContDiffAt ℝ n φ.sumSq ξ₀ := by
  obtain ⟨s, hs⟩ := φ.exists_finset_eventually_littlewoodPaley_eq_zero hξ₀
  exact (ContDiff.contDiffAt (ContDiff.sum fun j _ ↦ (φ.contDiff_littlewoodPaley j).pow 2)
    ).congr_of_eventuallyEq (hs.mono fun ξ hξ ↦ φ.sumSq_eq_sum hξ)

/-- `Ψ` is invariant under the dilations by powers of `2`. -/
private theorem sumSq_two_zpow_inv_smul (l : ℤ) (ξ : E) :
    φ.sumSq (((2 : ℝ) ^ l)⁻¹ • ξ) = φ.sumSq ξ := by
  have h (j : ℤ) :
      φ.littlewoodPaley j (((2 : ℝ) ^ l)⁻¹ • ξ) = φ.littlewoodPaley (j + l) ξ := by
    rw [φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply, smul_smul, ← mul_inv,
      ← zpow_add₀ two_ne_zero, ← φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply]
  simp only [sumSq, h]
  exact (Equiv.addRight l).tsum_eq fun j ↦ φ.littlewoodPaley j ξ ^ 2

/-! ### The inverse of `Ψ` on a dyadic annulus -/

/-- A Schwartz function `θ₀` equal to `1 / Ψ ((φ.rIn / 2) • η)` on the annulus
`1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`: `1 / Ψ` is smooth away from the origin. -/
private theorem exists_invSumSq : ∃ σ : 𝓢(E, ℂ), Set.EqOn σ
    (fun η ↦ (((φ.sumSq ((φ.rIn / 2) • η))⁻¹ : ℝ) : ℂ))
    {η | 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn} := by
  have ha : φ.rIn / 2 ≠ 0 := (half_pos φ.rIn_pos).ne'
  refine SchwartzMap.exists_eqOn_annulus_of_contDiffOn
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (ContDiffOn.inv (fun η hη ↦ ?_) fun η hη ↦ ?_)) _
  · exact ((φ.contDiffAt_sumSq (smul_ne_zero ha hη)).comp η
      (contDiff_const_smul _).contDiffAt).contDiffWithinAt
  · exact (φ.sumSq_pos (smul_ne_zero ha hη)).ne'

/-- The Schwartz function `θ₀` of `exists_invSumSq`. -/
private def invSumSq : 𝓢(E, ℂ) :=
  φ.exists_invSumSq.choose

/-- The symbol `θ(2^{-j} ·)` as a Schwartz function, where `θ = θ₀((φ.rIn / 2)⁻¹ ·)` equals `1 / Ψ`
on the annulus `φ.rIn / 2 ≤ ‖ξ‖ ≤ φ.rOut` containing the support of `ψ₀`. -/
private def invSumSqSchwartz (j : ℤ) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.smulLeft
    (Units.mk0 ((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ (inv_ne_zero
      (mul_pos (zpow_pos two_pos j) (half_pos φ.rIn_pos)).ne'))) φ.invSumSq

/-- The values of `θ(2^{-j} ·)`. -/
private theorem invSumSqSchwartz_apply (j : ℤ) (ξ : E) :
    φ.invSumSqSchwartz j ξ = φ.invSumSq (((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ • ξ) := by
  rw [invSumSqSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_mk0]

/-- On the support of `ψⱼ`, `θ(2^{-j} ·)` inverts `Ψ`. -/
private theorem invSumSqSchwartz_mul_sumSq {j : ℤ} {ξ : E} (hξ : φ.littlewoodPaley j ξ ≠ 0) :
    φ.invSumSqSchwartz j ξ * (φ.sumSq ξ : ℂ) = 1 := by
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hb : (0 : ℝ) < 2 ^ j * (φ.rIn / 2) := mul_pos h2j (half_pos φ.rIn_pos)
  have h1 : 2 ^ (j - 1) * φ.rIn < ‖ξ‖ := by
    by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_norm_le (not_lt.1 h))
  have h2 : ‖ξ‖ < 2 ^ j * φ.rOut := by
    by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_le_norm (not_lt.1 h))
  rw [zpow_sub_one₀ two_ne_zero] at h1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    exact hξ (φ.littlewoodPaley_apply_zero j)
  set η := ((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ • ξ
  have hη : ‖η‖ = ‖ξ‖ / (2 ^ j * (φ.rIn / 2)) := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hb.le), inv_mul_eq_div]
  have hmem : 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn := by
    rw [hη, le_div_iff₀ hb, div_le_div_iff₀ hb φ.rIn_pos]
    constructor <;> nlinarith [φ.rIn_pos]
  have haη : (φ.rIn / 2) • η = ((2 : ℝ) ^ j)⁻¹ • ξ := by
    rw [smul_smul, mul_inv, ← mul_assoc, mul_comm (φ.rIn / 2), mul_assoc,
      mul_inv_cancel₀ (half_pos φ.rIn_pos).ne', mul_one]
  rw [invSumSqSchwartz_apply, invSumSq, φ.exists_invSumSq.choose_spec hmem]
  beta_reduce
  rw [haη, sumSq_two_zpow_inv_smul, Complex.ofReal_inv]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (φ.sumSq_pos hξ0).ne')

/-- **Reassembling a block from squared blocks**, pointwise: if the cutoffs whose indices differ
by at least `L` have disjoint supports, then `∑_{|d| < L} ψ_{d + l}² θ(2^{-l} ·) ψₗ = ψₗ`. -/
private theorem sum_littlewoodPaley_mul_littlewoodPaley_mul_invSumSqSchwartz {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : E, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    (l : ℤ) (ξ : E) :
    ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (φ.littlewoodPaley (d + l) ξ : ℂ) *
        ((φ.littlewoodPaley (d + l) ξ : ℂ) *
          (φ.invSumSqSchwartz l ξ * (φ.littlewoodPaley l ξ : ℂ))) =
      φ.littlewoodPaley l ξ := by
  by_cases h : φ.littlewoodPaley l ξ = 0
  · simp only [h, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  -- Only the cutoffs `ψⱼ` with `|j - l| < L` are nonzero at `ξ`, so they sum their squares to `Ψ`.
  have hs : ∀ j ∉ (Finset.Ioo (-(L : ℤ)) L).map (addRightEmbedding l),
      φ.littlewoodPaley j ξ = 0 := by
    intro j hj
    rw [Finset.map_add_right_Ioo, Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hj
    rcases hj with hj | hj
    · exact (mul_eq_zero.1 (hL j l (by omega) ξ)).resolve_right h
    · exact (mul_eq_zero.1 (hL l j (by omega) ξ)).resolve_left h
  have hsum := φ.sumSq_eq_sum hs
  rw [Finset.sum_map] at hsum
  simp only [addRightEmbedding_apply] at hsum
  have key := φ.invSumSqSchwartz_mul_sumSq h
  rw [hsum] at key
  push_cast at key
  rw [← Finset.sum_congr rfl fun d _ ↦ (by ring :
      (φ.littlewoodPaley (d + l) ξ : ℂ) ^ 2 *
          (φ.invSumSqSchwartz l ξ * (φ.littlewoodPaley l ξ : ℂ)) =
        (φ.littlewoodPaley (d + l) ξ : ℂ) * ((φ.littlewoodPaley (d + l) ξ : ℂ) *
          (φ.invSumSqSchwartz l ξ * (φ.littlewoodPaley l ξ : ℂ)))), ← Finset.sum_mul]
  linear_combination (φ.littlewoodPaley l ξ : ℂ) * key

variable [MeasurableSpace E] [BorelSpace E]

/-- The kernel of the multiplier `θ(2^{-j} ·)` has the same `L¹` norm for every `j`. -/
private theorem eLpNorm_fourierInv_invSumSqSchwartz (j : ℤ) :
    eLpNorm (𝓕⁻ ⇑(φ.invSumSqSchwartz j)) 1 volume =
      eLpNorm (𝓕⁻ ⇑(φ.invSumSqSchwartz 0)) 1 volume := by
  have h : ⇑(φ.invSumSqSchwartz j) =
      fun ξ ↦ (⇑(φ.invSumSqSchwartz 0)) (((2 : ℝ) ^ j)⁻¹ • ξ) :=
    funext fun ξ ↦ by
      rw [invSumSqSchwartz_apply, invSumSqSchwartz_apply, smul_smul, zpow_zero, one_mul,
        ← mul_inv, mul_comm (φ.rIn / 2)]
  rw [h, TauCeti.eLpNorm_fourierInv_comp_inv_smul _ (zpow_pos two_pos j)]
  simp

/-- The kernel `𝓕⁻ θ` is integrable, so its `L¹` norm is a finite constant. -/
private theorem coe_toNNReal_eLpNorm_fourierInv_invSumSqSchwartz :
    ((eLpNorm (𝓕⁻ ⇑(φ.invSumSqSchwartz 0)) 1 volume).toNNReal : ℝ≥0∞) =
      eLpNorm (𝓕⁻ ⇑(φ.invSumSqSchwartz 0)) 1 volume := by
  rw [← SchwartzMap.fourierInv_coe]
  exact ENNReal.coe_toNNReal ((𝓕⁻ (φ.invSumSqSchwartz 0)).memLp 1 volume).eLpNorm_ne_top

/-- The multiplier `Qⱼ` with symbol `θ(2^{-j} ·)`: on frequencies `‖ξ‖ ≈ 2^j` it is `1 / Ψ`. -/
private def invSumSqMultiplier (j : ℤ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM ℂ ((φ.invSumSqSchwartz j).toLp ∞)

/-- `Qⱼ` costs at most the factor `‖𝓕⁻ θ‖₁` in every mixed norm `L^p_t L^r_x` with `r ≥ 1`. -/
private theorem eLpNorm_eLpNorm_invSumSqMultiplier_le (j : ℤ)
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : AEStronglyMeasurable F) {p r : ℝ≥0∞}
    (hp : 0 < p) (hr : 1 ≤ r) :
    eLpNorm (fun s ↦ eLpNorm (φ.invSumSqMultiplier j (F s)) r volume) p volume ≤
      eLpNorm (𝓕⁻ ⇑(φ.invSumSqSchwartz 0)) 1 volume *
        eLpNorm (fun s ↦ eLpNorm (F s) r volume) p volume :=
  calc _ ≤ eLpNorm (fun s ↦ eLpNorm (𝓕⁻ ⇑(φ.invSumSqSchwartz 0)) 1 volume *
        eLpNorm (F s) r volume) p volume :=
      eLpNorm_mono_eNorm (((φ.invSumSqMultiplier j).continuous.comp_aestronglyMeasurable
        hF).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable fun s ↦ by
        rw [eNorm_eq_self, eNorm_eq_self, ← φ.eLpNorm_fourierInv_invSumSqSchwartz j]
        exact (φ.invSumSqSchwartz j).eLpNorm_fourierMultiplierCLM_toLp_le (F s) hr
    _ = _ := eLpNorm_const_mul_ennreal_of_pos hp

/-- **Reassembling a block from squared blocks.** If the cutoffs whose indices differ by at least
`L` have disjoint supports, then `Pₗ g = ∑_{|d| < L} P_{d + l} P_{d + l} Qₗ Pₗ g` for `g ∈ L²`. -/
private theorem sum_fourierMultiplierCLM_fourierMultiplierCLM_invSumSqMultiplier {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : E, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (l : ℤ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, Lp.fourierMultiplierCLM ℂ (m (d + l))
        (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (φ.invSumSqMultiplier l (Lp.fourierMultiplierCLM ℂ (m l) g))) =
      Lp.fourierMultiplierCLM ℂ (m l) g := by
  set θ : Lp ℂ ∞ (volume : Measure E) := (φ.invSumSqSchwartz l).toLp ∞ volume
  -- As symbols in `L^∞`, `∑_{|d| < L} ψ_{d + l} ψ_{d + l} θ ψₗ = ψₗ`.
  have hsym : ∑ d ∈ Finset.Ioo (-(L : ℤ)) L,
      (m (d + l) • m (d + l) • θ • m l : Lp ℂ ∞ (volume : Measure E)) = m l := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_finsetSum (Finset.Ioo (-(L : ℤ)) L)
        (fun d ↦ (m (d + l) • m (d + l) • θ • m l : Lp ℂ ∞ (volume : Measure E))),
      (Filter.eventually_all_finset _).2 fun d _ ↦
        Lp.coeFn_lpSMul (r := ∞) (m (d + l)) (m (d + l) • θ • m l),
      (Filter.eventually_all_finset _).2 fun d _ ↦ Lp.coeFn_lpSMul (r := ∞) (m (d + l)) (θ • m l),
      (Filter.eventually_all_finset _).2 fun d _ ↦ hm (d + l),
      Lp.coeFn_lpSMul (r := ∞) θ (m l), (φ.invSumSqSchwartz l).coeFn_toLp ∞ volume, hm l]
      with ξ h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁, Finset.sum_apply, h₇,
      ← φ.sum_littlewoodPaley_mul_littlewoodPaley_mul_invSumSqSchwartz hL l ξ]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [h₂ d hd, Pi.smul_apply', h₃ d hd, Pi.smul_apply', h₅, Pi.smul_apply', h₄ d hd, h₆, h₇,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
  simp only [invSumSqMultiplier, Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
  conv_rhs => rw [← hsym]
  rw [Lp.fourierMultiplierCLM_sum, FunLike.coe_sum, Finset.sum_apply]

/-! ### The retarded estimate -/

omit [FiniteDimensional ℝ E] in
/-- Shifting the index by `d` costs the factor `2^{dσ}`:
`∑ₗ ∑_{d ∈ S} 2^{(d + l)σ} Yₗ = (∑_{d ∈ S} 2^{dσ}) ∑ₗ 2^{lσ} Yₗ`. -/
private theorem tsum_sum_ofReal_two_zpow_add_rpow_mul (σ : ℝ) (S : Finset ℤ) (Y : ℤ → ℝ≥0∞) :
    ∑' l, ∑ d ∈ S, ENNReal.ofReal (((2 : ℝ) ^ (d + l)) ^ σ) * Y l =
      ((∑ d ∈ S, (((2 : ℝ) ^ d) ^ σ).toNNReal : ℝ≥0) : ℝ≥0∞) *
        ∑' l, ENNReal.ofReal (((2 : ℝ) ^ l) ^ σ) * Y l := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [ENNReal.ofNNReal_toNNReal, zpow_add₀ two_ne_zero,
    Real.mul_rpow (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
  ring

variable [Nontrivial E]

/-- At each time, the retarded Duhamel integral `u(t)` satisfies
`‖u(t)‖_r ≤ ∑ₗ ∑_{|d| < L} ‖Φ_{d + l, l}(t)‖_r`, where `Φⱼₗ` is the retarded integral of
`Pⱼ Pⱼ Qₗ Pₗ F`: by `‖u(t)‖_r ≤ ∑ₗ ‖Pₗ u(t)‖_r` and `Pₗ = ∑_{|d| < L} P_{d + l} P_{d + l} Qₗ Pₗ`. -/
private theorem eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sum {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : E, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) {r : ℝ≥0∞} (hr : 1 ≤ r) (t : ℝ) :
    eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
        Lp ℂ 2 (volume : Measure E))) r volume ≤
      ∑' l, ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.invSumSqMultiplier l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume := by
  by_cases hint : IntegrableOn (fun s ↦ waveSinPropagator ℂ (t - s) (F s)) (Set.Iio t)
  · refine (φ.eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM hm
      (ContinuousLinearMap.id ℂ _) _ hr).trans (tsum_le_tsum fun l ↦ ?_)
    rw [ContinuousLinearMap.id_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
    have hdec (s : ℝ) :
        Lp.fourierMultiplierCLM ℂ (m l) (waveSinPropagator ℂ (t - s) (F s)) =
          ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ (m (d + l)) (Lp.fourierMultiplierCLM ℂ (m (d + l))
              (φ.invSumSqMultiplier l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) := by
      rw [fourierMultiplierCLM_waveSinPropagator_apply, ← map_sum,
        φ.sum_fourierMultiplierCLM_fourierMultiplierCLM_invSumSqMultiplier hL hm l (F s)]
    simp_rw [hdec]
    have hH := (φ.invSumSqMultiplier l).integrable_comp
      ((Lp.fourierMultiplierCLM ℂ (m l)).integrable_comp hF)
    rw [integral_finsetSum _ fun d _ ↦
        (φ.integrable_waveSinPropagator_sub_littlewoodPaley (hm (d + l)) hH t).integrableOn,
      eLpNorm_congr_ae (Lp.coeFn_finsetSum _ _)]
    exact eLpNorm_sum_le hr
  · rw [integral_undef hint, eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    exact zero_le

/-- **The retarded Strichartz estimate for the wave equation with Besov forcing.** Let `E` be
nontrivial of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley
cutoff `ψⱼ` built from `φ` as symbol, let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, and let `(q₁, r₁)` be wave-admissible with
`2 < q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`. Put `γ = n / 2 - n / r - 1 / q` and
`γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every integrable forcing term
`F : ℝ → L²(E)`, the retarded Duhamel integral `u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`,
the solution of `∂ₜ²u - Δu = F` with zero data at `t = -∞`, satisfies

`‖u‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`.

Here `u(t)` is a Bochner integral, taken to be `0` where it does not exist. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    {q r : ℝ≥0∞} (hq : 2 < q) (hq_top : q ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 < q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  obtain ⟨hq2, hqr'⟩ := waveAdmissible_toNNReal hq hq_top hqr
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq2 hr0 hqr' Module.finrank_pos
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
      (p₁ := p₁) (r₁' := r₁') hq hq_top hqr hq₁ hqr₁
  have hK := φ.coe_toNNReal_eLpNorm_fourierInv_invSumSqSchwartz
  set K := eLpNorm (𝓕⁻ ⇑(φ.invSumSqSchwartz 0)) 1 volume
  set S := Finset.Ioo (-(L : ℤ)) L
  set σ := ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) +
    ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1
  refine ⟨C * K.toNNReal * ∑ d ∈ S, (((2 : ℝ) ^ d) ^ σ).toNNReal, fun m hm F hF ↦ ?_⟩
  -- `Hₗ = Qₗ Pₗ F` and `a j l t = ‖Φⱼₗ(t)‖_r`, with `Φⱼₗ` the retarded integral of `Pⱼ Pⱼ Hₗ`.
  have hPF (l : ℤ) := (Lp.fourierMultiplierCLM ℂ (m l)).integrable_comp hF
  have hH (l : ℤ) := (φ.invSumSqMultiplier l).integrable_comp (hPF l)
  set a : ℤ → ℤ → ℝ → ℝ≥0∞ := fun j l t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
    (Lp.fourierMultiplierCLM ℂ (m j) (Lp.fourierMultiplierCLM ℂ (m j)
      (φ.invSumSqMultiplier l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
        Lp ℂ 2 (volume : Measure E))) r volume
  have hpt := φ.eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sum hL hm hF
    (one_le_two.trans hr2)
  calc eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume
      ≤ eLpNorm (fun t ↦ ∑' l, ∑ d ∈ S, a (d + l) l t) q volume :=
        eLpNorm_mono_eNorm ((aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
          hF.aestronglyMeasurable).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
          fun t ↦ by simpa only [eNorm_eq_self] using hpt t
    _ ≤ ∑' l, ∑ d ∈ S, eLpNorm (a (d + l) l) q volume :=
        (eLpNorm_tsum_le (fun l ↦ Finset.aemeasurable_fun_sum _ fun d _ ↦
          (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub ((Lp.fourierMultiplierCLM ℂ
            _ ∘L Lp.fourierMultiplierCLM ℂ _).integrable_comp (hH l)).aestronglyMeasurable
              ).aemeasurable_eLpNorm_Lp .rfl r) (one_le_two.trans hq.le)).trans
          (tsum_le_tsum fun l ↦ by
            rw [← Finset.sum_fn]
            exact eLpNorm_sum_le (one_le_two.trans hq.le))
    -- The frequency-localized estimate and the bound for `Qₗ`.
    _ ≤ ∑' l, ∑ d ∈ S, C * K * (ENNReal.ofReal (((2 : ℝ) ^ (d + l)) ^ σ) * eLpNorm (fun s ↦
          eLpNorm (Lp.fourierMultiplierCLM ℂ (m l) (F s)) r₁' volume) p₁ volume) :=
        tsum_le_tsum fun l ↦ Finset.sum_le_sum fun d _ ↦
          (hC (d + l) (m (d + l)) (hm (d + l)) _ (hH l)).trans <| by
            rw [mul_assoc, mul_assoc, mul_left_comm K]
            gcongr
            exact φ.eLpNorm_eLpNorm_invSumSqMultiplier_le l (hPF l).aestronglyMeasurable
              (ENNReal.HolderConjugate.pos p₁ q₁) (ENNReal.HolderConjugate.one_le r₁' r₁)
    _ = _ := by
        simp_rw [← Finset.mul_sum]
        rw [ENNReal.tsum_mul_left, tsum_sum_ofReal_two_zpow_add_rpow_mul, ENNReal.coe_mul,
          ENNReal.coe_mul, hK]
        ring

end ContDiffBump
