/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import TauCeti.Analysis.Normed.Group.RelativeApproximation
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.Order.Squeeze

/-!
# Volumes of small preimages of balls under a map with injective derivative

Suppose `g : E → F` has injective derivative `A` at `z₀`, where `E` is an `n`-dimensional real
normed space and `F` is a real normed space. Assume that on `B_δ(z₀)`, for `δ > 0`,
`‖g z - g z₀ - A (z - z₀)‖ ≤ c ‖A (z - z₀)‖` for some `c < 1`.
For every `ε ∈ (0, 1)` and sufficiently small `r > 0` (depending on `ε`), the localized set
`S_r = B_δ(z₀) ∩ g⁻¹(B_r(g z₀))` lies between the preimages
`z₀ + A⁻¹(B_{r/(1+ε)})` and `z₀ + A⁻¹(B_{r/(1-ε)})`.
For any additive Haar measure `μ`, this gives `μ(S_r) / rⁿ → μ(A⁻¹(B_1))`.
If `J` is Banach-valued, continuous at `z₀`, and almost everywhere strongly measurable on
`B_δ(z₀)`, then `r⁻ⁿ • ∫_{S_r} J dμ → μ(A⁻¹(B_1)) • J z₀`. Measurability of `S_r` is not needed.

For an inner product codomain, a basis `b` of `E`, and real-valued `J` whose value at `z₀` is
the square root of the Gram determinant of `A ∘ b`, the normalized integral tends to the
volume `ωₙ` of the unit ball of `ℝⁿ`. Read in a chart, this says that the part near a point of
an immersed submanifold inside a small ambient ball of radius `r` has area `≈ ωₙ rⁿ`.

## Main results

* `MeasureTheory.Measure.tendsto_measureReal_ball_inter_preimage_ball_div_pow`: the localized
  measure limit for any additive Haar measure.
* `MeasureTheory.Measure.tendsto_setIntegral_ball_inter_preimage_ball_inv_pow_smul`: the
  corresponding limit for a continuous Banach-valued density.
* `Module.Basis.tendsto_setIntegral_ball_inter_preimage_ball_div_pow`: the Gram-normalized
  area limit `∫_{S_r} J dλ_b / rⁿ → ωₙ`.

The linear volume identities are in `Haar.InnerProductSpace` and `Lebesgue.EqHaar`.
The relative linearization estimate follows from Mathlib's `HasFDerivAt.isEquivalent_sub`
and `Asymptotics.IsEquivalent.isLittleO`, since an injective linear map on a finite-dimensional
space is antilipschitz (`LinearMap.injective_iff_antilipschitz`). The density step uses
`ContinuousAt.integral_sub_linear_isLittleO_ae`.

## References

* T. H. Colding and W. P. Minicozzi II, *A Course in Minimal Surfaces*, Graduate Studies in
  Mathematics 121, American Mathematical Society (2011), Chapter 1, §3.
-/

public section

open Filter Function MeasureTheory Metric Module Set
open scoped ENNReal NNReal Pointwise Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For small `r`, the set `S_r = B_δ(z₀) ∩ g⁻¹(B_r(g z₀))` lies in `B_{δε}(z₀)` and between the
linear preimages `z₀ + A⁻¹(B_{r/(1+ε)})` and `z₀ + A⁻¹(B_{r/(1-ε)})`. -/
private theorem preimage_ball_subset_and_subset {g : E → F} {z₀ : E} {A : E →L[ℝ] F}
    {K δ δε ε r c : ℝ} (hK : 0 ≤ K) (hc : c < 1) (hKA : ∀ w, ‖w‖ ≤ K * ‖A w‖)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖)
    (hest : ∀ z ∈ ball z₀ δε, ‖g z - g z₀ - A (z - z₀)‖ ≤ ε * ‖A (z - z₀)‖)
    (hδε : δε ≤ δ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hrδ : (1 + (1 - c)⁻¹) * K * r < δε) :
    (fun z ↦ A (z - z₀)) ⁻¹' ball 0 (r / (1 + ε)) ⊆ ball z₀ δ ∩ g ⁻¹' ball (g z₀) r ∧
      ball z₀ δ ∩ g ⁻¹' ball (g z₀) r ⊆
        ball z₀ δε ∩ (fun z ↦ A (z - z₀)) ⁻¹' ball 0 (r / (1 - ε)) := by
  constructor
  · intro z hz
    rw [mem_preimage, mem_ball_zero_iff, lt_div_iff₀ (by linarith)] at hz
    have hzδε : z ∈ ball z₀ δε := by
      rw [mem_ball, dist_eq_norm]
      calc ‖z - z₀‖ ≤ K * ‖A (z - z₀)‖ := hKA _
        _ ≤ K * r := by gcongr; nlinarith [norm_nonneg (A (z - z₀))]
        _ < δε := by
          have := mul_nonneg (inv_nonneg.2 (sub_pos.2 hc).le) (mul_nonneg hK hr.le)
          nlinarith
    refine ⟨ball_subset_ball hδε hzδε, ?_⟩
    rw [mem_preimage, mem_ball, dist_eq_norm]
    nlinarith [(TauCeti.one_sub_mul_norm_le_and_norm_le_one_add_mul_norm (hest z hzδε)).2]
  · rintro z ⟨hzδ, hzr⟩
    rw [mem_preimage, mem_ball, dist_eq_norm] at hzr
    have hA2 := (TauCeti.one_sub_mul_norm_le_and_norm_le_one_add_mul_norm (hgδ z hzδ)).1
    have hzδε : z ∈ ball z₀ δε := by
      rw [mem_ball, dist_eq_norm]
      calc ‖z - z₀‖ ≤ K * ‖A (z - z₀)‖ := hKA _
        _ < δε := by
          have hAc : ‖A (z - z₀)‖ < r / (1 - c) :=
            (lt_div_iff₀ (sub_pos.2 hc)).2 (by nlinarith [hA2.trans_lt hzr])
          have hbound := mul_le_mul_of_nonneg_left hAc.le hK
          rw [← mul_div_assoc] at hbound
          have hδr : K * r / (1 - c) < δε := by
            rw [div_eq_mul_inv]
            linarith [mul_nonneg hK hr.le]
          exact hbound.trans_lt hδr
    refine ⟨hzδε, ?_⟩
    rw [mem_preimage, mem_ball_zero_iff, lt_div_iff₀ (by linarith)]
    nlinarith [(TauCeti.one_sub_mul_norm_le_and_norm_le_one_add_mul_norm (hest z hzδε)).1]

/-- The localization error bound forces the localized preimages to shrink to `z₀`. -/
private theorem tendsto_ball_inter_preimage_ball_smallSets {g : E → F} {z₀ : E}
    {A : E →L[ℝ] F} {K : ℝ≥0} (hK : AntilipschitzWith K A) {δ c : ℝ} (hc : c < 1)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖) :
    Tendsto (fun r ↦ ball z₀ δ ∩ g ⁻¹' ball (g z₀) r) (𝓝[>] 0) (𝓝 z₀).smallSets := by
  apply tendsto_smallSets_iff.2
  intro s hs
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  have hpos : 0 < ε / ((K : ℝ) + 1) * (1 - c) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with r hr z hz
  apply hεs
  rw [mem_ball, dist_eq_norm]
  have hnorm : ‖A (z - z₀)‖ < r / (1 - c) := by
    rw [lt_div_iff₀ (sub_pos.2 hc)]
    simpa only [mul_comm] using
      (one_sub_mul_norm_le_and_norm_le_one_add_mul_norm (hgδ z hz.1)).1.trans_lt
        (by simpa [dist_eq_norm] using hz.2)
  have hKA : ‖z - z₀‖ ≤ (K : ℝ) * ‖A (z - z₀)‖ := by
    simpa using hK.le_mul_dist (z - z₀) 0
  have hrε : r / (1 - c) < ε / ((K : ℝ) + 1) :=
    (div_lt_iff₀ (sub_pos.2 hc)).2 hr.2
  have hεK : (K : ℝ) * (ε / ((K : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  exact hKA.trans_lt ((mul_le_mul_of_nonneg_left (hnorm.trans hrε).le K.coe_nonneg).trans_lt hεK)

end TauCeti

namespace MeasureTheory.Measure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The two-sided estimate for the localized measure, at a fixed relative error `ε`. -/
private theorem eventually_le_measureReal_div_pow_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {g : E → F} {z₀ : E} {A : E →L[ℝ] F} (hg : HasFDerivAt g A z₀) (hA : Injective A)
    {δ c : ℝ} (hδ : 0 < δ) (hc : c < 1)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ((1 + ε)⁻¹) ^ finrank ℝ E * μ.real (A ⁻¹' ball 0 1) ≤
          μ.real (ball z₀ δ ∩ g ⁻¹' ball (g z₀) r) / r ^ finrank ℝ E ∧
        μ.real (ball z₀ δ ∩ g ⁻¹' ball (g z₀) r) / r ^ finrank ℝ E ≤
          ((1 - ε)⁻¹) ^ finrank ℝ E * μ.real (A ⁻¹' ball 0 1) := by
  obtain ⟨K, hK0, hK⟩ := (LinearMap.injective_iff_antilipschitz (A : E →ₗ[ℝ] F)).1 hA
  have hKA (w : E) : ‖w‖ ≤ K * ‖A w‖ := by simpa using hK.le_mul_dist w 0
  obtain ⟨δ', hδ', hest⟩ := Metric.eventually_nhds_iff_ball.1
    ((hg.isEquivalent_sub (hK.isInducing A.continuous)).isLittleO.def hε)
  set δε := min δ δ'
  have hδε : 0 < δε := lt_min hδ hδ'
  have : 0 < 1 - c := sub_pos.2 hc
  have : (0 : ℝ) < K := NNReal.coe_pos.2 hK0
  have hrad : 0 < δε / ((1 + (1 - c)⁻¹) * K) := div_pos hδε (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hrad] with r hr
  obtain ⟨hsub, hsup⟩ := TauCeti.preimage_ball_subset_and_subset K.coe_nonneg hc hKA hgδ
    (fun z hz ↦ hest z (ball_subset_ball (min_le_right _ _) hz)) (min_le_left _ _) hε hε1 hr.1
    (by simpa only [mul_comm r] using
      (lt_div_iff₀ (by positivity : 0 < (1 + (1 - c)⁻¹) * (K : ℝ))).1 hr.2)
  have hscale (s : ℝ) (hs : 0 < s) :=
    μ.addHaar_preimage_comp_sub_right_ball A.toLinearMap z₀ hs
  simp only [ContinuousLinearMap.coe_coe] at hscale
  have hP (s : ℝ) (hs : 0 < s) : μ.real ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) =
      s ^ finrank ℝ E * μ.real (A ⁻¹' ball 0 1) := by
    rw [measureReal_def, hscale s hs,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), measureReal_def]
  have hPfin (s : ℝ) (hs : 0 < s) : μ ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) < ⊤ := by
    rw [hscale s hs]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hK.isBounded_preimage isBounded_ball).measure_lt_top
  have hs₁ : 0 < r / (1 - ε) := div_pos hr.1 (by linarith)
  have hSfin := (measure_mono (hsup.trans inter_subset_right)).trans_lt (hPfin _ hs₁)
  have hμ1 := hP _ (div_pos hr.1 (by linarith : (0 : ℝ) < 1 + ε)) ▸ measureReal_mono hsub hSfin.ne
  have hμ2 := hP _ hs₁ ▸ measureReal_mono (hsup.trans inter_subset_right) (hPfin _ hs₁).ne
  have hrn : 0 < r ^ finrank ℝ E := pow_pos hr.1 _
  constructor
  · rw [le_div_iff₀ hrn]
    convert hμ1 using 1; ring
  · rw [div_le_iff₀ hrn]
    convert hμ2 using 1; ring

/-- If `g` has injective derivative `A` and relative linearization error at most `c < 1` on
`B_δ(z₀)`, with `δ > 0`, its localized preimages have normalized Haar measure tending to the
measure of `A⁻¹(B_1)`. No measurability of the preimages is required. -/
theorem tendsto_measureReal_ball_inter_preimage_ball_div_pow (μ : Measure E) [μ.IsAddHaarMeasure]
    {g : E → F} {z₀ : E} {A : E →L[ℝ] F} (hg : HasFDerivAt g A z₀) (hA : Injective A)
    {δ c : ℝ} (hδ : 0 < δ) (hc : c < 1)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖) :
    Tendsto (fun r ↦ μ.real (ball z₀ δ ∩ g ⁻¹' ball (g z₀) r) / r ^ finrank ℝ E)
      (𝓝[>] 0) (𝓝 (μ.real (A ⁻¹' ball 0 1))) := by
  set L := μ.real (A ⁻¹' ball 0 1)
  have hl : Tendsto (fun ε : ℝ ↦ ((1 + ε)⁻¹) ^ finrank ℝ E * L) (𝓝[>] 0) (𝓝 L) := by
    have : ContinuousAt (fun ε : ℝ ↦ ((1 + ε)⁻¹) ^ finrank ℝ E * L) 0 := by
      fun_prop (disch := norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun ε : ℝ ↦ ((1 - ε)⁻¹) ^ finrank ℝ E * L) (𝓝[>] 0) (𝓝 L) := by
    have : ContinuousAt (fun ε : ℝ ↦ ((1 - ε)⁻¹) ^ finrank ℝ E * L) 0 := by
      fun_prop (disch := norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  apply hl.squeeze_of_eventually_eventually_le hh
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  exact eventually_le_measureReal_div_pow_le μ hg hA hδ hc hgδ hε.1 hε.2

/-- A continuous Banach-valued density on localized small preimages has leading term equal to
its value at the center times the Haar measure of `A⁻¹(B_1)`. The density need only be almost
everywhere strongly measurable on the localization ball; the preimages need not be measurable. -/
theorem tendsto_setIntegral_ball_inter_preimage_ball_inv_pow_smul (μ : Measure E)
    [μ.IsAddHaarMeasure] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {g : E → F} {z₀ : E} {A : E →L[ℝ] F} (hg : HasFDerivAt g A z₀) (hA : Injective A)
    {J : E → G} {δ c : ℝ} (hJ : ContinuousAt J z₀)
    (hJm : AEStronglyMeasurable J (μ.restrict (ball z₀ δ))) (hδ : 0 < δ) (hc : c < 1)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖) :
    Tendsto (fun r ↦ (r ^ finrank ℝ E)⁻¹ •
      ∫ z in ball z₀ δ ∩ g ⁻¹' ball (g z₀) r, J z ∂μ)
      (𝓝[>] 0) (𝓝 (μ.real (A ⁻¹' ball 0 1) • J z₀)) := by
  have hvol := μ.tendsto_measureReal_ball_inter_preimage_ball_div_pow hg hA hδ hc hgδ
  obtain ⟨K, _, hK⟩ := (LinearMap.injective_iff_antilipschitz (A : E →ₗ[ℝ] F)).1 hA
  have hs := TauCeti.tendsto_ball_inter_preimage_ball_smallSets hK hc hgδ
  have ho := hJ.integral_sub_linear_isLittleO_ae
    (_root_.AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hJm (ball_mem_nhds z₀ hδ)) hs
  have hO := Asymptotics.isBigO_of_div_tendsto_nhds
    (eventually_nhdsWithin_of_forall fun r hr h0 ↦ absurd h0 (pow_pos hr _).ne')
    (μ.real (A ⁻¹' ball 0 1)) hvol
  have hlim := (ho.trans_isBigO hO).tendsto_inv_smul_nhds_zero.add (hvol.smul_const (J z₀))
  simpa only [smul_sub, smul_smul, div_eq_inv_mul, sub_add_cancel, zero_add] using hlim

end MeasureTheory.Measure

namespace Module.Basis

/-- **Volumes of small preimages of balls.** Suppose `g` has injective derivative `A` at `z₀`,
and relative linearization error at most `c < 1` on `B_δ(z₀)`, with `δ > 0`. A real density `J`
continuous at `z₀` and almost everywhere strongly measurable on `B_δ(z₀)`, whose central value
is the square root of the Gram determinant of `A ∘ b`, has normalized localized integral
`∫_{B_δ(z₀) ∩ g⁻¹(B_r(g z₀))} J dλ_b / rⁿ → ωₙ` as `r → 0⁺`. -/
theorem tendsto_setIntegral_ball_inter_preimage_ball_div_pow
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) {g : E → F} {z₀ : E} {A : E →L[ℝ] F}
    (hg : HasFDerivAt g A z₀) (hA : Injective A) {J : E → ℝ} {δ : ℝ}
    (hJ : ContinuousAt J z₀) (hJm : AEStronglyMeasurable J (b.addHaar.restrict (ball z₀ δ)))
    (hδ : 0 < δ) (hJ0 : J z₀ = √(Matrix.gram ℝ fun i ↦ A (b i)).det) {c : ℝ} (hc : c < 1)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖) :
    Tendsto (fun r ↦ (∫ z in ball z₀ δ ∩ g ⁻¹' ball (g z₀) r, J z ∂b.addHaar) /
      r ^ finrank ℝ E) (𝓝[>] 0)
      (𝓝 (volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1))) := by
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have hLω : b.addHaar.real (A ⁻¹' ball 0 1) * J z₀ =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
    have h := congrArg ENNReal.toReal
      (b.ofReal_sqrt_det_gram_mul_addHaar_preimage_ball (A := A.toLinearMap) hA 1)
    simp only [ContinuousLinearMap.coe_coe] at h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ← hJ0, ← measureReal_def, ← measureReal_def, mul_comm] at h
  simpa only [smul_eq_mul, ← div_eq_inv_mul, hLω] using
    b.addHaar.tendsto_setIntegral_ball_inter_preimage_ball_inv_pow_smul hg hA hJ hJm hδ hc hgδ

end Module.Basis
