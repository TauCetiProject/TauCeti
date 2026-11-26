/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Fatou.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Fatou's theorem for Poisson integrals of measures

Let `ν` be a Poisson-finite measure on `ℝ`, with Lebesgue decomposition
`ν = w dx + ν_s`, where `w = dν / dx` is the Radon–Nikodym derivative and `ν_s` the singular
part. For almost every `x`, the Poisson integral `P[ν](z)` tends to `w(x)` as `z → x`
nontangentially; in particular `P[ν_s] → 0` nontangentially almost everywhere. Off one null set
this holds through the cones `Γ^α_∞(x)` of every aperture `α`.

The absolutely continuous part is Fatou's theorem for functions in `L¹(Π)`
(`TauCeti.ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun`). For the singular
part, the proof works at every `x` with `ν_s(B(x, r)) / |B(x, r)| → 0` as `r → 0⁺`, which holds
almost everywhere by the Besicovitch differentiation theorem since `dν_s / dx = 0` almost
everywhere. At such a point split `ν_s` into its parts on the closed ball `B(x, δ)` and off it.

* Near part. The superlevel sets of the Poisson kernel at a pole `x + iy` are balls centred at
  `x`, so the layer cake formula bounds its Poisson integral by any `M` with
  `μ(B(x, r)) ≤ M |B(x, r)|` for all `r > 0`
  (`TauCeti.upperHalfPlanePoissonLIntegral_le_of_measure_ball_le`). On the cone the Poisson
  integral is at most `max 2 (1 + 2 α ^ 2)` times that at the vertical pole of the same height
  (`TauCeti.upperHalfPlanePoissonLIntegral_le_mul_of_mem_nontangentialCone`).
* Far part. For `|Re z - x| ≤ δ / 2` and `|s - x| > δ`, `P(z, s) ≤ K Im z / (1 + s ^ 2)`
  (`TauCeti.upperHalfPlanePoissonKernel_le_of_lt_abs_sub`), so the far part is at most
  `K Im z ∫ dν / (1 + s ^ 2)`, which tends to `0`.

## Main results

* `TauCeti.upperHalfPlanePoissonLIntegral_restrict_closedBall_le`: the Poisson integral at a
  vertical pole over `x` of the restriction of `ν` to `B(x, δ)` is at most any `M` bounding the
  ball averages of `ν` around `x` up to radius `δ`.
* `TauCeti.tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_zero_of_tendsto`: if
  `ν(B(x, r)) / |B(x, r)| → 0`, then `P[ν] → 0` nontangentially at `x`.
* `TauCeti.ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_of_mutuallySingular`,
  `TauCeti.ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_singularPart`: for `μ`
  singular with respect to Lebesgue measure, in particular for `ν_s`, `P[μ] → 0` nontangentially
  almost everywhere.
* `TauCeti.ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral`: **Fatou's theorem for
  measures**: `P[ν] → dν / dx` nontangentially almost everywhere, through cones of every aperture.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §§3-5.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286
  (2022), Lemmas 4 and 7.
-/

public section

noncomputable section

namespace TauCeti

open Complex MeasureTheory Filter Metric Set Topology

open scoped ENNReal NNReal Real

/-- **The near part.** If `ν(B(x, r)) ≤ M |B(x, r)|` for `0 < r ≤ δ`, then the extended Poisson
integral of the restriction of `ν` to `B(x, δ)` is at most `M` at every vertical pole `x + iy`. -/
theorem upperHalfPlanePoissonLIntegral_restrict_closedBall_le {ν : Measure ℝ} {x δ : ℝ}
    {M : ℝ≥0∞} (hδ : 0 < δ)
    (hM : ∀ r ∈ Ioc 0 δ, ν (closedBall x r) ≤ M * volume (closedBall x r)) (y : ℝ) :
    upperHalfPlanePoissonLIntegral (ν.restrict (closedBall x δ)) ((x : ℂ) + y * I) ≤ M := by
  refine upperHalfPlanePoissonLIntegral_le_of_measure_ball_le fun r hr => ?_
  have hre : ((x : ℂ) + y * I).re = x := by simp
  rw [hre, Measure.restrict_apply measurableSet_ball]
  rcases le_or_gt r δ with hrδ | hrδ
  · calc ν (ball x r ∩ closedBall x δ) ≤ ν (closedBall x r) :=
          measure_mono (inter_subset_left.trans ball_subset_closedBall)
      _ ≤ M * volume (closedBall x r) := hM r ⟨hr, hrδ⟩
      _ = M * volume (ball x r) := by rw [Real.volume_closedBall, Real.volume_ball]
  · calc ν (ball x r ∩ closedBall x δ) ≤ ν (closedBall x δ) :=
          measure_mono inter_subset_right
      _ ≤ M * volume (closedBall x δ) := hM δ ⟨hδ, le_rfl⟩
      _ ≤ M * volume (ball x r) := by
          rw [Real.volume_closedBall, Real.volume_ball]
          gcongr

/-- **The far part.** If `|Re z - x| ≤ δ / 2`, the integral of the Poisson kernel `P(z, ·)` against
`ν` off `B(x, δ)` is at most `Im z · K ∫ dν / (1 + s ^ 2)`, with the constant
`K = 4 (2 + (1 + 2 x ^ 2) / δ ^ 2) / π` of
`TauCeti.upperHalfPlanePoissonKernel_le_of_lt_abs_sub`. -/
theorem setLIntegral_compl_closedBall_upperHalfPlanePoissonKernel_le (ν : Measure ℝ) {z : ℂ}
    {x δ : ℝ} (hδ : 0 < δ) (hzx : |z.re - x| ≤ δ / 2) :
    ∫⁻ s in (closedBall x δ)ᶜ, ENNReal.ofReal (upperHalfPlanePoissonKernel z s) ∂ν ≤
      ENNReal.ofReal (z.im * (4 * (2 + (1 + 2 * x ^ 2) / δ ^ 2) / π)) *
        ∫⁻ s, ENNReal.ofReal (1 + s ^ 2)⁻¹ ∂ν := by
  rcases lt_or_ge z.im 0 with hz | hz
  · simp [ENNReal.ofReal_of_nonpos, upperHalfPlanePoissonKernel_nonpos hz.le]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (setLIntegral_mono' measurableSet_closedBall.compl fun s hs => ?_).trans
    (setLIntegral_le_lintegral _ _)
  have hs' : δ < |s - x| := by simpa [Real.dist_eq] using hs
  rw [← ENNReal.ofReal_mul' (by positivity)]
  exact ENNReal.ofReal_le_ofReal (upperHalfPlanePoissonKernel_le_of_lt_abs_sub hz hδ hzx hs')

/-- **Vanishing nontangential limits at points of zero density.** Let `ν` be Poisson-finite and let
`x` be a point where `ν(B(x, r)) / |B(x, r)| → 0` as `r → 0⁺`. Then the extended Poisson integral
`P[ν](z) → 0` as `z → x` nontangentially, through the cones `Γ^α_∞(x)` of every aperture `α`. -/
theorem tendsto_nontangentialFilter_upperHalfPlanePoissonLIntegral_zero_of_tendsto
    {ν : Measure ℝ} (hν : IsPoissonFinite ν) {x : ℝ}
    (hx : Tendsto (fun r => ν (closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 0))
    (α : ℝ) :
    Tendsto (upperHalfPlanePoissonLIntegral ν) (nontangentialFilter α x) (𝓝 0) := by
  set C : ℝ≥0∞ := ENNReal.ofReal (max 2 (1 + 2 * α ^ 2))
  have hC0 : C ≠ 0 := by
    simp only [C, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_max_of_lt_left two_pos
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by simp)
  -- The near part: choose `δ` from the density condition.
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ r ∈ Ioc 0 δ,
      ν (closedBall x r) / volume (closedBall x r) ≤ ε / 2 / C := by
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1
      (hx.eventually (ge_mem_nhds (ENNReal.div_pos hε2.ne' ENNReal.ofReal_ne_top)))
    exact ⟨u, hu, fun r hr => hsub hr⟩
  have hball : ∀ r ∈ Ioc 0 δ, ν (closedBall x r) ≤ ε / 2 / C * volume (closedBall x r) :=
    fun r hr => (ENNReal.div_le_iff (by simp [Real.volume_closedBall, hr.1])
      measure_closedBall_lt_top.ne).1 (hδc r hr)
  have hfar : Tendsto (fun z : ℂ =>
      ENNReal.ofReal (z.im * (4 * (2 + (1 + 2 * x ^ 2) / δ ^ 2) / π)) *
        ∫⁻ s, ENNReal.ofReal (1 + s ^ 2)⁻¹ ∂ν) (nontangentialFilter α x) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal
      ((tendsto_im_nontangentialFilter α x).mul_const _))
      (Or.inr ((isPoissonFinite_iff_lintegral_lt_top ν).1 hν).ne)
  filter_upwards [hfar.eventually (ge_mem_nhds hε2),
    eventually_nontangentialFilter_abs_re_sub_le α x hδ,
    nontangentialCone_mem_nontangentialFilter α x (h := ⊤) (by simp)] with z hzfar ⟨_, hzx⟩ hz'
  rw [upperHalfPlanePoissonLIntegral_def, ← lintegral_add_compl _ measurableSet_closedBall]
  calc _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · rw [← upperHalfPlanePoissonLIntegral_def]
          calc _ ≤ C * upperHalfPlanePoissonLIntegral (ν.restrict (closedBall x δ))
                ((x : ℂ) + z.im * I) :=
                upperHalfPlanePoissonLIntegral_le_mul_of_mem_nontangentialCone _ hz'
            _ ≤ C * (ε / 2 / C) := by
                gcongr
                exact upperHalfPlanePoissonLIntegral_restrict_closedBall_le hδ hball _
            _ = ε / 2 := ENNReal.mul_div_cancel hC0 ENNReal.ofReal_ne_top
        · exact (setLIntegral_compl_closedBall_upperHalfPlanePoissonKernel_le ν hδ hzx).trans
            hzfar
    _ = ε := ENNReal.add_halves ε

/-- **Vanishing nontangential limits at points of zero density.** Let `x` be a point where
`ν(B(x, r)) / |B(x, r)| → 0` as `r → 0⁺`. Then `P[ν](z) → 0` as `z → x` nontangentially, through
the cones `Γ^α_∞(x)` of every aperture `α`. For `ν` not Poisson-finite, `P[ν]` is the junk value
`0`. -/
theorem tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_zero_of_tendsto
    {ν : Measure ℝ} {x : ℝ}
    (hx : Tendsto (fun r => ν (closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 0))
    (α : ℝ) :
    Tendsto (upperHalfPlanePoissonIntegral ν) (nontangentialFilter α x) (𝓝 0) := by
  by_cases hν : IsPoissonFinite ν
  swap
  · rw [funext (upperHalfPlanePoissonIntegral_of_not_isPoissonFinite hν)]
    exact tendsto_const_nhds
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_nontangentialFilter_upperHalfPlanePoissonLIntegral_zero_of_tendsto hν hx α)
  refine h.congr' ?_
  filter_upwards [nontangentialCone_mem_nontangentialFilter α x (h := ⊤) (by simp)] with z hz
  have hz0 := (mem_nontangentialCone.1 hz).1
  rw [Function.comp_apply, ← ofReal_upperHalfPlanePoissonIntegral hν,
    ENNReal.toReal_ofReal (upperHalfPlanePoissonIntegral_nonneg ν hz0.le)]

/-- **Singular measures have vanishing nontangential limits.** For a measure `μ` singular with
respect to Lebesgue measure, `P[μ](z) → 0` as `z → x` nontangentially at almost every `x`, through
the cones of every aperture. -/
theorem ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_of_mutuallySingular
    {μ : Measure ℝ} (hμ : μ ⟂ₘ volume) :
    ∀ᵐ x, ∀ α : ℝ, Tendsto (upperHalfPlanePoissonIntegral μ) (nontangentialFilter α x) (𝓝 0) := by
  by_cases hμP : IsPoissonFinite μ
  swap
  · rw [funext (upperHalfPlanePoissonIntegral_of_not_isPoissonFinite hμP)]
    exact .of_forall fun _ _ => tendsto_const_nhds
  have := hμP.isFiniteMeasureOnCompacts
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume,
    (Measure.rnDeriv_eq_zero μ volume).2 hμ] with x hx hx0 α
  rw [hx0, Pi.zero_apply] at hx
  exact tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_zero_of_tendsto hx α

/-- **The singular part has vanishing nontangential limits.** The Poisson integral of the singular
part `ν_s` of a measure `ν` with respect to Lebesgue measure tends to `0` nontangentially at almost
every `x`, through the cones of every aperture. -/
theorem ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_singularPart
    (ν : Measure ℝ) :
    ∀ᵐ x, ∀ α : ℝ, Tendsto (upperHalfPlanePoissonIntegral (ν.singularPart volume))
      (nontangentialFilter α x) (𝓝 0) :=
  ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_of_mutuallySingular
    (ν.mutuallySingular_singularPart volume)

/-- **Fatou's theorem for Poisson integrals of measures.** Let `ν` be a Poisson-finite measure on
`ℝ`, with Lebesgue decomposition `ν = w dx + ν_s`, `w = dν / dx`. For almost every `x`,
`P[ν](z) → w(x)` as `z → x` nontangentially; the null set does not depend on the aperture, so off
it the limits through the cones `Γ^α_∞(x)` exist and equal `w(x)` for every `α`. -/
theorem ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral
    {ν : Measure ℝ} (hν : IsPoissonFinite ν) :
    ∀ᵐ x, ∀ α : ℝ, Tendsto (upperHalfPlanePoissonIntegral ν) (nontangentialFilter α x)
      (𝓝 (ν.rnDeriv volume x).toReal) := by
  have := hν.isFiniteMeasureOnCompacts
  set w : ℝ → ℝ≥0 := fun x => (ν.rnDeriv volume x).toNNReal
  have hwm : AEMeasurable w := (Measure.measurable_rnDeriv ν volume).ennreal_toNNReal.aemeasurable
  have hwd : volume.withDensity (fun x => (w x : ℝ≥0∞)) = volume.withDensity (ν.rnDeriv volume) :=
    withDensity_congr_ae (by
      filter_upwards [Measure.rnDeriv_lt_top ν volume] with x hx
      exact ENNReal.coe_toNNReal hx.ne)
  have hle : volume.withDensity (fun x => (w x : ℝ≥0∞)) ≤ ν :=
    hwd ▸ Measure.withDensity_rnDeriv_le ν volume
  set h : ℝ → ℂ := fun x => ((w x : ℝ) : ℂ)
  have hh : Integrable h upperHalfPlanePoissonMeasure := by
    have hhm : AEStronglyMeasurable h volume :=
      ((Complex.continuous_ofReal.comp NNReal.continuous_coe).measurable.comp_aemeasurable
        hwm).aestronglyMeasurable
    refine (integrable_upperHalfPlanePoissonMeasure_iff hhm).2 ?_
    have hnorm : (fun x => ‖h x‖ₑ) = fun x => (w x : ℝ≥0∞) := funext fun x => by
      simp [h, eNorm_eq_nnNorm, Complex.nnNorm_real]
    rw [hnorm]
    exact lt_top_iff_ne_top.2 fun h0 =>
      ((upperHalfPlanePoissonLIntegral_eq_top_iff (by simp)).1 h0) (hν.mono hle)
  have hνs : IsPoissonFinite (ν.singularPart volume) := hν.mono (ν.singularPart_le volume)
  have hac : IsPoissonFinite (volume.withDensity (ν.rnDeriv volume)) :=
    hν.mono (Measure.withDensity_rnDeriv_le ν volume)
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_singularPart ν,
    ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun hh] with x hxs hxa α
  have hre := (Complex.continuous_re.tendsto _).comp (hxa α)
  have hsum := (hxs α).add hre
  have hlim : (0 : ℝ) + (h x).re = (ν.rnDeriv volume x).toReal := by
    simp [h, w, ENNReal.coe_toNNReal_eq_toReal]
  rw [hlim] at hsum
  refine hsum.congr fun z => ?_
  rw [Function.comp_apply,
    upperHalfPlanePoissonIntegralFun_eq_upperHalfPlanePoissonIntegral_withDensity hwm, ofReal_re,
    hwd]
  conv_rhs => rw [ν.haveLebesgueDecomposition_add volume]
  simp only [upperHalfPlanePoissonIntegral_def]
  rw [integral_add_measure (hνs.integrable_upperHalfPlanePoissonKernel z)
    (hac.integrable_upperHalfPlanePoissonKernel z)]

end TauCeti
