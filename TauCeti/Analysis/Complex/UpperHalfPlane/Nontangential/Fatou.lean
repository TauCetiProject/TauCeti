/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Limit
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Function
import TauCeti.MeasureTheory.Covering.DensityTheorem

/-!
# Fatou's theorem for Poisson integrals of functions in `L¹(Π)`

For `h : ℝ → ℂ` integrable for the Poisson measure `Π = dx / (1 + x ^ 2)`, the Poisson integral
`P[h](z) = ∫ P(z, s) h(s) ds` tends to `h(x)` as `z → x` nontangentially, for almost every `x`.
The exceptional null set does not depend on the aperture: off one null set, the limits through the
cones `Γ^α_∞(x)` exist and equal `h(x)` for every `α`.

The proof works at every Lebesgue point `x` of `h`, which is a condition on `x` alone. Write
`P[h](z) - h(x) = ∫ P(z, s) (h(s) - h(x)) ds` and split `h - h(x)` into its parts on the closed
ball `B(x, δ)` and off it.

* Near part. On the cone `Γ^α_∞(x)` the Poisson integral of `|g| dx` is at most
  `max 2 (1 + 2 α ^ 2)` times the Hardy–Littlewood maximal function `M g(x)`
  (`TauCeti.nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le`), and for `g` the part
  of `h - h(x)` on `B(x, δ)`, `M g(x)` is at most the largest average of `|h - h(x)|` over the
  balls `B(x, r)`, `0 < r ≤ δ` (`TauCeti.maximalFunction_indicator_closedBall_le`), which is small
  for small `δ` at a Lebesgue point.
* Far part. For `|Re z - x| ≤ δ / 2` and `|s - x| > δ`, `P(z, s) ≤ K Im z / (1 + s ^ 2)` with `K`
  depending on `x` and `δ` (`TauCeti.upperHalfPlanePoissonKernel_le_of_lt_abs_sub`), so the far
  part is at most `K Im z ∫ |h - h(x)| dΠ`, which tends to `0`.

## Main results

* `TauCeti.tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun_of_tendsto`: at a
  Lebesgue point `x` of `h ∈ L¹(Π)`, `P[h] → h(x)` nontangentially, through cones of every
  aperture.
* `TauCeti.ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun`: **Fatou's theorem**
  for `h ∈ L¹(Π)`: for almost every `x`, `P[h] → h(x)` nontangentially through cones of every
  aperture.
* `TauCeti.ae_tendsto_vertical_upperHalfPlanePoissonIntegralFun`: in particular
  `P[h](x + i t) → h(x)` as `t → 0⁺` for almost every `x`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §§3-5.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286
  (2022), Lemmas 4 and 7.
-/

public section

noncomputable section

namespace TauCeti

open Complex MeasureTheory Filter Metric Set Topology

open scoped ENNReal Real

/-- **The near and far bound.** Let `h ∈ L¹(Π)` and let `z` be in the cone `Γ^α_∞(x)`, with
`P(z, s) ≤ c / (1 + s ^ 2)` whenever `|s - x| > δ`. Then `‖P[h](z) - h(x)‖` is at most
`max 2 (1 + 2 α ^ 2)` times the maximal function at `x` of `h - h(x)` truncated to `B(x, δ)`, plus
`c ∫ |h - h(x)| dΠ`. -/
theorem enorm_upperHalfPlanePoissonIntegralFun_sub_le {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) {α x δ c : ℝ} {z : ℂ}
    (hz : z ∈ nontangentialCone α ⊤ x)
    (hc : ∀ s, δ < |s - x| → upperHalfPlanePoissonKernel z s ≤ c * (1 + s ^ 2)⁻¹) :
    ‖upperHalfPlanePoissonIntegralFun h z - h x‖ₑ ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) *
          maximalFunction volume ((closedBall x δ).indicator fun s => h s - h x) x +
        ENNReal.ofReal c * ∫⁻ s, ‖h s - h x‖ₑ ∂upperHalfPlanePoissonMeasure := by
  have hz0 := (mem_nontangentialCone.1 hz).1
  have hmeas : AEMeasurable fun s => ‖h s - h x‖ₑ :=
    ((aestronglyMeasurable_of_integrable_upperHalfPlanePoissonMeasure hh).sub
      aestronglyMeasurable_const).eNorm
  set g : ℝ → ℂ := (closedBall x δ).indicator fun s => h s - h x
  have hg : AEMeasurable fun s => ‖g s‖ₑ := by
    simp_rw [g, eNorm_indicator_eq_indicator_eNorm]
    exact hmeas.indicator measurableSet_closedBall
  have hsplit : ∀ s, ‖h s - h x‖ₑ * ENNReal.ofReal (upperHalfPlanePoissonKernel z s) =
      ‖g s‖ₑ * ENNReal.ofReal (upperHalfPlanePoissonKernel z s) +
        (closedBall x δ)ᶜ.indicator (fun s => ‖h s - h x‖ₑ) s *
          ENNReal.ofReal (upperHalfPlanePoissonKernel z s) := fun s => by
    rw [← add_mul, eNorm_indicator_eq_indicator_eNorm]
    simp only [Set.indicator_self_add_compl_apply]
  have hnear : ∫⁻ s, ‖g s‖ₑ * ENNReal.ofReal (upperHalfPlanePoissonKernel z s) ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume g x := by
    rw [← upperHalfPlanePoissonLIntegral_withDensity hg]
    exact (le_nontangentialMaximalFunction
      (u := upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) hz).trans'
        (eNorm_eq_self _).ge |>.trans
          (nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α ⊤ g x)
  calc ‖upperHalfPlanePoissonIntegralFun h z - h x‖ₑ
      = ‖upperHalfPlanePoissonIntegralFun (fun s => h s - h x) z‖ₑ := by
        rw [upperHalfPlanePoissonIntegralFun_sub_const hh _ hz0]
    _ ≤ upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖h s - h x‖ₑ) z :=
        enorm_upperHalfPlanePoissonIntegralFun_le _ hz0
    _ = (∫⁻ s, ‖g s‖ₑ * ENNReal.ofReal (upperHalfPlanePoissonKernel z s)) +
          ∫⁻ s, (closedBall x δ)ᶜ.indicator (fun s => ‖h s - h x‖ₑ) s *
            ENNReal.ofReal (upperHalfPlanePoissonKernel z s) := by
        rw [upperHalfPlanePoissonLIntegral_withDensity hmeas, lintegral_congr hsplit]
        exact lintegral_add_left' (hg.mul
          (measurable_upperHalfPlanePoissonKernel z).ennreal_ofReal.aemeasurable) _
    _ ≤ _ := add_le_add hnear
        (lintegral_indicator_compl_mul_upperHalfPlanePoissonKernel_le hmeas fun s hs =>
          hc s (by simpa [Real.dist_eq] using hs))

/-- **Fatou's theorem at a Lebesgue point.** Let `h ∈ L¹(Π)` and let `x` be a Lebesgue point of
`h`: the averages of `‖h - h(x)‖` over the closed balls `B(x, r)` tend to `0` as `r → 0⁺`. Then
`P[h](z) → h(x)` as `z → x` nontangentially, through the cones `Γ^α_∞(x)` of every aperture `α`. -/
theorem tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun_of_tendsto {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) {x : ℝ}
    (hx : Tendsto (fun r => (∫⁻ y in closedBall x r, ‖h y - h x‖ₑ) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) (α : ℝ) :
    Tendsto (upperHalfPlanePoissonIntegralFun h) (nontangentialFilter α x) (𝓝 (h x)) := by
  set C : ℝ≥0∞ := ENNReal.ofReal (max 2 (1 + 2 * α ^ 2))
  have hC0 : C ≠ 0 := by
    simp only [C, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_max_of_lt_left two_pos
  have hN : ∫⁻ s, ‖h s - h x‖ₑ ∂upperHalfPlanePoissonMeasure ≠ ∞ :=
    (hh.sub (integrable_const (h x))).2.ne
  refine EMetric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨ε', hε'0, hε'ε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hε'0' : (0 : ℝ≥0∞) < ε' / 2 := ENNReal.div_pos (ne_of_gt hε'0) (by simp)
  -- The near part: choose `δ` from the Lebesgue point condition.
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ r ∈ Ioc 0 δ,
      (∫⁻ y in closedBall x r, ‖h y - h x‖ₑ) / volume (closedBall x r) ≤ ε' / 2 / C := by
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1
      (hx.eventually (ge_mem_nhds (ENNReal.div_pos hε'0'.ne' ENNReal.ofReal_ne_top)))
    exact ⟨u, hu, fun r hr => hsub hr⟩
  -- The far part tends to `0`; `K` is the constant of
  -- `TauCeti.upperHalfPlanePoissonKernel_le_of_lt_abs_sub`.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.im → |z.re - x| ≤ δ / 2 → ∀ s, δ < |s - x| →
      upperHalfPlanePoissonKernel z s ≤ z.im * K * (1 + s ^ 2)⁻¹ :=
    ⟨_, fun _ hz hzx _ hs => upperHalfPlanePoissonKernel_le_of_lt_abs_sub hz hδ hzx hs⟩
  have hfar : Tendsto (fun z : ℂ => ENNReal.ofReal (z.im * K) *
      ∫⁻ s, ‖h s - h x‖ₑ ∂upperHalfPlanePoissonMeasure) (nontangentialFilter α x) (𝓝 0) := by
    have him : Tendsto (fun z : ℂ => z.im * K) (nontangentialFilter α x) (𝓝 0) := by
      rw [nontangentialFilter_def]
      simpa using ((by fun_prop : Continuous fun z : ℂ => z.im * K).tendsto (x : ℂ)).mono_left
        nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal him) (Or.inr hN)
  have hη : 0 < δ / (2 * (|α| + 1)) := by positivity
  filter_upwards [hfar.eventually (gt_mem_nhds hε'0'),
    nontangentialCone_mem_nontangentialFilter α x (ENNReal.ofReal_pos.2 hη),
    nontangentialCone_mem_nontangentialFilter α x (h := ⊤) (by simp)] with z hzfar hz hz'
  obtain ⟨hz0, hzα, hzη⟩ := mem_nontangentialCone.1 hz
  have hzη' : z.im < δ / (2 * (|α| + 1)) := (ENNReal.ofReal_lt_ofReal_iff hη).1 hzη
  have hzx : |z.re - x| ≤ δ / 2 := by
    have h1 : α * z.im ≤ (|α| + 1) * z.im := by nlinarith [le_abs_self α]
    have h2 : (|α| + 1) * z.im ≤ (|α| + 1) * (δ / (2 * (|α| + 1))) := by gcongr
    have h3 : (|α| + 1) * (δ / (2 * (|α| + 1))) = δ / 2 := by field_simp
    linarith
  have hnear : C * maximalFunction volume ((closedBall x δ).indicator fun s => h s - h x) x ≤
      ε' / 2 :=
    (mul_le_mul_right (maximalFunction_indicator_closedBall_le hδ hδc) C).trans_eq
      (ENNReal.mul_div_cancel hC0 ENNReal.ofReal_ne_top)
  rw [eDist_eq_eNorm_sub]
  calc _ ≤ _ := enorm_upperHalfPlanePoissonIntegralFun_sub_le hh hz' (hK z hz0.le hzx)
    _ < ε' / 2 + ε' / 2 := ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top
          (ENNReal.div_ne_top ENNReal.coe_ne_top two_ne_zero) hnear) hnear hzfar
    _ = ε' := ENNReal.add_halves _
    _ < ε := hε'ε

/-- **Fatou's theorem for Poisson integrals of functions in `L¹(Π)`.** For `h : ℝ → ℂ` integrable
for the Poisson measure, for almost every `x`, `P[h](z) → h(x)` as `z → x` nontangentially; the
null set does not depend on the aperture, so off it the limits through the cones `Γ^α_∞(x)` exist
and equal `h(x)` for every `α`. -/
theorem ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) :
    ∀ᵐ x, ∀ α : ℝ,
      Tendsto (upperHalfPlanePoissonIntegralFun h) (nontangentialFilter α x) (𝓝 (h x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_lintegral_closedBall_eNorm_sub_div volume
    (locallyIntegrable_of_integrable_upperHalfPlanePoissonMeasure hh)] with x hx α
  exact tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun_of_tendsto hh hx α

/-- **Vertical boundary values.** For `h : ℝ → ℂ` integrable for the Poisson measure,
`P[h](x + i t) → h(x)` as `t → 0⁺` for almost every `x`. -/
theorem ae_tendsto_vertical_upperHalfPlanePoissonIntegralFun {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) :
    ∀ᵐ x : ℝ, Tendsto (fun t : ℝ => upperHalfPlanePoissonIntegralFun h ((x : ℂ) + t * I))
      (𝓝[>] 0) (𝓝 (h x)) := by
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun hh] with x hx
  exact tendsto_vertical_of_tendsto_nontangentialFilter one_pos (hx 1)

end TauCeti
