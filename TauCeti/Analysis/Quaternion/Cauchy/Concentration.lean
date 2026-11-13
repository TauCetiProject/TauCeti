/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cutoff
public import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# Concentration of the Cauchy–Fueter cutoff density

The divergence of the cut-off Cauchy–Fueter field contains the nonnegative real density
`ε⁻¹ ψ'(‖q - q₀‖ / ε) ‖q - q₀‖⁻³`, where `ψ = cauchyFueterCutoff`. Its mass is `2π²`,
and its support shrinks to the pole. Consequently its integral against a coefficient
continuous at the pole tends to `2π²` times that coefficient. This is the limit needed to
remove the cutoff in the Cauchy–Fueter representation formula.

The localized theorem requires only integrability on a measurable neighbourhood and
continuity within that neighbourhood at the pole. In particular, it applies to coefficients
continuous on a closed box with the pole in its interior. The codomain can be any complete
real normed space. Integration takes place on `Fin 4 → ℝ`, using the Euclidean quaternion
norm through `Quaternion.dq`, not the sup norm of the integration domain.

The convergence argument uses Mathlib's
`tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto`.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open MeasureTheory Set Filter Real Function Metric
open scoped Quaternion Topology

namespace TauCeti

open TauCeti.Quaternion

/-- The supports of the cutoff densities shrink to the pole, also in the topology of
the real coordinate space. -/
theorem tendsto_support_cauchyFueterCutoffDensity (x₀ : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ ↦ Function.support
      (fun x : Fin 4 → ℝ ↦ cauchyFueterCutoffDensity ε (dq x) (dq x₀)))
      (𝓝[>] 0) (𝓝 x₀).smallSets := by
  rw [tendsto_smallSets_iff]
  intro u hu
  let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
  have hdq (x : Fin 4 → ℝ) : dq x = e x := congrFun coe_dq x
  have he : e.symm ⁻¹' u ∈ 𝓝 (dq x₀) := by
    rw [hdq]
    exact e.symm.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [e.symm_apply_apply] using hu)
  obtain ⟨δ, hδ, hδu⟩ := Metric.mem_nhds_iff.1 he
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
  intro x hx
  have hxδ : ‖dq x - dq x₀‖ < δ := by
    by_contra h
    exact hx (cauchyFueterCutoffDensity_eq_zero hε (Or.inr (hεδ.trans_le (le_of_not_gt h))))
  have := hδu (by simpa [Metric.mem_ball, dist_eq_norm] using hxδ)
  simpa only [mem_preimage, hdq, e.symm_apply_apply] using this

/-- Removing the cutoff recovers `2π²` times the coefficient at the pole. Only
integrability on a measurable neighbourhood and continuity within it at the pole are
needed; values outside the neighbourhood play no role. -/
theorem tendsto_setIntegral_cauchyFueterCutoff_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : (Fin 4 → ℝ) → E} {s : Set (Fin 4 → ℝ)} {x₀ : Fin 4 → ℝ}
    (hs : MeasurableSet s) (hs₀ : s ∈ 𝓝 x₀) (hf : IntegrableOn f s)
    (hc : ContinuousWithinAt f s x₀) :
    Tendsto (fun ε : ℝ ↦ ∫ x in s, cauchyFueterCutoffDensity ε (dq x) (dq x₀) • f x)
      (𝓝[>] 0) (𝓝 ((2 * π ^ 2) • f x₀)) := by
  let m : ℝ := 2 * π ^ 2
  have hm : m ≠ 0 := by dsimp [m]; positivity
  let φ := fun ε (x : Fin 4 → ℝ) ↦ m⁻¹ * cauchyFueterCutoffDensity ε (dq x) (dq x₀)
  have hsupp := tendsto_support_cauchyFueterCutoffDensity x₀
  rw [tendsto_smallSets_iff] at hsupp
  let t := s ∩ Metric.closedBall x₀ 1
  have ht : MeasurableSet t := hs.inter measurableSet_closedBall
  have ht₀ : t ∈ 𝓝 x₀ := inter_mem hs₀ (Metric.closedBall_mem_nhds _ zero_lt_one)
  have hmass : Tendsto (fun ε ↦ ∫ x in t, φ ε x) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin, hsupp t ht₀] with ε hε hsupport
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [φ, integral_const_mul,
        _root_.Quaternion.integral_cauchyFueterCutoff_density _ hε]
      exact (inv_mul_cancel₀ hm).symm
    · intro x hx
      simp only [φ, notMem_support.mp (mt (@hsupport x) hx), mul_zero]
  have hlimit := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    hs ht inter_subset_left (nhdsWithin_le_nhds ht₀)
    (ne_of_lt ((isCompact_closedBall x₀ (1 : ℝ)).measure_lt_top.trans_le'
      (measure_mono inter_subset_right)))
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε x _
      exact mul_nonneg (inv_nonneg.2 (by dsimp [m]; positivity))
        (cauchyFueterCutoffDensity_nonneg hε _ _))
    (by
      intro u hu hxu
      apply tendstoUniformlyOn_iff.2
      intro η hη
      filter_upwards [hsupp u (hu.mem_nhds hxu)] with ε hsupport x hx
      have hz := notMem_support.mp (mt (@hsupport x) hx.2)
      simpa [φ, hz] using hη)
    hmass
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((integrable_cauchyFueterCutoffDensity hε _).const_mul _).aestronglyMeasurable.restrict)
    hf hc
  have := hlimit.const_smul m
  simpa only [φ, ← integral_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hm, one_mul]
    using this

/-- The cutoff limit on a closed coordinate box, assuming only continuity of the
coefficient on the box and that the pole is strictly inside each coordinate interval. -/
theorem tendsto_integral_Icc_cauchyFueterCutoff_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : (Fin 4 → ℝ) → E} {a b x₀ : Fin 4 → ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    Tendsto (fun ε : ℝ ↦ ∫ x in Icc a b,
      cauchyFueterCutoffDensity ε (dq x) (dq x₀) • f x)
      (𝓝[>] 0) (𝓝 ((2 * π ^ 2) • f x₀)) :=
  tendsto_setIntegral_cauchyFueterCutoff_density measurableSet_Icc (pi_Icc_mem_nhds ha hb)
    hf.integrableOn_Icc (hf x₀ ⟨fun i ↦ (ha i).le, fun i ↦ (hb i).le⟩)

end TauCeti
