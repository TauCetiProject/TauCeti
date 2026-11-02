/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.MeasureTheory.Integral.Lebesgue.BiUnion

/-!
# The Sobolev inequality on a closed Riemannian manifold

Let `M` be a compact manifold without boundary, of dimension `n`, with a continuous Riemannian
metric and its Riemannian volume `dV`. For `1 ≤ p` and the Sobolev conjugate exponent `p'` given by
`1 / p' = 1 / p - 1 / n`, the **Sobolev inequality** says that there is a constant `C` with

`‖u‖_{L^{p'}} ≤ C (‖∇u‖_{Lᵖ} + ‖u‖_{Lᵖ})`

for every `C¹` function `u` (`TauCeti.Manifold.exists_eLpNorm_le_mul_eLpNorm_mgradient_add`). For
`n > 2` and `p = 2` the exponent `p'` is the critical exponent `2 n / (n - 2)`, and the inequality
bounds the `L^{2n/(n-2)}` norm of `u` by its `H¹` norm
(`TauCeti.Manifold.exists_eLpNorm_le_mul_eLpNorm_mgradient_two_add`). This is the a priori estimate
behind the continuous embedding of `H¹(M)` into `L^{2n/(n-2)}(M)`, and the denominator bound of the
Yamabe quotient.

The proof localizes the Gagliardo–Nirenberg–Sobolev inequality on the model space,
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, exactly as Trudinger's inequality is localized in
`TauCeti.Geometry.Manifold.Riemannian.Trudinger`. Near each point `c`, in a coordinate ball around
the chart image of `c`, the chart density is comparable to its value at `c` and the coordinate
derivative of every function is bounded by a fixed multiple of the length of its gradient. A bump
function equal to `1` on a smaller coordinate ball cuts `u` off to a compactly supported `C¹`
function on the model space, whose derivative has `Lᵖ` norm at most a constant times
`‖∇u‖_{Lᵖ} + ‖u‖_{Lᵖ}` (`ContDiffBump.lintegral_enorm_fderiv_mul_comp_extChartAt_symm_rpow_le`).
The flat inequality then bounds the `L^{p'}` norm of `u` over the chart preimage of the smaller
ball (`TauCeti.Manifold.exists_mem_nhds_eLpNorm_restrict_le_mul_eLpNorm_mgradient_add`), and
finitely many such neighbourhoods cover `M`.

## Main results

* `TauCeti.Manifold.exists_mem_nhds_eLpNorm_restrict_le_mul_eLpNorm_mgradient_add`: the local
  Sobolev inequality, near any point of a manifold without boundary.
* `TauCeti.Manifold.exists_eLpNorm_le_mul_eLpNorm_mgradient_add`: the Sobolev inequality on a
  closed Riemannian manifold.
* `TauCeti.Manifold.exists_eLpNorm_le_mul_eLpNorm_mgradient_two_add`: its form for `p = 2` and the
  critical exponent `2 n / (n - 2)`.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 2.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), Chapter 3.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
-/

public section

open Bundle Filter MeasureTheory Metric Module Set
open scoped ENNReal NNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable [MeasurableSpace M] [BorelSpace M]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **The Sobolev inequality near a point.** Let `1 ≤ p` and let `p'` be the Sobolev conjugate
exponent, `1 / p' = 1 / p - 1 / n`, on a manifold without boundary of dimension `n > 0` with a
continuous Riemannian metric. Every point `c` has a neighbourhood `V` with a constant `C` such that
`‖u‖_{L^{p'}(V)} ≤ C (‖∇u‖_{Lᵖ} + ‖u‖_{Lᵖ})` for every `C¹` function `u`. -/
theorem exists_mem_nhds_eLpNorm_restrict_le_mul_eLpNorm_mgradient_add [LindelofSpace M]
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) (c : M) :
    ∃ V ∈ 𝓝 c, ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm u p' ((riemannianVolume I M).restrict V) ≤
        C * (eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M) +
          eLpNorm u p (riemannianVolume I M)) := by
  -- A coordinate ball of radius `r` around the chart image of `c`, adapted to the metric.
  obtain ⟨C₁, hC₁, r, hr, hrt, hball⟩ :=
    exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo (I := I) (M := M) c
  set φ := extChartAt I c
  set μ := (Module.finBasis ℝ E).addHaar
  set ρ := chartVolumeDensity (I := I) c
  set dV := riemannianVolume I M
  have hρc : 0 < ρ c := chartVolumeDensity_pos c (FiberBundle.mem_baseSet_trivializationAt' c)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpR : 0 < (p : ℝ) := NNReal.coe_pos.2 (zero_lt_one.trans_le hp)
  -- The bump function equal to `1` on the ball of radius `r / 4`, supported in radius `r / 2`.
  let b : ContDiffBump (φ c) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbr : closedBall (φ c) b.rOut ⊆ ball (φ c) r := closedBall_subset_ball (half_lt_self hr)
  obtain ⟨G, hG⟩ := ((b.contDiff (n := 1)).continuous_fderiv one_ne_zero
    ).bounded_above_of_compact_support (b.hasCompactSupport.fderiv ℝ)
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  -- The constants: `D` bounds the derivative of the cut-off function, `K` is the flat constant.
  set D : ℝ≥0∞ := 2 * ENNReal.ofReal (C₁ + G) * ENNReal.ofReal (ρ c / 2)⁻¹ ^ (p : ℝ)⁻¹
  set K : ℝ≥0 := SNormLESNormFDerivOfEqConst ℝ μ p
  set A : ℝ≥0∞ := ENNReal.ofReal (2 * ρ c) ^ (p' : ℝ)⁻¹
  have hA : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hD : D ≠ ∞ := by
    have : ENNReal.ofReal (ρ c / 2)⁻¹ ^ (p : ℝ)⁻¹ ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    finiteness
  refine ⟨φ.source ∩ φ ⁻¹' ball (φ c) b.rIn,
    inter_mem (extChartAt_source_mem_nhds c)
      ((continuousAt_extChartAt c).preimage_mem_nhds (ball_mem_nhds _ b.rIn_pos)),
    (A * K * D).toNNReal, fun u hu ↦ ?_⟩
  set X := eLpNorm (fun x ↦ ‖mgradient I u x‖) p dV + eLpNorm u p dV
  -- Cut `u` off in the chart.
  set w : E → ℝ := fun y ↦ b y * u (φ.symm y)
  have hw : ContDiff ℝ 1 w := b.contDiff_mul_comp_extChartAt_symm (hbr.trans hrt) hu
  have hwcs : HasCompactSupport w := b.hasCompactSupport.mul_right
  -- The `Lᵖ` integrals are bounded by the `p`-th powers of the norms, measurable or not.
  have hle : ∀ f : M → ℝ, ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂dV ≤ eLpNorm f p dV ^ (p : ℝ) := fun f ↦ by
    by_cases hf : AEStronglyMeasurable f dV
    · exact (eLpNorm_nnreal_pow_eq_lintegral hp0 hf).ge
    · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.top_rpow_of_pos hpR]
      exact le_top
  have hgrad := hle fun x ↦ ‖mgradient I u x‖
  simp only [enorm_norm] at hgrad
  -- The derivative of the cut-off function has `Lᵖ` norm at most `D X`.
  have hDw : eLpNorm (fderiv ℝ w) p μ ≤ D * X := by
    rw [← ENNReal.rpow_le_rpow_iff hpR,
      eLpNorm_nnreal_pow_eq_lintegral hp0 (hw.continuous_fderiv one_ne_zero).aestronglyMeasurable]
    have hK : ENNReal.ofReal C₁ ≤ ENNReal.ofReal (C₁ + G) :=
      ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hG0)
    have hK' : ENNReal.ofReal G ≤ ENNReal.ofReal (C₁ + G) :=
      ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hC₁.le)
    have hX₁ : eLpNorm (fun x ↦ ‖mgradient I u x‖) p dV ≤ X := le_self_add
    have hX₂ : eLpNorm u p dV ≤ X := le_add_self
    calc ∫⁻ y, ‖fderiv ℝ w y‖ₑ ^ (p : ℝ) ∂μ
        ≤ 2 ^ ((p : ℝ) - 1) * ENNReal.ofReal (ρ c / 2)⁻¹ *
            (ENNReal.ofReal C₁ ^ (p : ℝ) * ∫⁻ x, ‖mgradient I u x‖ₑ ^ (p : ℝ) ∂dV +
              ENNReal.ofReal G ^ (p : ℝ) * ∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂dV) :=
          b.lintegral_enorm_fderiv_mul_comp_extChartAt_symm_rpow_le hbr hrt hC₁.le
            (fun y hy ↦ (hball y hy).1) (by positivity) (fun y hy ↦ (hball y hy).2.1.le) hG hu
            (by exact_mod_cast hp)
      _ ≤ 2 ^ ((p : ℝ) - 1) * ENNReal.ofReal (ρ c / 2)⁻¹ *
            (ENNReal.ofReal (C₁ + G) ^ (p : ℝ) * X ^ (p : ℝ) +
              ENNReal.ofReal (C₁ + G) ^ (p : ℝ) * X ^ (p : ℝ)) := by
          gcongr
          · exact hgrad.trans (ENNReal.rpow_le_rpow hX₁ hpR.le)
          · exact (hle u).trans (ENNReal.rpow_le_rpow hX₂ hpR.le)
      _ = (D * X) ^ (p : ℝ) := by
          have h2 : (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * 2 ^ (1 : ℝ) = 2 ^ (p : ℝ) := by
            rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, sub_add_cancel]
          rw [ENNReal.rpow_one] at h2
          rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ hpR.le,
            ENNReal.mul_rpow_of_nonneg _ _ hpR.le, ENNReal.mul_rpow_of_nonneg _ _ hpR.le,
            ENNReal.rpow_inv_rpow hpR.ne', ← h2]
          ring
  -- The flat Sobolev inequality for `w`.
  have hGNS : eLpNorm w p' μ ≤ K * eLpNorm (fderiv ℝ w) p μ :=
    eLpNorm_le_eLpNorm_fderiv_of_eq μ hw hwcs hp hn hp'
  -- Read the `L^{p'}` norm of `u` over the chart preimage of the small ball in the chart.
  have hloc : eLpNorm u p' (dV.restrict (φ.source ∩ φ ⁻¹' ball (φ c) b.rIn)) ≤
      A * eLpNorm w p' μ := by
    rcases eq_or_ne p' 0 with hp'0 | hp'0
    · simp [hp'0, eLpNorm_exponent_zero hu.continuous.aestronglyMeasurable]
    have hp'R : 0 < (p' : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hp'0)
    rw [← ENNReal.rpow_le_rpow_iff hp'R,
      eLpNorm_nnreal_pow_eq_lintegral hp'0 hu.continuous.aestronglyMeasurable,
      ENNReal.mul_rpow_of_nonneg _ _ hp'R.le, ENNReal.rpow_inv_rpow hp'R.ne',
      eLpNorm_nnreal_pow_eq_lintegral hp'0 hw.continuous.aestronglyMeasurable]
    have hb : ball (φ c) b.rIn ⊆ ball (φ c) r :=
      ball_subset_closedBall.trans ((closedBall_subset_closedBall b.rIn_lt_rOut.le).trans hbr)
    exact (b.setLIntegral_inter_preimage_le_mul_setLIntegral_mul_comp_extChartAt_symm
      (hb.trans hrt) (fun y hy ↦ (hball y (hb hy)).2.2.le) u fun t ↦ ‖t‖ₑ ^ (p' : ℝ)).trans
      (by gcongr; exact Measure.restrict_le_self)
  calc eLpNorm u p' (dV.restrict (φ.source ∩ φ ⁻¹' ball (φ c) b.rIn))
      ≤ A * (K * (D * X)) := hloc.trans (by gcongr; exact hGNS.trans (by gcongr))
    _ = (A * K * D).toNNReal * X := by
        rw [ENNReal.coe_toNNReal (by finiteness)]
        ring

/-- **The Sobolev inequality on a closed Riemannian manifold.** Let `1 ≤ p` and let `p'` be the
Sobolev conjugate exponent, `1 / p' = 1 / p - 1 / n`, on a compact manifold without boundary of
dimension `n > 0` with a continuous Riemannian metric. There is a constant `C` such that
`‖u‖_{L^{p'}} ≤ C (‖∇u‖_{Lᵖ} + ‖u‖_{Lᵖ})` for every `C¹` function `u`. -/
theorem exists_eLpNorm_le_mul_eLpNorm_mgradient_add [CompactSpace M] {p p' : ℝ≥0} (hp : 1 ≤ p)
    (hn : 0 < finrank ℝ E) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm u p' (riemannianVolume I M) ≤
        C * (eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M) +
          eLpNorm u p (riemannianVolume I M)) := by
  choose V hV C hC using
    exists_mem_nhds_eLpNorm_restrict_le_mul_eLpNorm_mgradient_add (I := I) (M := M) hp hn hp'
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover V fun c _ ↦ hV c
  rcases eq_or_ne p' 0 with hp'0 | hp'0
  · refine ⟨0, fun u hu ↦ ?_⟩
    simp [hp'0, eLpNorm_exponent_zero hu.continuous.aestronglyMeasurable]
  have hp'R : 0 < (p' : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hp'0)
  -- The common constant: `C₀ ^ p' = ∑ c ∈ t, C c ^ p'`.
  set C₀ : ℝ≥0∞ := (∑ c ∈ t, (C c : ℝ≥0∞) ^ (p' : ℝ)) ^ (p' : ℝ)⁻¹
  have hC₀ : C₀ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.sum_ne_top.2 fun c _ ↦ ENNReal.rpow_ne_top_of_nonneg hp'R.le ENNReal.coe_ne_top)
  refine ⟨C₀.toNNReal, fun u hu ↦ ?_⟩
  set X := eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M) +
    eLpNorm u p (riemannianVolume I M)
  rw [ENNReal.coe_toNNReal hC₀, ← ENNReal.rpow_le_rpow_iff hp'R,
    eLpNorm_nnreal_pow_eq_lintegral hp'0 hu.continuous.aestronglyMeasurable,
    ENNReal.mul_rpow_of_nonneg _ _ hp'R.le, ENNReal.rpow_inv_rpow hp'R.ne', Finset.sum_mul]
  calc ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂riemannianVolume I M
      ≤ ∑ c ∈ t, ∫⁻ x in V c, ‖u x‖ₑ ^ (p' : ℝ) ∂riemannianVolume I M := by
        rw [← setLIntegral_univ]
        exact (lintegral_mono_set ht).trans (lintegral_biUnion_finset_le _ _ _)
    _ ≤ ∑ c ∈ t, (C c : ℝ≥0∞) ^ (p' : ℝ) * X ^ (p' : ℝ) := by
        refine Finset.sum_le_sum fun c _ ↦ ?_
        rw [← eLpNorm_nnreal_pow_eq_lintegral hp'0 hu.continuous.aestronglyMeasurable,
          ← ENNReal.mul_rpow_of_nonneg _ _ hp'R.le]
        exact ENNReal.rpow_le_rpow (hC c u hu) hp'R.le

/-- **The Sobolev inequality for `H¹` on a closed Riemannian manifold.** On a compact manifold
without boundary of dimension `n > 2` with a continuous Riemannian metric, there is a constant `C`
such that `‖u‖_{L^{2n/(n-2)}} ≤ C (‖∇u‖_{L²} + ‖u‖_{L²})` for every `C¹` function `u`. -/
theorem exists_eLpNorm_le_mul_eLpNorm_mgradient_two_add [CompactSpace M] (hn : 2 < finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm u (ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (riemannianVolume I M) ≤
        C * (eLpNorm (fun x ↦ ‖mgradient I u x‖) 2 (riemannianVolume I M) +
          eLpNorm u 2 (riemannianVolume I M)) := by
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  have hp' : ((2 * finrank ℝ E / (finrank ℝ E - 2) : ℝ).toNNReal : ℝ)⁻¹ =
      ((2 : ℝ≥0) : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹ := by
    rw [Real.coe_toNNReal _ (div_nonneg (by positivity) (by linarith)), NNReal.coe_ofNat]
    field_simp
  exact exists_eLpNorm_le_mul_eLpNorm_mgradient_add (I := I) (M := M) one_le_two (by omega) hp'

end TauCeti.Manifold
