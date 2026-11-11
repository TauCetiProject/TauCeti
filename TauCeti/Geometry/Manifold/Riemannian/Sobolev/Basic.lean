/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

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
`‖∇u‖_{Lᵖ} + ‖u‖_{Lᵖ}` (`ContDiffBump.eLpNorm_fderiv_mul_comp_extChartAt_symm_le`).
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
* `TauCeti.Manifold.exists_integral_abs_rpow_rpow_le_mul_integral_mgradient_sq_add`: the same
  inequality squared and written with integrals,
  `(∫ |u| ^ p' dV) ^ (2 / p') ≤ K (∫ |∇u|² dV + ∫ u² dV)` for `p' = 2 n / (n - 2)`.

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
  -- The bump function equal to `1` on the ball of radius `r / 4`, supported in radius `r / 2`.
  let b : ContDiffBump (φ c) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbr : closedBall (φ c) b.rOut ⊆ ball (φ c) r := closedBall_subset_ball (half_lt_self hr)
  obtain ⟨G, hG⟩ := ((b.contDiff (n := 1)).continuous_fderiv one_ne_zero
    ).bounded_above_of_compact_support (b.hasCompactSupport.fderiv ℝ)
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
  -- The derivative of the cut-off function has `Lᵖ` norm at most `D X`.
  have hDw : eLpNorm (fderiv ℝ w) p μ ≤ D * X :=
    b.eLpNorm_fderiv_mul_comp_extChartAt_symm_le hbr hrt hC₁.le (fun y hy ↦ (hball y hy).1)
      (by positivity) (fun y hy ↦ (hball y hy).2.1.le) hG hu hp
  -- The flat Sobolev inequality for `w`.
  have hGNS : eLpNorm w p' μ ≤ K * eLpNorm (fderiv ℝ w) p μ :=
    eLpNorm_le_eLpNorm_fderiv_of_eq μ hw hwcs hp hn hp'
  -- Read the `L^{p'}` norm of `u` over the chart preimage of the small ball in the chart.
  have hb : ball (φ c) b.rIn ⊆ ball (φ c) r :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall b.rIn_lt_rOut.le).trans hbr)
  have hloc : eLpNorm u p' (dV.restrict (φ.source ∩ φ ⁻¹' ball (φ c) b.rIn)) ≤
      A * eLpNorm w p' μ :=
    b.eLpNorm_restrict_inter_preimage_ball_le_mul_eLpNorm_mul_comp_extChartAt_symm
      (hb.trans hrt) (fun y hy ↦ (hball y (hb hy)).2.2.le) hu.continuous.aestronglyMeasurable
      hw.continuous.aestronglyMeasurable
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
  -- Away from `p' = 0`, the exponent is at least `1`, since `1 / p' ≤ 1 - 1 / n < 1`.
  have hp'1 : (1 : ℝ≥0∞) ≤ p' := by
    have hp'R : 0 < (p' : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hp'0)
    have hp1 : ((p⁻¹ : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast inv_le_one_of_one_le₀ hp
    have hnR : 0 < (finrank ℝ E : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hn)
    have : (1 : ℝ) ≤ p' := by
      rw [← inv_le_inv₀ hp'R one_pos, inv_one]
      linarith
    exact_mod_cast this
  refine ⟨∑ c ∈ t, C c, fun u hu ↦ ?_⟩
  set dV := riemannianVolume I M
  calc eLpNorm u p' dV = eLpNorm u p' (dV.restrict univ) := by rw [Measure.restrict_univ]
    _ ≤ eLpNorm u p' (dV.restrict (⋃ c ∈ t, V c)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono ht le_rfl)
    _ ≤ ∑ c ∈ t, eLpNorm u p' (dV.restrict (V c)) := eLpNorm_restrict_biUnion_finset_le u hp'1 t V
    _ ≤ ∑ c ∈ t, C c * (eLpNorm (fun x ↦ ‖mgradient I u x‖) p dV + eLpNorm u p dV) :=
        Finset.sum_le_sum fun c _ ↦ hC c u hu
    _ = _ := by push_cast; rw [Finset.sum_mul]

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

/-- **The Sobolev inequality for `H¹` with integrals.** On a compact manifold without boundary of
dimension `n > 2` with a continuous Riemannian metric, let `p' = 2 n / (n - 2)`. There is a constant
`K > 0` such that `(∫ |u| ^ p' dV) ^ (2 / p') ≤ K (∫ |∇u|² dV + ∫ u² dV)` for every `C¹`
function `u`. -/
theorem exists_integral_abs_rpow_rpow_le_mul_integral_mgradient_sq_add [CompactSpace M]
    (hn : 2 < finrank ℝ E) :
    ∃ K, 0 < K ∧ ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      (∫ x, |u x| ^ (2 * finrank ℝ E / (finrank ℝ E - 2) : ℝ) ∂riemannianVolume I M) ^
          (2 / (2 * finrank ℝ E / (finrank ℝ E - 2) : ℝ)) ≤
        K * (∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, u x ^ 2 ∂riemannianVolume I M) := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_le_mul_eLpNorm_mgradient_two_add (I := I) (M := M) hn
  set p : ℝ := 2 * finrank ℝ E / (finrank ℝ E - 2)
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  have hp : 0 < p := div_pos (by positivity) (by linarith)
  refine ⟨2 * ((K : ℝ) + 1) ^ 2, by positivity, fun u hu ↦ ?_⟩
  set A := ∫ x, |u x| ^ p ∂riemannianVolume I M
  set B := ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M
  set D := ∫ x, u x ^ 2 ∂riemannianVolume I M
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  have hD : 0 ≤ D := integral_nonneg fun _ ↦ sq_nonneg _
  -- The Sobolev inequality in real numbers: `A ^ (1 / p) ≤ K (B ^ (1 / 2) + D ^ (1 / 2))`.
  have hsob : A ^ p⁻¹ ≤ K * (B ^ (2 : ℝ)⁻¹ + D ^ (2 : ℝ)⁻¹) := by
    have h := hK u hu
    rw [hu.continuous.eLpNorm_eq_integral_rpow_norm (by simpa using hp) ENNReal.ofReal_ne_top,
      (continuous_norm_mgradient hu).eLpNorm_eq_integral_rpow_norm two_ne_zero
        ENNReal.ofNat_ne_top,
      hu.continuous.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top] at h
    simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_norm,
      Real.rpow_two, sq_abs] at h
    have hK' : (K : ℝ≥0∞) * (ENNReal.ofReal (B ^ (2 : ℝ)⁻¹) + ENNReal.ofReal (D ^ (2 : ℝ)⁻¹)) =
        ENNReal.ofReal (K * (B ^ (2 : ℝ)⁻¹ + D ^ (2 : ℝ)⁻¹)) := by
      rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h.trans_eq hK')
  have hsq (X : ℝ) (hX : 0 ≤ X) (q : ℝ) (hq : q ≠ 0) : (X ^ q⁻¹) ^ 2 = X ^ (2 / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
    congr 1
    field_simp
    norm_num
  -- Squaring, with `(y + z) ^ 2 ≤ 2 (y ^ 2 + z ^ 2)`.
  have h2 := pow_le_pow_left₀ (by positivity) hsob 2
  rw [hsq A hA p hp.ne'] at h2
  have hB2 := hsq B hB 2 two_ne_zero
  have hD2 := hsq D hD 2 two_ne_zero
  rw [div_self two_ne_zero, Real.rpow_one] at hB2 hD2
  set y := B ^ (2 : ℝ)⁻¹
  set z := D ^ (2 : ℝ)⁻¹
  calc A ^ (2 / p) ≤ (K * (y + z)) ^ 2 := h2
    _ ≤ ((K : ℝ) + 1) ^ 2 * (2 * (y ^ 2 + z ^ 2)) := by
      rw [mul_pow]
      gcongr
      · linarith [K.coe_nonneg]
      · nlinarith [sq_nonneg (y - z)]
    _ = 2 * ((K : ℝ) + 1) ^ 2 * (B + D) := by
      rw [hB2, hD2]
      ring

end TauCeti.Manifold
