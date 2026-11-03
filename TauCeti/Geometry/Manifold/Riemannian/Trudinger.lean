/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.Sobolev.Trudinger
public import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.MeasureTheory.Integral.Lebesgue.BiUnion

/-!
# Trudinger's inequality on a closed Riemannian manifold

Let `M` be a compact manifold without boundary, of dimension `n ≥ 2`, with a continuous
Riemannian metric and its Riemannian volume `dV`. **Trudinger's inequality** says that a function
of unit `W^{1,n}` norm is exponentially integrable: there are constants `β > 0` and `C` such that

`∫_M exp (β |u| ^ (n / (n - 1))) dV ≤ C`

for every `C¹` function `u` with `‖∇u‖_{Lⁿ} + ‖u‖_{Lⁿ} ≤ 1`
(`TauCeti.Manifold.exists_lintegral_exp_mul_abs_rpow_le`). On a closed surface, `n = 2`, this is
the two-dimensional exponential estimate `∫_M exp (β u²) dV ≤ C` for `‖∇u‖_{L²} + ‖u‖_{L²} ≤ 1`
(`TauCeti.Manifold.exists_lintegral_exp_mul_sq_le_of_finrank_eq_two`). It is what makes `e^(2u)`
integrable, with a bound in terms of the `H¹` norm of `u`, in the variational treatment of the
prescribed Gaussian curvature equation `Δ⁺u + K₀ = K e^(2u)` on a closed surface.

The proof localizes the flat inequality
`TauCeti.setLIntegral_exp_norm_div_rpow_le_of_eLpNorm_fderiv_le`. Near each point `c`, in a
coordinate ball around the chart image of `c`, the chart density is comparable to its value at `c`
and the coordinate derivative of every function is bounded by a fixed multiple of the length of
its gradient
(`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`). A bump
function equal to `1` on a smaller coordinate ball cuts `u` off to a compactly supported `C¹`
function on the model space, whose derivative has `Lⁿ` norm bounded by a constant depending only
on `c`, the metric and the bump; the flat inequality then bounds the integral of
`exp (β |u| ^ (n / (n - 1)))` over the chart preimage of the smaller ball
(`TauCeti.Manifold.exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le`). Finitely many such
neighbourhoods cover `M`.

## Main results

* `TauCeti.Manifold.exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le`: the local inequality,
  near any point of a manifold without boundary.
* `TauCeti.Manifold.exists_lintegral_exp_mul_abs_rpow_le`: Trudinger's inequality on a closed
  Riemannian manifold of dimension at least two.
* `TauCeti.Manifold.exists_lintegral_exp_mul_sq_le_of_finrank_eq_two`: its form on a closed
  surface.

## References

* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 2.
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
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

/-! ### Trudinger's inequality -/

/-- **Trudinger's inequality near a point.** Every point `c` of a manifold without boundary, of
dimension `n ≥ 2`, with a continuous Riemannian metric, has a neighbourhood `V` with constants
`β > 0` and `C` such that `∫_V exp (β |u| ^ (n / (n - 1))) dV ≤ C` for every `C¹` function `u`
with `‖∇u‖_{Lⁿ} + ‖u‖_{Lⁿ} ≤ 1`. -/
theorem exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le [LindelofSpace M] (hn : 2 ≤ finrank ℝ E)
    (c : M) :
    ∃ V ∈ 𝓝 c, ∃ β > 0, ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm (fun x ↦ ‖mgradient I u x‖) (finrank ℝ E) (riemannianVolume I M) +
          eLpNorm u (finrank ℝ E) (riemannianVolume I M) ≤ 1 →
        ∫⁻ x in V, ENNReal.ofReal (Real.exp (β * |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1))))
          ∂riemannianVolume I M ≤ C := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- A coordinate ball of radius `r` around the chart image of `c`, adapted to the metric.
  obtain ⟨C₁, hC₁, r, hr, hrt, hball⟩ :=
    exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo (I := I) (M := M) c
  set n := finrank ℝ E
  set q : ℝ := (n : ℝ) / (n - 1)
  set φ := extChartAt I c
  set μ := (Module.finBasis ℝ E).addHaar
  set ρ := chartVolumeDensity (I := I) c
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 < q := div_pos (by positivity) (by linarith)
  have hρc : 0 < ρ c := chartVolumeDensity_pos c (FiberBundle.mem_baseSet_trivializationAt' c)
  -- The bump function equal to `1` on the ball of radius `r / 4`, supported in radius `r / 2`.
  let b : ContDiffBump (φ c) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbr : closedBall (φ c) b.rOut ⊆ ball (φ c) r := closedBall_subset_ball (half_lt_self hr)
  obtain ⟨G, hG⟩ := ((b.contDiff (n := 1)).continuous_fderiv one_ne_zero
    ).bounded_above_of_compact_support (b.hasCompactSupport.fderiv ℝ)
  -- The constants: `D X` bounds `‖D(b u)‖_{Lⁿ}`, so `A` bounds it when `X ≤ 1`.
  set D : ℝ≥0∞ := 2 * ENNReal.ofReal (C₁ + G) * ENNReal.ofReal (ρ c / 2)⁻¹ ^ (n : ℝ)⁻¹
  have hD : D ≠ ∞ := by
    have : ENNReal.ofReal (ρ c / 2)⁻¹ ^ (n : ℝ)⁻¹ ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    finiteness
  set A : ℝ := D.toReal + 1
  have hA : 0 < A := by positivity
  set κ : ℝ := (2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * (n : ℝ)⁻¹ *
    μ.real (ball 0 1) ^ (-(n : ℝ)⁻¹)
  have hκ : 0 < κ := by
    have : 0 < μ.real (ball 0 1) :=
      ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
    positivity
  set C : ℝ≥0∞ := ENNReal.ofReal (2 * ρ c) *
    (ENNReal.ofReal (Real.exp 1 * (n ^ n + 5)) * μ (ball (φ c) r))
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
  refine ⟨φ.source ∩ φ ⁻¹' ball (φ c) b.rIn,
    inter_mem (extChartAt_source_mem_nhds c)
      ((continuousAt_extChartAt c).preimage_mem_nhds (ball_mem_nhds _ b.rIn_pos)),
    ((κ * A) ^ q)⁻¹, by positivity, C.toNNReal, fun u hu hnorm ↦ ?_⟩
  -- Cut `u` off in the chart.
  set w : E → ℝ := fun y ↦ b y * u (φ.symm y)
  have hw : ContDiff ℝ 1 w := b.contDiff_mul_comp_extChartAt_symm (hbr.trans hrt) hu
  have hwcs : HasCompactSupport w := b.hasCompactSupport.mul_right
  have hwsupp : tsupport w ⊆ ball (φ c) r := tsupport_mul_subset_left.trans (b.tsupport_eq ▸ hbr)
  -- The derivative of the cut-off function has `Lⁿ` norm at most `A`.
  have hDwA : eLpNorm (fderiv ℝ w) n μ ≤ ENNReal.ofReal A := by
    have h := b.eLpNorm_fderiv_mul_comp_extChartAt_symm_le hbr hrt hC₁.le
      (fun y hy ↦ (hball y hy).1) (m := ρ c / 2) (by positivity)
      (fun y hy ↦ (hball y hy).2.1.le) hG hu (p := n) (by exact_mod_cast (by omega : 1 ≤ n))
    rw [ENNReal.coe_natCast, NNReal.coe_natCast] at h
    calc _ ≤ D * 1 := h.trans (by gcongr)
      _ = ENNReal.ofReal D.toReal := by rw [mul_one, ENNReal.ofReal_toReal hD]
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
  -- The flat Trudinger inequality for `w` on the ball of radius `r`, read back on `M`.
  have htr := setLIntegral_exp_norm_div_rpow_le_of_eLpNorm_fderiv_le (μ := μ) hw hwcs
    hwsupp hn hA hDwA
  have hb : ball (φ c) b.rIn ⊆ ball (φ c) r :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall b.rIn_lt_rOut.le).trans hbr)
  have hF (t : ℝ) : ((κ * A) ^ q)⁻¹ * |t| ^ q = (‖t‖ / (κ * A)) ^ q := by
    rw [Real.div_rpow (norm_nonneg _) (by positivity), Real.norm_eq_abs, div_eq_inv_mul]
  rw [ENNReal.coe_toNNReal hC]
  simp only [hF]
  calc _ ≤ ENNReal.ofReal (2 * ρ c) * ∫⁻ y in ball (φ c) b.rIn,
          ENNReal.ofReal (Real.exp ((‖w y‖ / (κ * A)) ^ q)) ∂μ :=
        b.setLIntegral_inter_preimage_le_mul_setLIntegral_mul_comp_extChartAt_symm (hb.trans hrt)
          (fun y hy ↦ (hball y (hb hy)).2.2.le) u
          fun t ↦ ENNReal.ofReal (Real.exp ((‖t‖ / (κ * A)) ^ q))
    _ ≤ ENNReal.ofReal (2 * ρ c) *
          ∫⁻ y in ball (φ c) r, ENNReal.ofReal (Real.exp ((‖w y‖ / (κ * A)) ^ q)) ∂μ := by
        gcongr _ * ?_
        exact lintegral_mono_set hb
    _ ≤ C := mul_le_mul_of_nonneg_left htr bot_le

/-- **Trudinger's inequality on a closed Riemannian manifold.** On a compact manifold without
boundary, of dimension `n ≥ 2`, with a continuous Riemannian metric, there are constants `β > 0`
and `C` such that `∫_M exp (β |u| ^ (n / (n - 1))) dV ≤ C` for every `C¹` function `u` with
`‖∇u‖_{Lⁿ} + ‖u‖_{Lⁿ} ≤ 1`. -/
theorem exists_lintegral_exp_mul_abs_rpow_le [CompactSpace M] (hn : 2 ≤ finrank ℝ E) :
    ∃ β > 0, ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm (fun x ↦ ‖mgradient I u x‖) (finrank ℝ E) (riemannianVolume I M) +
          eLpNorm u (finrank ℝ E) (riemannianVolume I M) ≤ 1 →
        ∫⁻ x, ENNReal.ofReal (Real.exp (β * |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1))))
          ∂riemannianVolume I M ≤ C := by
  choose V hV β hβ C hC using exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le (I := I) (M := M) hn
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover V fun c _ ↦ hV c
  -- A common exponent: `β₀⁻¹ = 1 + ∑ c ∈ t, (β c)⁻¹`.
  have hsum : 0 ≤ ∑ c ∈ t, (β c)⁻¹ := Finset.sum_nonneg fun c _ ↦ (inv_pos.2 (hβ c)).le
  refine ⟨(1 + ∑ c ∈ t, (β c)⁻¹)⁻¹, inv_pos.2 (by linarith), ∑ c ∈ t, C c,
    fun u hu hnorm ↦ ?_⟩
  calc ∫⁻ x, ENNReal.ofReal (Real.exp ((1 + ∑ c ∈ t, (β c)⁻¹)⁻¹ *
          |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1)))) ∂riemannianVolume I M
      ≤ ∑ c ∈ t, ∫⁻ x in V c, ENNReal.ofReal (Real.exp ((1 + ∑ c ∈ t, (β c)⁻¹)⁻¹ *
          |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1)))) ∂riemannianVolume I M := by
        rw [← setLIntegral_univ]
        exact (lintegral_mono_set ht).trans (lintegral_biUnion_finset_le _ _ _)
    _ ≤ ∑ c ∈ t, (C c : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun c hc ↦ (lintegral_mono fun x ↦ ?_).trans (hC c u hu hnorm)
        gcongr
        exact inv_le_of_inv_le₀ (hβ c) (le_add_of_nonneg_of_le zero_le_one
          (Finset.single_le_sum (f := fun c ↦ (β c)⁻¹) (fun c _ ↦ (inv_pos.2 (hβ c)).le) hc))
    _ = ((∑ c ∈ t, C c : ℝ≥0) : ℝ≥0∞) := (ENNReal.ofNNReal_finsetSum _ _).symm

/-- **The two-dimensional exponential estimate.** On a closed surface with a continuous Riemannian
metric, there are constants `β > 0` and `C` such that `∫_M exp (β u²) dV ≤ C` for every `C¹`
function `u` with `‖∇u‖_{L²} + ‖u‖_{L²} ≤ 1`. -/
theorem exists_lintegral_exp_mul_sq_le_of_finrank_eq_two [CompactSpace M]
    (hE : finrank ℝ E = 2) :
    ∃ β > 0, ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm (fun x ↦ ‖mgradient I u x‖) 2 (riemannianVolume I M) +
          eLpNorm u 2 (riemannianVolume I M) ≤ 1 →
        ∫⁻ x, ENNReal.ofReal (Real.exp (β * u x ^ 2)) ∂riemannianVolume I M ≤ C := by
  obtain ⟨β, hβ, C, h⟩ := exists_lintegral_exp_mul_abs_rpow_le (I := I) (M := M) hE.ge
  refine ⟨β, hβ, C, fun u hu hnorm ↦ ?_⟩
  have h2 := h u hu (by rwa [hE, Nat.cast_ofNat])
  norm_num [hE] at h2
  simpa only [Real.rpow_two, sq_abs] using h2

end TauCeti.Manifold
