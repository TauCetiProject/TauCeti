/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Dilation
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.SpecialFunctions.Log.InvLog
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Sobolev.Local.LogLogExample
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving

/-!
# The exponents of the `L²`-based Gagliardo–Nirenberg inequality

The `L²`-based Gagliardo–Nirenberg inequality on a space `E` of dimension `d` reads

`‖u‖_q ≤ C ‖u‖₂ ^ (1 - θ) ‖∇u‖₂ ^ θ`,  `θ = d (1/2 - 1/q)`,

for `2 ≤ q ≤ 2d / (d - 2)` when `d ≥ 3` and `2 ≤ q < ∞` when `d = 2`. This file records the two
facts that fix its exponents.

* **Scaling forces `θ`.** Replacing `u` by its dilate `u (r⁻¹ •)` multiplies `‖u‖_q` by
  `r ^ (d / q)`, `‖u‖₂` by `r ^ (d / 2)` and `‖∇u‖₂` by `r ^ (d / 2 - 1)`
  (`MeasureTheory.Measure.eLpNorm_comp_inv_smul`,
  `MeasureTheory.Measure.eLpNorm_fderiv_comp_inv_smul`). If the inequality held, for some `θ`
  and some constant, for all compactly supported smooth functions, then applying it to the
  dilates of one bump function would bound `r ^ (d / q - d / 2 + θ)` uniformly in `r > 0`, so
  that exponent vanishes and `θ = d / 2 - d / q` (`eq_of_forall_eLpNorm_le_mul_rpow_mul_rpow`).
  This holds for every exponent `q`, `q = ∞` included, and on every finite-dimensional real
  normed space with an additive Haar measure.
* **In dimension two the endpoint `q = ∞` is excluded.** In a two-dimensional real inner product
  space, the function `log log (4 / ‖x‖)`, multiplied by a smooth cutoff equal to `1` near the
  origin, lies in `W^{1,2}` of the whole space but is not essentially bounded
  (`exists_w1p_value_eq_log_log_not_memLp_top_of_finrank_eq_two`). Hence no inequality
  `‖u‖_∞ ≤ C ‖u‖₂ ^ (1 - θ) ‖∇u‖₂ ^ θ` with `0 ≤ θ ≤ 1` holds on `W^{1,2}`
  (`not_exists_eLpNorm_w1p_value_top_le_of_finrank_eq_two`), although scaling alone allows
  `θ = 1` there. The function is transported from the planar example `TauCeti.logLogInterior`
  on `ℂ` along a linear isometry onto `ℂ`.

## References

* O. A. Ladyzhenskaya, *The Mathematical Theory of Viscous Incompressible Flow*, 2nd ed., Gordon
  and Breach, 1969, Chapter 1, §1.
* J. Bedrossian and V. Vicol, *The Mathematical Analysis of the Incompressible Euler and
  Navier–Stokes Equations: An Introduction*, Graduate Studies in Mathematics 225, American
  Mathematical Society, 2022, Theorem A.26.
* L. C. Evans, *Partial Differential Equations*, §5.6.3 (the example `log log (1 / |x|)` of an
  unbounded `W^{1,n}` function).
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti.Examples.GagliardoNirenberg

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Testing a putative Gagliardo–Nirenberg inequality on the dilate `u (r⁻¹ •)` of a compactly
supported `Cᵏ` function `u` and collecting the powers of `r`: the left side carries
`r ^ (d / q)` and the right side `r ^ (d / 2 - θ)`. -/
private theorem ofReal_rpow_mul_eLpNorm_le_of_forall {q : ℝ≥0∞} {k : ℕ∞} {θ : ℝ} {C : ℝ≥0}
    (h : ∀ u : E → ℝ, ContDiff ℝ k u → HasCompactSupport u →
      eLpNorm u q μ ≤ C * (eLpNorm u 2 μ ^ (1 - θ) * eLpNorm (fderiv ℝ u) 2 μ ^ θ))
    {u : E → ℝ} (hu : ContDiff ℝ k u) (huc : HasCompactSupport u) (hB : eLpNorm u 2 μ ≠ ∞)
    (hG : eLpNorm (fderiv ℝ u) 2 μ ≠ ∞) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / q.toReal)) * eLpNorm u q μ ≤
      C * (ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / 2 - θ)) *
        (eLpNorm u 2 μ ^ (1 - θ) * eLpNorm (fderiv ℝ u) 2 μ ^ θ)) := by
  have h1 := h (fun x ↦ u (r⁻¹ • x))
    (hu.comp (ContDiff.const_smul r⁻¹ (contDiff_id (𝕜 := ℝ) (E := E))))
    (huc.comp_homeomorph (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))))
  rw [μ.eLpNorm_comp_inv_smul _ hr.ne' q, μ.eLpNorm_comp_inv_smul _ hr.ne' 2,
    μ.eLpNorm_fderiv_comp_inv_smul _ hr.ne' 2, abs_of_pos hr, ENNReal.toReal_ofNat] at h1
  refine h1.trans_eq ?_
  rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hB,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hG,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _),
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _), ← Real.rpow_mul hr.le,
    ← Real.rpow_mul hr.le, mul_mul_mul_comm, ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_add hr]
  congr 4
  ring

/-- **Scaling forces the exponent of the Gagliardo–Nirenberg inequality.** Let `E` be a nontrivial
finite-dimensional real normed space of dimension `d` with an additive Haar measure `μ`, and let
`q ≠ 0`. If for some real `θ` and some constant `C` the inequality

`‖u‖_q ≤ C ‖u‖₂ ^ (1 - θ) ‖Du‖₂ ^ θ`

holds for every compactly supported `Cᵏ` function `u : E → ℝ`, then `θ = d / 2 - d / q`, where
`1 / q` is `0` for `q = ∞`. -/
theorem eq_of_forall_eLpNorm_le_mul_rpow_mul_rpow [Nontrivial E] {q : ℝ≥0∞} (hq : q ≠ 0)
    {k : ℕ∞} {θ : ℝ} {C : ℝ≥0}
    (h : ∀ u : E → ℝ, ContDiff ℝ k u → HasCompactSupport u →
      eLpNorm u q μ ≤ C * (eLpNorm u 2 μ ^ (1 - θ) * eLpNorm (fderiv ℝ u) 2 μ ^ θ)) :
    θ = finrank ℝ E / 2 - finrank ℝ E * (q⁻¹).toReal := by
  -- Fix one bump function; its dilates are admissible test functions.
  set φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hφc : Continuous (φ : E → ℝ) := (φ.contDiff (n := 0)).continuous
  have hdφc : Continuous (fderiv ℝ (φ : E → ℝ)) :=
    (φ.contDiff (n := 1)).continuous_fderiv one_ne_zero
  have hφ0 : (φ : E → ℝ) 0 ≠ 0 := by
    rw [φ.one_of_mem_closedBall (by simp [φ.rIn_pos.le])]
    exact one_ne_zero
  -- The bump is not constant, since it vanishes at distance `2` from the origin.
  have hdφ : ∃ x, fderiv ℝ (φ : E → ℝ) x ≠ 0 := by
    by_contra! hcon
    obtain ⟨y, hy⟩ := exists_norm_eq E (zero_le_two (α := ℝ))
    refine hφ0 ((is_const_of_fderiv_eq_zero (φ.contDiff (n := 1)).differentiable_one hcon
      0 y).trans (φ.zero_of_le_dist ?_))
    rw [dist_zero_right, hy]
  obtain ⟨x₁, hx₁⟩ := hdφ
  set A := eLpNorm (φ : E → ℝ) q μ
  set B := eLpNorm (φ : E → ℝ) 2 μ
  set G := eLpNorm (fderiv ℝ (φ : E → ℝ)) 2 μ with hG
  -- A continuous function vanishing almost everywhere vanishes identically.
  have hφne : (φ : E → ℝ) ≠ 0 := fun h1 ↦ hφ0 (congrFun h1 0)
  have hA : A ≠ 0 := fun h0 ↦ hφne
    ((Continuous.ae_eq_iff_eq μ hφc continuous_zero).1 ((eLpNorm_eq_zero_iff hq).1 h0))
  have hB0 : B ≠ 0 := fun h0 ↦ hφne
    ((Continuous.ae_eq_iff_eq μ hφc continuous_zero).1 ((eLpNorm_eq_zero_iff two_ne_zero).1 h0))
  have hG0 : G ≠ 0 := by
    intro h0
    replace h0 := (eLpNorm_norm _ hdφc.aestronglyMeasurable).trans (hG ▸ h0)
    have h1 : (fun x ↦ ‖fderiv ℝ (φ : E → ℝ) x‖) = 0 :=
      (Continuous.ae_eq_iff_eq μ hdφc.norm continuous_zero).1
        ((eLpNorm_eq_zero_iff two_ne_zero).1 h0)
    exact hx₁ (norm_eq_zero.1 (congrFun h1 x₁))
  have hBt : B ≠ ∞ :=
    (hφc.memLp_of_hasCompactSupport (μ := μ) (p := 2) φ.hasCompactSupport).eLpNorm_lt_top.ne
  have hGt : G ≠ ∞ := (hdφc.memLp_of_hasCompactSupport (μ := μ) (p := 2)
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))).eLpNorm_lt_top.ne
  have hK : B ^ (1 - θ) * G ^ θ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hB0 hBt)
      (ENNReal.rpow_ne_top_of_ne_zero hG0 hGt)
  have he := Real.eq_zero_of_forall_rpow_le (K := C * (B ^ (1 - θ) * G ^ θ).toReal / A.toReal)
    fun r hr ↦ Real.rpow_sub_le_div_of_ofReal_rpow_mul_le hr hA hK
      (ofReal_rpow_mul_eLpNorm_le_of_forall h (φ.contDiff (n := k)) φ.hasCompactSupport hBt hGt hr)
  rw [ENNReal.toReal_inv, ← div_eq_mul_inv]
  linarith

end Scaling

section Endpoint

/-- The planar example `log log (4 / ‖z‖)` agrees on the closed unit disc with an element of
`W^{1,2}(ℂ)`: cut off and extended by zero, it lies in `W^{1,2}` of the whole plane. -/
private theorem exists_w1p_value_eq_logLogInterior :
    ∃ w : W1p (volume : Measure ℂ) ⊤ 2,
      ∀ᵐ z ∂volume, z ∈ closedBall (0 : ℂ) 1 → W1p.value w z = logLogInterior z := by
  obtain ⟨v, hv, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn (p := 2)
    (Omega := ⟨ball (0 : ℂ) 2, isOpen_ball⟩) (memLp_logLogInterior (by norm_num))
    (memLp_fderiv_logLogInterior (by norm_num))
    (hasWeakFDerivOn_logLogInterior.mono fun z hz ↦ ball_subset_ball (by norm_num) hz)
  obtain ⟨w, hw, -⟩ := W1p.exists_top_value_gradient_ae_eq_on_of_isCompact (by norm_num) v
    (isCompact_closedBall (0 : ℂ) 1) (closedBall_subset_ball (by norm_num))
  refine ⟨w, ?_⟩
  have hv' := (ae_restrict_iff' measurableSet_ball).1 hv
  filter_upwards [hw, hv'] with z h1 h2 hz
  rw [h1 hz, h2 (closedBall_subset_ball (by norm_num) hz)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A function equal near the origin to `log log (4 / ‖x‖)`, which tends to `∞` at the origin, is
not essentially bounded against any additive Haar measure. -/
private theorem not_memLp_top_of_ae_eq_log_log [Nontrivial E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : ∀ᵐ x ∂μ, ‖x‖ ≤ 1 → f x = Real.log (Real.log (4 / ‖x‖))) :
    ¬ MemLp f ∞ μ := by
  intro hmem
  set M := lpNorm f ∞ μ
  -- Near the origin, `log log (4 / ‖x‖)` exceeds the essential bound `M`.
  have hlim : Tendsto (fun x : E ↦ Real.log (Real.log (4 / ‖x‖))) (𝓝[≠] 0) atTop :=
    (Real.tendsto_log_log_const_div_nhdsNE_zero four_ne_zero).comp
      ((tendsto_norm_nhdsNE_zero (E := E)).mono_right (nhdsGT_le_nhdsNE 0))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1
    ((hlim.eventually_gt_atTop M).and eventually_mem_nhdsWithin |>.and
      (eventually_nhdsWithin_of_eventually_nhds (closedBall_mem_nhds 0 one_pos))))
  -- So almost every point of `ball 0 δ` is the origin, which is impossible.
  have hnull : μ (ball 0 δ) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hf, ae_le_lpNorm_exponent_top hmem,
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := μ) (0 : E))] with x hfx hM hx0 hx
    obtain ⟨⟨hgt, -⟩, hx1⟩ := hball x hx hx0
    rw [hfx (mem_closedBall_zero_iff.1 hx1)] at hM
    exact (hgt.trans_le ((le_abs_self _).trans_eq (Real.norm_eq_abs _ ▸ rfl) |>.trans hM)).false
  exact (measure_ball_pos μ 0 hδ).ne' hnull

/-- **`W^{1,2}` in dimension two contains unbounded functions.** In a two-dimensional real inner
product space `E`, some `u ∈ W^{1,2}(E)` equals `log log (4 / ‖x‖)` almost everywhere on the closed
unit ball and is not essentially bounded. So `W^{1,2}(E)` is not contained in `L^∞(E)`. -/
theorem exists_w1p_value_eq_log_log_not_memLp_top_of_finrank_eq_two (hE : finrank ℝ E = 2) :
    ∃ u : W1p (volume : Measure E) ⊤ 2,
      (∀ᵐ x ∂volume, ‖x‖ ≤ 1 → W1p.value u x = Real.log (Real.log (4 / ‖x‖))) ∧
        ¬ MemLp (W1p.value u) ∞ volume := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨w, hw⟩ := exists_w1p_value_eq_logLogInterior
  -- Transport the planar example to `E` along a linear isometry `E ≃ ℂ`.
  let l : E ≃ₗᵢ[ℝ] ℂ := ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)).repr.trans
    Complex.orthonormalBasisOneI.repr.symm
  let u := W1p.compAffineIsometryEquivL l.toAffineIsometryEquiv
    (U := (⊤ : Opens E)) (V := (⊤ : Opens ℂ)) (by simp) w
  have hval := W1p.value_compAffineIsometryEquivL_ae l.toAffineIsometryEquiv
    (U := (⊤ : Opens E)) (V := (⊤ : Opens ℂ)) (by simp) w
  have hval' := (ae_restrict_iff' (⊤ : Opens E).isOpen.measurableSet).1 hval
  have hpull := l.measurePreserving.quasiMeasurePreserving.ae hw
  have hu : ∀ᵐ x ∂volume, ‖x‖ ≤ 1 → W1p.value u x = Real.log (Real.log (4 / ‖x‖)) := by
    filter_upwards [hval', hpull] with x h1 h2 hx
    have hnorm : ‖l x‖ = ‖x‖ := l.norm_map x
    rw [h1 (by simp), LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      h2 (mem_closedBall_zero_iff.2 (hnorm ▸ hx)), logLogInterior_def, hnorm]
  exact ⟨u, hu, not_memLp_top_of_ae_eq_log_log hu⟩

/-- **The endpoint `q = ∞` of the Gagliardo–Nirenberg inequality fails in dimension two.** In a
two-dimensional real inner product space `E` there is no constant `C` and no `θ ∈ [0, 1]` with

`‖u‖_∞ ≤ C ‖u‖₂ ^ (1 - θ) ‖∇u‖₂ ^ θ`

for every `u ∈ W^{1,2}(E)`: the right side is always finite, while
`exists_w1p_value_eq_log_log_not_memLp_top_of_finrank_eq_two` supplies an element of `W^{1,2}(E)`
that is not essentially bounded. By `eq_of_forall_eLpNorm_le_mul_rpow_mul_rpow`, `θ = 1` is the
only exponent that scaling allows at `q = ∞` in dimension two. -/
theorem not_exists_eLpNorm_w1p_value_top_le_of_finrank_eq_two (hE : finrank ℝ E = 2) :
    ¬ ∃ (C : ℝ≥0) (θ : ℝ), 0 ≤ θ ∧ θ ≤ 1 ∧ ∀ u : W1p (volume : Measure E) ⊤ 2,
      eLpNorm (W1p.value u) ∞ volume ≤
        C * (eLpNorm (W1p.value u) 2 volume ^ (1 - θ) *
          eLpNorm (W1p.gradient u) 2 volume ^ θ) := by
  rintro ⟨C, θ, hθ0, hθ1, h⟩
  obtain ⟨u, -, hu⟩ := exists_w1p_value_eq_log_log_not_memLp_top_of_finrank_eq_two hE
  have hμ : (volume : Measure E) ≤ volume.restrict ((⊤ : Opens E) : Set E) := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hv := (Lp.memLp (W1p.value u)).mono_measure hμ
  have hg := (Lp.memLp (W1p.gradient u)).mono_measure hμ
  refine hu ((h u).trans_lt ?_)
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by linarith) hv.eLpNorm_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg hθ0 hg.eLpNorm_ne_top))

end Endpoint

end TauCeti.Examples.GagliardoNirenberg
