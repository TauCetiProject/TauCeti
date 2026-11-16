/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.MeasureTheory.Function.WeightL2Isometry
import TauCeti.MeasureTheory.Measure.Decomposition.Prod

/-!
# Differentiable paths of measures and path scores

In semiparametric statistics, tangent vectors to a statistical model at a law `P` are scores of
one-dimensional submodels `t ↦ Q t` passing through `Q 0 = P`, differentiated from the right at
`t = 0` in quadratic mean relative to a σ-finite dominating measure `ν`:
`t⁻¹ ‖√(d(Q t)/dν) - √(d(Q 0)/dν) - (t / 2) g √(d(Q 0)/dν)‖_{L²(ν)} → 0` as `t → 0⁺`.

Measuring the remainder by Mathlib's `eLpNorm` in `ℝ≥0∞` avoids Bochner-integral junk values: a
remainder that fails to be square integrable has infinite `L²(ν)` seminorm and cannot masquerade as
`o(t)`. Taking the right-hand limit `𝓝[>] 0` allows submodels whose parameter lies on a boundary at
`t = 0`, while leaving values of `Q t` for `t < 0` or away from `0` unconstrained.

## Main definitions

* `TauCeti.HasPathScore ν Q g`: quadratic-mean differentiability of `t ↦ Q t` from the right at `0`
  with score `g : X → ℝ` relative to a dominating measure `ν`.
* `TauCeti.tiltPath P g C t`: the bounded linear tilt `dP_t = (1 + t g) dP` for `|t| C < 1`, cut
  off to `P` when `1 ≤ |t| C`.

## Main statements

* `TauCeti.eLpNorm_mul_sqrt_rnDeriv`: for σ-finite measures `μ ≪ ν`, multiplying any `f : X → ℝ` by
  `√(dμ/dν)` preserves the `L²` seminorm (`‖f √(dμ/dν)‖_{L²(ν)} = ‖f‖_{L²(μ)}`).
* `TauCeti.HasPathScore.memLp`, `TauCeti.HasPathScore.tendsto_eLpNorm_sqrt_rnDeriv_sub`, and
  `TauCeti.HasPathScore.integral_eq_zero`: every path score of a path of finite measures is square
  integrable under `Q 0` (in particular `Q 0`-a.e. strongly measurable), implies `L²(ν)`
  right-continuity of `t ↦ √(d(Q t)/dν)` at `0`, and has mean zero when each `Q t` is a
  probability measure.
* `TauCeti.hasPathScore_iff_of_absolutelyContinuous`: `HasPathScore ν Q g` is independent of the
  choice of σ-finite measure dominating every `Q t`.
* `TauCeti.HasPathScore.ae_eq`: any two scores of the same path agree `Q 0`-almost everywhere.
* `TauCeti.isProbabilityMeasure_tiltPath` and `TauCeti.hasPathScore_tiltPath`: bounded mean-zero
  functions generate probability-measure tilts whose path score is the tilting function.
* `TauCeti.exists_hasPathScore_of_integral_eq_zero`: every square-integrable mean-zero function on
  a probability space is the score of a path of probability measures dominated by `P`.
* `TauCeti.HasPathScore.prod`: the product of two differentiable paths of probability measures has
  score `(x, y) ↦ g₁ x + g₂ y`.
* `TauCeti.sqrt_sub_sqrt_eq_intervalIntegral`,
  `TauCeti.isProbabilityMeasure_withDensity_ofReal_comp_sub_right`, and
  `TauCeti.hasPathScore_location`: for an absolutely continuous nonnegative density `η` on `ℝ` with
  locally integrable derivative `η'` and finite Fisher information `∫ η'² / η`, `√η` has increments
  given by `∫ η' / (2 √η)` and the location path `t ↦ η(x - θ - t) dx` has score
  `x ↦ -(η'(x - θ) / η(x - θ))` relative to Lebesgue measure.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.3
  (Lemma 25.14, Examples 25.15–25.16).
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A. Wellner, *Efficient and Adaptive Estimation
  for Semiparametric Models*, Johns Hopkins University Press, 1993, §2.1 (Example 2) and Appendix
  A.5 (Corollary 1).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section Basic

variable {X : Type*} [MeasurableSpace X]

/-- The path `t ↦ Q t` of measures is differentiable in quadratic mean from the right at `0` with
score `g`, relative to the dominating measure `ν` (typically σ-finite). The remainder is measured
by `eLpNorm` in `ℝ≥0∞`, so that a non-square-integrable remainder has infinite norm rather than
`0`. -/
def HasPathScore (ν : Measure X) (Q : ℝ → Measure X) (g : X → ℝ) : Prop :=
  (∀ t, Q t ≪ ν) ∧
    Tendsto (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
        Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
          - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) (𝓝[>] 0) (𝓝 0)

/-- Unfolding characterization of `HasPathScore`. -/
theorem hasPathScore_def (ν : Measure X) (Q : ℝ → Measure X) (g : X → ℝ) :
    HasPathScore ν Q g ↔
      (∀ t, Q t ≪ ν) ∧
        Tendsto (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
            Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
              - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- Every measure along a path with a score relative to `ν` is absolutely continuous with respect
to `ν`. -/
theorem HasPathScore.absolutelyContinuous {ν : Measure X} {Q : ℝ → Measure X}
    {g : X → ℝ} (h : HasPathScore ν Q g) (t : ℝ) : Q t ≪ ν :=
  h.1 t

/-- The `L²(ν)` quadratic-mean remainder limit of `HasPathScore`. -/
theorem HasPathScore.tendsto_eLpNorm {ν : Measure X} {Q : ℝ → Measure X}
    {g : X → ℝ} (h : HasPathScore ν Q g) :
    Tendsto (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
        Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
          - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) (𝓝[>] 0) (𝓝 0) :=
  h.2

/-- Modifying `g` on a `Q 0`-null set preserves `HasPathScore ν Q g`. -/
theorem HasPathScore.congr_ae {ν : Measure X} [SigmaFinite ν] {Q : ℝ → Measure X}
    [SigmaFinite (Q 0)] {g g' : X → ℝ} (h : HasPathScore ν Q g) (hgg' : g =ᵐ[Q 0] g') :
    HasPathScore ν Q g' := by
  refine ⟨h.1, h.2.congr fun t ↦ ?_⟩
  congr 1
  have hwd : Q 0 = ν.withDensity ((Q 0).rnDeriv ν) :=
    (Measure.withDensity_rnDeriv_eq (Q 0) ν (h.1 0)).symm
  have hae : ∀ᵐ x ∂ν, (Q 0).rnDeriv ν x ≠ 0 → g x = g' x := by
    rwa [EventuallyEq, hwd, ae_withDensity_iff (Measure.measurable_rnDeriv _ _)] at hgg'
  refine eLpNorm_congr_ae (hae.mono fun x hx ↦ ?_)
  by_cases h0 : (Q 0).rnDeriv ν x = 0
  · simp [h0]
  · simp [hx h0]

/-- Two paths dominated by `ν` that agree at `0` and eventually on `(0, ∞)` have the same path
scores. -/
theorem HasPathScore.congr_path {ν : Measure X} {Q Q' : ℝ → Measure X} {g : X → ℝ}
    (h : HasPathScore ν Q g) (hQ' : ∀ t, Q' t ≪ ν) (h0 : Q' 0 = Q 0)
    (hev : Q' =ᶠ[𝓝[>] 0] Q) : HasPathScore ν Q' g := by
  refine ⟨hQ', h.2.congr' ?_⟩
  filter_upwards [hev] with t ht
  simp [ht, h0]

/-- A constant path `t ↦ P` dominated by `ν` has path score `0`. -/
theorem hasPathScore_const {ν P : Measure X} (hP : P ≪ ν) :
    HasPathScore ν (fun _ ↦ P) 0 := by
  refine ⟨fun _ ↦ hP, ?_⟩
  simp

/-- Rescaling the parameter of a path by `c ≥ 0` scales its path score by `c`. -/
theorem HasPathScore.comp_mul_right {ν : Measure X} {Q : ℝ → Measure X}
    {g : X → ℝ} (h : HasPathScore ν Q g) {c : ℝ} (hc : 0 ≤ c) :
    HasPathScore ν (fun t ↦ Q (c * t)) (c • g) := by
  rcases hc.eq_or_lt with rfl | hc_pos
  · simpa [zero_smul] using hasPathScore_const (h.1 0)
  refine ⟨fun t ↦ h.1 (c * t), ?_⟩
  have hmap : Tendsto (fun t : ℝ ↦ c * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc_cont : Continuous fun t : ℝ ↦ c * t := by fun_prop
      simpa using (hc_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos hc_pos ht
  have hlim : Tendsto
      (fun t ↦ ENNReal.ofReal c *
        (ENNReal.ofReal (c * t)⁻¹ * eLpNorm (fun x ↦ Real.sqrt ((Q (c * t)).rnDeriv ν x).toReal -
          Real.sqrt ((Q 0).rnDeriv ν x).toReal -
          ((c * t) / 2) * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal c * 0)) :=
    ENNReal.Tendsto.const_mul (h.2.comp hmap) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hct : c * (c * t)⁻¹ = t⁻¹ := by
    have := hc_pos.ne'
    field_simp
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc, hct]
  refine congrArg (fun f ↦ ENNReal.ofReal t⁻¹ * eLpNorm f 2 ν) (funext fun x ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, mul_zero]
  ring

end Basic

/-! ### Square-integrability, mean zero, dominating-measure invariance, and uniqueness -/

section Properties

variable {X : Type*} [MeasurableSpace X]

/-- For σ-finite measures `μ ≪ ν` and any function `f : X → ℝ` (not assumed measurable),
multiplying `f` by `√(dμ/dν)` preserves the `L²` seminorm:
`‖f · √(dμ/dν)‖_{L²(ν)} = ‖f‖_{L²(μ)}`. -/
theorem eLpNorm_mul_sqrt_rnDeriv {μ ν : Measure X} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (f : X → ℝ) :
    eLpNorm (fun x ↦ f x * Real.sqrt ((μ.rnDeriv ν x).toReal)) 2 ν = eLpNorm f 2 μ := by
  set r : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hwd : ν.withDensity (fun x ↦ ENNReal.ofReal (r x)) = μ := by
    refine (withDensity_congr_ae ?_).trans (Measure.withDensity_rnDeriv_eq μ ν hμν)
    filter_upwards [μ.rnDeriv_lt_top ν] with x hlt
    exact ENNReal.ofReal_toReal hlt.ne
  by_cases hf : AEStronglyMeasurable f μ
  · set f₀ := hf.aemeasurable.mk f
    have hf₀_meas : Measurable f₀ := hf.aemeasurable.measurable_mk
    have hf₀_ae : f =ᵐ[μ] f₀ := hf.aemeasurable.ae_eq_mk
    have hae_ν : (fun x ↦ f x * Real.sqrt (r x)) =ᵐ[ν] fun x ↦ Real.sqrt (r x) • f₀ x := by
      have h1 : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ 0 → f x = f₀ x := by
        have hwd' : μ = ν.withDensity (μ.rnDeriv ν) :=
          (Measure.withDensity_rnDeriv_eq μ ν hμν).symm
        rwa [EventuallyEq, hwd', ae_withDensity_iff (Measure.measurable_rnDeriv μ ν)] at hf₀_ae
      filter_upwards [h1] with x hx
      by_cases h0 : μ.rnDeriv ν x = 0 <;> simp [r, h0, smul_eq_mul, mul_comm, hx]
    rw [eLpNorm_congr_ae hae_ν, eLpNorm_congr_ae hf₀_ae,
      TauCeti.eLpNorm_sqrt_smul_eq_eLpNorm_withDensity ν r hr_meas.aemeasurable
        hf₀_meas.aestronglyMeasurable, hwd]
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    refine eLpNorm_of_not_aestronglyMeasurable fun hν ↦ hf ?_
    set k₀ := hν.aemeasurable.mk _
    have hk₀_meas : Measurable k₀ := hν.aemeasurable.measurable_mk
    refine (hk₀_meas.div hr_meas.sqrt).aestronglyMeasurable.congr ?_
    filter_upwards [hμν hν.aemeasurable.ae_eq_mk, Measure.rnDeriv_pos hμν,
      hμν (μ.rnDeriv_lt_top ν)] with x hx hpos hlt
    have hw_ne : Real.sqrt ((μ.rnDeriv ν x).toReal) ≠ 0 :=
      (Real.sqrt_pos.mpr (ENNReal.toReal_pos hpos.ne' hlt.ne)).ne'
    dsimp [k₀, r]
    rw [← hx, mul_div_cancel_right₀ _ hw_ne]

private theorem memLp_sqrt_rnDeriv (μ ν : Measure X) [IsFiniteMeasure μ] :
    MemLp (fun x ↦ Real.sqrt ((μ.rnDeriv ν x).toReal)) 2 ν := by
  have hm : Measurable fun x ↦ Real.sqrt ((μ.rnDeriv ν x).toReal) :=
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal.sqrt
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact (integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv μ ν).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top μ ν).ne).congr
    (Eventually.of_forall fun _ ↦ (Real.sq_sqrt ENNReal.toReal_nonneg).symm)

private theorem eLpNorm_sqrt_rnDeriv_eq_one (μ ν : Measure X) [IsProbabilityMeasure μ]
    [SigmaFinite ν] (hμν : μ ≪ ν) :
    eLpNorm (fun x ↦ Real.sqrt ((μ.rnDeriv ν x).toReal)) 2 ν = 1 := by
  simpa [eLpNorm_const (1 : ℝ) two_ne_zero (NeZero.ne μ)] using
    eLpNorm_mul_sqrt_rnDeriv hμν (fun _ ↦ 1)

private theorem memLp_mul_sqrt_rnDeriv {ν : Measure X} [SigmaFinite ν] {μ : Measure X}
    [SigmaFinite μ] (hμν : μ ≪ ν) {g : X → ℝ} (hg_mem : MemLp g 2 μ) :
    MemLp (fun x ↦ g x * Real.sqrt ((μ.rnDeriv ν x).toReal)) 2 ν :=
  memLp_iff.mpr ((eLpNorm_mul_sqrt_rnDeriv hμν g).trans_lt hg_mem)

/-- Every path score of a path of finite measures is square integrable under `Q 0`, and in
particular `Q 0`-almost everywhere strongly measurable (van der Vaart, Lemma 25.14, first
assertion). -/
theorem HasPathScore.memLp {ν : Measure X} [SigmaFinite ν] {Q : ℝ → Measure X}
    [∀ t, IsFiniteMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) : MemLp g 2 (Q 0) := by
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
      Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
        - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν < 1 :=
    h.2.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨t, ht_lt, ht_pos : 0 < t⟩ := (hlt.and self_mem_nhdsWithin).exists
  set rem : X → ℝ := fun x ↦
    Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
      - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal
  have hinv_ne : ENNReal.ofReal t⁻¹ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ht_pos)
  have hrem_mem : MemLp rem 2 ν :=
    lt_top_iff_ne_top.mpr fun htop ↦ by simp [htop, ENNReal.mul_top hinv_ne] at ht_lt
  have hprod_mem : MemLp (fun x ↦ g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν := by
    have hlin := ((memLp_sqrt_rnDeriv (Q t) ν).sub (memLp_sqrt_rnDeriv (Q 0) ν)).sub hrem_mem
    refine (memLp_congr_ae (Eventually.of_forall fun x ↦ ?_)).mp (hlin.const_mul (2 / t))
    have ht0 : t ≠ 0 := ht_pos.ne'
    dsimp [rem]; field_simp; ring
  exact memLp_iff.mpr ((eLpNorm_mul_sqrt_rnDeriv (h.1 0) g).symm.trans_lt hprod_mem)

/-- Along a path of finite measures with a path score, the square-root densities `√(d(Q t)/dν)`
converge to `√(d(Q 0)/dν)` in `L²(ν)` as `t → 0⁺`. -/
theorem HasPathScore.tendsto_eLpNorm_sqrt_rnDeriv_sub {ν : Measure X} [SigmaFinite ν]
    {Q : ℝ → Measure X} [∀ t, IsFiniteMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦
      Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν)
      (𝓝[>] 0) (𝓝 0) := by
  have hprod_mem := memLp_mul_sqrt_rnDeriv (h.1 0) h.memLp
  have h_zero1 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal t * (ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
      Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
        - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν)) (𝓝[>] 0) (𝓝 0) := by
    have ht0 : Tendsto ENNReal.ofReal (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul ht0 (Or.inr ENNReal.zero_ne_top) h.2
      (Or.inr ENNReal.zero_ne_top)
  have h_zero2 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t / 2) *
      eLpNorm (fun x ↦ g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) (𝓝[>] 0) (𝓝 0) := by
    have ht0 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (t / 2) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const ht0 (Or.inr hprod_mem.ne)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using h_zero1.add h_zero2) (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hmul : ENNReal.ofReal t * (ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
      Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
        - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) =
      eLpNorm (fun x ↦ Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
        - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul ht.le, mul_inv_cancel₀ ht.ne', ENNReal.ofReal_one,
      one_mul]
  rw [hmul]
  have heq : (fun x ↦ Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal) =
      (fun x ↦ Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
        - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) +
      ((t / 2) • fun x ↦ g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) := by
    ext x; simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [heq]
  refine (eLpNorm_add_le one_le_two).trans ?_
  rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal (by positivity)]

private theorem tendsto_slope_sqrt_rnDeriv_toLp {ν : Measure X} [SigmaFinite ν]
    {Q : ℝ → Measure X} [∀ t, IsFiniteMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) :
    Tendsto (fun t : ℝ ↦ t⁻¹ • ((memLp_sqrt_rnDeriv (Q t) ν).toLp _
        - (memLp_sqrt_rnDeriv (Q 0) ν).toLp _)) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) • (memLp_mul_sqrt_rnDeriv (h.1 0) h.memLp).toLp _)) := by
  set S : ℝ → Lp ℝ 2 ν := fun t ↦ (memLp_sqrt_rnDeriv (Q t) ν).toLp _
  have hG_mem := memLp_mul_sqrt_rnDeriv (h.1 0) h.memLp
  set G : Lp ℝ 2 ν := hG_mem.toLp _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hto := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.2
  rw [ENNReal.toReal_zero] at hto
  refine hto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Function.comp_apply, Lp.norm_def]
  have hae : ((t⁻¹ • (S t - S 0) - (1 / 2 : ℝ) • G : Lp ℝ 2 ν) : X → ℝ) =ᵐ[ν]
      (t⁻¹ • fun x ↦ Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
        - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) := by
    filter_upwards [Lp.coeFn_smul t⁻¹ (S t - S 0), Lp.coeFn_sub (S t) (S 0),
      (memLp_sqrt_rnDeriv (Q t) ν).coeFn_toLp, (memLp_sqrt_rnDeriv (Q 0) ν).coeFn_toLp,
      Lp.coeFn_sub (t⁻¹ • (S t - S 0)) ((1 / 2 : ℝ) • G), Lp.coeFn_smul (1 / 2 : ℝ) G,
      hG_mem.coeFn_toLp] with x h1 h2 h3 h4 h5 h6 h7
    rw [h5, Pi.sub_apply, h1, Pi.smul_apply, h2, Pi.sub_apply, h6, Pi.smul_apply]
    dsimp only [S, G]
    rw [h3, h4, h7]
    simp only [Pi.smul_apply, smul_eq_mul]
    have ht0 : t ≠ 0 := ht.ne'
    field_simp
  rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, Real.eNorm_eq_ofReal (inv_nonneg.mpr ht.le)]

/-- Every path score of a path of probability measures has mean zero under `Q 0`
(van der Vaart, Lemma 25.14, first assertion). -/
theorem HasPathScore.integral_eq_zero {ν : Measure X} [SigmaFinite ν] {Q : ℝ → Measure X}
    [∀ t, IsProbabilityMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) :
    ∫ x, g x ∂Q 0 = 0 := by
  set S : ℝ → Lp ℝ 2 ν := fun t ↦ (memLp_sqrt_rnDeriv (Q t) ν).toLp _
  have hG_mem := memLp_mul_sqrt_rnDeriv (h.1 0) h.memLp
  set G : Lp ℝ 2 ν := hG_mem.toLp _
  have hS_norm (t : ℝ) : ‖S t‖ = 1 := by
    simp [S, eLpNorm_sqrt_rnDeriv_eq_one (Q t) ν (h.1 t)]
  have hS_tendsto : Tendsto S (𝓝[>] 0) (𝓝 (S 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hto := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.tendsto_eLpNorm_sqrt_rnDeriv_sub
    rw [ENNReal.toReal_zero] at hto
    refine hto.congr fun t ↦ ?_
    rw [Function.comp_apply, Lp.norm_def]
    exact congr_arg ENNReal.toReal (eLpNorm_congr_ae ((Lp.coeFn_sub (S t) (S 0)).trans
      ((memLp_sqrt_rnDeriv (Q t) ν).coeFn_toLp.sub
        (memLp_sqrt_rnDeriv (Q 0) ν).coeFn_toLp))).symm
  have hinner_lim : Tendsto (fun t : ℝ ↦ inner ℝ (t⁻¹ • (S t - S 0)) (S t + S 0)) (𝓝[>] 0)
      (𝓝 (inner ℝ ((1 / 2 : ℝ) • G) (S 0 + S 0))) :=
    Filter.Tendsto.inner (tendsto_slope_sqrt_rnDeriv_toLp h) (hS_tendsto.add tendsto_const_nhds)
  have hinner_zero (t : ℝ) : inner ℝ (t⁻¹ • (S t - S 0)) (S t + S 0) = 0 := by
    rw [inner_smul_left, RCLike.conj_to_real, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_comm (S 0) (S t), real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      hS_norm t, hS_norm 0]
    ring
  simp_rw [hinner_zero] at hinner_lim
  have hGS : inner ℝ G (S 0) = 0 := by
    have heq := tendsto_nhds_unique hinner_lim tendsto_const_nhds
    rw [inner_smul_left, RCLike.conj_to_real, inner_add_right] at heq
    linarith
  rw [← integral_toReal_rnDeriv_mul (h.1 0)]
  rw [L2.inner_def] at hGS
  refine (integral_congr_ae ?_).trans hGS
  filter_upwards [hG_mem.coeFn_toLp, (memLp_sqrt_rnDeriv (Q 0) ν).coeFn_toLp] with x hGx hSx
  simp only [RCLike.inner_apply, RCLike.conj_to_real, S, G, hGx, hSx]
  rw [← mul_assoc (Real.sqrt _), mul_comm (Real.sqrt _) (g x), mul_assoc, ← sq,
    Real.sq_sqrt ENNReal.toReal_nonneg, mul_comm]

/-- **Independence of the dominating measure.** If every `Q t` is σ-finite and absolutely
continuous with respect to both `ν` and `ν'`, then `HasPathScore ν Q g` and `HasPathScore ν' Q g`
are equivalent. -/
theorem hasPathScore_iff_of_absolutelyContinuous {ν ν' : Measure X} [SigmaFinite ν]
    [SigmaFinite ν'] {Q : ℝ → Measure X} [∀ t, SigmaFinite (Q t)] {g : X → ℝ}
    (hQ : ∀ t, Q t ≪ ν) (hQ' : ∀ t, Q t ≪ ν') :
    HasPathScore ν Q g ↔ HasPathScore ν' Q g := by
  suffices ∀ {ρ μ : Measure X} [SigmaFinite ρ] [SigmaFinite μ],
      (∀ t, Q t ≪ ρ) → ρ ≪ μ → (HasPathScore ρ Q g ↔ HasPathScore μ Q g) by
    exact (this hQ (rfl.absolutelyContinuous.add_right ν')).trans
      (this hQ' (rfl.absolutelyContinuous.add_right' ν)).symm
  intro ρ μ _ _ hQρ hρμ
  have heq (t : ℝ) : eLpNorm (fun x ↦
        Real.sqrt ((Q t).rnDeriv ρ x).toReal - Real.sqrt ((Q 0).rnDeriv ρ x).toReal
          - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ρ x).toReal) 2 ρ =
      eLpNorm (fun x ↦
        Real.sqrt ((Q t).rnDeriv μ x).toReal - Real.sqrt ((Q 0).rnDeriv μ x).toReal
          - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv μ x).toReal) 2 μ := by
    rw [← eLpNorm_mul_sqrt_rnDeriv hρμ]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ) (hQρ t),
      Measure.rnDeriv_mul_rnDeriv (κ := μ) (hQρ 0)] with x hqt hq0
    simp only [← hqt, ← hq0, Pi.mul_apply, ENNReal.toReal_mul,
      Real.sqrt_mul ENNReal.toReal_nonneg]
    ring
  exact ⟨fun h ↦ ⟨fun t ↦ (hQρ t).trans hρμ, by simp_rw [← heq]; exact h.2⟩,
    fun h ↦ ⟨hQρ, by simp_rw [heq]; exact h.2⟩⟩

/-- **Uniqueness of path scores.** Any two path scores of one path agree `Q 0`-almost everywhere. -/
theorem HasPathScore.ae_eq {ν : Measure X} [SigmaFinite ν] {Q : ℝ → Measure X}
    [SigmaFinite (Q 0)] {g g' : X → ℝ} (h : HasPathScore ν Q g) (h' : HasPathScore ν Q g') :
    g =ᵐ[Q 0] g' := by
  set s₀ : X → ℝ := fun x ↦ Real.sqrt ((Q 0).rnDeriv ν x).toReal
  have hdiff_zero : eLpNorm (fun x ↦ (1 / 2 : ℝ) * (g' x - g x) * s₀ x) 2 ν = 0 := by
    refine le_antisymm ?_ zero_le
    have hsum : Tendsto (fun t : ℝ ↦
        ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
          Real.sqrt ((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g x * s₀ x) 2 ν +
        ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
          Real.sqrt ((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g' x * s₀ x) 2 ν)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [add_zero] using h.2.add h'.2
    refine ge_of_tendsto hsum ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    set r₁ : X → ℝ := fun x ↦
      Real.sqrt ((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g x * s₀ x
    set r₂ : X → ℝ := fun x ↦
      Real.sqrt ((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g' x * s₀ x
    have heq : (fun x ↦ (1 / 2 : ℝ) * (g' x - g x) * s₀ x) =
        (t⁻¹ • r₁) + ((-t⁻¹) • r₂) := by
      ext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, r₁, r₂]
      have ht0 : t ≠ 0 := ht.ne'
      field_simp
      ring
    rw [heq]
    refine (eLpNorm_add_le one_le_two).trans ?_
    rw [eLpNorm_const_smul, eLpNorm_const_smul, eNorm_neg,
      Real.eNorm_eq_ofReal (inv_nonneg.mpr ht.le)]
  have hae_ν : (fun x ↦ (1 / 2 : ℝ) * (g' x - g x) * s₀ x) =ᵐ[ν] 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).mp hdiff_zero
  filter_upwards [(h.1 0) hae_ν, Measure.rnDeriv_pos (h.1 0),
    (h.1 0) ((Q 0).rnDeriv_lt_top ν)] with x hx hpos hlt
  have hs₀_ne : s₀ x ≠ 0 := (Real.sqrt_pos.mpr (ENNReal.toReal_pos hpos.ne' hlt.ne)).ne'
  simp only [Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with (h12 | hsub) | hs0
  · norm_num at h12
  · linarith
  · exact absurd hs0 hs₀_ne

end Properties

/-! ### Bounded tilts, logistic tilts of arbitrary `L²₀` scores, and product paths -/

section Constructions

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The bounded linear tilt `dP_t = (1 + t g) dP` for `|t| C < 1`, cut off to `P` when
`1 ≤ |t| C` so that `tiltPath P g C t` remains a probability measure for every `t : ℝ`. -/
def tiltPath (P : Measure X) (g : X → ℝ) (C : ℝ) (t : ℝ) : Measure X :=
  if |t| * C < 1 then P.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x)) else P

/-- Unfolding characterization of `tiltPath`. -/
theorem tiltPath_def (P : Measure X) (g : X → ℝ) (C : ℝ) (t : ℝ) :
    tiltPath P g C t =
      if |t| * C < 1 then P.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x)) else P :=
  (rfl)

/-- At `t = 0`, `tiltPath P g C` equals the base measure `P`. -/
@[simp]
theorem tiltPath_zero (P : Measure X) (g : X → ℝ) (C : ℝ) : tiltPath P g C 0 = P := by
  simp [tiltPath]

/-- Within the cutoff `|t| * C < 1`, `tiltPath P g C t` has density `1 + t * g` against `P`. -/
theorem tiltPath_of_lt {P : Measure X} {g : X → ℝ} {C t : ℝ} (ht : |t| * C < 1) :
    tiltPath P g C t = P.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x)) := by
  simp [tiltPath, ht]

/-- Beyond the cutoff `1 ≤ |t| * C`, `tiltPath P g C t` falls back to `P`. -/
theorem tiltPath_of_le {P : Measure X} {g : X → ℝ} {C t : ℝ} (ht : 1 ≤ |t| * C) :
    tiltPath P g C t = P := by
  simp [tiltPath, not_lt.mpr ht]

/-- Tilting `P` in direction `0` leaves `P` unchanged for every `t`. -/
@[simp]
theorem tiltPath_zero_score (P : Measure X) (C t : ℝ) : tiltPath P 0 C t = P := by
  by_cases ht : |t| * C < 1 <;> simp [tiltPath, ht]

/-- Every measure along `tiltPath P g C` is absolutely continuous with respect to `P`. -/
theorem absolutelyContinuous_tiltPath (P : Measure X) (g : X → ℝ) (C t : ℝ) :
    tiltPath P g C t ≪ P := by
  by_cases ht : |t| * C < 1
  · rw [tiltPath_of_lt ht]
    exact withDensity_absolutelyContinuous _ _
  · rw [tiltPath_of_le (not_lt.mp ht)]

/-- For a bounded `P`-almost-everywhere measurable function `g` with mean zero under a probability
measure `P`, every measure along `tiltPath P g C` is a probability measure. -/
theorem isProbabilityMeasure_tiltPath {P : Measure X} [IsProbabilityMeasure P] {g : X → ℝ}
    (hg : AEStronglyMeasurable g P) {C : ℝ} (hC : ∀ᵐ x ∂P, |g x| ≤ C)
    (hmean : ∫ x, g x ∂P = 0) (t : ℝ) : IsProbabilityMeasure (tiltPath P g C t) := by
  rcases eq_or_ne t 0 with rfl | _
  · rw [tiltPath_zero]; infer_instance
  by_cases ht : |t| * C < 1
  · rw [tiltPath_of_lt ht]
    have hg_int : Integrable g P := (memLp_top_of_bound hg C hC).integrable le_top
    have h1tg_int : Integrable (fun x ↦ 1 + t * g x) P :=
      (integrable_const 1).add (hg_int.const_mul t)
    have hnonneg : 0 ≤ᵐ[P] fun x ↦ 1 + t * g x := by
      filter_upwards [hC] with x hx
      have h1 : |t * g x| ≤ |t| * C := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
      simp only [Pi.zero_apply]
      linarith [neg_abs_le (t * g x)]
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal h1tg_int hnonneg,
      integral_add (integrable_const 1) (hg_int.const_mul t), integral_const, probReal_univ,
      smul_eq_mul, mul_one, integral_const_mul, hmean, mul_zero, add_zero, ENNReal.ofReal_one]
  · rw [tiltPath_of_le (not_lt.mp ht)]; infer_instance

private theorem abs_sqrt_one_add_sub_le {u : ℝ} (hu : -(1 / 2) ≤ u) :
    |Real.sqrt (1 + u) - 1 - u / 2| ≤ u ^ 2 / 2 := by
  have h1u : 0 ≤ 1 + u := by linarith
  have hden : 1 / 2 ≤ Real.sqrt (1 + u) + (1 + u / 2) := by
    have := Real.sqrt_nonneg (1 + u); linarith
  have hprod : (Real.sqrt (1 + u) - 1 - u / 2) * (Real.sqrt (1 + u) + (1 + u / 2)) =
      -(u ^ 2 / 4) := by
    have hsq : Real.sqrt (1 + u) * Real.sqrt (1 + u) = 1 + u := Real.mul_self_sqrt h1u
    nlinarith
  have habs := congr_arg abs hprod
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt (1 + u) + (1 + u / 2)), abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ u ^ 2 / 4)] at habs
  nlinarith [abs_nonneg (Real.sqrt (1 + u) - 1 - u / 2)]

/-- A bounded `P`-almost-everywhere measurable function `g` is the path score of `tiltPath P g C`
relative to `P` (van der Vaart, Example 25.16). Zero mean is needed only to make the tilted
measures probability measures (`isProbabilityMeasure_tiltPath`). -/
theorem hasPathScore_tiltPath {P : Measure X} [IsProbabilityMeasure P] {g : X → ℝ}
    (hg : AEStronglyMeasurable g P) {C : ℝ} (hC : ∀ᵐ x ∂P, |g x| ≤ C) :
    HasPathScore P (tiltPath P g C) g := by
  refine ⟨absolutelyContinuous_tiltPath P g C, ?_⟩
  set M := max C 1
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t * C ^ 2 / 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using ((ENNReal.continuous_ofReal.comp
      (by fun_prop : Continuous fun t ↦ t * C ^ 2 / 2)).tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, t * M < 1 / 2 :=
    (((by fun_prop : Continuous fun t : ℝ ↦ t * M).tendsto 0).mono_left
      nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hev] with t (ht : 0 < t) htM
  have htC : |t| * C < 1 := by
    rw [abs_of_pos ht]; linarith [mul_le_mul_of_nonneg_left (le_max_left C 1) ht.le]
  have hd_t : (tiltPath P g C t).rnDeriv P =ᵐ[P] fun x ↦ ENNReal.ofReal (1 + t * g x) := by
    rw [tiltPath_of_lt htC]
    exact Measure.rnDeriv_withDensity₀ P
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (aemeasurable_const.add (hg.aemeasurable.const_mul t)))
  have hd_0 : (tiltPath P g C 0).rnDeriv P =ᵐ[P] 1 := by rw [tiltPath_zero]; exact P.rnDeriv_self
  have hrem_asm : AEStronglyMeasurable (fun x ↦
      Real.sqrt ((tiltPath P g C t).rnDeriv P x).toReal
        - Real.sqrt ((tiltPath P g C 0).rnDeriv P x).toReal
        - t / 2 * g x * Real.sqrt ((tiltPath P g C 0).rnDeriv P x).toReal) P := by
    have h1 := (Measure.measurable_rnDeriv (tiltPath P g C t) P).ennreal_toReal.sqrt
    have h2 := (Measure.measurable_rnDeriv (tiltPath P g C 0) P).ennreal_toReal.sqrt
    exact (h1.aestronglyMeasurable.sub h2.aestronglyMeasurable).sub
      ((hg.const_mul (t / 2)).mul h2.aestronglyMeasurable)
  have hbound : eLpNorm (fun x ↦ Real.sqrt ((tiltPath P g C t).rnDeriv P x).toReal -
      Real.sqrt ((tiltPath P g C 0).rnDeriv P x).toReal -
      t / 2 * g x * Real.sqrt ((tiltPath P g C 0).rnDeriv P x).toReal) 2 P ≤
      ENNReal.ofReal (t ^ 2 * C ^ 2 / 2) := by
    refine (eLpNorm_le_of_ae_bound hrem_asm (C := t ^ 2 * C ^ 2 / 2) ?_).trans (by simp)
    filter_upwards [hd_t, hd_0, hC] with x hxt hx0 hxC
    have htg : |t * g x| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos ht]
      exact (mul_le_mul_of_nonneg_left (hxC.trans (le_max_left C 1)) ht.le).trans htM.le
    have htg_div : t / 2 * g x = t * g x / 2 := by ring
    simp only [hxt, hx0, Pi.one_apply, ENNReal.toReal_one, Real.sqrt_one, mul_one,
      ENNReal.toReal_ofReal (by linarith [neg_abs_le (t * g x)] : 0 ≤ 1 + t * g x),
      Real.norm_eq_abs, htg_div]
    exact (abs_sqrt_one_add_sub_le (by linarith [neg_abs_le (t * g x)])).trans
      (by rw [mul_pow]; nlinarith [sq_le_sq.mpr (hxC.trans (le_abs_self C)), sq_nonneg t])
  refine (mul_le_mul_right hbound _).trans_eq ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  exact congrArg ENNReal.ofReal (by have := ht.ne'; field_simp)

private def logisticKernel (u : ℝ) : ℝ :=
  2 / (1 + Real.exp (-2 * u))

private theorem logisticKernel_pos (u : ℝ) : 0 < logisticKernel u := by
  unfold logisticKernel
  have := Real.exp_pos (-2 * u)
  positivity

private theorem logisticKernel_lt_two (u : ℝ) : logisticKernel u < 2 := by
  unfold logisticKernel
  rw [div_lt_iff₀ (by linarith [Real.exp_pos (-2 * u)])]
  linarith [Real.exp_pos (-2 * u)]

private theorem logisticKernel_zero : logisticKernel 0 = 1 := by
  norm_num [logisticKernel]

private def logisticKernelDeriv (u : ℝ) : ℝ :=
  4 * Real.exp (-2 * u) / (1 + Real.exp (-2 * u)) ^ 2

private theorem hasDerivAt_logisticKernel (u : ℝ) :
    HasDerivAt logisticKernel (logisticKernelDeriv u) u := by
  unfold logisticKernel logisticKernelDeriv
  have hid : HasDerivAt (fun x : ℝ ↦ -2 * x) (-2) u := by
    simpa using (hasDerivAt_id u).const_mul (-2)
  have hexp : HasDerivAt (fun x : ℝ ↦ 1 + Real.exp (-2 * x)) (-2 * Real.exp (-2 * u)) u := by
    convert hid.exp.const_add 1 using 1
    ring
  have hne : 1 + Real.exp (-2 * u) ≠ 0 := by linarith [Real.exp_pos (-2 * u)]
  convert (hasDerivAt_const u (2 : ℝ)).div hexp hne using 1
  ring

private theorem logisticKernelDeriv_nonneg (u : ℝ) : 0 ≤ logisticKernelDeriv u := by
  unfold logisticKernelDeriv
  have := Real.exp_pos (-2 * u)
  positivity

private theorem logisticKernelDeriv_le_one (u : ℝ) : 0 ≤ 1 - logisticKernelDeriv u := by
  unfold logisticKernelDeriv
  rw [sub_nonneg, div_le_one (by linarith [Real.exp_pos (-2 * u), sq_nonneg (Real.exp (-2 * u))])]
  nlinarith [sq_nonneg (1 - Real.exp (-2 * u))]

private theorem logisticKernelDeriv_zero : logisticKernelDeriv 0 = 1 := by
  norm_num [logisticKernelDeriv]

private theorem hasDerivAt_sqrt_logisticKernel (u : ℝ) :
    HasDerivAt (fun x ↦ Real.sqrt (logisticKernel x))
      (logisticKernelDeriv u / (2 * Real.sqrt (logisticKernel u))) u :=
  (hasDerivAt_logisticKernel u).sqrt (logisticKernel_pos u).ne'

private theorem abs_deriv_sqrt_logisticKernel_le (u : ℝ) :
    |logisticKernelDeriv u / (2 * Real.sqrt (logisticKernel u))| ≤ 2 := by
  have hpos : 0 < Real.sqrt (logisticKernel u) := Real.sqrt_pos.mpr (logisticKernel_pos u)
  rw [abs_of_nonneg (div_nonneg (logisticKernelDeriv_nonneg u) (by positivity))]
  set w := Real.exp (-2 * u)
  have hw : 0 < w := Real.exp_pos (-2 * u)
  have hsq : (logisticKernelDeriv u / (2 * Real.sqrt (logisticKernel u))) ^ 2 ≤ 2 ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (logisticKernel_pos u).le]
    unfold logisticKernelDeriv logisticKernel
    have heq : (4 * w / (1 + w) ^ 2) ^ 2 / (2 ^ 2 * (2 / (1 + w))) =
        2 * w ^ 2 / (1 + w) ^ 3 := by
      field_simp; ring
    rw [heq, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg w, mul_pos hw (sq_pos_of_pos hw)]
  nlinarith [div_nonneg (logisticKernelDeriv_nonneg u) (by positivity : 0 ≤ 2 * Real.sqrt _)]

private theorem abs_sqrt_logisticKernel_sub_one_le (u : ℝ) :
    |Real.sqrt (logisticKernel u) - 1| ≤ 2 * |u| := by
  have hd : ∀ y ∈ Set.univ, DifferentiableAt ℝ (fun x ↦ Real.sqrt (logisticKernel x)) y :=
    fun y _ ↦ (hasDerivAt_sqrt_logisticKernel y).differentiableAt
  have hb : ∀ y ∈ Set.univ, ‖deriv (fun x ↦ Real.sqrt (logisticKernel x)) y‖ ≤ 2 := fun y _ ↦ by
    rw [(hasDerivAt_sqrt_logisticKernel y).deriv, Real.norm_eq_abs]
    exact abs_deriv_sqrt_logisticKernel_le y
  simpa [logisticKernel_zero, Real.norm_eq_abs] using
    convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (mem_univ 0) (mem_univ u)

private theorem sq_logistic_slope_le {t : ℝ} (ht : 0 < t) (v : ℝ) :
    (t⁻¹ * (Real.sqrt (logisticKernel (t * v)) - 1) - 1 / 2 * v) ^ 2 ≤ (5 / 2 * |v|) ^ 2 := by
  have hb : |t⁻¹ * (Real.sqrt (logisticKernel (t * v)) - 1) - 1 / 2 * v| ≤ 5 / 2 * |v| := by
    calc |t⁻¹ * (Real.sqrt (logisticKernel (t * v)) - 1) - 1 / 2 * v|
        ≤ |t⁻¹ * (Real.sqrt (logisticKernel (t * v)) - 1)| + |1 / 2 * v| := abs_sub _ _
      _ ≤ t⁻¹ * (2 * |t * v|) + 1 / 2 * |v| := by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le), abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr
          exact abs_sqrt_logisticKernel_sub_one_le _
      _ = 5 / 2 * |v| := by
          rw [abs_mul, abs_of_pos ht]
          have := ht.ne'; field_simp; ring
  exact sq_le_sq.mpr (hb.trans (le_abs_self _))

private theorem tendsto_eLpNorm_logistic_slope (P : Measure X) {g₀ : X → ℝ}
    (hg₀_meas : Measurable g₀) (hg₀_mem : MemLp g₀ 2 P) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦
      t⁻¹ * (Real.sqrt (logisticKernel (t * g₀ x)) - 1) - 1 / 2 * g₀ x) 2 P) (𝓝[>] 0) (𝓝 0) := by
  set s : ℝ → ℝ := fun u ↦ Real.sqrt (logisticKernel u)
  have hs_meas : Measurable s := by unfold s logisticKernel; fun_prop
  have hdom : Integrable (fun x ↦ (5 / 2 * |g₀ x|) ^ 2) P :=
    (((memLp_two_iff_integrable_sq hg₀_mem.aestronglyMeasurable).mp hg₀_mem).const_mul
      ((5 / 2 : ℝ) ^ 2)).congr (Eventually.of_forall fun x ↦ by dsimp only; rw [mul_pow, sq_abs])
  have hdom_ev : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ x ∂P,
      ‖(t⁻¹ * (s (t * g₀ x) - 1) - 1 / 2 * g₀ x) ^ 2‖ ≤ (5 / 2 * |g₀ x|) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact sq_logistic_slope_le ht (g₀ x)
  have hint_lim : Tendsto (fun t : ℝ ↦
      ∫ x, (t⁻¹ * (s (t * g₀ x) - 1) - 1 / 2 * g₀ x) ^ 2 ∂P) (𝓝[>] 0) (𝓝 0) := by
    have hdc := tendsto_integral_filter_of_dominated_convergence
      (bound := fun x ↦ (5 / 2 * |g₀ x|) ^ 2)
      (Eventually.of_forall fun t ↦ (by fun_prop : Measurable fun x ↦
        (t⁻¹ * (s (t * g₀ x) - 1) - 1 / 2 * g₀ x) ^ 2).aestronglyMeasurable)
      hdom_ev hdom
      (Eventually.of_forall fun x ↦ by
        have hd : HasDerivAt (fun t : ℝ ↦ s (t * g₀ x)) (1 / 2 * g₀ x) 0 := by
          simpa [Function.comp_def, s, logisticKernelDeriv_zero, logisticKernel_zero] using
            (hasDerivAt_sqrt_logisticKernel (0 * g₀ x)).comp (0 : ℝ)
              ((hasDerivAt_id 0).mul_const (g₀ x))
        have h1 : Tendsto (fun t : ℝ ↦ t⁻¹ * (s (t * g₀ x) - 1) - 1 / 2 * g₀ x) (𝓝[>] 0) (𝓝 0) := by
          simpa [s, logisticKernel_zero, smul_eq_mul, sub_self] using
            hd.tendsto_slope_zero_right.sub_const (1 / 2 * g₀ x)
        simpa using h1.pow 2)
    rwa [integral_zero] at hdc
  have hrpow : Tendsto (fun t : ℝ ↦
      (ENNReal.ofReal (∫ x, (t⁻¹ * (s (t * g₀ x) - 1) - 1 / 2 * g₀ x) ^ 2 ∂P)) ^ (1 / 2 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ ↦ (ENNReal.ofReal r) ^ (1 / 2 : ℝ) :=
      ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal
    simpa [Function.comp_def] using (hc.tendsto 0).comp hint_lim
  refine hrpow.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hm : Measurable fun x ↦ t⁻¹ * (s (t * g₀ x) - 1) - 1 / 2 * g₀ x := by fun_prop
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hm.aestronglyMeasurable, ENNReal.toReal_ofNat]
  congr 1
  have hint_sq : Integrable (fun x ↦ (t⁻¹ * (s (t * g₀ x) - 1) - 1 / 2 * g₀ x) ^ 2) P :=
    hdom.mono' (hm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact sq_logistic_slope_le ht (g₀ x))
  rw [ofReal_integral_eq_lintegral_ofReal hint_sq (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  refine lintegral_congr fun x ↦ ?_
  rw [ENNReal.rpow_two, Real.eNorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

private theorem integrable_logisticKernel (P : Measure X) [IsFiniteMeasure P]
    {g₀ : X → ℝ} (hg₀_meas : Measurable g₀) (t : ℝ) :
    Integrable (fun x ↦ logisticKernel (t * g₀ x)) P := by
  have hm : Measurable fun x ↦ logisticKernel (t * g₀ x) := by unfold logisticKernel; fun_prop
  exact (memLp_top_of_bound hm.aestronglyMeasurable 2 (Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (logisticKernel_pos _)]
    exact (logisticKernel_lt_two _).le)).integrable le_top

private theorem logisticPartition_pos (P : Measure X) [IsProbabilityMeasure P]
    {g₀ : X → ℝ} (hg₀_meas : Measurable g₀) (t : ℝ) :
    0 < ∫ x, logisticKernel (t * g₀ x) ∂P := by
  rw [integral_pos_iff_support_of_nonneg (fun _ ↦ (logisticKernel_pos _).le)
    (integrable_logisticKernel P hg₀_meas t)]
  have hsupp : Function.support (fun x ↦ logisticKernel (t * g₀ x)) = univ :=
    eq_univ_of_forall fun x ↦ (logisticKernel_pos (t * g₀ x)).ne'
  simp [hsupp]

private theorem hasDerivAt_logisticPartition {P : Measure X} [IsProbabilityMeasure P]
    {g₀ : X → ℝ} (hg₀_meas : Measurable g₀) (hg₀_int : Integrable g₀ P)
    (hg₀_mean : ∫ x, g₀ x ∂P = 0) :
    HasDerivAt (fun t ↦ ∫ x, logisticKernel (t * g₀ x) ∂P) 0 0 := by
  have hk_meas (t : ℝ) : Measurable fun x ↦ logisticKernel (t * g₀ x) := by
    unfold logisticKernel; fun_prop
  have hk_int0 : Integrable (fun x ↦ logisticKernel (0 * g₀ x)) P := by
    simp [logisticKernel_zero]
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball (0 : ℝ) 1)
    (Metric.ball_mem_nhds 0 zero_lt_one)
    (Eventually.of_forall fun t ↦ (hk_meas t).aestronglyMeasurable) hk_int0
    (F' := fun t x ↦ logisticKernelDeriv (t * g₀ x) * g₀ x)
    (by simp only [zero_mul, logisticKernelDeriv_zero, one_mul]; exact hg₀_int.aestronglyMeasurable)
    (Eventually.of_forall fun x t _ ↦ by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (logisticKernelDeriv_nonneg _)]
      nlinarith [logisticKernelDeriv_le_one (t * g₀ x), abs_nonneg (g₀ x)])
    hg₀_int.norm
    (Eventually.of_forall fun x t _ ↦ by
      have hc := (hasDerivAt_logisticKernel (t * g₀ x)).comp t ((hasDerivAt_id t).mul_const (g₀ x))
      simpa [Function.comp_def] using hc)).2
  simpa [logisticKernelDeriv_zero, hg₀_mean] using hd

private theorem tendsto_eLpNorm_logistic_norm_term (P : Measure X) [IsProbabilityMeasure P]
    {g₀ : X → ℝ} (hg₀_meas : Measurable g₀) {Z : ℝ → ℝ} (hZ0 : Z 0 = 1)
    (hZ_sqrt_deriv : HasDerivAt (fun t ↦ Real.sqrt ((Z t)⁻¹)) 0 0) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦
      t⁻¹ * (Real.sqrt ((Z t)⁻¹) - 1) * Real.sqrt (logisticKernel (t * g₀ x))) 2 P)
      (𝓝[>] 0) (𝓝 0) := by
  have hk_meas (t : ℝ) : Measurable fun x ↦ logisticKernel (t * g₀ x) := by
    unfold logisticKernel; fun_prop
  have hslope : Tendsto (fun t : ℝ ↦ ENNReal.ofReal
      (|t⁻¹ * (Real.sqrt ((Z t)⁻¹) - 1)| * Real.sqrt 2)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ ↦ t⁻¹ * (Real.sqrt ((Z t)⁻¹) - 1)) (𝓝[>] 0) (𝓝 0) := by
      simpa [hZ0, smul_eq_mul] using hZ_sqrt_deriv.tendsto_slope_zero_right
    have h2 : Tendsto (fun t : ℝ ↦ |t⁻¹ * (Real.sqrt ((Z t)⁻¹) - 1)| * Real.sqrt 2)
        (𝓝[>] 0) (𝓝 0) := by simpa using h1.abs.mul_const (Real.sqrt 2)
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hslope
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun t ↦ ?_)
  have hm1 : Measurable fun x ↦
      t⁻¹ * (Real.sqrt ((Z t)⁻¹) - 1) * Real.sqrt (logisticKernel (t * g₀ x)) := by
    have := hk_meas t; fun_prop
  refine (eLpNorm_le_of_ae_bound hm1.aestronglyMeasurable
    (C := |t⁻¹ * (Real.sqrt ((Z t)⁻¹) - 1)| * Real.sqrt 2)
    (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (logisticKernel_lt_two _).le) (abs_nonneg _)

private theorem isProbabilityMeasure_logisticTilt (P : Measure X) [IsProbabilityMeasure P]
    {g₀ : X → ℝ} (hg₀_meas : Measurable g₀) (t : ℝ) :
    IsProbabilityMeasure (P.withDensity fun x ↦
      ENNReal.ofReal ((∫ y, logisticKernel (t * g₀ y) ∂P)⁻¹ * logisticKernel (t * g₀ x))) := ⟨by
  have hZ_pos := logisticPartition_pos P hg₀_meas t
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_logisticKernel P hg₀_meas t).const_mul _)
      (Eventually.of_forall fun _ ↦
        mul_nonneg (inv_nonneg.mpr hZ_pos.le) (logisticKernel_pos _).le),
    integral_const_mul, inv_mul_cancel₀ hZ_pos.ne', ENNReal.ofReal_one]⟩

/-- **Every element of `L²₀(P)` is a path score** (van der Vaart, Example 25.16). For any
square-integrable mean-zero function `g` on a probability space `(X, P)`, there exists a path `Q`
of probability measures through `Q 0 = P`, each dominated by `P`, with `HasPathScore P Q g`. -/
theorem exists_hasPathScore_of_integral_eq_zero (P : Measure X) [IsProbabilityMeasure P]
    {g : X → ℝ} (hg : MemLp g 2 P) (hmean : ∫ x, g x ∂P = 0) :
    ∃ Q : ℝ → Measure X, (∀ t, IsProbabilityMeasure (Q t)) ∧ Q 0 = P ∧
      (∀ t, Q t ≪ P) ∧ HasPathScore P Q g := by
  set g₀ := hg.aestronglyMeasurable.aemeasurable.mk g
  have hg₀_meas : Measurable g₀ := hg.aestronglyMeasurable.aemeasurable.measurable_mk
  have hg₀_ae : g =ᵐ[P] g₀ := hg.aemeasurable.ae_eq_mk
  have hg₀_mem : MemLp g₀ 2 P := (memLp_congr_ae hg₀_ae).mp hg
  have hk_meas (t : ℝ) : Measurable fun x ↦ logisticKernel (t * g₀ x) := by
    unfold logisticKernel; fun_prop
  set Z : ℝ → ℝ := fun t ↦ ∫ x, logisticKernel (t * g₀ x) ∂P
  have hZ0 : Z 0 = 1 := by simp [Z, logisticKernel_zero]
  have hZ_sqrt_deriv : HasDerivAt (fun t ↦ Real.sqrt ((Z t)⁻¹)) 0 0 := by
    have hd : HasDerivAt Z 0 0 := hasDerivAt_logisticPartition hg₀_meas
      (hg₀_mem.integrable one_le_two) ((integral_congr_ae hg₀_ae.symm).trans hmean)
    simpa [hZ0] using (hd.inv (by rw [hZ0]; exact one_ne_zero)).sqrt
      (inv_ne_zero (by rw [hZ0]; exact one_ne_zero))
  set Q : ℝ → Measure X := fun t ↦
    P.withDensity (fun x ↦ ENNReal.ofReal ((Z t)⁻¹ * logisticKernel (t * g₀ x)))
  have hQ0 : Q 0 = P := by simp [Q, hZ0, logisticKernel_zero]
  have hQ_ac (t : ℝ) : Q t ≪ P := withDensity_absolutelyContinuous _ _
  have hQ_prob (t : ℝ) : IsProbabilityMeasure (Q t) :=
    isProbabilityMeasure_logisticTilt P hg₀_meas t
  refine ⟨Q, hQ_prob, hQ0, hQ_ac, ?_⟩
  suffices hscore₀ : HasPathScore P Q g₀ by
    have : IsProbabilityMeasure (Q 0) := hQ_prob 0
    exact hscore₀.congr_ae (hQ0 ▸ hg₀_ae.symm)
  have hsum := (tendsto_eLpNorm_logistic_norm_term P hg₀_meas hZ0 hZ_sqrt_deriv).add
    (tendsto_eLpNorm_logistic_slope P hg₀_meas hg₀_mem)
  rw [add_zero] at hsum
  refine ⟨hQ_ac, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hd_t : (Q t).rnDeriv P =ᵐ[P]
      fun x ↦ ENNReal.ofReal ((Z t)⁻¹ * logisticKernel (t * g₀ x)) :=
    Measure.rnDeriv_withDensity P (by have := hk_meas t; fun_prop)
  have hd_0 : (Q 0).rnDeriv P =ᵐ[P] 1 := by rw [hQ0]; exact P.rnDeriv_self
  have hae : (t⁻¹ • fun x ↦ Real.sqrt ((Q t).rnDeriv P x).toReal
        - Real.sqrt ((Q 0).rnDeriv P x).toReal
        - t / 2 * g₀ x * Real.sqrt ((Q 0).rnDeriv P x).toReal) =ᵐ[P]
      (fun x ↦ t⁻¹ * (Real.sqrt ((Z t)⁻¹) - 1) * Real.sqrt (logisticKernel (t * g₀ x))) +
      (fun x ↦ t⁻¹ * (Real.sqrt (logisticKernel (t * g₀ x)) - 1) - 1 / 2 * g₀ x) := by
    filter_upwards [hd_t, hd_0] with x hxt hx0
    have hZ_nonneg : 0 ≤ (Z t)⁻¹ := inv_nonneg.mpr (logisticPartition_pos P hg₀_meas t).le
    have hnonneg : 0 ≤ (Z t)⁻¹ * logisticKernel (t * g₀ x) :=
      mul_nonneg hZ_nonneg (logisticKernel_pos _).le
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, hxt, hx0, Pi.one_apply,
      ENNReal.toReal_one, Real.sqrt_one, mul_one, ENNReal.toReal_ofReal hnonneg,
      Real.sqrt_mul hZ_nonneg]
    have := ht.ne'; field_simp; ring
  rw [← Real.eNorm_eq_ofReal (inv_nonneg.mpr ht.le), ← eLpNorm_const_smul, eLpNorm_congr_ae hae]
  exact eLpNorm_add_le one_le_two

private theorem eLpNorm_prod_remainder_le {ν₁ : Measure X} [SigmaFinite ν₁] {ν₂ : Measure Y}
    [SigmaFinite ν₂] {Q₁ : ℝ → Measure X} {Q₂ : ℝ → Measure Y} [∀ t, IsProbabilityMeasure (Q₁ t)]
    [∀ t, IsProbabilityMeasure (Q₂ t)] {g₁₀ : X → ℝ} {g₂₀ : Y → ℝ}
    (hg₁₀_meas : Measurable g₁₀) (hg₂₀_meas : Measurable g₂₀)
    (h₁₀ : ∀ t, Q₁ t ≪ ν₁) (h₂₀ : ∀ t, Q₂ t ≪ ν₂) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t⁻¹ * eLpNorm (fun z : X × Y ↦
        Real.sqrt ((((Q₁ t).prod (Q₂ t)).rnDeriv (ν₁.prod ν₂) z).toReal)
          - Real.sqrt ((((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal)
          - t / 2 * (g₁₀ z.1 + g₂₀ z.2) *
              Real.sqrt ((((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal)) 2 (ν₁.prod ν₂) ≤
      ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦ Real.sqrt (((Q₁ t).rnDeriv ν₁ x).toReal) -
          Real.sqrt (((Q₁ 0).rnDeriv ν₁ x).toReal) -
          t / 2 * g₁₀ x * Real.sqrt (((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ +
        ENNReal.ofReal (1 / 2) *
          eLpNorm (fun x ↦ g₁₀ x * Real.sqrt (((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ *
          eLpNorm (fun y ↦ Real.sqrt (((Q₂ t).rnDeriv ν₂ y).toReal) -
            Real.sqrt (((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂ +
        ENNReal.ofReal t⁻¹ * eLpNorm (fun y ↦ Real.sqrt (((Q₂ t).rnDeriv ν₂ y).toReal) -
          Real.sqrt (((Q₂ 0).rnDeriv ν₂ y).toReal) -
          t / 2 * g₂₀ y * Real.sqrt (((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂ := by
  set s₁ : ℝ → X → ℝ := fun u x ↦ Real.sqrt (((Q₁ u).rnDeriv ν₁ x).toReal)
  set s₂ : ℝ → Y → ℝ := fun u y ↦ Real.sqrt (((Q₂ u).rnDeriv ν₂ y).toReal)
  set r₁ : X → ℝ := fun x ↦ s₁ t x - s₁ 0 x - t / 2 * g₁₀ x * s₁ 0 x
  set r₂ : Y → ℝ := fun y ↦ s₂ t y - s₂ 0 y - t / 2 * g₂₀ y * s₂ 0 y
  have hs₁_meas (u : ℝ) : Measurable (s₁ u) := (Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt
  have hs₂_meas (u : ℝ) : Measurable (s₂ u) := (Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt
  have hae : (fun z : X × Y ↦
      Real.sqrt ((((Q₁ t).prod (Q₂ t)).rnDeriv (ν₁.prod ν₂) z).toReal)
        - Real.sqrt ((((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal)
        - t / 2 * (g₁₀ z.1 + g₂₀ z.2) *
            Real.sqrt ((((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal)) =ᵐ[ν₁.prod ν₂]
      ((fun z : X × Y ↦ r₁ z.1 • s₂ t z.2) +
        (fun z : X × Y ↦ ((t / 2) • fun x ↦ g₁₀ x * s₁ 0 x) z.1 • (s₂ t z.2 - s₂ 0 z.2))) +
      (fun z : X × Y ↦ s₁ 0 z.1 • r₂ z.2) := by
    filter_upwards [Measure.rnDeriv_prod (Q₁ t) ν₁ (Q₂ t) ν₂,
      Measure.rnDeriv_prod (Q₁ 0) ν₁ (Q₂ 0) ν₂] with z hzt hz0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzt, hz0, ENNReal.toReal_mul,
      Real.sqrt_mul ENNReal.toReal_nonneg, s₁, s₂, r₁, r₂]; ring
  rw [eLpNorm_congr_ae hae]
  have htri : eLpNorm (((fun z : X × Y ↦ r₁ z.1 • s₂ t z.2) +
        (fun z : X × Y ↦ ((t / 2) • fun x ↦ g₁₀ x * s₁ 0 x) z.1 • (s₂ t z.2 - s₂ 0 z.2))) +
        (fun z : X × Y ↦ s₁ 0 z.1 • r₂ z.2)) 2 (ν₁.prod ν₂) ≤
      eLpNorm r₁ 2 ν₁ * eLpNorm (s₂ t) 2 ν₂ +
        eLpNorm ((t / 2) • fun x ↦ g₁₀ x * s₁ 0 x) 2 ν₁ *
          eLpNorm (fun y ↦ s₂ t y - s₂ 0 y) 2 ν₂ +
        eLpNorm (s₁ 0) 2 ν₁ * eLpNorm r₂ 2 ν₂ := by
    refine (eLpNorm_add_le one_le_two).trans ?_
    gcongr
    · refine (eLpNorm_add_le one_le_two).trans ?_
      rw [TauCeti.eLpNorm_prod_smul (f := r₁) (g := s₂ t)
          (by have := hs₁_meas t; have := hs₁_meas 0; fun_prop) (hs₂_meas t).aestronglyMeasurable,
        TauCeti.eLpNorm_prod_smul (f := (t / 2) • fun x ↦ g₁₀ x * s₁ 0 x)
          (g := fun y ↦ s₂ t y - s₂ 0 y) (by have := hs₁_meas 0; fun_prop)
          (by have := hs₂_meas t; have := hs₂_meas 0; fun_prop)]
    · rw [TauCeti.eLpNorm_prod_smul (f := s₁ 0) (g := r₂) (hs₁_meas 0).aestronglyMeasurable
        (by have := hs₂_meas t; have := hs₂_meas 0; fun_prop)]
  refine (mul_le_mul_right htri _).trans_eq ?_
  rw [eLpNorm_sqrt_rnDeriv_eq_one (Q₂ t) ν₂ (h₂₀ t),
    eLpNorm_sqrt_rnDeriv_eq_one (Q₁ 0) ν₁ (h₁₀ 0),
    eLpNorm_const_smul, Real.eNorm_eq_ofReal (by positivity), mul_one, one_mul]
  simp only [left_distrib, ← mul_assoc]
  congr 2
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  exact congrArg (fun a ↦ a * _ * _) (congrArg ENNReal.ofReal (by have := ht.ne'; field_simp))

/-- **Product paths.** The product of two paths of probability measures with scores `g₁` and `g₂`
relative to `ν₁` and `ν₂` has path score `(x, y) ↦ g₁ x + g₂ y` relative to `ν₁ ⊗ ν₂`. -/
theorem HasPathScore.prod {ν₁ : Measure X} [SigmaFinite ν₁] {ν₂ : Measure Y} [SigmaFinite ν₂]
    {Q₁ : ℝ → Measure X} {Q₂ : ℝ → Measure Y} [∀ t, IsProbabilityMeasure (Q₁ t)]
    [∀ t, IsProbabilityMeasure (Q₂ t)] {g₁ : X → ℝ} {g₂ : Y → ℝ}
    (h₁ : HasPathScore ν₁ Q₁ g₁) (h₂ : HasPathScore ν₂ Q₂ g₂) :
    HasPathScore (ν₁.prod ν₂) (fun t ↦ (Q₁ t).prod (Q₂ t)) (fun z ↦ g₁ z.1 + g₂ z.2) := by
  have hg₁ : AEStronglyMeasurable g₁ (Q₁ 0) := h₁.memLp.aestronglyMeasurable
  have hg₂ : AEStronglyMeasurable g₂ (Q₂ 0) := h₂.memLp.aestronglyMeasurable
  set g₁₀ := hg₁.aemeasurable.mk g₁
  set g₂₀ := hg₂.aemeasurable.mk g₂
  have hg₁₀_meas : Measurable g₁₀ := hg₁.aemeasurable.measurable_mk
  have hg₂₀_meas : Measurable g₂₀ := hg₂.aemeasurable.measurable_mk
  have h₁₀ : HasPathScore ν₁ Q₁ g₁₀ := h₁.congr_ae hg₁.aemeasurable.ae_eq_mk
  have h₂₀ : HasPathScore ν₂ Q₂ g₂₀ := h₂.congr_ae hg₂.aemeasurable.ae_eq_mk
  suffices hscore₀ :
      HasPathScore (ν₁.prod ν₂) (fun t ↦ (Q₁ t).prod (Q₂ t)) (fun z ↦ g₁₀ z.1 + g₂₀ z.2) by
    refine hscore₀.congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hg₁.aemeasurable.ae_eq_mk.symm,
      Measure.quasiMeasurePreserving_snd.ae_eq_comp hg₂.aemeasurable.ae_eq_mk.symm] with z hz₁ hz₂
    exact congr_arg₂ (· + ·) hz₁ hz₂
  refine ⟨fun t ↦ (h₁₀.1 t).prod (h₂₀.1 t), ?_⟩
  have hg₁s_mem := memLp_mul_sqrt_rnDeriv (h₁₀.1 0) h₁₀.memLp
  have hlim₂ : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (1 / 2) *
      eLpNorm (fun x ↦ g₁₀ x * Real.sqrt (((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ *
      eLpNorm (fun y ↦ Real.sqrt (((Q₂ t).rnDeriv ν₂ y).toReal) -
        Real.sqrt (((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂)
      (𝓝[>] 0) (𝓝 0) := by
    have hfin : ENNReal.ofReal (1 / 2) *
        eLpNorm (fun x ↦ g₁₀ x * Real.sqrt (((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg₁s_mem.ne
    simpa using ENNReal.Tendsto.const_mul h₂₀.tendsto_eLpNorm_sqrt_rnDeriv_sub (Or.inr hfin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using (h₁₀.2.add hlim₂).add h₂₀.2)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact eLpNorm_prod_remainder_le hg₁₀_meas hg₂₀_meas h₁₀.1 h₂₀.1 ht

end Constructions

/-! ### Location models with absolutely continuous density -/

section Location

/-- Shifting an almost-everywhere nonnegative real density with unit integral produces a
probability measure with respect to Lebesgue measure. -/
theorem isProbabilityMeasure_withDensity_ofReal_comp_sub_right {η : ℝ → ℝ} (hη : 0 ≤ᵐ[volume] η)
    (hη1 : ∫ x, η x = 1) (c : ℝ) :
    IsProbabilityMeasure (volume.withDensity fun x ↦ ENNReal.ofReal (η (x - c))) := by
  have hsub_int : Integrable (fun x ↦ η (x - c)) volume :=
    Integrable.comp_sub_right (integrable_of_integral_eq_one hη1) c
  have hsub_nn : 0 ≤ᵐ[volume] fun x ↦ η (x - c) :=
    (measurePreserving_sub_right volume c).quasiMeasurePreserving.ae hη
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hsub_int hsub_nn,
    integral_sub_right_eq_self η c, hη1, ENNReal.ofReal_one]

private theorem locallyIntegrable_of_all_intervalIntegrable {η' : ℝ → ℝ}
    (hη' : ∀ a b, IntervalIntegrable η' volume a b) : LocallyIntegrable η' volume :=
  fun x ↦ ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith),
    (hη' (x - 1) (x + 1)).1.mono_set Ioo_subset_Ioc_self⟩

private theorem absolutelyContinuousOnInterval_of_eq_integral {η η' : ℝ → ℝ}
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t) (a b : ℝ) :
    AbsolutelyContinuousOnInterval η a b := by
  have hshift (x : ℝ) : η x = η a + ∫ t in a..x, η' t := by
    rw [hac x, hac a, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (hη' 0 a) (hη' a x)]
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ η a) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  exact (hconst.add ((hη' a b).absolutelyContinuousOnInterval_intervalIntegral
    left_mem_uIcc)).congr fun x _ ↦ (hshift x).symm

private theorem continuous_of_eq_integral {η η' : ℝ → ℝ}
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t) : Continuous η := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc := (absolutelyContinuousOnInterval_of_eq_integral hη' hac (x - 1) (x + 1)).continuousOn
  rw [uIcc_of_le (by linarith)] at hc
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

private theorem ae_hasDerivAt_and_zero_of_eq_integral {η η' : ℝ → ℝ} (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t) :
    ∀ᵐ x ∂volume, HasDerivAt η (η' x) x ∧ (η x = 0 → η' x = 0) := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (locallyIntegrable_of_all_intervalIntegrable hη')] with x hx
  have hd : HasDerivAt η (η' x) x := by
    rw [funext hac]
    simpa [Pi.add_def] using (hasDerivAt_const x (η 0)).add (hx 0)
  refine ⟨hd, fun hx0 ↦ ?_⟩
  have hmin : IsLocalMin η x := Eventually.of_forall fun y ↦ by rw [hx0]; exact hη y
  rw [← hd.deriv, hmin.deriv_eq_zero]

private theorem memLp_half_score_sqrt {η η' : ℝ → ℝ} (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t)
    (hfisher : Integrable fun x ↦ η' x ^ 2 / η x) :
    MemLp (fun x ↦ η' x / (2 * Real.sqrt (η x))) 2 volume := by
  have hη_meas : Measurable η := (continuous_of_eq_integral hη' hac).measurable
  have hη'_asm : AEStronglyMeasurable η' volume :=
    (locallyIntegrable_of_all_intervalIntegrable hη').aestronglyMeasurable
  have hs'_asm : AEStronglyMeasurable (fun x ↦ η' x / (2 * Real.sqrt (η x))) volume :=
    (hη'_asm.aemeasurable.div (by fun_prop)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hs'_asm]
  refine (hfisher.const_mul (1 / 4 : ℝ)).congr (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [div_pow, mul_pow, Real.sq_sqrt (hη x)]
  ring

private theorem lipschitzOnWith_sqrt_add_pos {ε : ℝ} (hε : 0 < ε) :
    LipschitzOnWith (Real.toNNReal (2 * Real.sqrt ε)⁻¹)
      (fun y : ℝ ↦ Real.sqrt (y + ε)) (Ici 0) := by
  refine LipschitzOnWith.of_dist_le_mul fun x (hx : 0 ≤ x) y (hy : 0 ≤ y) ↦ ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
  have hden : 2 * Real.sqrt ε ≤ Real.sqrt (x + ε) + Real.sqrt (y + ε) := by
    have := Real.sqrt_le_sqrt (by linarith : ε ≤ x + ε)
    have := Real.sqrt_le_sqrt (by linarith : ε ≤ y + ε)
    linarith
  have hprod : |Real.sqrt (x + ε) - Real.sqrt (y + ε)| *
      (Real.sqrt (x + ε) + Real.sqrt (y + ε)) = |x - y| := by
    have heq : (Real.sqrt (x + ε) - Real.sqrt (y + ε)) *
        (Real.sqrt (x + ε) + Real.sqrt (y + ε)) = x - y := by
      nlinarith [Real.mul_self_sqrt (by linarith : 0 ≤ x + ε),
        Real.mul_self_sqrt (by linarith : 0 ≤ y + ε)]
    rw [← heq, abs_mul, abs_of_nonneg (a := Real.sqrt (x + ε) + Real.sqrt (y + ε)) (by positivity)]
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [abs_nonneg (Real.sqrt (x + ε) - Real.sqrt (y + ε))]

private theorem integral_div_sqrt_add_pos {η η' : ℝ → ℝ} (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t) (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ u in a..b, η' u / (2 * Real.sqrt (η u + ε))) =
      Real.sqrt (η b + ε) - Real.sqrt (η a + ε) := by
  have hf_ac : AbsolutelyContinuousOnInterval (fun u ↦ Real.sqrt (η u + ε)) a b :=
    (lipschitzOnWith_sqrt_add_pos hε).comp_absolutelyContinuousOnInterval (fun x _ ↦ hη x)
      (absolutelyContinuousOnInterval_of_eq_integral hη' hac a b)
  rw [← hf_ac.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_hasDerivAt_and_zero_of_eq_integral hη hη' hac] with u ⟨hu, _⟩ _
  exact ((hu.add_const ε).sqrt (by have := hη u; positivity)).deriv.symm

/-- **Increments of a square-root density under finite Fisher information** (van der Vaart, Example
25.15; Bickel–Klaassen–Ritov–Wellner, §2.1 Lemma 1). If `η : ℝ → ℝ` is nonnegative, absolutely
continuous with locally integrable derivative `η'`, and has finite Fisher information
`∫ (η' x)² / η x dx`, then `√(η b) - √(η a) = ∫ u in a..b, η' u / (2 √(η u))`. -/
theorem sqrt_sub_sqrt_eq_intervalIntegral {η η' : ℝ → ℝ} (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t)
    (hfisher : Integrable fun x ↦ η' x ^ 2 / η x) (a b : ℝ) :
    Real.sqrt (η b) - Real.sqrt (η a) = ∫ u in a..b, η' u / (2 * Real.sqrt (η u)) := by
  have hs' : MemLp (fun u ↦ η' u / (2 * Real.sqrt (η u))) 2 volume :=
    memLp_half_score_sqrt hη hη' hac hfisher
  have hη_meas : Measurable η := (continuous_of_eq_integral hη' hac).measurable
  have hη'_asm : AEStronglyMeasurable η' volume :=
    (locallyIntegrable_of_all_intervalIntegrable hη').aestronglyMeasurable
  have hae := ae_hasDerivAt_and_zero_of_eq_integral hη hη' hac
  have hftc : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ u in a..b, η' u / (2 * Real.sqrt (η u + ε))) =
        Real.sqrt (η b + ε) - Real.sqrt (η a + ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using integral_div_sqrt_add_pos hη hη' hac a b hε
  have hbound_int : IntervalIntegrable (fun u ↦ ‖η' u / (2 * Real.sqrt (η u))‖) volume a b := by
    have : IsFiniteMeasure (volume.restrict (uIoc a b)) := ⟨by simp⟩
    exact intervalIntegrable_iff.mpr ((hs'.norm.restrict (uIoc a b)).integrable one_le_two)
  have hlim_lhs : Tendsto (fun ε : ℝ ↦ ∫ u in a..b, η' u / (2 * Real.sqrt (η u + ε)))
      (𝓝[>] 0) (𝓝 (∫ u in a..b, η' u / (2 * Real.sqrt (η u)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ ‖η' u / (2 * Real.sqrt (η u))‖) ?_ ?_ hbound_int ?_
    · exact Eventually.of_forall fun ε ↦
        (hη'_asm.aemeasurable.div (by fun_prop)).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      filter_upwards [hae] with u ⟨_, hu0⟩ _
      rcases eq_or_ne (η u) 0 with h0 | h0
      · simp [hu0 h0]
      · have hpos : 0 < η u := lt_of_le_of_ne (hη u) (Ne.symm h0)
        simp only [Real.norm_eq_abs, abs_div,
          abs_of_pos (by positivity : 0 < 2 * Real.sqrt (η u + ε)),
          abs_of_pos (by positivity : 0 < 2 * Real.sqrt (η u))]
        gcongr; linarith
    · filter_upwards [hae] with u ⟨_, hu0⟩ _
      rcases eq_or_ne (η u) 0 with h0 | h0
      · simp [hu0 h0]
      · have hpos : 0 < η u := lt_of_le_of_ne (hη u) (Ne.symm h0)
        have hden_ne : 2 * Real.sqrt (η u + 0) ≠ 0 := by rw [add_zero]; positivity
        have hc : ContinuousAt (fun ε : ℝ ↦ η' u / (2 * Real.sqrt (η u + ε))) 0 :=
          ContinuousAt.div continuousAt_const
            (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).sqrt)) hden_ne
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim_rhs : Tendsto (fun ε : ℝ ↦ Real.sqrt (η b + ε) - Real.sqrt (η a + ε))
      (𝓝[>] 0) (𝓝 (Real.sqrt (η b) - Real.sqrt (η a))) := by
    have hc : Continuous fun ε : ℝ ↦ Real.sqrt (η b + ε) - Real.sqrt (η a + ε) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim_rhs (hlim_lhs.congr' hftc)

private theorem eLpNorm_location_remainder_le {s'₀ : ℝ → ℝ} (hs'₀_meas : Measurable s'₀)
    (θ t : ℝ) :
    eLpNorm (fun x ↦ ∫ u in Ioc (0 : ℝ) 1, (s'₀ (x - θ) - s'₀ (x - θ - t * u))) 2 volume ≤
      eLpNorm (fun u ↦ eLpNorm (fun x ↦ s'₀ (x - t * u) - s'₀ x) 2 volume) 2
        (volume.restrict (Ioc 0 1)) := by
  set φ : ℝ × ℝ → ℝ := fun p ↦ s'₀ (p.2 - θ) - s'₀ (p.2 - θ - t * p.1)
  have hφ : Measurable φ := by fun_prop
  set μ₁ := volume.restrict (Ioc (0 : ℝ) 1)
  have hμ₁_univ : μ₁ univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num
  have hsec_le (x : ℝ) : ‖∫ u, φ (u, x) ∂μ₁‖ₑ ≤ ‖eLpNorm (fun u ↦ φ (u, x)) 2 μ₁‖ₑ := by
    have hm : AEStronglyMeasurable (fun u ↦ φ (u, x)) μ₁ :=
      (hφ.comp measurable_prodMk_right).aestronglyMeasurable
    rw [eNorm_eq_self]
    calc ‖∫ u, φ (u, x) ∂μ₁‖ₑ
        ≤ ∫⁻ u, ‖φ (u, x)‖ₑ ∂μ₁ := eNorm_integral_le_lintegral_eNorm _
      _ = eLpNorm (fun u ↦ φ (u, x)) 1 μ₁ := (eLpNorm_one_eq_lintegral_eNorm hm).symm
      _ ≤ eLpNorm (fun u ↦ φ (u, x)) 2 μ₁ *
            μ₁ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two hm
      _ = eLpNorm (fun u ↦ φ (u, x)) 2 μ₁ := by rw [hμ₁_univ, ENNReal.one_rpow, mul_one]
  have hint_m : AEStronglyMeasurable (fun x ↦ ∫ u, φ (u, x) ∂μ₁) volume :=
    hφ.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  calc eLpNorm (fun x ↦ ∫ u, φ (u, x) ∂μ₁) 2 volume
      ≤ eLpNorm (fun x ↦ eLpNorm (fun u ↦ φ (u, x)) 2 μ₁) 2 volume :=
        eLpNorm_mono_eNorm hint_m hsec_le
    _ = eLpNorm (fun p : ℝ × ℝ ↦ φ (p.2, p.1)) 2 (volume.prod μ₁) :=
        (TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm
          (hφ.comp measurable_swap).aestronglyMeasurable).symm
    _ = eLpNorm φ 2 (μ₁.prod volume) :=
        eLpNorm_comp_measurePreserving hφ.aestronglyMeasurable
          (Measure.measurePreserving_swap (μ := volume) (ν := μ₁))
    _ = eLpNorm (fun u ↦ eLpNorm (fun x ↦ φ (u, x)) 2 volume) 2 μ₁ :=
        TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm hφ.aestronglyMeasurable
    _ = eLpNorm (fun u ↦ eLpNorm (fun x ↦ s'₀ (x - t * u) - s'₀ x) 2 volume) 2 μ₁ := by
        refine congrArg (fun f ↦ eLpNorm f 2 μ₁) (funext fun u ↦ ?_)
        have hm : AEStronglyMeasurable (fun x ↦ s'₀ x - s'₀ (x - t * u)) volume := by fun_prop
        have htr : eLpNorm (fun x ↦ φ (u, x)) 2 volume =
            eLpNorm (fun x ↦ s'₀ x - s'₀ (x - t * u)) 2 volume := by
          simpa [φ, Function.comp_def, sub_right_comm] using
            eLpNorm_comp_measurePreserving hm (measurePreserving_sub_right volume θ)
        rw [htr, ← eLpNorm_neg]
        exact eLpNorm_congr_ae (Eventually.of_forall fun x ↦ by simp)

private theorem ae_location_remainder_eq {η η' s'₀ : ℝ → ℝ} (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t)
    (hfisher : Integrable fun x ↦ η' x ^ 2 / η x)
    (hs'₀_ae : (fun y ↦ η' y / (2 * Real.sqrt (η y))) =ᵐ[volume] s'₀)
    (hs'₀_mem : MemLp s'₀ 2 volume) (θ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    (t⁻¹ • fun x ↦ Real.sqrt
          (((volume.withDensity fun y ↦
            ENNReal.ofReal (η (y - (θ + t)))).rnDeriv volume x).toReal) -
        Real.sqrt
          (((volume.withDensity fun y ↦ ENNReal.ofReal (η (y - θ))).rnDeriv volume x).toReal) -
        t / 2 * (-(η' (x - θ) / η (x - θ))) *
          Real.sqrt
            (((volume.withDensity fun y ↦ ENNReal.ofReal (η (y - θ))).rnDeriv volume x).toReal))
      =ᵐ[volume] fun x ↦ ∫ u in Ioc (0 : ℝ) 1, (s'₀ (x - θ) - s'₀ (x - θ - t * u)) := by
  have hη_meas : Measurable η := (continuous_of_eq_integral hη' hac).measurable
  have hd (c : ℝ) : (volume.withDensity fun y ↦ ENNReal.ofReal (η (y - c))).rnDeriv volume
      =ᵐ[volume] fun x ↦ ENNReal.ofReal (η (x - c)) :=
    Measure.rnDeriv_withDensity volume (by fun_prop)
  have hs'₀_ii (a b : ℝ) : IntervalIntegrable s'₀ volume a b := by
    have : IsFiniteMeasure (volume.restrict (uIoc a b)) := ⟨by simp⟩
    exact intervalIntegrable_iff.mpr ((hs'₀_mem.restrict (uIoc a b)).integrable one_le_two)
  filter_upwards [hd (θ + t), hd θ,
    (measurePreserving_sub_right volume θ).quasiMeasurePreserving.ae_eq_comp hs'₀_ae]
    with x hxt hx0 hxθ
  simp only [Pi.smul_apply, smul_eq_mul, hxt, hx0, ENNReal.toReal_ofReal (hη _)]
  have hscore_eq : -(η' (x - θ) / η (x - θ)) * Real.sqrt (η (x - θ)) = -2 * s'₀ (x - θ) := by
    dsimp only [Function.comp_apply] at hxθ
    rw [← hxθ]
    rcases eq_or_ne (η (x - θ)) 0 with h0 | h0
    · simp [h0]
    · have hsq : Real.sqrt (η (x - θ)) * Real.sqrt (η (x - θ)) = η (x - θ) :=
        Real.mul_self_sqrt (hη _)
      have hsr_ne : Real.sqrt (η (x - θ)) ≠ 0 :=
        (Real.sqrt_pos.mpr (lt_of_le_of_ne (hη _) (Ne.symm h0))).ne'
      nth_rw 1 [← hsq]
      field_simp
  have hsub_mul := intervalIntegral.integral_comp_sub_mul s'₀ ht0.ne' (x - θ) (a := 0) (b := 1)
  simp only [mul_zero, sub_zero, mul_one, smul_eq_mul] at hsub_mul
  rw [sub_sub x θ t] at hsub_mul
  have hint_eq : (∫ v in (x - (θ + t))..(x - θ), s'₀ v) =
      Real.sqrt (η (x - θ)) - Real.sqrt (η (x - (θ + t))) := by
    rw [intervalIntegral.integral_congr_ae (hs'₀_ae.symm.mono fun _ hv _ ↦ hv)]
    exact (sqrt_sub_sqrt_eq_intervalIntegral hη hη' hac hfisher (x - (θ + t)) (x - θ)).symm
  have hint1 : IntervalIntegrable (fun u ↦ s'₀ ((x - θ) - t * u)) volume 0 1 := by
    have h1 : IntervalIntegrable (fun v ↦ s'₀ ((x - θ) - v)) volume 0 t := by
      simpa using (hs'₀_ii (x - θ) (x - θ - t)).comp_sub_left (x - θ)
    simpa [ht0.ne'] using h1.comp_mul_left (c := t)
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub intervalIntegrable_const hint1, intervalIntegral.integral_const,
    sub_zero, one_smul, hsub_mul, hint_eq, mul_assoc (t / 2), hscore_eq]
  have := ht0.ne'; field_simp; ring

/-- **Path score of a location model** (van der Vaart, Example 25.15; Bickel–Klaassen–Ritov–Wellner,
§2.1 Example 2). If `η : ℝ → ℝ` is nonnegative, absolutely continuous with derivative `η'`, and has
finite Fisher information `∫ (η' x)² / η x dx`, then the location path
`t ↦ volume.withDensity (x ↦ ENNReal.ofReal (η (x - (θ + t))))` has path score
`x ↦ -(η' (x - θ) / η (x - θ))` relative to Lebesgue measure. -/
theorem hasPathScore_location (η η' : ℝ → ℝ) (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t)
    (hfisher : Integrable fun x ↦ η' x ^ 2 / η x) (θ : ℝ) :
    HasPathScore volume
      (fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (η (x - (θ + t))))
      (fun x ↦ -(η' (x - θ) / η (x - θ))) := by
  refine ⟨fun _ ↦ withDensity_absolutelyContinuous _ _, ?_⟩
  have hs' : MemLp (fun y ↦ η' y / (2 * Real.sqrt (η y))) 2 volume :=
    memLp_half_score_sqrt hη hη' hac hfisher
  set s'₀ : ℝ → ℝ := hs'.aestronglyMeasurable.aemeasurable.mk _
  have hs'₀_meas : Measurable s'₀ := hs'.aestronglyMeasurable.aemeasurable.measurable_mk
  have hs'₀_ae := hs'.aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hs'₀_mem : MemLp s'₀ 2 volume := (memLp_congr_ae hs'₀_ae).mp hs'
  have htr_lim : Tendsto (fun w : ℝ ↦ eLpNorm (fun x ↦ s'₀ (x - w) - s'₀ x) 2 volume)
      (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (hs'₀_mem.tendsto_eLpNorm_comp_add_sub one_le_two ENNReal.ofNat_ne_top).comp
        (continuous_neg.tendsto' 0 0 neg_zero)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (ENNReal.tendsto_nhds_zero.mp htr_lim ε hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ⟨ht0, htδ⟩
  have hae := ae_location_remainder_eq hη hη' hac hfisher hs'₀_ae hs'₀_mem θ ht0
  simp only [add_zero]
  rw [← Real.eNorm_eq_ofReal (inv_nonneg.mpr ht0.le), ← eLpNorm_const_smul, eLpNorm_congr_ae hae]
  refine (eLpNorm_location_remainder_le hs'₀_meas θ t).trans ?_
  set μ₁ := volume.restrict (Ioc (0 : ℝ) 1)
  have hsec_m : AEStronglyMeasurable
      (fun u ↦ eLpNorm (fun x ↦ s'₀ (x - t * u) - s'₀ x) 2 volume) μ₁ :=
    (by fun_prop : Measurable fun p : ℝ × ℝ ↦
      s'₀ (p.2 - t * p.1) - s'₀ p.2).aestronglyMeasurable.eLpNorm_prod_right
  have hae_le : ∀ᵐ u ∂μ₁, ‖eLpNorm (fun x ↦ s'₀ (x - t * u) - s'₀ x) 2 volume‖ₑ ≤ ‖ε‖ₑ := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u ⟨hu0, hu1⟩ ↦ ?_
    simp only [eNorm_eq_self]
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos ht0 hu0)]
    nlinarith
  refine (eLpNorm_mono_eNorm_ae hsec_m hae_le).trans ?_
  rw [eLpNorm_const' ε two_ne_zero ENNReal.ofNat_ne_top, eNorm_eq_self,
    Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

end Location

end TauCeti
end
