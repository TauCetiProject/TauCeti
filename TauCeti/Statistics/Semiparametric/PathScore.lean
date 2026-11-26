/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod
public import TauCeti.MeasureTheory.Measure.Decomposition.RNDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.Sigmoid
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.MeasureTheory.Function.WeightL2Isometry
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.Measure.Decomposition.Prod
import TauCeti.MeasureTheory.Measure.Weighted
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Differentiable paths of measures and path scores

In semiparametric statistics, tangent vectors to a statistical model at a law `P` are scores of
one-dimensional submodels `t ↦ Q t` passing through `Q 0 = P`, differentiated from the right at
`t = 0` in quadratic mean relative to a dominating measure `ν`:
`t⁻¹ ‖√(d(Q t)/dν) - √(d(Q 0)/dν) - (t / 2) g √(d(Q 0)/dν)‖_{L²(ν)} → 0` as `t → 0⁺`.

Measuring the remainder by Mathlib's `eLpNorm` in `ℝ≥0∞` avoids Bochner-integral junk values: a
remainder that fails to be square integrable has infinite `L²(ν)` seminorm and cannot masquerade as
`o(t)`. Likewise, `HasPathScore ν Q g` requires both `∀ t, Q t ≪ ν` and
`∀ t, (Q t).HaveLebesgueDecomposition ν` (which holds automatically whenever `ν` is σ-finite and
every `Q t` is s-finite), preventing `rnDeriv` from collapsing to its junk value `0`. Densities are
read into `ℝ` through `((Q t).rnDeriv ν x).toReal`, which agrees `ν`-almost everywhere with
`(Q t).rnDeriv ν` whenever `Q t` is σ-finite (while mapping infinite density values to `0` on
non-σ-finite measures). Taking the right-hand limit `𝓝[>] 0` allows submodels whose parameter lies
on a boundary at `t = 0`.

## Main definitions

* `TauCeti.HasPathScore ν Q g`: quadratic-mean differentiability of `t ↦ Q t` from the right at `0`
  with score `g : X → ℝ` relative to a dominating measure `ν`.
* `TauCeti.tiltPath P g C t`: the bounded linear tilt weighting `P` by
  `ENNReal.ofReal (1 + t * g x)` for `|t| * C < 1` (which clips negative values in general, and
  equals `1 + t * g x` `P`-almost everywhere inside the cutoff when `|g| ≤ C` `P`-almost
  everywhere), cut off to `P` when `1 ≤ |t| * C`.

## Main statements

* `TauCeti.HasPathScore.congr_ae`, `TauCeti.HasPathScore.congr_path`,
  `TauCeti.hasPathScore_const_zero_iff`, and `TauCeti.HasPathScore.comp_mul_left`: congruence under
  `Q 0`-almost-everywhere score equality and eventual right-hand path agreement, constant paths, and
  nonnegative left parameter rescaling.
* `TauCeti.HasPathScore.memLp_mul_sqrt_toReal_rnDeriv`, `TauCeti.HasPathScore.memLp`,
  `TauCeti.hasPathScore_iff_hasDerivWithinAt_sqrt_toReal_rnDeriv_toLp`,
  `TauCeti.HasPathScore.hasDerivWithinAt_sqrt_toReal_rnDeriv_toLp`,
  `TauCeti.HasPathScore.tendsto_eLpNorm_sqrt_toReal_rnDeriv_sub`, and
  `TauCeti.HasPathScore.integral_eq_zero`: every path score of a path of finite measures is square
  integrable under `Q 0` (in particular `Q 0`-a.e. strongly measurable); when `Q t ≪ ν` with
  Lebesgue decompositions and `g · √(d(Q 0)/dν) ∈ L²(ν)`, `HasPathScore ν Q g` is equivalent to
  right differentiability of `t ↦ √(d(Q t)/dν)` in `L²(ν)` at `0` with right derivative
  `(1 / 2) • (g · √(d(Q 0)/dν))`, hence implies `L²(ν)` right-continuity at `0` and mean zero under
  `Q 0` when each `Q t` is a probability measure.
* `TauCeti.hasPathScore_iff_of_absolutelyContinuous`: for a path of σ-finite measures,
  `HasPathScore ν Q g` is independent of the choice of σ-finite measure dominating every `Q t`.
* `TauCeti.HasPathScore.ae_eq`: when `Q 0` is σ-finite, any two scores of the same path agree
  `Q 0`-almost everywhere.
* `TauCeti.isProbabilityMeasure_tiltPath` and `TauCeti.hasPathScore_tiltPath`: `P`-a.e. strongly
  measurable functions satisfying `|g| ≤ C` `P`-a.e. on a finite measure space generate linear tilts
  whose path score is `g` (and are probability measures when `P` is a probability measure and
  `∫ g ∂P = 0`).
* `TauCeti.exists_hasPathScore_of_integral_eq_zero`: every square-integrable mean-zero function on
  a probability space is the score of a path of probability measures dominated by `P`.
* `TauCeti.HasPathScore.prod`: the product of two differentiable paths of finite measures with
  respect to σ-finite reference measures `ν₁` and `ν₂` has score `(x, y) ↦ g₁ x + g₂ y` relative to
  `ν₁ ⊗ ν₂`.
* `TauCeti.hasPathScore_location`: for an absolutely continuous nonnegative density `η` on `ℝ` with
  locally integrable derivative `η'` and finite Fisher information `∫ η'² / η`, the location path
  `t ↦ η(x - θ - t) dx` has score `x ↦ -(η'(x - θ) / η(x - θ))` relative to Lebesgue measure.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.3
  (eq. (25.13), Lemma 25.14, Example 25.16).
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A. Wellner, *Efficient and Adaptive Estimation
  for Semiparametric Models*, Johns Hopkins University Press, 1993, §2.1 (Example 2) and Appendix
  A.5 (Corollary 1, citing J. Hájek and Z. Šidák, *Theory of Rank Tests*, Academic Press, 1967).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section Basic

variable {X : Type*} [MeasurableSpace X]

/-- The path `t ↦ Q t` of measures is differentiable in quadratic mean from the right at `0` with
score `g`, relative to the dominating measure `ν`. Every `Q t` is required to be absolutely
continuous with respect to `ν` and to admit a Lebesgue decomposition against `ν` (which holds
automatically when `ν` is σ-finite and each `Q t` is s-finite). Densities are read into `ℝ` via
`((Q t).rnDeriv ν x).toReal` (which agrees `ν`-a.e. with `(Q t).rnDeriv ν` when `Q t` is σ-finite,
and maps `∞` to `0`), and the remainder is measured by `eLpNorm` in `ℝ≥0∞` so that a
non-square-integrable remainder has infinite norm rather than `0`. -/
def HasPathScore (ν : Measure X) (Q : ℝ → Measure X) (g : X → ℝ) : Prop :=
  (∀ t, Q t ≪ ν) ∧ (∀ t, (Q t).HaveLebesgueDecomposition ν) ∧
    Tendsto (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
        Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
          - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) (𝓝[>] 0) (𝓝 0)

/-- Unfolding characterization of `HasPathScore`. -/
theorem hasPathScore_def (ν : Measure X) (Q : ℝ → Measure X) (g : X → ℝ) :
    HasPathScore ν Q g ↔
      (∀ t, Q t ≪ ν) ∧ (∀ t, (Q t).HaveLebesgueDecomposition ν) ∧
        Tendsto (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
            Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
              - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) (𝓝[>] 0) (𝓝 0) := Iff.rfl

/-- Every measure along a path with a score relative to `ν` is absolutely continuous with respect
to `ν`. -/
theorem HasPathScore.absolutelyContinuous {ν : Measure X} {Q : ℝ → Measure X} {g : X → ℝ}
    (h : HasPathScore ν Q g) (t : ℝ) : Q t ≪ ν := h.1 t

/-- Every measure along a path with a score relative to `ν` admits a Lebesgue decomposition with
respect to `ν`. -/
theorem HasPathScore.haveLebesgueDecomposition {ν : Measure X} {Q : ℝ → Measure X} {g : X → ℝ}
    (h : HasPathScore ν Q g) (t : ℝ) : (Q t).HaveLebesgueDecomposition ν := h.2.1 t

/-- The `L²(ν)` quadratic-mean remainder limit of `HasPathScore`. -/
theorem HasPathScore.tendsto {ν : Measure X} {Q : ℝ → Measure X} {g : X → ℝ}
    (h : HasPathScore ν Q g) :
    Tendsto (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
        Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal
          - t / 2 * g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) (𝓝[>] 0) (𝓝 0) := h.2.2

/-- Modifying `g` on a `Q 0`-null set preserves `HasPathScore ν Q g`. -/
theorem HasPathScore.congr_ae {ν : Measure X} {Q : ℝ → Measure X} {g g' : X → ℝ}
    (h : HasPathScore ν Q g) (hgg' : g =ᵐ[Q 0] g') : HasPathScore ν Q g' := by
  refine ⟨h.1, h.2.1, h.tendsto.congr fun t ↦ ?_⟩
  congr 1
  have hae : ∀ᵐ x ∂ν, (Q 0).rnDeriv ν x ≠ 0 → g x = g' x :=
    (ae_withDensity_iff (Measure.measurable_rnDeriv _ _)).mp
      (hgg'.filter_mono (ae_mono (Measure.withDensity_rnDeriv_le (Q 0) ν)))
  refine eLpNorm_congr_ae (hae.mono fun x hx ↦ ?_)
  by_cases h0 : (Q 0).rnDeriv ν x = 0 <;> simp [h0, hx]

/-- Two paths dominated by `ν` (with Lebesgue decompositions against `ν`) that agree at `0` and
eventually as `t → 0⁺` (`Q' =ᶠ[𝓝[>] 0] Q`) have the same path scores. -/
theorem HasPathScore.congr_path {ν : Measure X} {Q Q' : ℝ → Measure X}
    [hLD : ∀ t, (Q' t).HaveLebesgueDecomposition ν] {g : X → ℝ} (h : HasPathScore ν Q g)
    (hQ' : ∀ t, Q' t ≪ ν) (h0 : Q' 0 = Q 0) (hev : Q' =ᶠ[𝓝[>] 0] Q) : HasPathScore ν Q' g := by
  refine ⟨hQ', hLD, h.tendsto.congr' ?_⟩
  filter_upwards [hev] with t ht using by simp [ht, h0]

/-- A constant path `t ↦ P` has path score `0` relative to `ν` if and only if `P ≪ ν` and `P`
admits a Lebesgue decomposition with respect to `ν`. -/
@[simp]
theorem hasPathScore_const_zero_iff (ν P : Measure X) :
    HasPathScore ν (fun _ ↦ P) 0 ↔ P ≪ ν ∧ P.HaveLebesgueDecomposition ν :=
  ⟨fun h ↦ ⟨h.1 0, h.2.1 0⟩, fun ⟨hP, hLD⟩ ↦ ⟨fun _ ↦ hP, fun _ ↦ hLD, by simp⟩⟩

/-- Rescaling the parameter of a path on the left by `c ≥ 0` scales its path score by `c`. -/
theorem HasPathScore.comp_mul_left {ν : Measure X} {Q : ℝ → Measure X} {g : X → ℝ}
    (h : HasPathScore ν Q g) {c : ℝ} (hc : 0 ≤ c) :
    HasPathScore ν (fun t ↦ Q (c * t)) (c • g) := by
  rcases hc.eq_or_lt with rfl | hc_pos
  · simpa [zero_smul] using ⟨h.1 0, h.2.1 0⟩
  refine ⟨fun t ↦ h.1 (c * t), fun t ↦ h.2.1 (c * t), ?_⟩
  have hmap : Tendsto (fun t : ℝ ↦ c * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc_cont : Continuous fun t : ℝ ↦ c * t := by fun_prop
      simpa using (hc_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) using mul_pos hc_pos ht
  have hlim : Tendsto (fun t ↦ ENNReal.ofReal c * (ENNReal.ofReal (c * t)⁻¹ * eLpNorm (fun x ↦
        √((Q (c * t)).rnDeriv ν x).toReal - √((Q 0).rnDeriv ν x).toReal -
          ((c * t) / 2) * g x * √((Q 0).rnDeriv ν x).toReal) 2 ν))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal c * 0)) :=
    ENNReal.Tendsto.const_mul (h.tendsto.comp hmap) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hct : c * (c * t)⁻¹ = t⁻¹ := by have := hc_pos.ne'; field_simp
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc, hct]
  refine congrArg (fun f ↦ ENNReal.ofReal t⁻¹ * eLpNorm f 2 ν) (funext fun x ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, mul_zero]
  ring

end Basic

/-! ### Square-integrability, `L²` right-differentiability, mean zero, and uniqueness -/

section Properties

variable {X : Type*} [MeasurableSpace X]

/-- Along a path of finite measures with score `g`, the weighted score `g · √(d(Q 0)/dν)` belongs
to `L²(ν)`. -/
theorem HasPathScore.memLp_mul_sqrt_toReal_rnDeriv {ν : Measure X} {Q : ℝ → Measure X}
    [∀ t, IsFiniteMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) :
    MemLp (fun x ↦ g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν := by
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
      √((Q t).rnDeriv ν x).toReal - √((Q 0).rnDeriv ν x).toReal
        - t / 2 * g x * √((Q 0).rnDeriv ν x).toReal) 2 ν < 1 :=
    h.tendsto.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨t, ht_lt, ht_pos : 0 < t⟩ := (hlt.and self_mem_nhdsWithin).exists
  set rem : X → ℝ := fun x ↦ √((Q t).rnDeriv ν x).toReal - √((Q 0).rnDeriv ν x).toReal -
    t / 2 * g x * √((Q 0).rnDeriv ν x).toReal
  have hinv_ne : ENNReal.ofReal t⁻¹ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ht_pos)
  have hrem_mem : MemLp rem 2 ν := memLp_iff.mpr (lt_top_iff_ne_top.mpr fun htop ↦ by
    simp [htop, ENNReal.mul_top hinv_ne] at ht_lt)
  have hlin := ((Measure.memLp_two_sqrt_toReal_rnDeriv (Q t) ν).sub
    (Measure.memLp_two_sqrt_toReal_rnDeriv (Q 0) ν)).sub hrem_mem
  refine (memLp_congr_ae (Eventually.of_forall fun x ↦ ?_)).mp (hlin.const_mul (2 / t))
  have ht0 : t ≠ 0 := ht_pos.ne'
  dsimp [rem]; field_simp; ring

/-- Every path score of a path of finite measures is square integrable under `Q 0`, and in
particular `Q 0`-almost everywhere strongly measurable (van der Vaart, Lemma 25.14, first
assertion). -/
theorem HasPathScore.memLp {ν : Measure X} {Q : ℝ → Measure X} [∀ t, IsFiniteMeasure (Q t)]
    {g : X → ℝ} (h : HasPathScore ν Q g) : MemLp g 2 (Q 0) := by
  have := h.haveLebesgueDecomposition 0
  exact (Measure.memLp_mul_sqrt_toReal_rnDeriv_iff (h.1 0)).mp h.memLp_mul_sqrt_toReal_rnDeriv

/-- **Hilbert-space characterization of path scores.** For a path `Q` of finite measures dominated
by `ν` (with Lebesgue decompositions against `ν`) and a function `g` with
`g · √(d(Q 0)/dν) ∈ L²(ν)`, `HasPathScore ν Q g` holds if and only if the curve `t ↦ √(d(Q t)/dν)`
in `L²(ν)` has right derivative `(1 / 2) • (g · √(d(Q 0)/dν))` at `0`. -/
theorem hasPathScore_iff_hasDerivWithinAt_sqrt_toReal_rnDeriv_toLp {ν : Measure X}
    {Q : ℝ → Measure X} [∀ t, IsFiniteMeasure (Q t)] [hLD : ∀ t, (Q t).HaveLebesgueDecomposition ν]
    {g : X → ℝ} (hQ : ∀ t, Q t ≪ ν)
    (hg : MemLp (fun x ↦ g x * Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν) :
    HasPathScore ν Q g ↔
      HasDerivWithinAt (fun t ↦ (Measure.memLp_two_sqrt_toReal_rnDeriv (Q t) ν).toLp _)
        ((1 / 2 : ℝ) • hg.toLp _) (Ici 0) 0 := by
  have hs_mem (t : ℝ) : MemLp (t⁻¹ • ((fun x ↦ √((Q t).rnDeriv ν x).toReal) -
      fun x ↦ √((Q 0).rnDeriv ν x).toReal)) 2 ν :=
    ((Measure.memLp_two_sqrt_toReal_rnDeriv (Q t) ν).sub
      (Measure.memLp_two_sqrt_toReal_rnDeriv (Q 0) ν)).const_smul t⁻¹
  have hg_half : MemLp ((1 / 2 : ℝ) • fun x ↦ g x * √((Q 0).rnDeriv ν x).toReal) 2 ν :=
    hg.const_smul (1 / 2 : ℝ)
  have hIci : Ici (0 : ℝ) \ {0} = Ioi 0 := by ext x; simp [lt_iff_le_and_ne, ne_comm]
  have hslope_eq : slope (fun t ↦ (Measure.memLp_two_sqrt_toReal_rnDeriv (Q t) ν).toLp _) 0 =
      fun t ↦ (hs_mem t).toLp _ := funext fun t ↦ by
    rw [slope_def_module, sub_zero, ← MemLp.toLp_sub, ← MemLp.toLp_const_smul]
  rw [hasPathScore_def, and_iff_right hQ, and_iff_right hLD, hasDerivWithinAt_iff_tendsto_slope,
    hIci, hslope_eq, ← MemLp.toLp_const_smul (1 / 2 : ℝ) hg,
    Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hs_mem _ hg_half]
  refine tendsto_congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [← Real.eNorm_eq_ofReal (inv_nonneg.mpr ht.le), ← eLpNorm_const_smul]
  refine eLpNorm_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have ht0 : t ≠ 0 := ht.ne'
  field_simp

/-- Along a path of finite measures with score `g`, the curve `t ↦ √(d(Q t)/dν)` in `L²(ν)` has
right derivative `(1 / 2) • (g · √(d(Q 0)/dν))` at `0`. -/
theorem HasPathScore.hasDerivWithinAt_sqrt_toReal_rnDeriv_toLp {ν : Measure X}
    {Q : ℝ → Measure X} [∀ t, IsFiniteMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) :
    HasDerivWithinAt (fun t ↦ (Measure.memLp_two_sqrt_toReal_rnDeriv (Q t) ν).toLp _)
      ((1 / 2 : ℝ) • h.memLp_mul_sqrt_toReal_rnDeriv.toLp _) (Ici 0) 0 := by
  have := h.haveLebesgueDecomposition
  exact (hasPathScore_iff_hasDerivWithinAt_sqrt_toReal_rnDeriv_toLp h.1
    h.memLp_mul_sqrt_toReal_rnDeriv).mp h

/-- Along a path of finite measures with a path score, the square-root densities `√(d(Q t)/dν)`
converge to `√(d(Q 0)/dν)` in `L²(ν)` as `t → 0⁺`. -/
theorem HasPathScore.tendsto_eLpNorm_sqrt_toReal_rnDeriv_sub {ν : Measure X} {Q : ℝ → Measure X}
    [∀ t, IsFiniteMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦
      Real.sqrt ((Q t).rnDeriv ν x).toReal - Real.sqrt ((Q 0).rnDeriv ν x).toReal) 2 ν)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [Pi.sub_def] using
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
      (fun t ↦ Measure.memLp_two_sqrt_toReal_rnDeriv (Q t) ν) _
      (Measure.memLp_two_sqrt_toReal_rnDeriv (Q 0) ν)).mp
      (h.hasDerivWithinAt_sqrt_toReal_rnDeriv_toLp.continuousWithinAt.tendsto.mono_left
        (nhdsWithin_mono 0 Ioi_subset_Ici_self))

/-- Every path score of a path of probability measures has mean zero under `Q 0`
(van der Vaart, Lemma 25.14, first assertion). -/
theorem HasPathScore.integral_eq_zero {ν : Measure X} {Q : ℝ → Measure X}
    [∀ t, IsProbabilityMeasure (Q t)] {g : X → ℝ} (h : HasPathScore ν Q g) :
    ∫ x, g x ∂Q 0 = 0 := by
  have := h.haveLebesgueDecomposition
  set S : ℝ → Lp ℝ 2 ν := fun t ↦ (Measure.memLp_two_sqrt_toReal_rnDeriv (Q t) ν).toLp _
  have hG_mem := h.memLp_mul_sqrt_toReal_rnDeriv
  set G : Lp ℝ 2 ν := hG_mem.toLp _
  have hd : HasDerivWithinAt (fun t ↦ ‖S t‖ ^ 2)
      (2 * inner ℝ (S 0) ((1 / 2 : ℝ) • G)) (Ici 0) 0 :=
    h.hasDerivWithinAt_sqrt_toReal_rnDeriv_toLp.norm_sq
  have hconst : (fun t ↦ ‖S t‖ ^ 2) = fun _ ↦ (1 : ℝ) := funext fun t ↦ by
    rw [Lp.norm_toLp, (Q t).eLpNorm_sqrt_toReal_rnDeriv_eq_one ν (h.1 t)]
    norm_num
  have hd0 : HasDerivWithinAt (fun t ↦ ‖S t‖ ^ 2) 0 (Ici 0) 0 :=
    hconst ▸ hasDerivWithinAt_const 0 (Ici 0) (1 : ℝ)
  have h0 : 2 * inner ℝ (S 0) ((1 / 2 : ℝ) • G) = 0 := by
    rw [← hd.derivWithin (uniqueDiffWithinAt_Ici 0), hd0.derivWithin (uniqueDiffWithinAt_Ici 0)]
  have hSG : inner ℝ (S 0) G = 0 := by
    simp only [inner_smul_right] at h0
    linarith
  rw [L2.inner_def] at hSG
  rw [← integral_toReal_rnDeriv_mul (h.1 0)]
  refine (integral_congr_ae ?_).trans hSG
  filter_upwards [(Measure.memLp_two_sqrt_toReal_rnDeriv (Q 0) ν).coeFn_toLp,
    hG_mem.coeFn_toLp] with x hSx hGx
  simp only [RCLike.inner_apply, RCLike.conj_to_real, S, G, hSx, hGx]
  linear_combination -g x * Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := (Q 0).rnDeriv ν x))

/-- **Independence of the dominating measure.** If every `Q t` is σ-finite and absolutely
continuous with respect to both `ν` and `ν'`, then `HasPathScore ν Q g` and `HasPathScore ν' Q g`
are equivalent. -/
theorem hasPathScore_iff_of_absolutelyContinuous {ν ν' : Measure X} [SigmaFinite ν]
    [SigmaFinite ν'] {Q : ℝ → Measure X} [∀ t, SigmaFinite (Q t)] {g : X → ℝ}
    (hQ : ∀ t, Q t ≪ ν) (hQ' : ∀ t, Q t ≪ ν') :
    HasPathScore ν Q g ↔ HasPathScore ν' Q g := by
  suffices ∀ {ρ μ : Measure X} [SigmaFinite ρ] [SigmaFinite μ],
      (∀ t, Q t ≪ ρ) → ρ ≪ μ → (HasPathScore ρ Q g ↔ HasPathScore μ Q g) from
    (this hQ (rfl.absolutelyContinuous.add_right ν')).trans
      (this hQ' (rfl.absolutelyContinuous.add_right' ν)).symm
  intro ρ μ _ _ hQρ hρμ
  have heq (t : ℝ) : eLpNorm (fun x ↦ √((Q t).rnDeriv ρ x).toReal - √((Q 0).rnDeriv ρ x).toReal
        - t / 2 * g x * √((Q 0).rnDeriv ρ x).toReal) 2 ρ =
      eLpNorm (fun x ↦ √((Q t).rnDeriv μ x).toReal - √((Q 0).rnDeriv μ x).toReal
        - t / 2 * g x * √((Q 0).rnDeriv μ x).toReal) 2 μ := by
    rw [← Measure.eLpNorm_mul_sqrt_toReal_rnDeriv hρμ]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ) (hQρ t),
      Measure.rnDeriv_mul_rnDeriv (κ := μ) (hQρ 0)] with x hqt hq0
    simp only [← hqt, ← hq0, Pi.mul_apply, ENNReal.toReal_mul,
      Real.sqrt_mul ENNReal.toReal_nonneg]
    ring
  exact ⟨fun h ↦ ⟨fun t ↦ (hQρ t).trans hρμ, inferInstance, by simp_rw [← heq]; exact h.tendsto⟩,
    fun h ↦ ⟨hQρ, inferInstance, by simp_rw [heq]; exact h.tendsto⟩⟩

/-- **Uniqueness of path scores.** When `Q 0` is σ-finite, any two path scores of `Q` agree
`Q 0`-almost everywhere. -/
theorem HasPathScore.ae_eq {ν : Measure X} {Q : ℝ → Measure X} [SigmaFinite (Q 0)] {g g' : X → ℝ}
    (h : HasPathScore ν Q g) (h' : HasPathScore ν Q g') : g =ᵐ[Q 0] g' := by
  have := h.haveLebesgueDecomposition 0
  set s₀ : X → ℝ := fun x ↦ √((Q 0).rnDeriv ν x).toReal
  have hdiff_zero : eLpNorm (fun x ↦ (1 / 2 : ℝ) * (g' x - g x) * s₀ x) 2 ν = 0 := by
    refine le_antisymm ?_ zero_le
    have hsum : Tendsto (fun t : ℝ ↦
        ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
          √((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g x * s₀ x) 2 ν +
        ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦
          √((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g' x * s₀ x) 2 ν) (𝓝[>] 0) (𝓝 0) := by
      simpa only [add_zero] using h.tendsto.add h'.tendsto
    refine ge_of_tendsto hsum ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    set r₁ : X → ℝ := fun x ↦ √((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g x * s₀ x
    set r₂ : X → ℝ := fun x ↦ √((Q t).rnDeriv ν x).toReal - s₀ x - t / 2 * g' x * s₀ x
    have heq : (fun x ↦ (1 / 2 : ℝ) * (g' x - g x) * s₀ x) = (t⁻¹ • r₁) + ((-t⁻¹) • r₂) := by
      ext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, r₁, r₂]
      have ht0 : t ≠ 0 := ht.ne'
      field_simp
      ring
    rw [heq]
    exact (eLpNorm_add_le one_le_two).trans_eq (by
      rw [eLpNorm_const_smul, eLpNorm_const_smul, eNorm_neg,
        Real.eNorm_eq_ofReal (inv_nonneg.mpr ht.le)])
  have hae_ν : (fun x ↦ (1 / 2 : ℝ) * (g' x - g x) * s₀ x) =ᵐ[ν] 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).mp hdiff_zero
  filter_upwards [(h.1 0) hae_ν, Measure.ae_sqrt_toReal_rnDeriv_pos (h.1 0)] with x hx hs₀_pos
  simp only [Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with (h12 | hsub) | hs0
  · norm_num at h12
  · linarith
  · exact absurd hs0 hs₀_pos.ne'

end Properties

/-! ### Bounded tilts, logistic tilts of arbitrary `L²₀` scores, and product paths -/

section Constructions

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The bounded linear tilt weighting `P` by `ENNReal.ofReal (1 + t * g x)` for `|t| * C < 1`, cut
off to `P` when `1 ≤ |t| * C`. In general `ENNReal.ofReal` clips negative values of `1 + t * g x`;
when `|g| ≤ C` `P`-almost everywhere, `1 + t * g x ≥ 0` `P`-almost everywhere inside the cutoff so
no clipping occurs, and if moreover `P` is a probability measure, `g` is `P`-a.e. strongly
measurable, and `∫ g ∂P = 0`, every `tiltPath P g C t` is a probability measure
(`isProbabilityMeasure_tiltPath`). -/
def tiltPath (P : Measure X) (g : X → ℝ) (C : ℝ) (t : ℝ) : Measure X :=
  if |t| * C < 1 then P.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x)) else P

/-- Unfolding characterization of `tiltPath`. -/
theorem tiltPath_def (P : Measure X) (g : X → ℝ) (C : ℝ) (t : ℝ) :
    tiltPath P g C t =
      if |t| * C < 1 then P.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x)) else P := (rfl)

/-- At `t = 0`, `tiltPath P g C` equals the base measure `P`. -/
@[simp]
theorem tiltPath_zero (P : Measure X) (g : X → ℝ) (C : ℝ) : tiltPath P g C 0 = P := by
  simp [tiltPath]

/-- Within the cutoff `|t| * C < 1`, `tiltPath P g C t` weights `P` by
`ENNReal.ofReal (1 + t * g x)` (which agrees `P`-almost everywhere with `1 + t * g x` when
`|g| ≤ C` `P`-almost everywhere). -/
theorem tiltPath_of_lt {P : Measure X} {g : X → ℝ} {C t : ℝ} (ht : |t| * C < 1) :
    tiltPath P g C t = P.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x)) := by
  simp [tiltPath, ht]

/-- Beyond the cutoff `1 ≤ |t| * C`, `tiltPath P g C t` falls back to `P`. -/
theorem tiltPath_of_le {P : Measure X} {g : X → ℝ} {C t : ℝ} (ht : 1 ≤ |t| * C) :
    tiltPath P g C t = P := by simp [tiltPath, not_lt.mpr ht]

/-- Tilting `P` in direction `0` leaves `P` unchanged for every `t`. -/
@[simp]
theorem tiltPath_zero_score (P : Measure X) (C t : ℝ) : tiltPath P 0 C t = P := by
  by_cases ht : |t| * C < 1 <;> simp [tiltPath, ht]

/-- Every measure along `tiltPath P g C` is absolutely continuous with respect to `P`. -/
theorem tiltPath_absolutelyContinuous (P : Measure X) (g : X → ℝ) (C t : ℝ) :
    tiltPath P g C t ≪ P := by
  by_cases ht : |t| * C < 1
  · rw [tiltPath_of_lt ht]; exact withDensity_absolutelyContinuous _ _
  · rw [tiltPath_of_le (not_lt.mp ht)]

/-- When `P` is σ-finite, every measure along `tiltPath P g C` is σ-finite. -/
instance sigmaFinite_tiltPath (P : Measure X) [SigmaFinite P] (g : X → ℝ) (C t : ℝ) :
    SigmaFinite (tiltPath P g C t) := by
  unfold tiltPath; split_ifs <;> infer_instance

/-- For a bounded `P`-almost-everywhere measurable function `g` with mean zero under a probability
measure `P`, every measure along `tiltPath P g C` is a probability measure. -/
theorem isProbabilityMeasure_tiltPath {P : Measure X} [IsProbabilityMeasure P] {g : X → ℝ}
    (hg : AEStronglyMeasurable g P) {C : ℝ} (hC : ∀ᵐ x ∂P, |g x| ≤ C)
    (hmean : ∫ x, g x ∂P = 0) (t : ℝ) : IsProbabilityMeasure (tiltPath P g C t) := by
  by_cases ht : |t| * C < 1
  · rw [tiltPath_of_lt ht]
    have hg_int : Integrable g P := (memLp_top_of_bound hg C hC).integrable le_top
    refine isProbabilityMeasure_withDensity_ofReal ?_ ?_
    · filter_upwards [hC] with x hx
      have h1 : |t * g x| ≤ |t| * C := abs_mul t (g x) ▸ mul_le_mul_of_nonneg_left hx (abs_nonneg t)
      simp only [Pi.zero_apply]; linarith [neg_abs_le (t * g x)]
    · simp [integral_add (integrable_const 1) (hg_int.const_mul t), integral_const_mul, hmean]
  · rw [tiltPath_of_le (not_lt.mp ht)]; infer_instance

private theorem eLpNorm_tiltPath_remainder_le {P : Measure X} [IsFiniteMeasure P] {g : X → ℝ}
    (hg : AEStronglyMeasurable g P) {C t : ℝ} (hC : ∀ᵐ x ∂P, |g x| ≤ C) (ht : 0 < t)
    (htM : t * max C 1 < 1) :
    eLpNorm (fun x ↦ √((tiltPath P g C t).rnDeriv P x).toReal -
      √((tiltPath P g C 0).rnDeriv P x).toReal -
      t / 2 * g x * √((tiltPath P g C 0).rnDeriv P x).toReal) 2 P ≤
      ENNReal.ofReal (t ^ 2 * C ^ 2 / 2) * P univ ^ (2 : ℝ≥0∞).toReal⁻¹ := by
  have htC : |t| * C < 1 := by
    rw [abs_of_pos ht]; linarith [mul_le_mul_of_nonneg_left (le_max_left C 1) ht.le]
  have hd_t : (tiltPath P g C t).rnDeriv P =ᵐ[P] fun x ↦ ENNReal.ofReal (1 + t * g x) := by
    rw [tiltPath_of_lt htC]
    exact Measure.rnDeriv_withDensity₀ P (ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_const.add (hg.aemeasurable.const_mul t)))
  have hd_0 : (tiltPath P g C 0).rnDeriv P =ᵐ[P] 1 := by rw [tiltPath_zero]; exact P.rnDeriv_self
  have hrem_asm : AEStronglyMeasurable (fun x ↦ √((tiltPath P g C t).rnDeriv P x).toReal -
      √((tiltPath P g C 0).rnDeriv P x).toReal -
      t / 2 * g x * √((tiltPath P g C 0).rnDeriv P x).toReal) P := by
    have h1 := (Measure.measurable_rnDeriv (tiltPath P g C t) P).ennreal_toReal.sqrt
    have h2 := (Measure.measurable_rnDeriv (tiltPath P g C 0) P).ennreal_toReal.sqrt
    exact (h1.aestronglyMeasurable.sub h2.aestronglyMeasurable).sub
      ((hg.const_mul (t / 2)).mul h2.aestronglyMeasurable)
  refine (eLpNorm_le_of_ae_bound hrem_asm (C := t ^ 2 * C ^ 2 / 2) ?_).trans_eq (by simp [mul_comm])
  filter_upwards [hd_t, hd_0, hC] with x hxt hx0 hxC
  have htg : |t * g x| ≤ 1 := by
    rw [abs_mul, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left (hxC.trans (le_max_left C 1)) ht.le).trans htM.le
  have htg_div : t / 2 * g x = t * g x / 2 := by ring
  simp only [hxt, hx0, Pi.one_apply, ENNReal.toReal_one, Real.sqrt_one, mul_one,
    ENNReal.toReal_ofReal (by linarith [neg_abs_le (t * g x)] : 0 ≤ 1 + t * g x),
    Real.norm_eq_abs, htg_div]
  exact (Real.abs_sqrt_one_add_sub_one_sub_div_two_le (t * g x)).trans
    (by rw [mul_pow]; nlinarith [sq_le_sq.mpr (hxC.trans (le_abs_self C)), sq_nonneg t])

/-- A bounded `P`-almost-everywhere measurable function `g` on a finite measure space is the path
score of `tiltPath P g C` relative to `P` (van der Vaart, Example 25.16). Zero mean and unit total
mass are needed only to make the tilted measures probability measures
(`isProbabilityMeasure_tiltPath`). -/
theorem hasPathScore_tiltPath {P : Measure X} [IsFiniteMeasure P] {g : X → ℝ}
    (hg : AEStronglyMeasurable g P) {C : ℝ} (hC : ∀ᵐ x ∂P, |g x| ≤ C) :
    HasPathScore P (tiltPath P g C) g := by
  -- Step 1: Establish the `O(t)` majorant `t * C² / 2 · P(univ)^(1/2) → 0` as `t → 0⁺`.
  refine ⟨tiltPath_absolutelyContinuous P g C, inferInstance, ?_⟩
  have hP_ne : P univ ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top P univ)
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t * C ^ 2 / 2) * P univ ^ (2 : ℝ≥0∞).toReal⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t * C ^ 2 / 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa [Function.comp_def] using ((ENNReal.continuous_ofReal.comp
        (by fun_prop : Continuous fun t ↦ t * C ^ 2 / 2)).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hP_ne)
  -- Step 2: Within the cutoff `t * max C 1 < 1`, apply the quadratic Taylor remainder bound
  -- `eLpNorm_tiltPath_remainder_le` and cancel one factor of `t`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, t * max C 1 < 1 :=
    (((by fun_prop : Continuous fun t : ℝ ↦ t * max C 1).tendsto 0).mono_left
      nhdsWithin_le_nhds).eventually (gt_mem_nhds (by simp))
  filter_upwards [self_mem_nhdsWithin, hev] with t (ht : 0 < t) htM
  refine (mul_le_mul_right (eLpNorm_tiltPath_remainder_le hg hC ht htM) _).trans_eq ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  exact congrArg (· * _) (congrArg ENNReal.ofReal (by have := ht.ne'; field_simp))

private theorem tendsto_eLpNorm_logistic_slope (P : Measure X) {g₀ : X → ℝ}
    (hg₀_meas : Measurable g₀) (hg₀_mem : MemLp g₀ 2 P) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦
      t⁻¹ * (√(2 * Real.sigmoid (2 * (t * g₀ x))) - 1) - 1 / 2 * g₀ x) 2 P) (𝓝[>] 0) (𝓝 0) := by
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (m := P) (l := 𝓝[>] (0 : ℝ)) (q := 2)
    (f := fun t x ↦ t⁻¹ * (√(2 * Real.sigmoid (2 * (t * g₀ x))) - 1))
    (g := fun x ↦ 1 / 2 * g₀ x) (bound := g₀) (C := 3 / 2)
    ENNReal.ofNat_ne_top (Eventually.of_forall fun t ↦ by fun_prop) hg₀_mem ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine Eventually.of_forall fun x ↦ ?_
    have hle : |t⁻¹ * (√(2 * Real.sigmoid (2 * (t * g₀ x))) - 1) - 1 / 2 * g₀ x| ≤
        3 / 2 * |g₀ x| := by
      calc |t⁻¹ * (√(2 * Real.sigmoid (2 * (t * g₀ x))) - 1) - 1 / 2 * g₀ x|
          ≤ |t⁻¹ * (√(2 * Real.sigmoid (2 * (t * g₀ x))) - 1)| + |1 / 2 * g₀ x| := abs_sub _ _
        _ ≤ t⁻¹ * |t * g₀ x| + 1 / 2 * |g₀ x| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le), abs_mul,
              abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            exact add_le_add (mul_le_mul_of_nonneg_left
              (Real.abs_sqrt_two_mul_sigmoid_two_mul_sub_one_le _) (inv_nonneg.mpr ht.le)) le_rfl
        _ = 3 / 2 * |g₀ x| := by rw [abs_mul, abs_of_pos ht]; have := ht.ne'; field_simp; ring
    have h32 : ((3 / 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (3 / 2) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]; congr 1
    rw [Real.eNorm_eq_ofReal_abs, Real.eNorm_eq_ofReal_abs, h32, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hle
  · refine Eventually.of_forall fun x ↦ ?_
    have hd : HasDerivAt (fun t : ℝ ↦ √(2 * Real.sigmoid (2 * (t * g₀ x)))) (1 / 2 * g₀ x) 0 := by
      have h1 := ((Real.hasDerivAt_two_mul_sigmoid_two_mul (0 * g₀ x)).sqrt (by norm_num)).comp
        (0 : ℝ) ((hasDerivAt_id 0).mul_const (g₀ x))
      exact h1.congr_deriv (by norm_num)
    simpa [smul_eq_mul] using hd.tendsto_slope_zero_right

private theorem integrable_two_mul_sigmoid (P : Measure X) [IsFiniteMeasure P] {g₀ : X → ℝ}
    (hg₀_meas : Measurable g₀) (t : ℝ) :
    Integrable (fun x ↦ 2 * Real.sigmoid (2 * (t * g₀ x))) P :=
  (memLp_top_of_bound (by fun_prop) 2 (Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos zero_lt_two (Real.sigmoid_pos _))]
    linarith [Real.sigmoid_le_one (2 * (t * g₀ x))])).integrable le_top

private theorem logisticPartition_pos (P : Measure X) [IsProbabilityMeasure P] {g₀ : X → ℝ}
    (hg₀_meas : Measurable g₀) (t : ℝ) : 0 < ∫ x, 2 * Real.sigmoid (2 * (t * g₀ x)) ∂P := by
  rw [integral_pos_iff_support_of_nonneg (fun _ ↦ mul_nonneg zero_le_two (Real.sigmoid_pos _).le)
    (integrable_two_mul_sigmoid P hg₀_meas t)]
  have hsupp : Function.support (fun x ↦ 2 * Real.sigmoid (2 * (t * g₀ x))) = univ :=
    eq_univ_of_forall fun _ ↦ (mul_pos zero_lt_two (Real.sigmoid_pos _)).ne'
  simp [hsupp]

private theorem hasDerivAt_logisticPartition {P : Measure X} [IsProbabilityMeasure P] {g₀ : X → ℝ}
    (hg₀_meas : Measurable g₀) (hg₀_int : Integrable g₀ P) (hg₀_mean : ∫ x, g₀ x ∂P = 0) :
    HasDerivAt (fun t ↦ ∫ x, 2 * Real.sigmoid (2 * (t * g₀ x)) ∂P) 0 0 := by
  have hk_int0 : Integrable (fun x ↦ 2 * Real.sigmoid (2 * (0 * g₀ x))) P := by norm_num
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x ↦ 2 * Real.sigmoid (2 * (t * g₀ x)))
    (F' := fun t x ↦ 4 * Real.sigmoid (2 * (t * g₀ x)) * (1 - Real.sigmoid (2 * (t * g₀ x))) * g₀ x)
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds 0 zero_lt_one)
    (Eventually.of_forall fun t ↦ by fun_prop) hk_int0
    (by simp only [zero_mul]; norm_num; exact hg₀_int.aestronglyMeasurable)
    (Eventually.of_forall fun x t _ ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (Real.abs_four_mul_sigmoid_mul_one_sub_sigmoid_le_one (2 * (t * g₀ x))))
    hg₀_int.norm
    (Eventually.of_forall fun x t _ ↦ by
      simpa [Function.comp_def] using (Real.hasDerivAt_two_mul_sigmoid_two_mul (t * g₀ x)).comp t
        ((hasDerivAt_id t).mul_const (g₀ x)))).2
  convert hd using 1
  simp only [zero_mul]; norm_num
  exact hg₀_mean.symm

private theorem tendsto_eLpNorm_logistic_norm_term (P : Measure X) [IsProbabilityMeasure P]
    {g₀ : X → ℝ} (hg₀_meas : Measurable g₀) {Z : ℝ → ℝ} (hZ0 : Z 0 = 1)
    (hZ_sqrt_deriv : HasDerivAt (fun t ↦ √((Z t)⁻¹)) 0 0) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦
      t⁻¹ * (√((Z t)⁻¹) - 1) * √(2 * Real.sigmoid (2 * (t * g₀ x)))) 2 P) (𝓝[>] 0) (𝓝 0) := by
  have hslope : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (|t⁻¹ * (√((Z t)⁻¹) - 1)| * √2))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ ↦ t⁻¹ * (√((Z t)⁻¹) - 1)) (𝓝[>] 0) (𝓝 0) := by
      simpa [hZ0, smul_eq_mul] using hZ_sqrt_deriv.tendsto_slope_zero_right
    have h2 : Tendsto (fun t : ℝ ↦ |t⁻¹ * (√((Z t)⁻¹) - 1)| * √2) (𝓝[>] 0) (𝓝 0) := by
      simpa using h1.abs.mul_const √2
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hslope
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun t ↦ ?_)
  refine (eLpNorm_le_of_ae_bound (by fun_prop) (C := |t⁻¹ * (√((Z t)⁻¹) - 1)| * √2)
    (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by linarith [Real.sigmoid_le_one (2 * (t * g₀ x))])) (abs_nonneg _)

/-- **Every element of `L²₀(P)` is a path score** (van der Vaart, Example 25.16). For any
square-integrable mean-zero function `g` on a probability space `(X, P)`, there exists a path `Q`
of probability measures through `Q 0 = P`, each dominated by `P`, with `HasPathScore P Q g`. -/
theorem exists_hasPathScore_of_integral_eq_zero (P : Measure X) [IsProbabilityMeasure P]
    {g : X → ℝ} (hg : MemLp g 2 P) (hmean : ∫ x, g x ∂P = 0) :
    ∃ Q : ℝ → Measure X, (∀ t, IsProbabilityMeasure (Q t)) ∧ Q 0 = P ∧
      (∀ t, Q t ≪ P) ∧ HasPathScore P Q g := by
  -- Step 1: Replace `g` by a measurable representative `g₀` and define the normalized logistic tilt
  -- `Q t = P.weighted (w t)` with `w t x = 2 σ(2 t g₀ x)` and total mass `Z(t) = ∫ 2 σ(2 t g₀) dP`.
  set g₀ := hg.aestronglyMeasurable.aemeasurable.mk g
  have hg₀_meas : Measurable g₀ := hg.aestronglyMeasurable.aemeasurable.measurable_mk
  have hg₀_ae : g =ᵐ[P] g₀ := hg.aemeasurable.ae_eq_mk
  have hg₀_mem : MemLp g₀ 2 P := (memLp_congr_ae hg₀_ae).mp hg
  set Z : ℝ → ℝ := fun t ↦ ∫ x, 2 * Real.sigmoid (2 * (t * g₀ x)) ∂P
  have hZ0 : Z 0 = 1 := by simp [Z]
  have hZ_sqrt_deriv : HasDerivAt (fun t ↦ √((Z t)⁻¹)) 0 0 := by
    have hd : HasDerivAt Z 0 0 := hasDerivAt_logisticPartition hg₀_meas
      (hg₀_mem.integrable one_le_two) ((integral_congr_ae hg₀_ae.symm).trans hmean)
    simpa [hZ0] using (hd.inv (by rw [hZ0]; exact one_ne_zero)).sqrt
      (inv_ne_zero (by rw [hZ0]; exact one_ne_zero))
  set w : ℝ → X → ℝ≥0 := fun t x ↦
    ⟨2 * Real.sigmoid (2 * (t * g₀ x)), mul_nonneg zero_le_two (Real.sigmoid_nonneg _)⟩
  have hw_meas (t : ℝ) : Measurable (w t) :=
    (by fun_prop : Measurable fun x ↦ 2 * Real.sigmoid (2 * (t * g₀ x))).subtype_mk
  have hw_coe (t : ℝ) (x : X) :
      (w t x : ℝ≥0∞) = ENNReal.ofReal (2 * Real.sigmoid (2 * (t * g₀ x))) :=
    (ENNReal.ofReal_eq_coe_nnreal (mul_nonneg zero_le_two (Real.sigmoid_nonneg _))).symm
  have hw_lintegral (t : ℝ) : ∫⁻ x, (w t x : ℝ≥0∞) ∂P = ENNReal.ofReal (Z t) := by
    simp_rw [hw_coe]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_two_mul_sigmoid P hg₀_meas t)
      (Eventually.of_forall fun _ ↦ mul_nonneg zero_le_two (Real.sigmoid_nonneg _))).symm
  set Q : ℝ → Measure X := fun t ↦ P.weighted (w t)
  have hQ0 : Q 0 = P := by
    have hw0 : w 0 = 1 := funext fun x ↦ Subtype.ext (by simp [w])
    simp only [Q, hw0, Measure.weighted_one]
  have hQ_ac (t : ℝ) : Q t ≪ P := Measure.weighted_absolutelyContinuous
  have hQ_prob (t : ℝ) : IsProbabilityMeasure (Q t) :=
    Measure.isProbabilityMeasure_weighted_iff.mpr <| by
      rw [hw_lintegral]
      exact ⟨ENNReal.ofReal_pos.mpr (logisticPartition_pos P hg₀_meas t), ENNReal.ofReal_ne_top⟩
  refine ⟨Q, hQ_prob, hQ0, hQ_ac, ?_⟩
  suffices hscore₀ : HasPathScore P Q g₀ from hscore₀.congr_ae (hQ0 ▸ hg₀_ae.symm)
  -- Step 2: Split the scaled `L²(P)` remainder into the normalization term `(√(Z(t)⁻¹) - 1)/t`
  -- and the logistic slope `(√(2 σ(2 t g₀)) - 1)/t - g₀ / 2`, then apply Minkowski's inequality.
  have hsum := (tendsto_eLpNorm_logistic_norm_term P hg₀_meas hZ0 hZ_sqrt_deriv).add
    (tendsto_eLpNorm_logistic_slope P hg₀_meas hg₀_mem)
  rw [add_zero] at hsum
  refine ⟨hQ_ac, inferInstance, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hd_t : (Q t).rnDeriv P =ᵐ[P] fun x ↦ (ENNReal.ofReal (Z t))⁻¹ * (w t x : ℝ≥0∞) := by
    simpa only [Q, hw_lintegral] using P.rnDeriv_weighted (hw_meas t).aemeasurable
  have hd_0 : (Q 0).rnDeriv P =ᵐ[P] 1 := by rw [hQ0]; exact P.rnDeriv_self
  have hae : (t⁻¹ • fun x ↦ √((Q t).rnDeriv P x).toReal - √((Q 0).rnDeriv P x).toReal -
        t / 2 * g₀ x * √((Q 0).rnDeriv P x).toReal) =ᵐ[P]
      (fun x ↦ t⁻¹ * (√((Z t)⁻¹) - 1) * √(2 * Real.sigmoid (2 * (t * g₀ x)))) +
      (fun x ↦ t⁻¹ * (√(2 * Real.sigmoid (2 * (t * g₀ x))) - 1) - 1 / 2 * g₀ x) := by
    filter_upwards [hd_t, hd_0] with x hxt hx0
    have hZ_pos : 0 < Z t := logisticPartition_pos P hg₀_meas t
    have hZ_nonneg : 0 ≤ (Z t)⁻¹ := inv_nonneg.mpr hZ_pos.le
    have hsig_nonneg : 0 ≤ 2 * Real.sigmoid (2 * (t * g₀ x)) :=
      mul_nonneg zero_le_two (Real.sigmoid_nonneg _)
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, hxt, hx0, Pi.one_apply,
      ENNReal.toReal_one, Real.sqrt_one, mul_one, hw_coe, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hZ_pos.le, ENNReal.toReal_ofReal hsig_nonneg,
      Real.sqrt_mul hZ_nonneg]
    have := ht.ne'; field_simp; ring
  rw [← Real.eNorm_eq_ofReal (inv_nonneg.mpr ht.le), ← eLpNorm_const_smul, eLpNorm_congr_ae hae]
  exact eLpNorm_add_le one_le_two

private theorem eLpNorm_prod_remainder_le {ν₁ : Measure X} [SigmaFinite ν₁] {ν₂ : Measure Y}
    [SigmaFinite ν₂] {Q₁ : ℝ → Measure X} {Q₂ : ℝ → Measure Y} [∀ t, IsFiniteMeasure (Q₁ t)]
    [∀ t, IsFiniteMeasure (Q₂ t)] {g₁₀ : X → ℝ} {g₂₀ : Y → ℝ}
    (hg₁₀_meas : Measurable g₁₀) (hg₂₀_meas : Measurable g₂₀) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t⁻¹ * eLpNorm (fun z : X × Y ↦
        √(((Q₁ t).prod (Q₂ t)).rnDeriv (ν₁.prod ν₂) z).toReal -
          √(((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal - t / 2 * (g₁₀ z.1 + g₂₀ z.2) *
            √(((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal) 2 (ν₁.prod ν₂) ≤
      ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦ √((Q₁ t).rnDeriv ν₁ x).toReal -
          √((Q₁ 0).rnDeriv ν₁ x).toReal - t / 2 * g₁₀ x * √((Q₁ 0).rnDeriv ν₁ x).toReal) 2 ν₁ *
          eLpNorm (fun y ↦ √((Q₂ t).rnDeriv ν₂ y).toReal) 2 ν₂ +
        ENNReal.ofReal (1 / 2) * eLpNorm (fun x ↦ g₁₀ x * √((Q₁ 0).rnDeriv ν₁ x).toReal) 2 ν₁ *
          eLpNorm (fun y ↦ √((Q₂ t).rnDeriv ν₂ y).toReal - √((Q₂ 0).rnDeriv ν₂ y).toReal) 2 ν₂ +
        eLpNorm (fun x ↦ √((Q₁ 0).rnDeriv ν₁ x).toReal) 2 ν₁ *
          (ENNReal.ofReal t⁻¹ * eLpNorm (fun y ↦ √((Q₂ t).rnDeriv ν₂ y).toReal -
            √((Q₂ 0).rnDeriv ν₂ y).toReal -
            t / 2 * g₂₀ y * √((Q₂ 0).rnDeriv ν₂ y).toReal) 2 ν₂) := by
  -- Step 1: Factor the product Radon–Nikodym derivatives via `Measure.rnDeriv_prod` and decompose
  -- the product remainder almost everywhere into three pure-tensor summands.
  set s₁ : ℝ → X → ℝ := fun u x ↦ √(((Q₁ u).rnDeriv ν₁ x).toReal)
  set s₂ : ℝ → Y → ℝ := fun u y ↦ √(((Q₂ u).rnDeriv ν₂ y).toReal)
  set r₁ : X → ℝ := fun x ↦ s₁ t x - s₁ 0 x - t / 2 * g₁₀ x * s₁ 0 x
  set r₂ : Y → ℝ := fun y ↦ s₂ t y - s₂ 0 y - t / 2 * g₂₀ y * s₂ 0 y
  have hs₁_meas (u : ℝ) : Measurable (s₁ u) := (Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt
  have hs₂_meas (u : ℝ) : Measurable (s₂ u) := (Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt
  have hae : (fun z : X × Y ↦ √(((Q₁ t).prod (Q₂ t)).rnDeriv (ν₁.prod ν₂) z).toReal -
        √(((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal - t / 2 * (g₁₀ z.1 + g₂₀ z.2) *
          √(((Q₁ 0).prod (Q₂ 0)).rnDeriv (ν₁.prod ν₂) z).toReal) =ᵐ[ν₁.prod ν₂]
      ((fun z : X × Y ↦ r₁ z.1 • s₂ t z.2) +
        (fun z : X × Y ↦ ((t / 2) • fun x ↦ g₁₀ x * s₁ 0 x) z.1 • (s₂ t z.2 - s₂ 0 z.2))) +
      (fun z : X × Y ↦ s₁ 0 z.1 • r₂ z.2) := by
    filter_upwards [Measure.rnDeriv_prod (Q₁ t) ν₁ (Q₂ t) ν₂,
      Measure.rnDeriv_prod (Q₁ 0) ν₁ (Q₂ 0) ν₂] with z hzt hz0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzt, hz0, ENNReal.toReal_mul,
      Real.sqrt_mul ENNReal.toReal_nonneg, s₁, s₂, r₁, r₂]; ring
  -- Step 2: Apply Minkowski's inequality and `eLpNorm_prod_smul` on each tensor summand, then
  -- distribute `t⁻¹`.
  rw [eLpNorm_congr_ae hae]
  have htri : eLpNorm (((fun z : X × Y ↦ r₁ z.1 • s₂ t z.2) +
        (fun z : X × Y ↦ ((t / 2) • fun x ↦ g₁₀ x * s₁ 0 x) z.1 • (s₂ t z.2 - s₂ 0 z.2))) +
        (fun z : X × Y ↦ s₁ 0 z.1 • r₂ z.2)) 2 (ν₁.prod ν₂) ≤
      eLpNorm r₁ 2 ν₁ * eLpNorm (s₂ t) 2 ν₂ +
        eLpNorm ((t / 2) • fun x ↦ g₁₀ x * s₁ 0 x) 2 ν₁ * eLpNorm (fun y ↦ s₂ t y - s₂ 0 y) 2 ν₂ +
        eLpNorm (s₁ 0) 2 ν₁ * eLpNorm r₂ 2 ν₂ := by
    refine (eLpNorm_add_le one_le_two).trans ?_
    gcongr
    · exact (eLpNorm_add_le one_le_two).trans_eq (by
        rw [TauCeti.eLpNorm_prod_smul (f := r₁) (g := s₂ t)
            (by have := hs₁_meas t; have := hs₁_meas 0; fun_prop) (hs₂_meas t).aestronglyMeasurable,
          TauCeti.eLpNorm_prod_smul (f := (t / 2) • fun x ↦ g₁₀ x * s₁ 0 x)
            (g := fun y ↦ s₂ t y - s₂ 0 y) (by have := hs₁_meas 0; fun_prop)
            (by have := hs₂_meas t; have := hs₂_meas 0; fun_prop)])
    · rw [TauCeti.eLpNorm_prod_smul (f := s₁ 0) (g := r₂) (hs₁_meas 0).aestronglyMeasurable
        (by have := hs₂_meas t; have := hs₂_meas 0; fun_prop)]
  refine (mul_le_mul_right htri _).trans_eq ?_
  rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal (by positivity)]
  simp only [left_distrib, ← mul_assoc]
  congr 1
  · congr 1; rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
    exact congrArg (fun a ↦ a * _ * _) (congrArg ENNReal.ofReal (by have := ht.ne'; field_simp))
  · ac_rfl

private theorem hasPathScore_prod_of_measurable {ν₁ : Measure X} [SigmaFinite ν₁]
    {ν₂ : Measure Y} [SigmaFinite ν₂] {Q₁ : ℝ → Measure X} {Q₂ : ℝ → Measure Y}
    [∀ t, IsFiniteMeasure (Q₁ t)] [∀ t, IsFiniteMeasure (Q₂ t)] {g₁₀ : X → ℝ} {g₂₀ : Y → ℝ}
    (hg₁₀_meas : Measurable g₁₀) (hg₂₀_meas : Measurable g₂₀)
    (h₁₀ : HasPathScore ν₁ Q₁ g₁₀) (h₂₀ : HasPathScore ν₂ Q₂ g₂₀) :
    HasPathScore (ν₁.prod ν₂) (fun t ↦ (Q₁ t).prod (Q₂ t)) (fun z ↦ g₁₀ z.1 + g₂₀ z.2) := by
  -- Step 1: Show each of the three product majorant terms from `eLpNorm_prod_remainder_le` tends to
  -- `0` as `t → 0⁺`, using `L²` right-continuity `tendsto_eLpNorm_sqrt_toReal_rnDeriv_sub`.
  refine ⟨fun t ↦ (h₁₀.1 t).prod (h₂₀.1 t), inferInstance, ?_⟩
  have hs₁₀_ne : eLpNorm (fun x ↦ √(((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ ≠ ∞ :=
    (Measure.memLp_two_sqrt_toReal_rnDeriv (Q₁ 0) ν₁).eLpNorm_ne_top
  have hs₂₀_ne : eLpNorm (fun y ↦ √(((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂ ≠ ∞ :=
    (Measure.memLp_two_sqrt_toReal_rnDeriv (Q₂ 0) ν₂).eLpNorm_ne_top
  have hlim₁ : Tendsto (fun t : ℝ ↦
      ENNReal.ofReal t⁻¹ * eLpNorm (fun x ↦ √(((Q₁ t).rnDeriv ν₁ x).toReal) -
        √(((Q₁ 0).rnDeriv ν₁ x).toReal) - t / 2 * g₁₀ x * √(((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ *
      (eLpNorm (fun y ↦ √(((Q₂ t).rnDeriv ν₂ y).toReal) - √(((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂ +
        eLpNorm (fun y ↦ √(((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul h₁₀.tendsto (Or.inr (by simp [hs₂₀_ne]))
      (h₂₀.tendsto_eLpNorm_sqrt_toReal_rnDeriv_sub.add tendsto_const_nhds)
      (Or.inr ENNReal.zero_ne_top)
  have hlim₂ : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (1 / 2) *
      eLpNorm (fun x ↦ g₁₀ x * √(((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ *
      eLpNorm (fun y ↦ √(((Q₂ t).rnDeriv ν₂ y).toReal) - √(((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂)
      (𝓝[>] 0) (𝓝 0) := by
    have hfin : ENNReal.ofReal (1 / 2) *
        eLpNorm (fun x ↦ g₁₀ x * √(((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₁₀.memLp_mul_sqrt_toReal_rnDeriv.eLpNorm_ne_top
    simpa using
      ENNReal.Tendsto.const_mul h₂₀.tendsto_eLpNorm_sqrt_toReal_rnDeriv_sub (Or.inr hfin)
  have hlim₃ : Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦ √(((Q₁ 0).rnDeriv ν₁ x).toReal)) 2 ν₁ *
      (ENNReal.ofReal t⁻¹ * eLpNorm (fun y ↦ √(((Q₂ t).rnDeriv ν₂ y).toReal) -
        √(((Q₂ 0).rnDeriv ν₂ y).toReal) - t / 2 * g₂₀ y * √(((Q₂ 0).rnDeriv ν₂ y).toReal)) 2 ν₂))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h₂₀.tendsto (Or.inr hs₁₀_ne)
  -- Step 2: Squeeze the product remainder norm beneath the sum of the three majorants.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using (hlim₁.add hlim₂).add hlim₃)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  refine (eLpNorm_prod_remainder_le hg₁₀_meas hg₂₀_meas ht).trans ?_
  gcongr
  have hsplit : (fun y ↦ √(((Q₂ t).rnDeriv ν₂ y).toReal)) =
      (fun y ↦ √(((Q₂ t).rnDeriv ν₂ y).toReal) - √(((Q₂ 0).rnDeriv ν₂ y).toReal)) +
      (fun y ↦ √(((Q₂ 0).rnDeriv ν₂ y).toReal)) := by ext y; simp
  exact hsplit ▸ eLpNorm_add_le one_le_two

/-- **Product paths.** The product of two paths of finite measures with scores `g₁` and `g₂`
relative to σ-finite reference measures `ν₁` and `ν₂` has path score `(x, y) ↦ g₁ x + g₂ y`
relative to `ν₁ ⊗ ν₂`. -/
theorem HasPathScore.prod {ν₁ : Measure X} [SigmaFinite ν₁] {ν₂ : Measure Y} [SigmaFinite ν₂]
    {Q₁ : ℝ → Measure X} {Q₂ : ℝ → Measure Y} [∀ t, IsFiniteMeasure (Q₁ t)]
    [∀ t, IsFiniteMeasure (Q₂ t)] {g₁ : X → ℝ} {g₂ : Y → ℝ}
    (h₁ : HasPathScore ν₁ Q₁ g₁) (h₂ : HasPathScore ν₂ Q₂ g₂) :
    HasPathScore (ν₁.prod ν₂) (fun t ↦ (Q₁ t).prod (Q₂ t)) (fun z ↦ g₁ z.1 + g₂ z.2) := by
  -- Replace `g₁` and `g₂` by measurable representatives `g₁₀` and `g₂₀` via `congr_ae` and apply
  -- `hasPathScore_prod_of_measurable`.
  have hg₁ : AEStronglyMeasurable g₁ (Q₁ 0) := h₁.memLp.aestronglyMeasurable
  have hg₂ : AEStronglyMeasurable g₂ (Q₂ 0) := h₂.memLp.aestronglyMeasurable
  refine (hasPathScore_prod_of_measurable hg₁.aemeasurable.measurable_mk
    hg₂.aemeasurable.measurable_mk (h₁.congr_ae hg₁.aemeasurable.ae_eq_mk)
    (h₂.congr_ae hg₂.aemeasurable.ae_eq_mk)).congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hg₁.aemeasurable.ae_eq_mk.symm,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hg₂.aemeasurable.ae_eq_mk.symm] with z hz₁ hz₂
  exact congr_arg₂ (· + ·) hz₁ hz₂

end Constructions

/-! ### Location models with absolutely continuous density -/

section Location

private theorem eLpNorm_location_remainder_le {s'₀ : ℝ → ℝ} (hs'₀_meas : Measurable s'₀) (θ t : ℝ) :
    eLpNorm (fun x ↦ ∫ u in Ioc (0 : ℝ) 1, (s'₀ (x - θ) - s'₀ (x - θ - t * u))) 2 volume ≤
      ∫⁻ u in Ioc (0 : ℝ) 1, eLpNorm (fun x ↦ s'₀ (x - t * u) - s'₀ x) 2 volume := by
  have hF : Measurable (Function.uncurry fun x u : ℝ ↦ s'₀ (x - θ) - s'₀ (x - θ - t * u)) := by
    fun_prop
  refine (TauCeti.eLpNorm_integral_le_lintegral_eLpNorm_of_ne_top hF.aestronglyMeasurable
    one_le_two ENNReal.ofNat_ne_top).trans_eq (lintegral_congr fun u ↦ ?_)
  have hm : AEStronglyMeasurable (fun x ↦ s'₀ x - s'₀ (x - t * u)) volume := by fun_prop
  have htr : eLpNorm (fun x ↦ s'₀ (x - θ) - s'₀ (x - θ - t * u)) 2 volume =
      eLpNorm (fun x ↦ s'₀ x - s'₀ (x - t * u)) 2 volume := by
    simpa only [Function.comp_def, sub_right_comm] using
      eLpNorm_comp_measurePreserving hm (measurePreserving_sub_right volume θ)
  rw [htr, ← eLpNorm_neg]
  exact eLpNorm_congr_ae (Eventually.of_forall fun x ↦ by simp)

private theorem integral_halfScore_eq_sqrt_sub_sqrt {η η' s'₀ : ℝ → ℝ} (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b) (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t)
    (hs'₀_ae : (fun y ↦ η' y / (2 * √(η y))) =ᵐ[volume] s'₀) (hs'₀_mem : MemLp s'₀ 2 volume)
    (a b : ℝ) : (∫ v in a..b, s'₀ v) = √(η b) - √(η a) := by
  have hs'₀_ii : IntervalIntegrable s'₀ volume a b :=
    (hs'₀_mem.locallyIntegrable one_le_two).intervalIntegrable a b
  have hderiv_eq : deriv η =ᵐ[volume] η' :=
    ((locallyIntegrable_iff_forall_intervalIntegrable.mpr hη').ae_hasDerivAt_of_eq_integral
      hac).mono fun _ hx ↦ hx.deriv
  have hderiv_score_ae : (fun v ↦ deriv η v / (2 * √(η v))) =ᵐ[volume] s'₀ := by
    filter_upwards [hderiv_eq, hs'₀_ae] with x hx1 hx2 using by rw [hx1, hx2]
  have hac_int : AbsolutelyContinuousOnInterval η a b :=
    (hη' 0 a).absolutelyContinuousOnInterval_of_eq_integral (hη' a b) (fun y _ ↦ hac y)
  have hint_deriv : IntervalIntegrable (fun v ↦ deriv η v / (2 * √(η v))) volume a b :=
    hs'₀_ii.congr_ae (ae_restrict_of_ae hderiv_score_ae.symm)
  rw [intervalIntegral.integral_congr_ae (hderiv_score_ae.symm.mono fun _ hv _ ↦ hv)]
  exact (hac_int.sqrt_sub_sqrt_eq_intervalIntegral (fun y _ ↦ hη y) hint_deriv).symm

private theorem ae_location_remainder_eq {η η' s'₀ : ℝ → ℝ} (hη : ∀ x, 0 ≤ η x)
    (hη_meas : Measurable η) (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t)
    (hs'₀_ae : (fun y ↦ η' y / (2 * √(η y))) =ᵐ[volume] s'₀)
    (hs'₀_mem : MemLp s'₀ 2 volume) (θ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    (t⁻¹ • fun x ↦
        √(((volume.withDensity fun y ↦ ENNReal.ofReal (η (y - (θ + t)))).rnDeriv volume x).toReal) -
        √(((volume.withDensity fun y ↦ ENNReal.ofReal (η (y - θ))).rnDeriv volume x).toReal) -
        t / 2 * (-(η' (x - θ) / η (x - θ))) *
          √(((volume.withDensity fun y ↦ ENNReal.ofReal (η (y - θ))).rnDeriv volume x).toReal))
      =ᵐ[volume] fun x ↦ ∫ u in Ioc (0 : ℝ) 1, (s'₀ (x - θ) - s'₀ (x - θ - t * u)) := by
  -- Step 1: Identify the shifted Radon–Nikodym derivatives almost everywhere with `η(· - c)`.
  have hd (c : ℝ) : (volume.withDensity fun y ↦ ENNReal.ofReal (η (y - c))).rnDeriv volume
      =ᵐ[volume] fun x ↦ ENNReal.ofReal (η (x - c)) :=
    Measure.rnDeriv_withDensity volume (by fun_prop)
  have hs'₀_ii (a b : ℝ) : IntervalIntegrable s'₀ volume a b :=
    (hs'₀_mem.locallyIntegrable one_le_two).intervalIntegrable a b
  filter_upwards [hd (θ + t), hd θ,
    (measurePreserving_sub_right volume θ).quasiMeasurePreserving.ae_eq_comp hs'₀_ae]
    with x hxt hx0 hxθ
  simp only [Pi.smul_apply, smul_eq_mul, hxt, hx0, ENNReal.toReal_ofReal (hη _)]
  -- Step 2: Rewrite the linear score term via `s'₀` and the square-root density difference via the
  -- fundamental theorem of calculus (`integral_halfScore_eq_sqrt_sub_sqrt`), then rescale `[0, 1]`.
  have hscore_eq : -(η' (x - θ) / η (x - θ)) * √(η (x - θ)) = -2 * s'₀ (x - θ) := by
    dsimp only [Function.comp_apply] at hxθ
    rw [← hxθ]
    rcases eq_or_ne (η (x - θ)) 0 with h0 | h0
    · simp [h0]
    · have hsr_ne : √(η (x - θ)) ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne (hη _) h0.symm)).ne'
      calc -(η' (x - θ) / η (x - θ)) * √(η (x - θ))
          = -(η' (x - θ) / (√(η (x - θ)) ^ 2)) * √(η (x - θ)) := by
              rw [Real.sq_sqrt (hη _)]
        _ = -2 * (η' (x - θ) / (2 * √(η (x - θ)))) := by field_simp
  have hsub_mul := intervalIntegral.integral_comp_sub_mul s'₀ ht0.ne' (x - θ) (a := 0) (b := 1)
  simp only [mul_zero, sub_zero, mul_one, smul_eq_mul] at hsub_mul
  rw [sub_sub x θ t] at hsub_mul
  have hint_eq := integral_halfScore_eq_sqrt_sub_sqrt hη hη' hac hs'₀_ae hs'₀_mem
    (x - (θ + t)) (x - θ)
  have hint1 : IntervalIntegrable (fun u ↦ s'₀ ((x - θ) - t * u)) volume 0 1 := by
    have h1 : IntervalIntegrable (fun v ↦ s'₀ ((x - θ) - v)) volume 0 t := by
      simpa using (hs'₀_ii (x - θ) (x - θ - t)).comp_sub_left (x - θ)
    simpa [ht0.ne'] using h1.comp_mul_left (c := t)
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub intervalIntegrable_const hint1, intervalIntegral.integral_const,
    sub_zero, one_smul, hsub_mul, hint_eq, mul_assoc (t / 2), hscore_eq]
  have := ht0.ne'; field_simp; ring

private theorem tendsto_setLIntegral_Ioc_eLpNorm_sub {s'₀ : ℝ → ℝ}
    (hs'₀_mem : MemLp s'₀ 2 volume) :
    Tendsto (fun t : ℝ ↦
      ∫⁻ u in Ioc (0 : ℝ) 1, eLpNorm (fun x ↦ s'₀ (x - t * u) - s'₀ x) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
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
  calc ∫⁻ u in Ioc (0 : ℝ) 1, eLpNorm (fun x ↦ s'₀ (x - t * u) - s'₀ x) 2 volume
      ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, ε :=
        setLIntegral_mono' measurableSet_Ioc fun u ⟨hu0, hu1⟩ ↦ hball <| by
          rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos ht0 hu0)]
          nlinarith
    _ = ε := by simp [Real.volume_Ioc]

/-- **Path score of a location model** (Bickel–Klaassen–Ritov–Wellner, §2.1 Example 2 and Appendix
A.5, Corollary 1, parts C–D, after Hájek–Šidák). If `η : ℝ → ℝ` is nonnegative, absolutely
continuous with derivative `η'`, and has finite Fisher information `∫ (η' x)² / η x dx`, then the
location path `t ↦ volume.withDensity (x ↦ ENNReal.ofReal (η (x - (θ + t))))` has path score
`x ↦ -(η' (x - θ) / η (x - θ))` relative to Lebesgue measure. -/
theorem hasPathScore_location (η η' : ℝ → ℝ) (hη : ∀ x, 0 ≤ η x)
    (hη' : ∀ a b, IntervalIntegrable η' volume a b)
    (hac : ∀ x, η x = η 0 + ∫ t in (0 : ℝ)..x, η' t)
    (hfisher : Integrable fun x ↦ η' x ^ 2 / η x) (θ : ℝ) :
    HasPathScore volume (fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (η (x - (θ + t))))
      (fun x ↦ -(η' (x - θ) / η (x - θ))) := by
  -- Following the direct argument of Hájek–Šidák as cited in Bickel–Klaassen–Ritov–Wellner,
  -- Appendix A.5, Corollary 1:
  -- Step 1: Place the half-score `η' / (2 √η)` in `L²(ℝ)` from finite Fisher information and pick a
  -- measurable representative `s'₀`.
  refine ⟨fun _ ↦ withDensity_absolutelyContinuous _ _, inferInstance, ?_⟩
  have hη_meas : Measurable η :=
    ((continuous_const.add (intervalIntegral.continuous_primitive hη' 0)).congr
      fun x ↦ (hac x).symm).measurable
  have hη'_asm : AEStronglyMeasurable η' volume :=
    (locallyIntegrable_iff_forall_intervalIntegrable.mpr hη').aestronglyMeasurable
  have hs' : MemLp (fun y ↦ η' y / (2 * √(η y))) 2 volume := by
    have h_asm : AEStronglyMeasurable (fun y ↦ η' y / (2 * √(η y))) volume :=
      (hη'_asm.aemeasurable.div (by fun_prop)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq h_asm]
    refine (hfisher.const_mul (1 / 4 : ℝ)).congr (Eventually.of_forall fun x ↦ ?_)
    dsimp only; rw [div_pow, mul_pow, Real.sq_sqrt (hη x)]; ring
  set s'₀ : ℝ → ℝ := hs'.aestronglyMeasurable.aemeasurable.mk _
  have hs'₀_meas : Measurable s'₀ := hs'.aestronglyMeasurable.aemeasurable.measurable_mk
  have hs'₀_ae := hs'.aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hs'₀_mem : MemLp s'₀ 2 volume := (memLp_congr_ae hs'₀_ae).mp hs'
  -- Step 2: Combine the FTC remainder identity (`ae_location_remainder_eq`), Minkowski's integral
  -- inequality (`eLpNorm_location_remainder_le`), and `L²` continuity of translation.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_setLIntegral_Ioc_eLpNorm_sub hs'₀_mem) (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht0 : 0 < t)
  simp only [add_zero]
  rw [← Real.eNorm_eq_ofReal (inv_nonneg.mpr ht0.le), ← eLpNorm_const_smul,
    eLpNorm_congr_ae (ae_location_remainder_eq hη hη_meas hη' hac hs'₀_ae hs'₀_mem θ ht0)]
  exact eLpNorm_location_remainder_le hs'₀_meas θ t

end Location

end TauCeti
end
