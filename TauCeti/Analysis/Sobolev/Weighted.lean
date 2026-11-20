/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Weighted Lebesgue and Sobolev classes with the Bartnik weight

Let `E` be a finite-dimensional real normed space of dimension `n`. Following Bartnik, a function
`v` lies in the weighted Lebesgue space `Lᵖ_δ` when

`‖v‖_{Lᵖ_δ} = (∫ ‖v x‖ ^ p ‖x‖ ^ (-δ p - n) dx) ^ (1 / p) < ∞`,

and for `p = ∞` the norm is the essential supremum of `‖v x‖ ‖x‖ ^ (-δ)`. Both are the `Lᵖ`
seminorm of `x ↦ ‖x‖ ^ (-δ - n / p) • v x`, which is how `TauCeti.weightedLpNorm` is defined, for
an arbitrary measure on `E`. The weight is meant for the exterior `{x | R < ‖x‖}` of a ball of
positive radius, where `‖x‖` is a radius function on an asymptotically Euclidean end; the
exterior is selected by restricting the measure, as in `μ.restrict (closedBall 0 R)ᶜ`.
With this convention a function of order `‖x‖ ^ (-t)` lies in `Lᵖ_δ` for finite `p` exactly when
`δ > -t`, independently of `p` and `n`, and the `L∞` endpoint is reached at `δ = -t`.
For finite `p` the space is `Lᵖ` of the measure with density `‖x‖ ^ (-δ p - n)`, but a density
does not change essential suprema; multiplying the function by the weight treats `p = ∞` in the
same way as finite `p`.

The weighted Sobolev class `TauCeti.MemWeightedSobolev v k p δ U μ` asks that `v` be `Cᵏ` on the
set `U` and that its `j`-th derivative lie in `Lᵖ_{δ - j}` for every `j ≤ k`, with the norm
`Σ_{j ≤ k} ‖Dʲ v‖_{Lᵖ_{δ - j}}` (`TauCeti.weightedSobolevNorm`). These are the weighted classes
of continuously differentiable coefficients, such as the coefficients `g_ij - δ_ij` of a metric in
an asymptotically Euclidean chart; weak derivatives and the completion are not treated here.

## Main declarations

* `TauCeti.weightedLpNorm`, `TauCeti.MemWeightedLp`: the weighted `Lᵖ_δ` norm and membership.
* `TauCeti.MemWeightedLp.of_le_mul`, `TauCeti.MemWeightedLp.mono_weight`: domination and
  monotonicity in the weight `δ` on an exterior.
* `TauCeti.memWeightedLp_norm_rpow_compl_closedBall_iff`: `‖x‖ ^ (-t)` is in `Lᵖ_δ` of an
  exterior, for finite nonzero `p`, exactly when `-t < δ`, and
  `TauCeti.weightedLpNorm_norm_rpow_compl_closedBall` computes its norm.
* `TauCeti.memWeightedLp_const_compl_closedBall_iff`: a nonzero constant is in `Lᵖ_δ` of an
  exterior exactly when `0 < δ`.
* `TauCeti.memWeightedLp_of_isBigO`: a measurable function that is `O(‖x‖ ^ (-t))` on an exterior
  is in `Lᵖ_δ` for every `p` and `δ > -t`.
* `TauCeti.memWeightedLp_top_of_isBigO`, `TauCeti.weightedLpNorm_norm_rpow_top`: at the endpoint
  `p = ∞` the same function is in `L∞_{-t}`, and `‖x‖ ^ (-t)` has norm `1` there.
* `TauCeti.MemWeightedSobolev`, `TauCeti.weightedSobolevNorm`, and
  `TauCeti.memWeightedSobolev_of_isBigO`: a `Cᵏ` function whose derivatives of order `j ≤ k` are
  `O(‖x‖ ^ (-t - j))` on an exterior is in `W^{k,p}_δ` for every `p` and `δ > -t`.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  §1 (the weighted norms and their indexing).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §9.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, arXiv:2108.11972, equations (2.3)–(2.4).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Filter Asymptotics
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The weighted Lebesgue norm -/

/-- The Bartnik weighted `Lᵖ_δ` norm of `v` with respect to `μ`: the `Lᵖ` seminorm of
`x ↦ ‖x‖ ^ (-δ - n / p) • v x`, where `n` is the dimension of `E`. For finite `p` its `p`-th power
is `∫ ‖v x‖ ^ p ‖x‖ ^ (-δ p - n) dμ`, and for `p = ∞` it is the essential supremum of
`‖v x‖ ‖x‖ ^ (-δ)`. It is meant for `μ` concentrated outside a ball of positive radius. -/
def weightedLpNorm (v : E → F) (p : ℝ≥0∞) (δ : ℝ) (μ : Measure E) : ℝ≥0∞ :=
  eLpNorm (fun x => ‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • v x) p μ

/-- Membership in the Bartnik weighted space `Lᵖ_δ` for `μ`: the function
`x ↦ ‖x‖ ^ (-δ - n / p) • v x` is in `Lᵖ(μ)`, where `n` is the dimension of `E`. -/
def MemWeightedLp (v : E → F) (p : ℝ≥0∞) (δ : ℝ) (μ : Measure E) : Prop :=
  MemLp (fun x => ‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • v x) p μ

theorem memWeightedLp_iff {v : E → F} {p : ℝ≥0∞} {δ : ℝ} {μ : Measure E} :
    MemWeightedLp v p δ μ ↔ weightedLpNorm v p δ μ < ∞ :=
  Iff.rfl

/-- At the weight `δ = -n / p` the weight is identically `1`: `Lᵖ_δ` is plain `Lᵖ`. -/
theorem weightedLpNorm_neg_finrank_mul (v : E → F) (p : ℝ≥0∞) (μ : Measure E) :
    weightedLpNorm v p (-(Module.finrank ℝ E * p⁻¹.toReal)) μ = eLpNorm v p μ := by
  simp [weightedLpNorm]

/-- At the weight `δ = -n / p` membership in `Lᵖ_δ` is membership in `Lᵖ`. -/
theorem memWeightedLp_neg_finrank_mul_iff {v : E → F} {p : ℝ≥0∞} {μ : Measure E} :
    MemWeightedLp v p (-(Module.finrank ℝ E * p⁻¹.toReal)) μ ↔ MemLp v p μ := by
  simp [MemWeightedLp]

theorem MemWeightedLp.add {v w : E → F} {p : ℝ≥0∞} {δ : ℝ} {μ : Measure E}
    (hv : MemWeightedLp v p δ μ) (hw : MemWeightedLp w p δ μ) :
    MemWeightedLp (v + w) p δ μ := by
  unfold MemWeightedLp at hv hw ⊢
  simp only [Pi.add_apply, smul_add]
  exact MemLp.add hv hw

theorem MemWeightedLp.const_smul {v : E → F} {p : ℝ≥0∞} {δ : ℝ} {μ : Measure E}
    (hv : MemWeightedLp v p δ μ) (c : ℝ) : MemWeightedLp (c • v) p δ μ := by
  unfold MemWeightedLp at hv ⊢
  convert MemLp.const_smul hv c using 1
  funext x
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

theorem MemWeightedLp.mono_measure {v : E → F} {p : ℝ≥0∞} {δ : ℝ} {μ ν : Measure E}
    (hv : MemWeightedLp v p δ μ) (hνμ : ν ≤ μ) : MemWeightedLp v p δ ν :=
  MemLp.mono_measure hνμ hv

omit [MeasurableSpace E] in
/-- The rule `‖x‖ ^ (-δ - n / p) ‖x‖ ^ (-t) = ‖x‖ ^ (-(t + δ) - n / p)` for `x ≠ 0`. -/
private theorem weight_smul_norm_rpow {x : E} (hx : x ≠ 0) (p : ℝ≥0∞) (t δ : ℝ) :
    ‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • ‖x‖ ^ (-t) =
      ‖x‖ ^ (-(t + δ) - Module.finrank ℝ E * p⁻¹.toReal) := by
  rw [smul_eq_mul, ← Real.rpow_add (norm_pos_iff.2 hx)]
  ring_nf

section Measurable

variable [BorelSpace E]

/-- On a measure that does not charge the origin, a function in `Lᵖ_δ` is almost everywhere
strongly measurable. -/
theorem MemWeightedLp.aestronglyMeasurable {v : E → F} {p : ℝ≥0∞} {δ : ℝ} {μ : Measure E}
    (hv : MemWeightedLp v p δ μ) (h0 : ∀ᵐ x ∂μ, x ≠ 0) : AEStronglyMeasurable v μ := by
  set a := -δ - Module.finrank ℝ E * p⁻¹.toReal
  have hmeas : AEStronglyMeasurable (fun x : E => ‖x‖ ^ (-a)) μ :=
    (by fun_prop : Measurable fun x : E => ‖x‖ ^ (-a)).aestronglyMeasurable
  refine (hmeas.smul (MemLp.aestronglyMeasurable hv)).congr ?_
  filter_upwards [h0] with x hx
  simp only [Pi.smul_apply']
  rw [smul_smul, ← Real.rpow_add (norm_pos_iff.2 hx), neg_add_cancel, Real.rpow_zero, one_smul]

/-- Domination: a measurable function bounded almost everywhere by a constant multiple of a
function in `Lᵖ_δ` is in `Lᵖ_δ`. -/
theorem MemWeightedLp.of_le_mul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {v : E → F} {w : E → G} {p : ℝ≥0∞} {δ c : ℝ} {μ : Measure E}
    (hw : MemWeightedLp w p δ μ) (hv : AEStronglyMeasurable v μ)
    (hvw : ∀ᵐ x ∂μ, ‖v x‖ ≤ c * ‖w x‖) : MemWeightedLp v p δ μ := by
  set a := -δ - Module.finrank ℝ E * p⁻¹.toReal
  refine MemLp.of_le_mul (c := c) hw
    ((by fun_prop : Measurable fun x : E => ‖x‖ ^ a).aestronglyMeasurable.smul hv) ?_
  filter_upwards [hvw] with x hx
  rw [norm_smul, norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- On an exterior `{x | R < ‖x‖}` with `R > 0`, the weighted spaces decrease as the weight
grows: `Lᵖ_δ ⊆ Lᵖ_{δ'}` for `δ ≤ δ'`. -/
theorem MemWeightedLp.mono_weight {v : E → F} {p : ℝ≥0∞} {δ δ' R : ℝ} {μ : Measure E}
    (hR : 0 < R) (hδ : δ ≤ δ') (hv : MemWeightedLp v p δ (μ.restrict (closedBall 0 R)ᶜ)) :
    MemWeightedLp v p δ' (μ.restrict (closedBall 0 R)ᶜ) := by
  set n := (Module.finrank ℝ E : ℝ) * p⁻¹.toReal
  have hmem : ∀ᵐ x ∂μ.restrict (closedBall (0 : E) R)ᶜ, R < ‖x‖ := by
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with x hx
    simpa using hx
  have heq : (fun x : E => ‖x‖ ^ (-δ' - n) • v x) =ᵐ[μ.restrict (closedBall (0 : E) R)ᶜ]
      fun x => ‖x‖ ^ (δ - δ') • ‖x‖ ^ (-δ - n) • v x := by
    filter_upwards [hmem] with x hx
    rw [smul_smul, ← Real.rpow_add (hR.trans hx)]
    ring_nf
  have hmeas : AEStronglyMeasurable (fun x : E => ‖x‖ ^ (-δ' - n) • v x)
      (μ.restrict (closedBall (0 : E) R)ᶜ) :=
    ((by fun_prop : Measurable fun x : E => ‖x‖ ^ (δ - δ')).aestronglyMeasurable.smul
      (MemLp.aestronglyMeasurable hv)).congr heq.symm
  refine MemLp.of_le_mul (c := R ^ (δ - δ')) hv hmeas ?_
  filter_upwards [heq, hmem] with x hx hxR
  rw [hx, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hR hxR.le (by linarith)) (norm_nonneg _)

/-- **The `L∞` endpoint.** A measurable function that is `O(‖x‖ ^ (-t))` on the exterior
`{x | R < ‖x‖}`, `R ≥ 0`, lies in `L∞_{-t}` there; by `MemWeightedLp.mono_weight` it then lies in
`L∞_δ` for every `δ ≥ -t` when `R > 0`. -/
theorem memWeightedLp_top_of_isBigO {μ : Measure E} {v : E → F} {t R : ℝ} (hR : 0 ≤ R)
    (hv : AEStronglyMeasurable v (μ.restrict (closedBall 0 R)ᶜ))
    (hO : v =O[𝓟 (closedBall 0 R)ᶜ] fun x => ‖x‖ ^ (-t)) :
    MemWeightedLp v ∞ (-t) (μ.restrict (closedBall 0 R)ᶜ) := by
  obtain ⟨c, hc⟩ := isBigO_principal.1 hO
  refine memLp_top_of_bound
    ((by fun_prop : Measurable fun x : E => ‖x‖ ^ (- -t - Module.finrank ℝ E *
      (∞ : ℝ≥0∞)⁻¹.toReal)).aestronglyMeasurable.smul hv) c ?_
  filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with x hx
  have hx0 : 0 < ‖x‖ := hR.trans_lt (by simpa using hx)
  have hbound := hc x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)] at hbound
  simp only [ENNReal.inv_top, ENNReal.toReal_zero, mul_zero, sub_zero, neg_neg, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  calc ‖x‖ ^ t * ‖v x‖ ≤ ‖x‖ ^ t * (c * ‖x‖ ^ (-t)) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (norm_nonneg x) _)
    _ = c := by
        rw [mul_left_comm, ← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero, mul_one]

/-- The `L∞_{-t}` norm of `‖x‖ ^ (-t)` on a nonempty exterior `{x | R < ‖x‖}`, `R ≥ 0`, is `1`. -/
theorem weightedLpNorm_norm_rpow_top [Nontrivial E] {μ : Measure E} [μ.IsOpenPosMeasure]
    {t R : ℝ} (hR : 0 ≤ R) :
    weightedLpNorm (fun x : E => ‖x‖ ^ (-t)) ∞ (-t) (μ.restrict (closedBall 0 R)ᶜ) = 1 := by
  have hcongr : (fun x : E => ‖x‖ ^ (- -t - Module.finrank ℝ E * (∞ : ℝ≥0∞)⁻¹.toReal) •
      ‖x‖ ^ (-t)) =ᵐ[μ.restrict (closedBall (0 : E) R)ᶜ] fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with x hx
    have hx0 : 0 < ‖x‖ := hR.trans_lt (by simpa using hx)
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, mul_zero, sub_zero, neg_neg, smul_eq_mul]
    rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
  have hne : μ.restrict (closedBall (0 : E) R)ᶜ ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ E R
    exact (isClosed_closedBall.isOpen_compl.measure_pos μ ⟨x, by simpa using hx⟩).ne'
  rw [weightedLpNorm, eLpNorm_congr_ae hcongr, eLpNorm_const _ ENNReal.top_ne_zero hne]
  simp

end Measurable

/-! ### Powers of the norm and decay classes on an exterior -/

section Exterior

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The model tail.** For finite nonzero `p` and `R > 0`, the function `‖x‖ ^ (-t)` lies in
`Lᵖ_δ` of the exterior `{x | R < ‖x‖}` exactly when `-t < δ`. At `δ = -t` the tail integral
`∫ ‖x‖ ^ (-n)` diverges logarithmically. -/
theorem memWeightedLp_norm_rpow_compl_closedBall_iff [Nontrivial E] {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {t δ R : ℝ} (hR : 0 < R) :
    MemWeightedLp (fun x : E => ‖x‖ ^ (-t)) p δ (μ.restrict (closedBall 0 R)ᶜ) ↔ -t < δ := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hcongr : (fun x : E => ‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • ‖x‖ ^ (-t)) =ᵐ[
      μ.restrict (closedBall (0 : E) R)ᶜ]
      fun x => ‖x‖ ^ (-(t + δ) - Module.finrank ℝ E * p⁻¹.toReal) := by
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with x hx
    refine weight_smul_norm_rpow (fun h => ?_) p t δ
    simp [h, hR.le] at hx
  rw [MemWeightedLp, memLp_congr_ae hcongr, memLp_norm_rpow_compl_closedBall_iff hR hp0 hp,
    ENNReal.toReal_inv, sub_mul, mul_assoc, inv_mul_cancel₀ hp'.ne', mul_one, neg_mul]
  constructor
  · intro h
    by_contra hle
    nlinarith
  · intro h
    nlinarith

/-- **The norm of the model tail.** For finite nonzero `p`, `R > 0` and `-t < δ`,

`‖‖x‖ ^ (-t)‖_{Lᵖ_δ}^p = n |B₁| R ^ (-(t + δ) p) / ((t + δ) p)`

on the exterior `{x | R < ‖x‖}`, where `|B₁|` is the measure of the unit ball. -/
theorem weightedLpNorm_norm_rpow_compl_closedBall {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {t δ R : ℝ} (hR : 0 < R) (hδ : -t < δ) :
    weightedLpNorm (fun x : E => ‖x‖ ^ (-t)) p δ (μ.restrict (closedBall 0 R)ᶜ) =
      ENNReal.ofReal (Module.finrank ℝ E * μ.real (ball 0 1) *
        (R ^ (-((t + δ) * p.toReal)) / ((t + δ) * p.toReal))) ^ (1 / p.toReal) := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set n := (Module.finrank ℝ E : ℝ)
  set s := (-(t + δ) - n * p⁻¹.toReal) * p.toReal
  have hs : s = -((t + δ) * p.toReal) - n := by
    simp only [s, ENNReal.toReal_inv]
    field_simp
  have hns : n + s = -((t + δ) * p.toReal) := by rw [hs]; ring
  have hcongr : (fun x : E => ‖x‖ ^ (-δ - n * p⁻¹.toReal) • ‖x‖ ^ (-t)) =ᵐ[
      μ.restrict (closedBall (0 : E) R)ᶜ]
      fun x => ‖x‖ ^ (-(t + δ) - n * p⁻¹.toReal) := by
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with x hx
    refine weight_smul_norm_rpow (fun h => ?_) p t δ
    simp [h, hR.le] at hx
  have hmeas : AEStronglyMeasurable (fun x : E => ‖x‖ ^ (-(t + δ) - n * p⁻¹.toReal))
      (μ.restrict (closedBall (0 : E) R)ᶜ) :=
    (by fun_prop : Measurable fun x : E => ‖x‖ ^ (-(t + δ) - n * p⁻¹.toReal)).aestronglyMeasurable
  have hpos : 0 < (t + δ) * p.toReal := mul_pos (by linarith) hp'
  have hint : IntegrableOn (fun x : E => ‖x‖ ^ s) (closedBall 0 R)ᶜ μ := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · have hempty : (closedBall (0 : E) R)ᶜ = ∅ := by
        ext x
        simp [Subsingleton.elim x 0, hR.le]
      simp [hempty]
    · exact (integrableOn_norm_rpow_compl_closedBall_iff hR).2 (by linarith)
  have hlin : ∫⁻ x, ‖‖x‖ ^ (-(t + δ) - n * p⁻¹.toReal)‖ₑ ^ p.toReal
      ∂μ.restrict (closedBall (0 : E) R)ᶜ = ENNReal.ofReal (∫ x in (closedBall (0 : E) R)ᶜ,
        ‖x‖ ^ s ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) s)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _) hp'.le,
      ← Real.rpow_mul (norm_nonneg x)]
  rw [weightedLpNorm, eLpNorm_congr_ae hcongr,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hmeas, hlin,
    integral_norm_rpow_compl_closedBall (by linarith) hR, hns, neg_neg]

/-- A nonzero constant lies in `Lᵖ_δ` of the exterior `{x | R < ‖x‖}`, for finite nonzero `p` and
`R > 0`, exactly when `0 < δ`. In particular constants are not in `L²_{-(n - 2)/2}` for `n ≥ 2`. -/
theorem memWeightedLp_const_compl_closedBall_iff [Nontrivial E] {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {δ R : ℝ} (hR : 0 < R) {c : F} (hc : c ≠ 0) :
    MemWeightedLp (fun _ : E => c) p δ (μ.restrict (closedBall 0 R)ᶜ) ↔ 0 < δ := by
  have hmodel := memWeightedLp_norm_rpow_compl_closedBall_iff (μ := μ) hp0 hp (t := 0)
    (δ := δ) hR
  simp only [neg_zero, Real.rpow_zero] at hmodel
  rw [← hmodel]
  constructor
  · intro h
    refine h.of_le_mul (c := ‖c‖⁻¹) aestronglyMeasurable_const (Eventually.of_forall fun _ => ?_)
    rw [norm_one, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc)]
  · intro h
    refine h.of_le_mul (c := ‖c‖) aestronglyMeasurable_const (Eventually.of_forall fun _ => ?_)
    rw [norm_one, mul_one]

/-- **Decay implies weighted integrability.** A measurable function that is `O(‖x‖ ^ (-t))` on the
exterior `{x | R < ‖x‖}`, `R > 0`, lies in `Lᵖ_δ` there for every `p` and every `δ > -t`. -/
theorem memWeightedLp_of_isBigO {v : E → F} {p : ℝ≥0∞} {t δ R : ℝ} (hR : 0 < R)
    (hδ : -t < δ) (hv : AEStronglyMeasurable v (μ.restrict (closedBall 0 R)ᶜ))
    (hO : v =O[𝓟 (closedBall 0 R)ᶜ] fun x => ‖x‖ ^ (-t)) :
    MemWeightedLp v p δ (μ.restrict (closedBall 0 R)ᶜ) := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact (memWeightedLp_top_of_isBigO hR.le hv hO).mono_weight hR hδ.le
  obtain ⟨c, hc⟩ := isBigO_principal.1 hO
  have hmodel : MemWeightedLp (fun x : E => ‖x‖ ^ (-t)) p δ (μ.restrict (closedBall 0 R)ᶜ) := by
    rcases eq_or_ne p 0 with rfl | hp0
    · exact memLp_zero_iff_aestronglyMeasurable.2
        (by fun_prop : Measurable fun x : E => _).aestronglyMeasurable
    rw [memWeightedLp_iff, weightedLpNorm_norm_rpow_compl_closedBall hp0 hp hR hδ]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  refine hmodel.of_le_mul (c := c) hv ?_
  filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with x hx
  exact hc x hx

end Exterior

/-! ### The weighted Sobolev class of continuously differentiable functions -/

/-- The weighted Sobolev norm `Σ_{j ≤ k} ‖Dʲ v‖_{Lᵖ_{δ - j}}` of `v` on the set `U` with respect
to `μ`, the derivatives being taken within `U`. It is meant for `v` of class `Cᵏ` on an open
set `U`. -/
def weightedSobolevNorm (v : E → F) (k : ℕ) (p : ℝ≥0∞) (δ : ℝ) (U : Set E) (μ : Measure E) :
    ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1), weightedLpNorm (iteratedFDerivWithin ℝ j v U) p (δ - j)
    (μ.restrict U)

/-- The weighted Sobolev class `W^{k,p}_δ` of continuously differentiable functions on `U`: `v` is
`Cᵏ` on `U` and its derivative of order `j` within `U` lies in `Lᵖ_{δ - j}` of `μ` restricted to
`U`, for every `j ≤ k`. -/
def MemWeightedSobolev (v : E → F) (k : ℕ) (p : ℝ≥0∞) (δ : ℝ) (U : Set E) (μ : Measure E) :
    Prop :=
  ContDiffOn ℝ k v U ∧
    ∀ j ≤ k, MemWeightedLp (iteratedFDerivWithin ℝ j v U) p (δ - j) (μ.restrict U)

theorem memWeightedSobolev_iff {v : E → F} {k : ℕ} {p : ℝ≥0∞} {δ : ℝ} {U : Set E}
    {μ : Measure E} : MemWeightedSobolev v k p δ U μ ↔ ContDiffOn ℝ k v U ∧
      ∀ j ≤ k, MemWeightedLp (iteratedFDerivWithin ℝ j v U) p (δ - j) (μ.restrict U) :=
  Iff.rfl

namespace MemWeightedSobolev

variable {v : E → F} {k : ℕ} {p : ℝ≥0∞} {δ : ℝ} {U : Set E} {μ : Measure E}

theorem contDiffOn (h : MemWeightedSobolev v k p δ U μ) : ContDiffOn ℝ k v U := h.1

theorem memWeightedLp_iteratedFDerivWithin (h : MemWeightedSobolev v k p δ U μ) {j : ℕ}
    (hj : j ≤ k) : MemWeightedLp (iteratedFDerivWithin ℝ j v U) p (δ - j) (μ.restrict U) :=
  h.2 j hj

theorem weightedSobolevNorm_lt_top (h : MemWeightedSobolev v k p δ U μ) :
    weightedSobolevNorm v k p δ U μ < ∞ :=
  ENNReal.sum_lt_top.2 fun j hj =>
    memWeightedLp_iff.1 (h.2 j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))

/-- A function in `W^{k,p}_δ` is in `W^{j,p}_δ` for `j ≤ k`. -/
theorem of_le (h : MemWeightedSobolev v k p δ U μ) {j : ℕ} (hj : j ≤ k) :
    MemWeightedSobolev v j p δ U μ :=
  ⟨h.1.of_le (by exact_mod_cast hj), fun i hi => h.2 i (hi.trans hj)⟩

/-- A function in `W^{k,p}_δ` is itself in `Lᵖ_δ`. -/
theorem memWeightedLp (h : MemWeightedSobolev v k p δ U μ) :
    MemWeightedLp v p δ (μ.restrict U) := by
  have h0 := h.2 0 (Nat.zero_le k)
  rw [Nat.cast_zero, sub_zero, MemWeightedLp, iteratedFDerivWithin_zero_eq_comp] at h0
  simpa [MemWeightedLp, Function.comp_def, ← map_smul] using
    h0.continuousLinearMap_comp
      (continuousMultilinearCurryFin0 ℝ E F : (E [×0]→L[ℝ] F) →L[ℝ] F)

end MemWeightedSobolev

/-- **Decay implies weighted Sobolev regularity.** On the exterior `{x | R < ‖x‖}`, `R > 0`, a
`Cᵏ` function whose derivatives of order `j ≤ k` are `O(‖x‖ ^ (-t - j))` lies in `W^{k,p}_δ` for
every `p` and every `δ > -t`. This is the passage from the decay of the coefficients of a
metric in an asymptotically Euclidean chart to weighted Sobolev membership at a weight `-q` with
`q < t`. -/
theorem memWeightedSobolev_of_isBigO [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {v : E → F} {k : ℕ} {p : ℝ≥0∞} {t δ R : ℝ} (hR : 0 < R)
    (hδ : -t < δ) (hv : ContDiffOn ℝ k v (closedBall 0 R)ᶜ)
    (hO : ∀ j ≤ k, iteratedFDeriv ℝ j v =O[𝓟 (closedBall 0 R)ᶜ] fun x => ‖x‖ ^ (-t - j)) :
    MemWeightedSobolev v k p δ (closedBall 0 R)ᶜ μ := by
  have hU : IsOpen (closedBall (0 : E) R)ᶜ := isClosed_closedBall.isOpen_compl
  refine ⟨hv, fun j hj => ?_⟩
  have hcont : ContinuousOn (iteratedFDerivWithin ℝ j v (closedBall 0 R)ᶜ) (closedBall 0 R)ᶜ :=
    hv.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn
  have hO' : iteratedFDerivWithin ℝ j v (closedBall 0 R)ᶜ =O[𝓟 (closedBall 0 R)ᶜ]
      fun x => ‖x‖ ^ (-(t + j)) := by
    refine ((hO j hj).congr' ?_ (Eventually.of_forall fun x => by ring_nf)).trans
      (isBigO_refl _ _)
    filter_upwards [mem_principal_self _] with x hx
    rw [iteratedFDerivWithin_of_isOpen j hU hx]
  exact memWeightedLp_of_isBigO hR (by linarith)
    (hcont.aestronglyMeasurable hU.measurableSet) hO'

end TauCeti
