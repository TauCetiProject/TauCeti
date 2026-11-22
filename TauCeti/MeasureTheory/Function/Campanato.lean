/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Campanato's characterization of Hölder continuity

Let `μ` be an additive Haar measure on a finite-dimensional real normed space `E` of dimension
`n`, and let `0 < α`. For a locally integrable `f : E → F`, write `f_{x,r}` for its average over
`closedBall x r`, and call `⨍_{closedBall x r} ‖f - f_{x,r}‖` its *mean oscillation* on that
ball. **Campanato's theorem** says that `f` agrees almost everywhere with an `α`-Hölder function
exactly when its mean oscillation on balls of radius `r` is `O(r^α)`. The Hölder representative
is the precise representative `TauCeti.MeasureTheory.preciseRepresentative μ f`, the limit of the
averages `f_{x,r}` as `r → 0`.

The hypothesis controls an integral average rather than an essential supremum, so it is much
weaker than the oscillation bound behind `TauCeti.MeasureTheory.holderOnWith_preciseRepresentative`.
This is the form in which energy estimates deliver regularity: Poincaré's inequality turns a
growth bound on `∫_{closedBall x r} ‖∇u‖ᵖ` (Morrey's Dirichlet growth condition) into such a mean
oscillation bound, and the Campanato approach to the Schauder estimates compares a solution with
solutions of a constant-coefficient problem in the same integral norms.

## Domains with the measure density property

Estimates up to the boundary need the theorem on a domain `Ω ⊆ E`, with the balls replaced by
their intersections with `Ω`: all averages and integrals below are taken for `μ.restrict Ω`. The
theorem holds as soon as `Ω` has the **measure density property**: there is `c > 0` with

`c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)`

for `x ∈ Ω` and `0 < r` up to twice the diameter of `Ω` (every `r`, if `Ω` is unbounded). The
classical examples are the bounded Lipschitz domains, by the interior cone condition. The whole
space has it with `c = 1`, and the whole-space theorems are the case `Ω = univ`. The Hölder
representative is the precise representative of `f` for `μ.restrict Ω`, which agrees with `f`
almost everywhere on `Ω` by Lebesgue's differentiation theorem for the locally finite measure
`μ.restrict Ω` (`TauCeti.MeasureTheory.ae_eq_preciseRepresentative_of_hasBesicovitchCovering`).

For exponents `p ≥ 1` and `λ`, the **Campanato seminorm** of `f` on `Ω` is

`[f]_{p,λ} = (sup_{x ∈ Ω, r > 0} r^(-λ) ∫_{B(x, r) ∩ Ω} ‖f - f_{x,r}‖^p)^(1/p)`,

and the Campanato space `𝓛^{p,λ}(Ω)` consists of the functions for which it is finite. Following
Giaquinta–Martinazzi, who state their estimates for `[f]_{p,λ}^p`, the declaration
`TauCeti.MeasureTheory.campanatoSeminormPow` is the `p`-th power `[f]_{p,λ}^p`, the supremum itself,
without the `p`-th root. It is `p`-homogeneous rather than homogeneous, and its finiteness is
membership in the Campanato space. On a null-measurable set with the measure density property a
locally integrable function lies in `𝓛^{p,n + p α}(Ω)` exactly when it agrees almost everywhere on
`Ω` with a function that is `α`-Hölder continuous on `Ω`
(`TauCeti.MeasureTheory.exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top`), with explicit
bounds between the Hölder constant and `[f]_{p,λ}^p` in both directions. For `λ = n` the
Campanato space is the space of functions of bounded mean oscillation, which contains unbounded
functions; the characterization needs `λ > n`, that is `α > 0`.

## The argument

The proof is a telescoping argument. Comparing the averages over `closedBall x r` and
`closedBall x (r / 2)` costs at most `2ⁿ / c · M r^α`, where `2ⁿ / c` bounds the ratio of the
`μ.restrict Ω`-measures of the two balls (by `TauCeti.norm_setAverage_sub_le_of_subset`,
`MeasureTheory.Measure.addHaar_real_closedBall_div_le` and the measure density property).
Summing over dyadic radii shows that the averages `f_{x,r}` converge as `r → 0`, with
`‖f_{x,r} - f*(x)‖ ≤ 2ⁿ / (c (1 - 2^(-α))) · M r^α`, and comparing the averages over
`closedBall y d ⊆ closedBall x (2 d)`, `d = dist x y`, then gives the Hölder bound. For the
Campanato seminorm, Hölder's inequality bounds the mean oscillation on `B(x, r) ∩ Ω` by
`((μ(B(x, r) ∩ Ω))⁻¹ [f]_{p,λ}^p r^λ)^(1/p)`, and the measure density property bounds the measure
below by `c μ(B(0, 1)) rⁿ`.

## Main declarations

All declarations are in the `TauCeti.MeasureTheory` namespace.

* `setAverage_norm_sub_setAverage_le_of_holderOnWith`: the mean oscillation of an `α`-Hölder
  function on a ball of radius `r` is at most a multiple of `r^α`.
* `ae_norm_sub_setAverage_le_of_holderOnWith`: on a set `Ω` where `f` is `α`-Hölder, `f` lies
  almost everywhere on a ball centred in `Ω` within a multiple of `r^α` of its average over the
  ball, both for the restriction of the measure to `Ω`.
* `tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_setAverage_norm_sub_le`,
  `tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le`: mean
  oscillation decaying like `r^α` at `x` makes the averages converge at `x`, on a domain with the
  measure density property and on the whole space.
* `norm_setAverage_closedBall_restrict_sub_preciseRepresentative_le`,
  `norm_setAverage_closedBall_sub_preciseRepresentative_le`: the rate of that convergence.
* `dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le`,
  `dist_preciseRepresentative_le_of_setAverage_norm_sub_le`: the local Hölder estimate between
  two points, from mean oscillation bounds on balls of radius comparable to their distance.
* `norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le`,
  `norm_setAverage_closedBall_sub_setAverage_closedBall_le`: mean oscillation decaying like `r^α`
  at `x` keeps the averages over concentric balls within `O(r^α)` of each other.
* `setAverage_closedBall_restrict_norm_sub_le_sqrt_of_setIntegral_le`: by Jensen's inequality, a
  bound on the square mean oscillation bounds the mean oscillation, on a set with density bounded
  below.
* `setAverage_closedBall_restrict_norm_sub_le`: square mean oscillation of order `r^{n+2κ}` gives
  mean oscillation of order `r^κ`, on a set with density bounded below.
* `norm_setAverage_closedBall_restrict_le_sqrt`: an `L²` bound bounds the averages, on a set with
  density bounded below.
* `exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`: square mean oscillation decaying like
  `r^{n+2κ}` at `x` keeps the averages bounded, so that `∫_{B(x, r) ∩ Ω} ‖f‖²` decays like `rⁿ`,
  on a set with density bounded below in the balls around `x`.
* `holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le`: the Hölder bound on a set, from
  mean oscillation bounds at scales below a fixed radius and a bound on the averages at that radius.
* `holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le`: **Campanato's
  theorem** on a domain with the measure density property.
* `holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le_of_norm_le`: the Hölder
  bound for the restriction to a set with the measure density property, on a set of points that
  may lie on its boundary, from mean oscillation bounds below a fixed scale.
* `setAverage_closedBall_restrict_norm_sub_le_sqrt`: the square mean distance from a constant on a
  larger set bounds the mean oscillation on a ball.
* `holderWith_preciseRepresentative_of_setAverage_norm_sub_le`: **Campanato's theorem** on the
  whole space.
* `exists_holderWith_ae_eq_iff_forall_setAverage_norm_sub_le`: a locally integrable function
  agrees almost everywhere with an `α`-Hölder function if and only if its mean oscillation on
  balls of radius `r` is `O(r^α)`.
* `campanatoSeminormPow`: the `p`-th power `[f]_{p,λ}^p` of the Campanato seminorm on a set.
* `campanatoSeminormPow_le_of_holderOnWith`: Hölder functions lie in the Campanato space.
* `setAverage_norm_sub_le_of_campanatoSeminormPow_le`: the Campanato seminorm bounds the mean
  oscillation on a domain with the measure density property.
* `exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top`: **Campanato's characterization**
  `𝓛^{p,n + p α}(Ω) = C^{0,α}(Ω)` on a domain with the measure density property.
* `campanatoSeminormPow_const`: constants have vanishing Campanato seminorm.
* `exists_ae_eq_const_iff_campanatoSeminormPow_ne_top`: for `α > 1`, that is `λ > n + p`, the
  Campanato space on a preconnected open set with the measure density property consists of the
  almost everywhere constant functions.

## References

* S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Theorem 5.5.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Theorem 3.1.
-/

public section

noncomputable section

open Filter Metric Set Topology MeasureTheory Module
open scoped NNReal ENNReal

namespace TauCeti

namespace MeasureTheory

section Holder

variable {X F : Type*} [MetricSpace X] [MeasurableSpace X] [ProperSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {Ω : Set X} {x : X}

omit [IsFiniteMeasureOnCompacts μ] in
/-- **The mean oscillation of a Hölder function.** If `f` is `α`-Hölder continuous on
`closedBall x r` with constant `K`, `α > 0`, and this ball has positive measure, then the mean
oscillation of `f` on the ball is at most `K (2 r)^α`. -/
theorem setAverage_norm_sub_setAverage_le_of_holderOnWith {K α : ℝ≥0} {r : ℝ} (hα : 0 < α)
    (hμ : μ (closedBall x r) ≠ 0) (hf : HolderOnWith K α f (closedBall x r)) :
    ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤
      K * (2 * r) ^ (α : ℝ) := by
  have hr : 0 ≤ r := by
    by_contra h
    exact hμ (by simp [closedBall_eq_empty.2 (not_le.1 h)])
  -- If the ball has infinite measure, both averages are `0` by convention.
  rcases eq_or_ne (μ (closedBall x r)) ⊤ with hμ' | hμ'
  · simp only [setAverage_eq, measureReal_def, hμ', ENNReal.toReal_top, inv_zero, zero_smul]
    positivity
  have hcont := hf.continuousOn hα
  -- Continuous functions are integrable on the ball, which is compact of finite measure.
  have hint : IntegrableOn f (closedBall x r) μ :=
    hcont.integrableOn_of_subset_isCompact (isCompact_closedBall x r) measurableSet_closedBall
      subset_rfl hμ'
  -- Every value of `f` on the ball lies within `K (2 r)^α` of every other one, hence of their
  -- average.
  have hpt : ∀ y ∈ closedBall x r,
      ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ≤ K * (2 * r) ^ (α : ℝ) := by
    intro y hy
    have hmem : ⨍ z in closedBall x r, f z ∂μ ∈ closedBall (f y) (K * (2 * r) ^ (α : ℝ)) := by
      refine (convex_closedBall _ _).set_average_mem isClosed_closedBall hμ hμ' ?_ hint
      filter_upwards [self_mem_ae_restrict measurableSet_closedBall] with z hz
      rw [mem_closedBall]
      refine (hf.dist_le hz hy).trans ?_
      gcongr
      calc dist z y ≤ dist z x + dist y x := dist_triangle_right _ _ _
        _ ≤ 2 * r := by linarith [mem_closedBall.1 hz, mem_closedBall.1 hy]
    rw [← dist_eq_norm, dist_comm]
    exact mem_closedBall.1 hmem
  refine (convex_Iic ((K : ℝ) * (2 * r) ^ (α : ℝ))).set_average_mem isClosed_Iic hμ hμ' ?_ ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_closedBall] with y hy using hpt y hy
  · exact (hcont.sub continuousOn_const).norm.integrableOn_of_subset_isCompact
      (isCompact_closedBall x r) measurableSet_closedBall subset_rfl hμ'

/-- **The oscillation of a Hölder function about its average on a domain.** If `f` is `α`-Hölder
continuous on a null-measurable set `Ω` with constant `K`, then almost everywhere on
`closedBall x r`, `x ∈ Ω`, for `μ.restrict Ω`, the function `f` lies within `K (2 r)^α` of its
average over that ball. -/
theorem ae_norm_sub_setAverage_le_of_holderOnWith {K α : ℝ≥0} {r : ℝ}
    (hΩ : NullMeasurableSet Ω μ) (hf : HolderOnWith K α f Ω)
    (hfm : AEStronglyMeasurable f (μ.restrict Ω)) (hx : x ∈ Ω) (hr : 0 < r) :
    ∀ᵐ y ∂(μ.restrict Ω).restrict (closedBall x r),
      ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ≤ K * (2 * r) ^ (α : ℝ) := by
  -- Almost every point of `closedBall x r` for `μ.restrict Ω` lies in `Ω`.
  have hmem : ∀ᵐ y ∂(μ.restrict Ω).restrict (closedBall x r), y ∈ closedBall x r ∩ Ω := by
    rw [Measure.restrict_restrict measurableSet_closedBall]
    exact ae_restrict_mem₀ (measurableSet_closedBall.nullMeasurableSet.inter hΩ)
  -- Any two values of `f` on `closedBall x r ∩ Ω` are at distance at most `K (2 r)^α`.
  have hdist : ∀ y ∈ closedBall x r ∩ Ω, ∀ z ∈ closedBall x r ∩ Ω,
      dist (f z) (f y) ≤ K * (2 * r) ^ (α : ℝ) := by
    intro y hy z hz
    have hzy : dist z y ≤ 2 * r :=
      calc dist z y ≤ dist z x + dist y x := dist_triangle_right _ _ _
        _ ≤ 2 * r := by linarith [mem_closedBall.1 hz.1, mem_closedBall.1 hy.1]
    exact (hf.dist_le hz.2 hy.2).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hzy α.property) K.property)
  rcases eq_or_ne (μ.restrict Ω (closedBall x r)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  have hfin : μ.restrict Ω (closedBall x r) ≠ ⊤ :=
    ((Measure.restrict_apply_le _ _).trans_lt measure_closedBall_lt_top).ne
  have hint : IntegrableOn f (closedBall x r) (μ.restrict Ω) := by
    refine Measure.integrableOn_of_bounded (M := ‖f x‖ + K * (2 * r) ^ (α : ℝ)) hfin hfm ?_
    filter_upwards [hmem] with z hz
    have := hdist x ⟨mem_closedBall_self hr.le, hx⟩ z hz
    rw [dist_eq_norm] at this
    linarith [norm_le_insert' (f z) (f x)]
  -- The average lies in every closed ball of radius `K (2 r)^α` about a value of `f`.
  filter_upwards [hmem] with y hy
  rw [← dist_eq_norm, dist_comm]
  refine mem_closedBall.1 <| (convex_closedBall _ _).set_average_mem isClosed_closedBall h0 hfin
    ?_ hint
  filter_upwards [hmem] with z hz using hdist y hy z hz

end Holder

/-! ### Campanato's theorem on a set with the measure density property -/

section Domain

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {Ω : Set E} {c : ℝ≥0}
  {x : E} {M α ρ : ℝ}

/-- For `α > 0`, `1 - 2^(-α)` is positive: the dyadic series of ratio `2^(-α)` converges. -/
private lemma one_sub_two_rpow_neg_pos (hα : 0 < α) : 0 < 1 - (2 : ℝ) ^ (-α) :=
  sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα))

/-- Comparing the averages over `closedBall y ε ⊆ closedBall x r` for `r ≤ 2 ε` costs at most
`2ⁿ / c` times the mean oscillation on `closedBall x r`, all with respect to `μ.restrict Ω`, if
`Ω` has density at least `c` in `closedBall y ε`. -/
private lemma norm_setAverage_closedBall_sub_le_of_le_two_mul {y : E} {ε r : ℝ} (hc : 0 < c)
    (hε : 0 < ε) (hsub : closedBall y ε ⊆ closedBall x r) (hrε : r ≤ 2 * ε)
    (hd : (c : ℝ≥0∞) * μ (closedBall y ε) ≤ μ (closedBall y ε ∩ Ω))
    (hf : IntegrableOn f (closedBall x r) (μ.restrict Ω))
    (hosc : ⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w ∂μ.restrict Ω‖
      ∂μ.restrict Ω ≤ M * r ^ α) :
    ‖(⨍ z in closedBall y ε, f z ∂μ.restrict Ω) - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ≤
      2 ^ finrank ℝ E / c * (M * r ^ α) := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.1 (hsub (mem_closedBall_self hε.le)))
  exact (norm_setAverage_sub_le_of_subset hsub (μ.restrict_closedBall_ne_zero_of_mul_le hc hε hd)
    ((Measure.restrict_apply_le _ _).trans_lt measure_closedBall_lt_top).ne hf _).trans <|
    mul_le_mul (μ.addHaar_real_restrict_closedBall_div_le x y hc hε hr hrε hd) hosc
      (average_nonneg fun _ ↦ norm_nonneg _) (by positivity)

/-- **Averages over concentric balls, on a set with the measure density property.** Let
`α > 0` and `c > 0`. If `Ω` has density at least `c` in `closedBall x r`, `f` is integrable on
`closedBall x ρ` and its mean oscillation on `closedBall x r` with respect to `μ.restrict Ω` is at
most `M r^α` for `0 < r ≤ ρ`, then the averages over `closedBall x ε` and `closedBall x r`,
`0 < ε ≤ r ≤ ρ`, with respect to `μ.restrict Ω` differ by at most
`2ⁿ / (c (1 - 2^(-α))) · M r^α`, where `n` is the dimension. The proof telescopes over dyadic
radii. -/
theorem norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le (hα : 0 < α)
    (hc : 0 < c)
    (hf : IntegrableOn f (closedBall x ρ) (μ.restrict Ω))
    (hdens : ∀ r, 0 < r → r ≤ ρ → (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ α)
    {ε r : ℝ} (hε : 0 < ε) (hεr : ε ≤ r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x ε, f y ∂μ.restrict Ω) - ⨍ y in closedBall x r, f y ∂μ.restrict Ω‖ ≤
      2 ^ finrank ℝ E / (c * (1 - 2 ^ (-α))) * (M * r ^ α) := by
  set D : ℝ := 2 ^ finrank ℝ E / c
  set C : ℝ := 2 ^ finrank ℝ E / (c * (1 - 2 ^ (-α)))
  have hq := one_sub_two_rpow_neg_pos hα
  have hCD : C = D / (1 - 2 ^ (-α)) := by simp only [C, D, div_div]
  have hC : D ≤ C := hCD ▸
    le_div_self (by positivity) hq (sub_le_self _ (Real.rpow_pos_of_pos two_pos _).le)
  have hCq : C * 2 ^ (-α) + D = C := by
    rw [hCD]
    field_simp [hq.ne']
    ring
  have hM : ∀ r, 0 < r → r ≤ ρ → 0 ≤ M * r ^ α := fun r hr hrρ ↦
    (average_nonneg fun _ ↦ norm_nonneg _).trans (hosc r hr hrρ)
  have hint : ∀ r ≤ ρ, IntegrableOn f (closedBall x r) (μ.restrict Ω) := fun r hrρ ↦
    hf.mono_set (closedBall_subset_closedBall hrρ)
  -- By induction on `k`, the bound holds for `r / 2 ^ k ≤ ε ≤ r`: either `ε ≥ r / 2`, and one
  -- step suffices, or `ε < r / 2`, and we pass through the average over `closedBall x (r / 2)`,
  -- the identity `C 2^(-α) + D = C` absorbing the extra step.
  have key : ∀ k : ℕ, ∀ r, 0 < r → r ≤ ρ → ∀ ε, r / 2 ^ k ≤ ε → ε ≤ r →
      ‖(⨍ y in closedBall x ε, f y ∂μ.restrict Ω) - ⨍ y in closedBall x r, f y ∂μ.restrict Ω‖ ≤
        C * (M * r ^ α) := by
    intro k
    induction k with
    | zero =>
      intro r hr hrρ ε h₁ h₂
      obtain rfl : ε = r := le_antisymm h₂ (by simpa using h₁)
      simpa using mul_nonneg ((by positivity : (0 : ℝ) ≤ D).trans hC) (hM ε hr hrρ)
    | succ k ih =>
      intro r hr hrρ ε h₁ h₂
      have hε : 0 < ε := (by positivity : 0 < r / 2 ^ (k + 1)).trans_le h₁
      rcases le_or_gt (r / 2) ε with h | h
      · exact (norm_setAverage_closedBall_sub_le_of_le_two_mul hc hε
          (closedBall_subset_closedBall h₂) (by linarith) (hdens ε hε (h₂.trans hrρ))
          (hint r hrρ) (hosc r hr hrρ)).trans (mul_le_mul_of_nonneg_right hC (hM r hr hrρ))
      have h₃ := ih (r / 2) (by positivity) (by linarith) ε
        (by rwa [div_div, ← pow_succ']) h.le
      have h₄ := norm_setAverage_closedBall_sub_le_of_le_two_mul hc (half_pos hr)
        (closedBall_subset_closedBall (half_le_self hr.le)) (by linarith)
        (hdens (r / 2) (half_pos hr) (by linarith)) (hint r hrρ) (hosc r hr hrρ)
      calc ‖(⨍ y in closedBall x ε, f y ∂μ.restrict Ω) -
            ⨍ y in closedBall x r, f y ∂μ.restrict Ω‖
          ≤ ‖(⨍ y in closedBall x ε, f y ∂μ.restrict Ω) -
              ⨍ y in closedBall x (r / 2), f y ∂μ.restrict Ω‖ +
            ‖(⨍ y in closedBall x (r / 2), f y ∂μ.restrict Ω) -
              ⨍ y in closedBall x r, f y ∂μ.restrict Ω‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C * (M * (r / 2) ^ α) + D * (M * r ^ α) := add_le_add h₃ h₄
        _ = (C * 2 ^ (-α) + D) * (M * r ^ α) := by
            rw [Real.div_rpow hr.le zero_le_two, Real.rpow_neg zero_le_two]
            ring
        _ = C * (M * r ^ α) := by rw [hCq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε (hε.trans_le hεr)) one_half_lt_one
  refine key k r (hε.trans_le hεr) hrρ ε ?_ hεr
  calc r / 2 ^ k = (1 / 2) ^ k * r := by rw [one_div_pow]; ring
    _ ≤ ε := ((lt_div_iff₀ (hε.trans_le hεr)).1 hk).le

/-- **Mean oscillation decay gives convergence of the averages, on a set with the measure density
property.** Let `α > 0`, `ρ > 0` and `c > 0`. Suppose that `Ω` has density at least `c` in the
closed balls around `x` of radius at most `ρ`, that is `c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)`, that `f` is
integrable on `closedBall x ρ` for `μ.restrict Ω`, and that its mean oscillation on `closedBall x r`
for `μ.restrict Ω` is at most `M r^α` for `0 < r ≤ ρ`. Then the averages of `f` over the closed
balls around `x` for `μ.restrict Ω` converge to the precise representative of `f` for
`μ.restrict Ω` at `x`. This is the integrable case of
`tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_setAverage_norm_sub_le`. -/
private theorem tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_integrableOn
    (hα : 0 < α) (hρ : 0 < ρ) (hc : 0 < c) (hf : IntegrableOn f (closedBall x ρ) (μ.restrict Ω))
    (hdens : ∀ r, 0 < r → r ≤ ρ → (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ α) :
    Tendsto (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ.restrict Ω) (𝓝[>] 0)
      (𝓝 (preciseRepresentative (μ.restrict Ω) f x)) := by
  set C : ℝ := 2 ^ finrank ℝ E / (c * (1 - 2 ^ (-α)))
  -- The averages form a Cauchy filter: those of radius at most `τ` lie within `C M τ^α` of the
  -- average of radius `τ`.
  have hcauchy : Cauchy (map (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ.restrict Ω)
      (𝓝[>] (0 : ℝ))) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun δ hδ ↦ ?_⟩
    have h0 : Tendsto (fun r : ℝ ↦ C * (M * r ^ α)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuous_rpow_const hα.le).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [Real.zero_rpow hα.ne'] using (h.const_mul M).const_mul C
    obtain ⟨τ, hτ, hτρ⟩ := ((h0.eventually (gt_mem_nhds (half_pos hδ))).and
      (Ioc_mem_nhdsGT hρ)).exists
    refine ⟨(fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ.restrict Ω) '' Ioc 0 τ,
      image_mem_map (Ioc_mem_nhdsGT hτρ.1), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    calc dist (⨍ y in closedBall x a, f y ∂μ.restrict Ω)
          (⨍ y in closedBall x b, f y ∂μ.restrict Ω)
        ≤ dist (⨍ y in closedBall x a, f y ∂μ.restrict Ω)
            (⨍ y in closedBall x τ, f y ∂μ.restrict Ω) +
          dist (⨍ y in closedBall x b, f y ∂μ.restrict Ω)
            (⨍ y in closedBall x τ, f y ∂μ.restrict Ω) :=
          dist_triangle_right _ _ _
      _ ≤ C * (M * τ ^ α) + C * (M * τ ^ α) := by
          rw [dist_eq_norm, dist_eq_norm]
          exact add_le_add
            (norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le hα hc hf hdens hosc
              ha.1 ha.2 hτρ.2)
            (norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le hα hc hf hdens hosc
              hb.1 hb.2 hτρ.2)
      _ < δ := by linarith
  obtain ⟨v, hv⟩ := CompleteSpace.complete hcauchy
  rwa [preciseRepresentative_eq_of_tendsto hv]

/-- **Mean oscillation decay gives convergence of the averages, on a set with the measure density
property.** Let `α > 0`, `ρ > 0` and `c > 0`. Suppose that `Ω` has density at least `c` in the
closed balls around `x` of radius at most `ρ`, that is `c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)`, and that
the mean oscillation of `f` on `closedBall x r` for `μ.restrict Ω` is at most `M r^α` for
`0 < r ≤ ρ`. Then the averages of `f` over the closed balls around `x` for `μ.restrict Ω` converge
to the precise representative of `f` for `μ.restrict Ω` at `x`. (If `f` is integrable for
`μ.restrict Ω` on no ball around `x`, all the averages are `0` by convention.) -/
theorem tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_setAverage_norm_sub_le
    (hα : 0 < α) (hρ : 0 < ρ) (hc : 0 < c)
    (hdens : ∀ r, 0 < r → r ≤ ρ → (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ α) :
    Tendsto (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ.restrict Ω) (𝓝[>] 0)
      (𝓝 (preciseRepresentative (μ.restrict Ω) f x)) := by
  by_cases hex : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ IntegrableOn f (closedBall x ρ') (μ.restrict Ω)
  · obtain ⟨ρ', hρ', hρ'ρ, hf⟩ := hex
    exact tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_integrableOn hα hρ' hc hf
      (fun r hr hrρ' ↦ hdens r hr (hrρ'.trans hρ'ρ))
      (fun r hr hrρ' ↦ hosc r hr (hrρ'.trans hρ'ρ))
  · push Not at hex
    have hzero : ∀ ε ∈ Ioc (0 : ℝ) ρ, ⨍ y in closedBall x ε, f y ∂μ.restrict Ω = 0 :=
      fun ε hε ↦ by rw [setAverage_eq, integral_undef (hex ε hε.1 hε.2), smul_zero]
    have h0 : Tendsto (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ.restrict Ω) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr'
        (eventuallyEq_of_mem (Ioc_mem_nhdsGT hρ) fun ε hε ↦ (hzero ε hε).symm)
    rwa [preciseRepresentative_eq_of_tendsto h0]

/-- **The rate of convergence of the averages, on a set with the measure density property.** Let
`α > 0` and `c > 0`. Suppose that `Ω` has density at least `c` in the closed balls around `x` of
radius at most `ρ`, that `f` is integrable on `closedBall x ρ` for `μ.restrict Ω`, and that its
mean oscillation on `closedBall x r` for `μ.restrict Ω` is at most `M r^α` for `0 < r ≤ ρ`. Then
for `0 < r ≤ ρ` the average of `f` over `closedBall x r` for `μ.restrict Ω` lies within
`2ⁿ / (c (1 - 2^(-α))) · M r^α` of the precise representative of `f` for `μ.restrict Ω` at `x`,
where `n` is the dimension. -/
theorem norm_setAverage_closedBall_restrict_sub_preciseRepresentative_le (hα : 0 < α)
    (hc : 0 < c) (hf : IntegrableOn f (closedBall x ρ) (μ.restrict Ω))
    (hdens : ∀ r, 0 < r → r ≤ ρ → (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ α)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x r, f y ∂μ.restrict Ω) - preciseRepresentative (μ.restrict Ω) f x‖ ≤
      2 ^ finrank ℝ E / (c * (1 - 2 ^ (-α))) * (M * r ^ α) := by
  have ht :=
    tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_setAverage_norm_sub_le hα
      (hr.trans_le hrρ) hc hdens hosc
  refine le_of_tendsto (tendsto_const_nhds.sub ht).norm ?_
  filter_upwards [Ioc_mem_nhdsGT hr] with ε hε
  rw [norm_sub_rev]
  exact norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le hα hc hf hdens hosc hε.1
    hε.2 hrρ

/-- **The local Campanato estimate on a set with the measure density property.** Let `α > 0`,
`c > 0` and `d = dist x y`. Suppose that `Ω` has density at least `c` in `closedBall x r` for
`0 < r ≤ 2 d` and in `closedBall y r` for `0 < r ≤ d`, that `f` is integrable on
`closedBall x (2 d)` for `μ.restrict Ω`, and that the mean oscillation of `f` for `μ.restrict Ω` is
at most `M r^α` on the same balls. Then the precise representatives of `f` for `μ.restrict Ω` at
`x` and `y` differ by at most `2 · 2^α · 2ⁿ / (c (1 - 2^(-α))) · M d^α`, where `n` is the
dimension. -/
theorem dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le {y : E} (hα : 0 < α)
    (hc : 0 < c) (hf : IntegrableOn f (closedBall x (2 * dist x y)) (μ.restrict Ω))
    (hdensx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hdensy : ∀ r, 0 < r → r ≤ dist x y →
      (c : ℝ≥0∞) * μ (closedBall y r) ≤ μ (closedBall y r ∩ Ω))
    (hoscx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      ⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ α)
    (hoscy : ∀ r, 0 < r → r ≤ dist x y →
      ⨍ z in closedBall y r, ‖f z - ⨍ w in closedBall y r, f w ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ α) :
    dist (preciseRepresentative (μ.restrict Ω) f x) (preciseRepresentative (μ.restrict Ω) f y) ≤
      2 * 2 ^ α * (2 ^ finrank ℝ E / (c * (1 - 2 ^ (-α)))) * (M * dist x y ^ α) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp [Real.zero_rpow hα.ne']
  set d := dist x y
  set D : ℝ := 2 ^ finrank ℝ E / c
  set C : ℝ := 2 ^ finrank ℝ E / (c * (1 - 2 ^ (-α)))
  have hd : 0 < d := dist_pos.2 hxy
  -- Pass from `x` to `y` through the averages over `closedBall x (2 d) ⊇ closedBall y d`.
  have hsub : closedBall y d ⊆ closedBall x (2 * d) :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  have h₁ := norm_setAverage_closedBall_restrict_sub_preciseRepresentative_le hα hc hf hdensx
    hoscx (by positivity) le_rfl
  have h₂ := norm_setAverage_closedBall_restrict_sub_preciseRepresentative_le hα hc
    (hf.mono_set hsub) hdensy hoscy hd le_rfl
  have h₃ : ‖(⨍ z in closedBall y d, f z ∂μ.restrict Ω) -
      ⨍ z in closedBall x (2 * d), f z ∂μ.restrict Ω‖ ≤ D * (M * (2 * d) ^ α) :=
    norm_setAverage_closedBall_sub_le_of_le_two_mul hc hd hsub le_rfl (hdensy d hd le_rfl) hf
      (hoscx _ (by positivity) le_rfl)
  have hCq : 2 ^ α * D = C * (2 ^ α - 1) := by
    simp only [C, D]
    field_simp [(one_sub_two_rpow_neg_pos hα).ne']
    rw [Real.rpow_neg zero_le_two]
    field_simp
  rw [dist_eq_norm]
  calc ‖preciseRepresentative (μ.restrict Ω) f x - preciseRepresentative (μ.restrict Ω) f y‖
      ≤ ‖preciseRepresentative (μ.restrict Ω) f x -
            ⨍ z in closedBall x (2 * d), f z ∂μ.restrict Ω‖ +
        ‖(⨍ z in closedBall x (2 * d), f z ∂μ.restrict Ω) -
            ⨍ z in closedBall y d, f z ∂μ.restrict Ω‖ +
        ‖(⨍ z in closedBall y d, f z ∂μ.restrict Ω) - preciseRepresentative (μ.restrict Ω) f y‖ :=
        (norm_sub_le_norm_sub_add_norm_sub _ (⨍ z in closedBall y d, f z ∂μ.restrict Ω) _).trans
          (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ ≤ C * (M * (2 * d) ^ α) + D * (M * (2 * d) ^ α) + C * (M * d ^ α) := by
        refine add_le_add (add_le_add ?_ ?_) h₂ <;> rw [norm_sub_rev]
        exacts [h₁, h₃]
    _ = (2 ^ α * C + 2 ^ α * D + C) * (M * d ^ α) := by
        rw [Real.mul_rpow zero_le_two hd.le]
        ring
    _ = 2 * 2 ^ α * C * (M * d ^ α) := by
        rw [hCq]
        ring

/-- **Campanato's theorem on a set with the measure density property.** Let `α > 0` and `c > 0`.
Suppose that `Ω` has density at least `c` in every closed ball centred in `Ω` of radius `r > 0` at
most twice the diameter of `Ω` (every radius, if `Ω` is unbounded):
`c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)`. If `f` is locally integrable for `μ.restrict Ω` and its mean
oscillation for `μ.restrict Ω` on these balls is at most `M r^α`, then the precise representative of
`f` for `μ.restrict Ω` is `α`-Hölder continuous on `Ω`, with constant
`2 · 2^α · 2ⁿ / (c (1 - 2^(-α))) · M`, where `n` is the dimension. It agrees with `f` almost
everywhere on `Ω` (`TauCeti.MeasureTheory.ae_eq_preciseRepresentative_of_hasBesicovitchCovering`).
-/
theorem holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le {α M : ℝ≥0}
    (hα : 0 < α) (hc : 0 < c) (hf : LocallyIntegrable f (μ.restrict Ω))
    (hdens : ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ 2 * ediam Ω →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hosc : ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ 2 * ediam Ω →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ (α : ℝ)) :
    HolderOnWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / (c * (1 - 2 ^ (-(α : ℝ)))))) * M) α
      (preciseRepresentative (μ.restrict Ω) f) Ω := by
  have hα' : (0 : ℝ) < α := hα
  have hC : (0 : ℝ) ≤ 2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / (c * (1 - 2 ^ (-(α : ℝ))))) :=
    mul_nonneg (by positivity)
      (div_nonneg (by positivity) (mul_nonneg c.property (one_sub_two_rpow_neg_pos hα').le))
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  -- Every radius up to `2 dist x y` is at most twice the diameter of `Ω`.
  have hdiam : ∀ r : ℝ, r ≤ 2 * dist x y → ENNReal.ofReal r ≤ 2 * ediam Ω := fun r hr ↦
    calc ENNReal.ofReal r ≤ ENNReal.ofReal (2 * dist x y) := ENNReal.ofReal_le_ofReal hr
      _ = 2 * edist x y := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, edist_dist]
      _ ≤ 2 * ediam Ω := by gcongr; exact edist_le_ediam_of_mem hx hy
  have hdiam' : ∀ r : ℝ, r ≤ dist x y → ENNReal.ofReal r ≤ 2 * ediam Ω := fun r hr ↦
    hdiam r (by linarith [dist_nonneg (x := x) (y := y)])
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hC, mul_assoc]
  exact dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le hα' hc
    (hf.integrableOn_isCompact (isCompact_closedBall _ _))
    (fun r hr hr' ↦ hdens x hx r hr (hdiam r hr')) (fun r hr hr' ↦ hdens y hy r hr (hdiam' r hr'))
    (fun r hr hr' ↦ hosc x hx r hr (hdiam r hr')) (fun r hr hr' ↦ hosc y hy r hr (hdiam' r hr'))

/-- **Campanato's theorem on a set with the measure density property, below a fixed scale.** Let
`α > 0`, `c > 0` and `ρ > 0`. Suppose that for every `x ∈ S`, `Ω` has density at least `c` in
`closedBall x r` for `0 < r ≤ ρ`, `f` is integrable on `closedBall x ρ` for `μ.restrict Ω`, its mean
oscillation for `μ.restrict Ω` on `closedBall x r` is at most `M r^α` for `0 < r ≤ ρ`, and the norm
of its average for `μ.restrict Ω` over `closedBall x ρ` is at most `B`. Then the precise
representative of `f` for `μ.restrict Ω` is `α`-Hölder continuous on `S`, with constant
`2 · 2^α · (2ⁿ / (c (1 - 2^(-α))) · M + B ρ^(-α))`, where `n` is the dimension. The set `S` need not
lie in `Ω`: its points may lie on the boundary of `Ω`, as long as `Ω` is dense enough around
them. -/
theorem holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le_of_norm_le
    {α : ℝ≥0} {S : Set E} {B : ℝ} (hα : 0 < α) (hc : 0 < c) (hρ : 0 < ρ)
    (hdens : ∀ x ∈ S, ∀ r, 0 < r → r ≤ ρ →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω))
    (hf : ∀ x ∈ S, IntegrableOn f (closedBall x ρ) (μ.restrict Ω))
    (hosc : ∀ x ∈ S, ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
        M * r ^ (α : ℝ))
    (havg : ∀ x ∈ S, ‖⨍ y in closedBall x ρ, f y ∂μ.restrict Ω‖ ≤ B) :
    HolderOnWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / (c * (1 - 2 ^ (-(α : ℝ)))) * M + B * ρ ^ (-(α : ℝ))))) α
      (preciseRepresentative (μ.restrict Ω) f) S := by
  have hα' : (0 : ℝ) < α := hα
  set C : ℝ := 2 ^ finrank ℝ E / (c * (1 - 2 ^ (-(α : ℝ))))
  have hC : 0 ≤ C :=
    div_nonneg (by positivity) (mul_nonneg c.property (one_sub_two_rpow_neg_pos hα').le)
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hB : 0 ≤ B := (norm_nonneg _).trans (havg x hx)
  -- The mean oscillation on `closedBall x ρ` is nonnegative, so `M ≥ 0`.
  have hM : 0 ≤ M := by
    have h := (average_nonneg fun _ => norm_nonneg _).trans (hosc x hx ρ hρ le_rfl)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  rw [Real.coe_toNNReal _ (by positivity)]
  rcases le_or_gt (2 * dist x y) ρ with hd | hd
  · -- Nearby points: the local Campanato estimate.
    have hdy : ∀ r, r ≤ dist x y → r ≤ ρ := fun r hr => by
      linarith [dist_nonneg (x := x) (y := y)]
    have h := dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le hα' hc
      ((hf x hx).mono_set (closedBall_subset_closedBall hd))
      (fun r hr hr' => hdens x hx r hr (hr'.trans hd)) (fun r hr hr' => hdens y hy r hr (hdy r hr'))
      (fun r hr hr' => hosc x hx r hr (hr'.trans hd)) (fun r hr hr' => hosc y hy r hr (hdy r hr'))
    have : 0 ≤ 2 * 2 ^ (α : ℝ) * (B * ρ ^ (-(α : ℝ))) * dist x y ^ (α : ℝ) := by positivity
    calc _ ≤ _ := h
      _ ≤ _ := by nlinarith
  · -- Distant points: both values lie within `B + C M ρ^α` of `0`.
    have hbound : ∀ z ∈ S, ‖preciseRepresentative (μ.restrict Ω) f z‖ ≤
        (C * M + B * ρ ^ (-(α : ℝ))) * ρ ^ (α : ℝ) := fun z hz => by
      have h := norm_setAverage_closedBall_restrict_sub_preciseRepresentative_le hα' hc (hf z hz)
        (hdens z hz) (hosc z hz) hρ le_rfl
      have h' := norm_sub_le (⨍ y in closedBall z ρ, f y ∂μ.restrict Ω)
        ((⨍ y in closedBall z ρ, f y ∂μ.restrict Ω) - preciseRepresentative (μ.restrict Ω) f z)
      rw [sub_sub_cancel] at h'
      have hρα : ρ ^ (-(α : ℝ)) * ρ ^ (α : ℝ) = 1 := by
        rw [← Real.rpow_add hρ, neg_add_cancel, Real.rpow_zero]
      calc _ ≤ _ := h'
        _ ≤ B + C * (M * ρ ^ (α : ℝ)) := add_le_add (havg z hz) h
        _ = _ := by rw [add_mul, mul_assoc B, hρα]; ring
    have hρd : ρ ^ (α : ℝ) ≤ 2 ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
      rw [← Real.mul_rpow zero_le_two dist_nonneg]
      exact Real.rpow_le_rpow hρ.le hd.le hα'.le
    calc dist (preciseRepresentative (μ.restrict Ω) f x) (preciseRepresentative (μ.restrict Ω) f y)
        ≤ ‖preciseRepresentative (μ.restrict Ω) f x‖ +
            ‖preciseRepresentative (μ.restrict Ω) f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * ((C * M + B * ρ ^ (-(α : ℝ))) * ρ ^ (α : ℝ)) := by
          linarith [hbound x hx, hbound y hy]
      _ ≤ 2 * ((C * M + B * ρ ^ (-(α : ℝ))) * (2 ^ (α : ℝ) * dist x y ^ (α : ℝ))) := by gcongr
      _ = _ := by ring


end Domain

/-! ### Morrey decay from Campanato decay on a set with the measure density property -/

section MorreyDecay

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Set E} {c : ℝ≥0} {z : E}

section NormedSpace

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}

/-- **Mean oscillation from a bound on the square mean oscillation.** Let `c > 0`, let `Ω` have
density at least `c` in `closedBall z t`, and let `∫_{B(z, t) ∩ Ω} ‖g - g_t‖² ≤ X`, where `g_t` is
the average of `g` over `ball z t ∩ Ω`. Then the mean oscillation of `g` on `closedBall z t` for
`μ.restrict Ω` is at most `√(X / (c μ(B(z, t))))`. -/
theorem setAverage_closedBall_restrict_norm_sub_le_sqrt_of_setIntegral_le {t X : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hd : (c : ℝ≥0∞) * μ (closedBall z t) ≤ μ (closedBall z t ∩ Ω))
    (hg : MemLp g 2 (μ.restrict (ball z t ∩ Ω)))
    (hX : ∫ x in ball z t ∩ Ω, ‖g x - ⨍ y in ball z t ∩ Ω, g y ∂μ‖ ^ 2 ∂μ ≤ X) :
    ⨍ y in closedBall z t, ‖g y - ⨍ w in closedBall z t, g w ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
      √(X / (c * μ.real (ball z t))) := by
  rw [μ.restrict_restrict_closedBall_eq_restrict_ball_inter]
  set S := ball z t ∩ Ω
  have hS : μ S ≠ ⊤ := measure_ball_inter_ne_top
  have hdS : (c : ℝ) * μ.real (ball z t) ≤ μ.real S :=
    μ.mul_measureReal_ball_le_measureReal_ball_inter hd
  have hcB : 0 < (c : ℝ) * μ.real (ball z t) := mul_pos hc (measureReal_ball_pos μ z ht)
  -- Jensen's inequality.
  have hJ := sq_setAverage_norm_le_setAverage_norm_sq
    (hg.integrableOn_norm_sub_sq_of_subset subset_rfl hS (⨍ y in S, g y ∂μ))
  have hav : ⨍ x in S, ‖g x - ⨍ y in S, g y ∂μ‖ ^ 2 ∂μ =
      (∫ x in S, ‖g x - ⨍ y in S, g y ∂μ‖ ^ 2 ∂μ) / μ.real S := by
    rw [setAverage_eq, smul_eq_mul, inv_mul_eq_div]
  rw [hav] at hJ
  have hX0 : 0 ≤ X := (integral_nonneg fun _ => by positivity).trans hX
  refine Real.le_sqrt_of_sq_le (hJ.trans ?_)
  exact (div_le_div_of_nonneg_right hX (hcB.le.trans hdS)).trans
    (div_le_div_of_nonneg_left hX0 hcB hdS)

/-- **Mean oscillation from square mean oscillation.** Let `c > 0`, let `Ω` have density at least
`c` in `closedBall z t`, and let `∫_{B(z, t) ∩ Ω} ‖g - g_t‖² ≤ C V ((t / R)ⁿ (t / R)^{2κ})`, where
`g_t` is the average of `g` over `ball z t ∩ Ω`. Then the mean oscillation of `g` on
`closedBall z t` for `μ.restrict Ω` is at most `√(C V / (μ(B(z, R)) c)) R^{-κ} t^κ`. -/
theorem setAverage_closedBall_restrict_norm_sub_le {κ C V R t : ℝ} (hc : 0 < c)
    (hR : 0 < R) (ht : 0 < t)
    (hd : (c : ℝ≥0∞) * μ (closedBall z t) ≤ μ (closedBall z t ∩ Ω))
    (hg : MemLp g 2 (μ.restrict (ball z t ∩ Ω)))
    (hψ : ∫ x in ball z t ∩ Ω, ‖g x - ⨍ y in ball z t ∩ Ω, g y ∂μ‖ ^ 2 ∂μ ≤
      C * V * ((t / R) ^ finrank ℝ E * (t / R) ^ (2 * κ))) :
    ⨍ y in closedBall z t, ‖g y - ⨍ w in closedBall z t, g w ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
      √(C * (V / μ.real (ball z R)) / c) * R ^ (-κ) * t ^ κ := by
  have hB := measureReal_ball_pos μ z hR
  have h2κ : (t / R) ^ (2 * κ) = ((t / R) ^ κ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_two]
  have hrhs : √(C * (V / μ.real (ball z R)) / c) * R ^ (-κ) * t ^ κ =
      √(C * V * ((t / R) ^ finrank ℝ E * (t / R) ^ (2 * κ)) / (c * μ.real (ball z t))) := by
    have heq : C * V * ((t / R) ^ finrank ℝ E * ((t / R) ^ κ) ^ 2) /
        (c * ((t / R) ^ finrank ℝ E * μ.real (ball z R))) =
        C * (V / μ.real (ball z R)) / c * ((t / R) ^ κ) ^ 2 := by
      field_simp
    rw [mul_assoc, ← Real.div_rpow_eq_rpow_neg_mul_rpow ht.le hR,
      (div_eq_iff hB.ne').1 (μ.addHaar_real_ball_div_addHaar_real_ball z z hR ht), h2κ, heq,
      Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (by positivity)]
  rw [hrhs]
  exact setAverage_closedBall_restrict_norm_sub_le_sqrt_of_setIntegral_le hc ht hd hg hψ

/-- If `Ω` has density at least `c` in `closedBall z s`, `s ≤ R`, and `∫_{B(z, R) ∩ Ω} ‖g‖² ≤ V`,
then the average `g_s` of `g` over `ball z s ∩ Ω` satisfies `c (s / R)ⁿ μ(B(z, R)) ‖g_s‖² ≤ V`. -/
private lemma mul_sq_norm_setAverage_ball_inter_le {s R V : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hR : 0 < R) (hd : (c : ℝ≥0∞) * μ (closedBall z s) ≤ μ (closedBall z s ∩ Ω))
    (hg : MemLp g 2 (μ.restrict (ball z R ∩ Ω))) (hΦR : ∫ x in ball z R ∩ Ω, ‖g x‖ ^ 2 ∂μ ≤ V) :
    c * ((s / R) ^ finrank ℝ E * μ.real (ball z R)) * ‖⨍ y in ball z s ∩ Ω, g y ∂μ‖ ^ 2 ≤ V := by
  have hsub : ball z s ∩ Ω ⊆ ball z R ∩ Ω := inter_subset_inter_left _ (ball_subset_ball hsR)
  have h1 := (measureReal_mul_sq_norm_setAverage_le measure_ball_inter_ne_top
    (hg.mono_measure (Measure.restrict_mono hsub le_rfl))).trans
    ((setIntegral_mono_set ((hg.integrableOn_norm_sub_sq_of_subset subset_rfl
      measure_ball_inter_ne_top 0).congr
      (ae_of_all _ fun _ => by simp only [sub_zero])) (ae_of_all _ fun _ => by positivity)
      hsub.eventuallySubset).trans hΦR)
  have h2 := μ.mul_measureReal_ball_le_measureReal_ball_inter hd
  rw [(div_eq_iff (measureReal_ball_pos μ z hR).ne').1
    (μ.addHaar_real_ball_div_addHaar_real_ball z z hR hs)] at h2
  exact (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)).trans h1

/-- **Bounded averages from an `L²` bound.** Let `c > 0`, let `Ω` have density at least `c` in
`closedBall z t`, and let `S ⊇ ball z t ∩ Ω` have finite measure with `∫_S ‖g‖² ≤ Φ`. Then the
average of `g` over `closedBall z t` for `μ.restrict Ω` has norm at most
`√(Φ / (c μ(B(z, t))))`. -/
theorem norm_setAverage_closedBall_restrict_le_sqrt {S : Set E} {t Φ : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hd : (c : ℝ≥0∞) * μ (closedBall z t) ≤ μ (closedBall z t ∩ Ω))
    (hS : ball z t ∩ Ω ⊆ S) (hSfin : μ S ≠ ⊤) (hg : MemLp g 2 (μ.restrict S))
    (hΦ : ∫ y in S, ‖g y‖ ^ 2 ∂μ ≤ Φ) :
    ‖⨍ y in closedBall z t, g y ∂μ.restrict Ω‖ ≤ √(Φ / (c * μ.real (ball z t))) := by
  rw [μ.restrict_restrict_closedBall_eq_restrict_ball_inter]
  have h1 := measureReal_mul_sq_norm_setAverage_le measure_ball_inter_ne_top
    (hg.mono_measure (Measure.restrict_mono hS le_rfl))
  have h2 : ∫ y in ball z t ∩ Ω, ‖g y‖ ^ 2 ∂μ ≤ Φ :=
    (setIntegral_mono_set (by
        simpa only [sub_zero] using hg.integrableOn_norm_sub_sq_of_subset subset_rfl hSfin 0)
      (ae_of_all _ fun _ => by positivity) hS.eventuallySubset).trans hΦ
  have h0 : 0 < (c : ℝ) * μ.real (ball z t) := mul_pos hc (measureReal_ball_pos μ z ht)
  have hΦ0 : 0 ≤ Φ := (integral_nonneg fun _ => by positivity).trans hΦ
  rw [Real.le_sqrt (norm_nonneg _) (div_nonneg hΦ0 h0.le), le_div_iff₀ h0, mul_comm]
  exact (mul_le_mul_of_nonneg_right (μ.mul_measureReal_ball_le_measureReal_ball_inter hd)
    (sq_nonneg _)).trans (h1.trans h2)

end NormedSpace

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {g : E → F}

/-- **Mean oscillation from the distance to a constant.** Let `c > 0`, let `Ω` have density at
least `c` in `closedBall x t`, and let `D ⊇ ball x t ∩ Ω`. For every constant `p`, the mean
oscillation of `g` on `closedBall x t` for `μ.restrict Ω` is at most
`√(∫_D ‖g - p‖² / (c μ(B(x, t))))`. So a square mean distance to a constant on a larger set, such
as a ball with another centre, bounds the mean oscillation on a smaller ball. -/
theorem setAverage_closedBall_restrict_norm_sub_le_sqrt {D : Set E} {x : E} {t : ℝ} {p : F}
    (hc : 0 < c) (ht : 0 < t)
    (hd : (c : ℝ≥0∞) * μ (closedBall x t) ≤ μ (closedBall x t ∩ Ω))
    (hD : ball x t ∩ Ω ⊆ D) (hg : MemLp g 2 (μ.restrict (ball x t ∩ Ω)))
    (hgp : IntegrableOn (fun y => ‖g y - p‖ ^ 2) D μ) :
    ⨍ y in closedBall x t, ‖g y - ⨍ w in closedBall x t, g w ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
      √((∫ y in D, ‖g y - p‖ ^ 2 ∂μ) / (c * μ.real (ball x t))) := by
  refine setAverage_closedBall_restrict_norm_sub_le_sqrt_of_setIntegral_le hc ht hd hg ?_
  exact (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_inter_ne_top
    (hg.integrableOn_of_subset one_le_two subset_rfl measure_ball_inter_ne_top)
      (hgp.mono_set hD)).trans
    (setIntegral_mono_set hgp (ae_of_all _ fun _ => by positivity) hD.eventuallySubset)

/-- **Bounded averages from Campanato decay.** Let `κ > 0`, `θ ∈ (0, 1]` and `c > 0`. Let `Ω` have
density at least `c` in the closed balls `closedBall z t`, `0 < t ≤ θ R`, let `g` be square
integrable on `ball z R ∩ Ω` with `∫_{B(z, R) ∩ Ω} ‖g‖² ≤ V`, and let
`∫_{B(z, t) ∩ Ω} ‖g - g_t‖² ≤ C₂ V (t / R)^{n+2κ}` for `0 < t ≤ θ R`, where `g_t` is the average of
`g` over `ball z t ∩ Ω` and `n` is the dimension. Then for `0 < t ≤ θ R`,
`‖g_t‖² ≤ (2 / (c θⁿ) + 2 c'² C₂ / c) V / μ(B(z, R))`, where `c' = 2ⁿ / (c (1 - 2^{-κ}))` is the
constant of Campanato's estimate
(`TauCeti.MeasureTheory.norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le`). -/
private lemma sq_norm_setAverage_ball_inter_le {κ θ C₂ R V t : ℝ} (hκ : 0 < κ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hC₂ : 0 ≤ C₂) (hc : 0 < c)
    (hdens : ∀ t, 0 < t → t ≤ θ * R →
      (c : ℝ≥0∞) * μ (closedBall z t) ≤ μ (closedBall z t ∩ Ω))
    (hg : MemLp g 2 (μ.restrict (ball z R ∩ Ω))) (hR : 0 < R)
    (hΦR : ∫ x in ball z R ∩ Ω, ‖g x‖ ^ 2 ∂μ ≤ V)
    (hψ : ∀ t, 0 < t → t ≤ θ * R →
      ∫ x in ball z t ∩ Ω, ‖g x - ⨍ y in ball z t ∩ Ω, g y ∂μ‖ ^ 2 ∂μ ≤
        C₂ * V * ((t / R) ^ finrank ℝ E * (t / R) ^ (2 * κ)))
    (ht : 0 < t) (htθ : t ≤ θ * R) :
    ‖⨍ y in ball z t ∩ Ω, g y ∂μ‖ ^ 2 ≤
      (2 / (c * θ ^ finrank ℝ E) + 2 * (2 ^ finrank ℝ E / (c * (1 - 2 ^ (-κ)))) ^ 2 * (C₂ / c)) *
        (V / μ.real (ball z R)) := by
  set cc : ℝ := 2 ^ finrank ℝ E / (c * (1 - 2 ^ (-κ)))
  set W := V / μ.real (ball z R)
  have hB := measureReal_ball_pos μ z hR
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hθR0 : 0 < θ * R := ht.trans_le htθ
  have hV0 : 0 ≤ V := (integral_nonneg fun _ => by positivity).trans hΦR
  have hcc : 0 ≤ cc := div_nonneg (by positivity) (mul_nonneg c.property
    (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hκ))).le)
  have hsub : ∀ r ≤ R, ball z r ∩ Ω ⊆ ball z R ∩ Ω := fun r hr =>
    inter_subset_inter_left _ (ball_subset_ball hr)
  have hgr : ∀ r ≤ R, MemLp g 2 (μ.restrict (ball z r ∩ Ω)) := fun r hr =>
    hg.mono_measure (Measure.restrict_mono (hsub r hr) le_rfl)
  -- By Campanato's estimate, the averages stay close to the average at radius `θ R`.
  have hcamp := norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le (μ := μ) (Ω := Ω)
    (f := g) (M := √(C₂ * W / c) * R ^ (-κ)) hκ hc
    (by rw [IntegrableOn, μ.restrict_restrict_closedBall_eq_restrict_ball_inter]
        exact (hgr _ hθR).integrableOn_of_subset one_le_two subset_rfl measure_ball_inter_ne_top)
    hdens
    (fun r hr hrθ => setAverage_closedBall_restrict_norm_sub_le hc hR hr
      (hdens r hr hrθ) (hgr r (hrθ.trans hθR)) (hψ r hr hrθ)) ht htθ le_rfl
  simp only [μ.restrict_restrict_closedBall_eq_restrict_ball_inter] at hcamp
  have hθκ : R ^ (-κ) * (θ * R) ^ κ ≤ 1 := by
    rw [← Real.div_rpow_eq_rpow_neg_mul_rpow hθR0.le hR]
    exact Real.rpow_le_one (by positivity) ((div_le_one hR).2 hθR) hκ.le
  have hd : ‖(⨍ y in ball z t ∩ Ω, g y ∂μ) - ⨍ y in ball z (θ * R) ∩ Ω, g y ∂μ‖ ≤
      cc * √(C₂ * W / c) := hcamp.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Real.sqrt_nonneg _) hθκ) hcc)
  -- The average at radius `θ R` is controlled by `∫_{B(z, R) ∩ Ω} ‖g‖² ≤ V`.
  have hmθ : ‖⨍ y in ball z (θ * R) ∩ Ω, g y ∂μ‖ ^ 2 ≤ W / (c * θ ^ finrank ℝ E) := by
    have h := mul_sq_norm_setAverage_ball_inter_le hθR0 hθR hR (hdens _ hθR0 le_rfl) hg hΦR
    rw [mul_div_cancel_right₀ θ hR.ne'] at h
    rw [div_div, le_div_iff₀ (by positivity)]
    exact (le_of_eq (by ring)).trans h
  have hsq : (cc * √(C₂ * W / c)) ^ 2 = cc ^ 2 * (C₂ / c) * W := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hmt := norm_le_norm_add_norm_sub' (⨍ y in ball z t ∩ Ω, g y ∂μ)
    (⨍ y in ball z (θ * R) ∩ Ω, g y ∂μ)
  calc _ ≤ (‖⨍ y in ball z (θ * R) ∩ Ω, g y ∂μ‖ + cc * √(C₂ * W / c)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    _ ≤ 2 * ‖⨍ y in ball z (θ * R) ∩ Ω, g y ∂μ‖ ^ 2 + 2 * (cc * √(C₂ * W / c)) ^ 2 :=
        add_sq_le.trans_eq (mul_add _ _ _)
    _ ≤ 2 * (W / (c * θ ^ finrank ℝ E)) + 2 * (cc ^ 2 * (C₂ / c) * W) := by rw [hsq]; gcongr
    _ = _ := by ring

/-- **Morrey decay from Campanato decay, on a set with the measure density property.** Let
`κ > 0`, `θ ∈ (0, 1]`, `C₂ ≥ 0` and `c > 0`, and let `n` be the dimension. There is `C₃`,
depending only on `n`, `κ`, `θ`, `C₂` and `c`, such that the following holds. Let `Ω` have density
at least `c` in the closed balls `closedBall z t`, `0 < t ≤ θ R`, that is
`c μ(B(z, t)) ≤ μ(B(z, t) ∩ Ω)`, let `g` be square integrable on `ball z R ∩ Ω` with
`∫_{B(z, R) ∩ Ω} ‖g‖² ≤ V`, and let `∫_{B(z, t) ∩ Ω} ‖g - g_t‖² ≤ C₂ V (t / R)^{n+2κ}` for
`0 < t ≤ θ R`, where `g_t` is the average of `g` over `ball z t ∩ Ω`. Then

`∫_{B(z, t) ∩ Ω} ‖g‖² ≤ C₃ V (t / R)ⁿ` for `0 < t ≤ θ R`.

By Campanato's estimate the averages `g_t` stay bounded, so the mass of `g` decays like the
volume of the balls. This is the step from Campanato decay to Morrey decay with the full exponent
in Campanato's approach to the Schauder estimates, both in the interior (`Ω = univ`, `c = 1`) and
at a flat boundary (`Ω` a half-space, `c = 1 / 2`). -/
theorem exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow {κ θ C₂ : ℝ} (hκ : 0 < κ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC₂ : 0 ≤ C₂) (hc : 0 < c) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ {Ω : Set E} {g : E → F} {z : E} {R V : ℝ},
      (∀ t, 0 < t → t ≤ θ * R → (c : ℝ≥0∞) * μ (closedBall z t) ≤ μ (closedBall z t ∩ Ω)) →
      MemLp g 2 (μ.restrict (ball z R ∩ Ω)) → 0 < R → ∫ x in ball z R ∩ Ω, ‖g x‖ ^ 2 ∂μ ≤ V →
      (∀ t, 0 < t → t ≤ θ * R →
        ∫ x in ball z t ∩ Ω, ‖g x - ⨍ y in ball z t ∩ Ω, g y ∂μ‖ ^ 2 ∂μ ≤
          C₂ * V * ((t / R) ^ finrank ℝ E * (t / R) ^ (2 * κ))) →
      ∀ t, 0 < t → t ≤ θ * R →
        ∫ x in ball z t ∩ Ω, ‖g x‖ ^ 2 ∂μ ≤ C₃ * V * (t / R) ^ finrank ℝ E := by
  set K : ℝ := 2 / (c * θ ^ finrank ℝ E) +
    2 * (2 ^ finrank ℝ E / (c * (1 - 2 ^ (-κ)))) ^ 2 * (C₂ / c)
  refine ⟨C₂ + K, by positivity, ?_⟩
  intro Ω g z R V hdens hg hR hΦR hψ t ht htθ
  have hB := measureReal_ball_pos μ z hR
  have htR : t ≤ R := htθ.trans (mul_le_of_le_one_left hR.le hθ1)
  have hV0 : 0 ≤ V := (integral_nonneg fun _ => by positivity).trans hΦR
  have hfin : μ (ball z t ∩ Ω) ≠ ⊤ := measure_ball_inter_ne_top
  have hgt : MemLp g 2 (μ.restrict (ball z t ∩ Ω)) :=
    hg.mono_measure
      (Measure.restrict_mono (inter_subset_inter_left _ (ball_subset_ball htR)) le_rfl)
  have hm := sq_norm_setAverage_ball_inter_le hκ hθ hθ1 hC₂ hc hdens hg hR hΦR hψ ht htθ
  -- Split `∫_{B(z, t) ∩ Ω} ‖g‖²` into the square mean oscillation and the squared average.
  have hsplit := setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add hfin
    (hgt.integrableOn_of_subset one_le_two subset_rfl hfin)
    (hgt.integrableOn_norm_sub_sq_of_subset subset_rfl hfin 0)
  simp only [sub_zero] at hsplit
  have hosc : C₂ * V * ((t / R) ^ finrank ℝ E * (t / R) ^ (2 * κ)) ≤
      C₂ * V * (t / R) ^ finrank ℝ E :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one (by positivity) ((div_le_one hR).2 htR) (by positivity))) (by positivity)
  have hvol : μ.real (ball z t ∩ Ω) ≤ (t / R) ^ finrank ℝ E * μ.real (ball z R) :=
    (measureReal_mono inter_subset_left measure_ball_lt_top.ne).trans_eq
      ((div_eq_iff hB.ne').1 (μ.addHaar_real_ball_div_addHaar_real_ball z z hR ht))
  rw [hsplit]
  calc _ ≤ C₂ * V * (t / R) ^ finrank ℝ E +
        (t / R) ^ finrank ℝ E * μ.real (ball z R) * (K * (V / μ.real (ball z R))) :=
      add_le_add ((hψ t ht htθ).trans hosc) (mul_le_mul hvol hm (sq_nonneg _) (by positivity))
    _ = (C₂ + K) * V * (t / R) ^ finrank ℝ E := by
      field_simp

end MorreyDecay

/-! ### Campanato's theorem on the whole space -/

section WholeSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {x : E} {M α ρ : ℝ}

/-- **Averages over concentric balls.** Let `α > 0`. If `f` is integrable on `closedBall x ρ`
and its mean oscillation on `closedBall x r` is at most `M r^α` for `0 < r ≤ ρ`, then the averages
of `f` over `closedBall x ε` and `closedBall x r`, `0 < ε ≤ r ≤ ρ`, differ by at most
`2ⁿ / (1 - 2^(-α)) · M r^α`, where `n` is the dimension. The proof telescopes over dyadic
radii. -/
theorem norm_setAverage_closedBall_sub_setAverage_closedBall_le (hα : 0 < α)
    (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α)
    {ε r : ℝ} (hε : 0 < ε) (hεr : ε ≤ r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x ε, f y ∂μ) - ⨍ y in closedBall x r, f y ∂μ‖ ≤
      2 ^ finrank ℝ E / (1 - 2 ^ (-α)) * (M * r ^ α) := by
  simpa using norm_setAverage_closedBall_restrict_sub_setAverage_closedBall_le (Ω := univ) (c := 1)
    hα one_pos (by simpa using hf) (fun _ _ _ ↦ by simp) (by simpa using hosc) hε hεr hrρ

/-- **Mean oscillation decay gives convergence of the averages.** Let `α > 0` and `ρ > 0`. If
the mean oscillation of `f` on `closedBall x r` is at most `M r^α` for `0 < r ≤ ρ`, then the
averages of `f` over the closed balls around `x` converge to the precise representative of `f`
at `x`. (If `f` is integrable on no ball around `x`, all the averages are `0` by convention.) -/
theorem tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le
    (hα : 0 < α) (hρ : 0 < ρ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α) :
    Tendsto (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)) := by
  simpa using
    tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_setAverage_norm_sub_le
      (Ω := univ) (c := 1) hα hρ one_pos (fun _ _ _ ↦ by simp) (by simpa using hosc)

/-- **The rate of convergence of the averages.** Let `α > 0`. If `f` is integrable on
`closedBall x ρ` and its mean oscillation on `closedBall x r` is at most `M r^α` for
`0 < r ≤ ρ`, then for `0 < r ≤ ρ` the average of `f` over `closedBall x r` lies within
`2ⁿ / (1 - 2^(-α)) · M r^α` of the precise representative of `f` at `x`, where `n` is the
dimension. -/
theorem norm_setAverage_closedBall_sub_preciseRepresentative_le (hα : 0 < α)
    (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x r, f y ∂μ) - preciseRepresentative μ f x‖ ≤
      2 ^ finrank ℝ E / (1 - 2 ^ (-α)) * (M * r ^ α) := by
  simpa using norm_setAverage_closedBall_restrict_sub_preciseRepresentative_le (Ω := univ)
    (c := 1) hα one_pos (by simpa using hf) (fun _ _ _ ↦ by simp) (by simpa using hosc) hr hrρ

/-- **The local Campanato estimate.** Let `α > 0` and `d = dist x y`. If `f` has mean oscillation
at most `M r^α` on `closedBall x r` for `0 < r ≤ 2 d` and on `closedBall y r` for `0 < r ≤ d`,
and is integrable on `closedBall x (2 d)`, then the precise representatives of `f` at `x`
and `y` differ by at most `2 · 2^α · 2ⁿ / (1 - 2^(-α)) · M d^α`, where `n` is the dimension. -/
theorem dist_preciseRepresentative_le_of_setAverage_norm_sub_le {y : E}
    (hα : 0 < α) (hf : IntegrableOn f (closedBall x (2 * dist x y)) μ)
    (hoscx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      ⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w ∂μ‖ ∂μ ≤ M * r ^ α)
    (hoscy : ∀ r, 0 < r → r ≤ dist x y →
      ⨍ z in closedBall y r, ‖f z - ⨍ w in closedBall y r, f w ∂μ‖ ∂μ ≤ M * r ^ α) :
    dist (preciseRepresentative μ f x) (preciseRepresentative μ f y) ≤
      2 * 2 ^ α * (2 ^ finrank ℝ E / (1 - 2 ^ (-α))) * (M * dist x y ^ α) := by
  simpa using dist_preciseRepresentative_restrict_le_of_setAverage_norm_sub_le (Ω := univ)
    (c := 1) hα one_pos (by simpa using hf) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (by simpa using hoscx) (by simpa using hoscy)

/-- **Campanato's theorem on a set, below a fixed scale.** Let `α > 0` and `ρ > 0`. Suppose that
for every `x ∈ S`, `f` is integrable on `closedBall x ρ`, has mean oscillation at most `M r^α` on
`closedBall x r` for `0 < r ≤ ρ`, and the norm of its average over `closedBall x ρ` is at most
`B`. Then the precise representative of `f` is `α`-Hölder continuous on `S`, with constant
`2 · 2^α · (2ⁿ / (1 - 2^(-α)) · M + B ρ^(-α))`, where `n` is the dimension. -/
theorem holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le {α : ℝ≥0} {S : Set E}
    {B : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hf : ∀ x ∈ S, IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ x ∈ S, ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ (α : ℝ))
    (havg : ∀ x ∈ S, ‖⨍ y in closedBall x ρ, f y ∂μ‖ ≤ B) :
    HolderOnWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ))) * M + B * ρ ^ (-(α : ℝ))))) α
      (preciseRepresentative μ f) S := by
  simpa using holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le_of_norm_le
    (Ω := univ) (c := 1) hα one_pos hρ (fun _ _ _ _ _ ↦ by simp) (by simpa using hf)
    (by simpa using hosc) (by simpa using havg)

/-- **Campanato's theorem.** Let `α > 0`, and let `f` be locally integrable, with mean oscillation
on every closed ball of radius `r > 0` at most `M r^α`. Then the precise representative of `f`
is `α`-Hölder continuous, with constant `2 · 2^α · 2ⁿ / (1 - 2^(-α)) · M`, where `n` is the
dimension. It agrees with `f` almost everywhere
(`TauCeti.MeasureTheory.ae_eq_preciseRepresentative`). -/
theorem holderWith_preciseRepresentative_of_setAverage_norm_sub_le
    {α M : ℝ≥0} (hα : 0 < α) (hf : LocallyIntegrable f μ)
    (hosc : ∀ x r, 0 < r →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ (α : ℝ)) :
    HolderWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ))))) * M) α (preciseRepresentative μ f) := by
  have hα' : (0 : ℝ) < α := hα
  have hC : (0 : ℝ) ≤ 2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ)))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (one_sub_two_rpow_neg_pos hα').le)
  refine holderOnWith_univ.1 <| HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hC, mul_assoc]
  exact dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα'
    (hf.integrableOn_isCompact (isCompact_closedBall _ _)) (fun r hr _ ↦ hosc x r hr)
    (fun r hr _ ↦ hosc y r hr)

/-- **Campanato's characterization of Hölder continuity.** Let `α > 0`. A locally integrable
function agrees almost everywhere with an `α`-Hölder continuous function if and only if its mean
oscillation on closed balls of radius `r > 0` is at most `M r^α` for some constant `M`. -/
theorem exists_holderWith_ae_eq_iff_forall_setAverage_norm_sub_le {α : ℝ≥0}
    (hα : 0 < α) (hf : LocallyIntegrable f μ) :
    (∃ (K : ℝ≥0) (g : E → F), HolderWith K α g ∧ f =ᵐ[μ] g) ↔
      ∃ M : ℝ≥0, ∀ x r, 0 < r →
        ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ (α : ℝ) := by
  constructor
  · rintro ⟨K, g, hg, hfg⟩
    refine ⟨K * 2 ^ (α : ℝ), fun x r hr ↦ ?_⟩
    -- The averages of `f` and `g` over every ball agree.
    have havg : ⨍ z in closedBall x r, f z ∂μ = ⨍ z in closedBall x r, g z ∂μ :=
      average_congr (ae_restrict_of_ae hfg)
    rw [havg, average_congr (ae_restrict_of_ae (hfg.mono fun y hy ↦ by rw [hy]))]
    refine (setAverage_norm_sub_setAverage_le_of_holderOnWith hα
      (measure_closedBall_pos μ x hr).ne' (hg.holderOnWith _)).trans_eq ?_
    push_cast
    rw [Real.mul_rpow zero_le_two hr.le]
    ring
  · rintro ⟨M, hM⟩
    exact ⟨_, _, holderWith_preciseRepresentative_of_setAverage_norm_sub_le hα hf hM,
      ae_eq_preciseRepresentative hf⟩

end WholeSpace

/-! ### Campanato spaces -/

section Seminorm

variable {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {μ : Measure X} {Ω : Set X} {p lam : ℝ} {f g : X → F} {x : X} {r : ℝ}

variable (μ Ω p lam f) in
/-- The `p`-th power `[f]_{p,λ}^p` of the **Campanato seminorm** of `f` on `Ω` with exponents `p`
and `λ`: the supremum, over the points `x ∈ Ω` and the radii `r > 0`, of

`r^(-λ) ∫_{B(x, r) ∩ Ω} ‖f - f_{x,r}‖^p`, where `f_{x,r} = ⨍_{B(x, r) ∩ Ω} f`

and `B(x, r)` is the closed ball, both the integral and the average being taken for
`μ.restrict Ω`. Following Giaquinta–Martinazzi, no `p`-th root is taken, so for `p > 0` this
quantity scales by `|a|^p`, not `|a|`, when `f` is multiplied by `a`; the Campanato seminorm
itself is its `p`-th root. The **Campanato space** `𝓛^{p,λ}(Ω)` consists of the functions for
which it is finite. -/
def campanatoSeminormPow : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (r ^ (-lam)) *
    ∫⁻ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ₑ ^ p ∂μ.restrict Ω

/-- The defining formula of `campanatoSeminormPow`, the supremum of the rescaled `p`-th power mean
oscillations over the points of `Ω` and the positive radii. -/
theorem campanatoSeminormPow_def :
    campanatoSeminormPow μ Ω p lam f = ⨆ x ∈ Ω, ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (r ^ (-lam)) *
      ∫⁻ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ₑ ^ p
        ∂μ.restrict Ω := by
  simp only [campanatoSeminormPow]

/-- The Campanato seminorm is at most `C` exactly when each of the quantities of which it is the
supremum is. -/
theorem campanatoSeminormPow_le_iff {C : ℝ≥0∞} :
    campanatoSeminormPow μ Ω p lam f ≤ C ↔ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ (-lam)) * ∫⁻ y in closedBall x r,
        ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ₑ ^ p ∂μ.restrict Ω ≤ C := by
  simp only [campanatoSeminormPow, iSup_le_iff]

/-- The quantity attached to a point `x ∈ Ω` and a radius `r > 0` is at most the Campanato
seminorm. -/
theorem le_campanatoSeminormPow (hx : x ∈ Ω) (hr : 0 < r) :
    ENNReal.ofReal (r ^ (-lam)) * ∫⁻ y in closedBall x r,
      ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ₑ ^ p ∂μ.restrict Ω ≤
        campanatoSeminormPow μ Ω p lam f :=
  campanatoSeminormPow_le_iff.1 le_rfl x hx r hr

/-- The Campanato seminorm only depends on the almost-everywhere class of `f` on `Ω`. -/
theorem campanatoSeminormPow_congr_ae (h : f =ᵐ[μ.restrict Ω] g) :
    campanatoSeminormPow μ Ω p lam f = campanatoSeminormPow μ Ω p lam g := by
  simp only [campanatoSeminormPow]
  refine iSup_congr fun x ↦ iSup_congr fun _ ↦ iSup_congr fun r ↦ iSup_congr fun _ ↦ ?_
  rw [average_congr (ae_restrict_of_ae h)]
  congr 1
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with y hy
  rw [hy]

/-- The Campanato seminorm on the empty set vanishes. -/
@[simp]
theorem campanatoSeminormPow_empty : campanatoSeminormPow μ ∅ p lam f = 0 := by
  simp [campanatoSeminormPow]

/-- For `p > 0`, the Campanato seminorm of the zero function vanishes. -/
@[simp]
theorem campanatoSeminormPow_zero (hp : 0 < p) :
    campanatoSeminormPow μ Ω p lam (0 : X → F) = 0 := by
  simp [campanatoSeminormPow, ENNReal.zero_rpow_of_pos hp]

/-- For `p > 0`, the Campanato seminorm of a constant function vanishes: on every ball the function
equals its average. -/
@[simp]
theorem campanatoSeminormPow_const [CompleteSpace F] [ProperSpace X] [IsFiniteMeasureOnCompacts μ]
    (hp : 0 < p) (c : F) : campanatoSeminormPow μ Ω p lam (fun _ ↦ c) = 0 := by
  refine le_antisymm (campanatoSeminormPow_le_iff.2 fun x _ r _ ↦ ?_) (zero_le)
  by_cases h0 : μ.restrict Ω (closedBall x r) = 0
  · rw [setLIntegral_measure_zero _ _ h0, mul_zero]
  · have hfin : μ.restrict Ω (closedBall x r) ≠ ⊤ :=
      ((Measure.restrict_apply_le _ _).trans_lt measure_closedBall_lt_top).ne
    rw [setAverage_const h0 hfin, sub_self, eNorm_zero, ENNReal.zero_rpow_of_pos hp, lintegral_zero,
      mul_zero]

end Seminorm

section Characterization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {Ω : Set E} {c : ℝ≥0}
  {p : ℝ} {x : E}

/-- The exponent bookkeeping behind `λ = n + p α`:
`r^(-(n + p α)) (K (2 r)^α)^p rⁿ = (2^α K)^p` for `r > 0`. -/
private lemma rpow_neg_add_mul_mul_rpow_mul_pow_eq {n : ℕ} {K α : ℝ≥0} {r : ℝ} (hr : 0 < r) :
    r ^ (-((n : ℝ) + p * α)) * ((K * (2 * r) ^ (α : ℝ)) ^ p * r ^ n) =
      (2 ^ (α : ℝ) * K) ^ p := by
  have hexp : -((n : ℝ) + p * α) + ((α : ℝ) * p + n) = 0 := by ring
  have h2r : (K : ℝ) * (2 * r) ^ (α : ℝ) = 2 ^ (α : ℝ) * K * r ^ (α : ℝ) := by
    rw [Real.mul_rpow zero_le_two hr.le]
    ring
  rw [h2r, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr.le,
    ← Real.rpow_natCast r]
  calc _ = (2 ^ (α : ℝ) * K) ^ p * r ^ (-((n : ℝ) + p * α) + ((α : ℝ) * p + n)) := by
        rw [Real.rpow_add hr, Real.rpow_add hr]
        ring
    _ = (2 ^ (α : ℝ) * K) ^ p := by rw [hexp, Real.rpow_zero, mul_one]

/-- **Hölder functions lie in the Campanato space.** If `f` is `α`-Hölder continuous on a
null-measurable set `Ω` with constant `K`, then for `p ≥ 0` the `p`-th power `[f]_{p,λ}^p` of its
Campanato seminorm with exponents `p` and `λ = n + p α` is at most `(2^α K)^p μ(B(0, 1))`, where
`n` is the dimension. -/
theorem campanatoSeminormPow_le_of_holderOnWith {K α : ℝ≥0} (hp : 0 ≤ p)
    (hΩ : NullMeasurableSet Ω μ) (hf : HolderOnWith K α f Ω)
    (hfm : AEStronglyMeasurable f (μ.restrict Ω)) :
    campanatoSeminormPow μ Ω p (finrank ℝ E + p * α) f ≤
      ENNReal.ofReal ((2 ^ (α : ℝ) * K) ^ p) * μ (closedBall 0 1) := by
  refine campanatoSeminormPow_le_iff.2 fun x hx r hr ↦ ?_
  have hL : (0 : ℝ) ≤ K * (2 * r) ^ (α : ℝ) := by positivity
  calc ENNReal.ofReal (r ^ (-((finrank ℝ E : ℝ) + p * α))) *
        ∫⁻ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ₑ ^ p
          ∂μ.restrict Ω
      ≤ ENNReal.ofReal (r ^ (-((finrank ℝ E : ℝ) + p * α))) *
          (ENNReal.ofReal (K * (2 * r) ^ (α : ℝ)) ^ p * μ (closedBall x r)) := by
        gcongr
        calc ∫⁻ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ₑ ^ p
              ∂μ.restrict Ω
            ≤ ∫⁻ _ in closedBall x r, ENNReal.ofReal (K * (2 * r) ^ (α : ℝ)) ^ p
                ∂μ.restrict Ω := by
              refine lintegral_mono_ae ?_
              filter_upwards [ae_norm_sub_setAverage_le_of_holderOnWith hΩ hf hfm hx hr] with y hy
              rw [← ofReal_norm]
              gcongr
          _ ≤ ENNReal.ofReal (K * (2 * r) ^ (α : ℝ)) ^ p * μ (closedBall x r) := by
              rw [setLIntegral_const]
              exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ = ENNReal.ofReal ((2 ^ (α : ℝ) * K) ^ p) * μ (closedBall 0 1) := by
        rw [μ.addHaar_closedBall' x hr.le, ← rpow_neg_add_mul_mul_rpow_mul_pow_eq hr,
          ENNReal.ofReal_rpow_of_nonneg hL hp, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        ring

omit [CompleteSpace F] in
/-- **The Campanato seminorm bounds the mean oscillation.** If `Ω` has density at least `c > 0` in
`closedBall x r`, `x ∈ Ω`, and the `p`-th power `[f]_{p,λ}^p` of the Campanato seminorm of `f`
with exponents `p ≥ 1` and `λ = n + p α` is at most `M`, then the mean oscillation of `f` on
`closedBall x r` for `μ.restrict Ω` is at most `(M / (c μ(B(0, 1))))^(1/p) r^α`, where `n` is the
dimension. -/
theorem setAverage_norm_sub_le_of_campanatoSeminormPow_le {M : ℝ≥0} {α r : ℝ} (hp : 1 ≤ p)
    (hc : 0 < c) (hM : campanatoSeminormPow μ Ω p (finrank ℝ E + p * α) f ≤ M) (hx : x ∈ Ω)
    (hr : 0 < r) (hd : (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)) :
    ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
      (M / (c * μ.real (closedBall 0 1))) ^ p⁻¹ * r ^ α := by
  set a := ⨍ z in closedBall x r, f z ∂μ.restrict Ω
  set A := ⨍ y in closedBall x r, ‖f y - a‖ ∂μ.restrict Ω
  set ω := μ.real (closedBall (0 : E) 1)
  set n : ℝ := (finrank ℝ E : ℝ)
  have hp0 : 0 < p := one_pos.trans_le hp
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_closedBall_pos μ 0 one_pos).ne' measure_closedBall_lt_top.ne
  have hA : 0 ≤ A := average_nonneg fun _ ↦ norm_nonneg _
  -- Hölder's inequality on the ball.
  have h₁ : ENNReal.ofReal A ^ p ≤ (μ.restrict Ω (closedBall x r))⁻¹ *
      ∫⁻ y in closedBall x r, ‖f y - a‖ₑ ^ p ∂μ.restrict Ω := by
    have h := enorm_setAverage_rpow_le (mu := μ.restrict Ω) (s := closedBall x r)
      (f := fun y ↦ ‖f y - a‖) hp
    -- `A` abbreviates the average in `h`, which `set` did not abstract there.
    change ‖A‖ₑ ^ p ≤ _ at h
    simpa [Real.eNorm_of_nonneg hA, eNorm_norm] using h
  -- The Campanato seminorm bounds the integral.
  have h₂ : ∫⁻ y in closedBall x r, ‖f y - a‖ₑ ^ p ∂μ.restrict Ω ≤
      ENNReal.ofReal (r ^ (n + p * α)) * M := by
    have h := (le_campanatoSeminormPow hx hr).trans hM
    calc ∫⁻ y in closedBall x r, ‖f y - a‖ₑ ^ p ∂μ.restrict Ω
        = ENNReal.ofReal (r ^ (n + p * α)) * (ENNReal.ofReal (r ^ (-(n + p * α))) *
            ∫⁻ y in closedBall x r, ‖f y - a‖ₑ ^ p ∂μ.restrict Ω) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hr,
            add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (r ^ (n + p * α)) * M := by gcongr
  -- The density of `Ω` bounds the measure of the ball from below.
  have h₃ : ENNReal.ofReal (c * r ^ n * ω) ≤ μ.restrict Ω (closedBall x r) :=
    μ.ofReal_mul_rpow_mul_le_addHaar_restrict_closedBall x hr hd
  have hpos : (0 : ℝ) < c * r ^ n * ω := by positivity
  have h₄ : A ^ p ≤ (c * r ^ n * ω)⁻¹ * (r ^ (n + p * α) * M) := by
    have hX : ENNReal.ofReal ((c * r ^ n * ω)⁻¹ * (r ^ (n + p * α) * M)) =
        (ENNReal.ofReal (c * r ^ n * ω))⁻¹ * (ENNReal.ofReal (r ^ (n + p * α)) * M) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), ENNReal.ofReal_inv_of_pos hpos,
        ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hA hp0.le,
      hX]
    exact h₁.trans (mul_le_mul' (ENNReal.inv_le_inv.2 h₃) h₂)
  have h₅ : (c * r ^ n * ω)⁻¹ * (r ^ (n + p * α) * M) = M / (c * ω) * r ^ (p * α) := by
    rw [Real.rpow_add hr]
    field_simp
  rw [h₅] at h₄
  calc A = (A ^ p) ^ p⁻¹ := (Real.rpow_rpow_inv hA hp0.ne').symm
    _ ≤ (M / (c * ω) * r ^ (p * α)) ^ p⁻¹ := by gcongr
    _ = (M / (c * ω)) ^ p⁻¹ * r ^ α := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr.le, mul_comm p α,
          mul_assoc, mul_inv_cancel₀ hp0.ne', mul_one]

/-- **Campanato's characterization of Hölder continuity on a set with the measure density
property.** Let `α > 0`, `p ≥ 1` and `c > 0`, and let `Ω` be a null-measurable set with density
at least `c` in every closed ball centred in `Ω` of radius `r > 0` at most twice the diameter of
`Ω` (every radius, if `Ω` is unbounded): `c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)`. A function `f` locally
integrable for `μ.restrict Ω` agrees almost everywhere on `Ω` with a function that is `α`-Hölder
continuous on `Ω` if and only if it belongs to the Campanato space `𝓛^{p,λ}(Ω)` for
`λ = n + p α`, where `n` is the dimension. -/
theorem exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top {α : ℝ≥0}
    (hα : 0 < α) (hp : 1 ≤ p) (hc : 0 < c) (hΩ : NullMeasurableSet Ω μ)
    (hf : LocallyIntegrable f (μ.restrict Ω))
    (hdens : ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ 2 * ediam Ω →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)) :
    (∃ (K : ℝ≥0) (g : E → F), HolderOnWith K α g Ω ∧ f =ᵐ[μ.restrict Ω] g) ↔
      campanatoSeminormPow μ Ω p (finrank ℝ E + p * α) f ≠ ⊤ := by
  constructor
  · rintro ⟨K, g, hg, hfg⟩
    rw [campanatoSeminormPow_congr_ae hfg]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne)
      (campanatoSeminormPow_le_of_holderOnWith (zero_le_one.trans hp) hΩ hg
        (hf.aestronglyMeasurable.congr hfg))
  · intro hfin
    have hM : campanatoSeminormPow μ Ω p (finrank ℝ E + p * α) f ≤
        (campanatoSeminormPow μ Ω p (finrank ℝ E + p * α) f).toNNReal :=
      (ENNReal.coe_toNNReal hfin).ge
    refine ⟨_, _, holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le
      (M := Real.toNNReal (((campanatoSeminormPow μ Ω p (finrank ℝ E + p * α) f).toNNReal /
        (c * μ.real (closedBall (0 : E) 1))) ^ p⁻¹)) hα hc hf hdens fun x hx r hr hr' ↦ ?_,
      ae_eq_preciseRepresentative_of_hasBesicovitchCovering hf⟩
    rw [Real.coe_toNNReal _ (by positivity)]
    exact setAverage_norm_sub_le_of_campanatoSeminormPow_le hp hc hM hx hr (hdens x hx r hr hr')

/-- **Campanato spaces beyond `λ = n + p`.** Let `α > 1`, `p ≥ 1` and `c > 0`, and let `Ω` be a
preconnected open set with density at least `c` in every closed ball centred in `Ω` of radius
`r > 0` at most twice the diameter of `Ω` (every radius, if `Ω` is unbounded):
`c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)`. A function `f` locally integrable for `μ.restrict Ω` belongs to
the Campanato space `𝓛^{p,λ}(Ω)` for `λ = n + p α`, where `n` is the dimension, if and only if it
is almost everywhere constant on `Ω`. So Campanato's characterization
`exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top` carries information only for
`n < λ ≤ n + p`. -/
theorem exists_ae_eq_const_iff_campanatoSeminormPow_ne_top {α : ℝ≥0} (hα : 1 < α) (hp : 1 ≤ p)
    (hc : 0 < c) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hf : LocallyIntegrable f (μ.restrict Ω))
    (hdens : ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ 2 * ediam Ω →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)) :
    (∃ a : F, f =ᵐ[μ.restrict Ω] fun _ ↦ a) ↔
      campanatoSeminormPow μ Ω p (finrank ℝ E + p * α) f ≠ ⊤ := by
  constructor
  · rintro ⟨a, hfa⟩
    rw [campanatoSeminormPow_congr_ae hfa, campanatoSeminormPow_const (zero_lt_one.trans_le hp)]
    exact ENNReal.zero_ne_top
  · intro hfin
    obtain ⟨K, g, hg, hfg⟩ := (exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top
      (zero_lt_one.trans hα) hp hc hΩ.nullMeasurableSet hf hdens).2 hfin
    rcases Ω.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact ⟨0, by simp [Filter.EventuallyEq]⟩
    · refine ⟨g x₀, ?_⟩
      filter_upwards [hfg, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
      rw [hx, hg.eq_of_one_lt hα hΩ hΩc hxΩ hx₀]

end Characterization

end MeasureTheory

end TauCeti
