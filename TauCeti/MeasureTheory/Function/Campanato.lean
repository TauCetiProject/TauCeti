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
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
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
* `holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le`: **Campanato's
  theorem** on a domain with the measure density property.
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

/-- **The mean oscillation of a Hölder function.** If `f` is `α`-Hölder continuous on
`closedBall x r` with constant `K`, `α > 0`, and this ball has positive measure, then the mean
oscillation of `f` on the ball is at most `K (2 r)^α`. -/
theorem setAverage_norm_sub_setAverage_le_of_holderOnWith {K α : ℝ≥0} {r : ℝ} (hα : 0 < α)
    (hμ : μ (closedBall x r) ≠ 0) (hf : HolderOnWith K α f (closedBall x r)) :
    ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤
      K * (2 * r) ^ (α : ℝ) := by
  have hμ' : μ (closedBall x r) ≠ ⊤ := (isCompact_closedBall x r).measure_lt_top.ne
  have hcont := hf.continuousOn hα
  have hint : IntegrableOn f (closedBall x r) μ :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
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
  · exact (hcont.sub continuousOn_const).norm.integrableOn_compact (isCompact_closedBall _ _)

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
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hzy α.2) K.2)
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

/-- **Telescoping over dyadic radii.** If `Ω` has density at least `c > 0` in `closedBall x r` and
the mean oscillation of `f` on `closedBall x r` with respect to `μ.restrict Ω` is at most `M r^α`
for `0 < r ≤ ρ`, then the averages over `closedBall x ε` and `closedBall x r`, `0 < ε ≤ r ≤ ρ`,
differ by at most `2ⁿ / (c (1 - 2^(-α))) · M r^α`. -/
private lemma norm_setAverage_closedBall_sub_le (hα : 0 < α) (hc : 0 < c)
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
`μ.restrict Ω` at `x`. -/
theorem tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_setAverage_norm_sub_le
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
            (norm_setAverage_closedBall_sub_le hα hc hf hdens hosc ha.1 ha.2 hτρ.2)
            (norm_setAverage_closedBall_sub_le hα hc hf hdens hosc hb.1 hb.2 hτρ.2)
      _ < δ := by linarith
  obtain ⟨v, hv⟩ := CompleteSpace.complete hcauchy
  rwa [preciseRepresentative_eq_of_tendsto hv]

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
      (hr.trans_le hrρ) hc hf hdens hosc
  refine le_of_tendsto (tendsto_const_nhds.sub ht).norm ?_
  filter_upwards [Ioc_mem_nhdsGT hr] with ε hε
  rw [norm_sub_rev]
  exact norm_setAverage_closedBall_sub_le hα hc hf hdens hosc hε.1 hε.2 hrρ

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
    have hc' : (0 : ℝ) < c := hc
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
      (div_nonneg (by positivity) (mul_nonneg c.2 (one_sub_two_rpow_neg_pos hα').le))
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

end Domain

/-! ### Campanato's theorem on the whole space -/

section WholeSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {x : E} {M α ρ : ℝ}

/-- **Mean oscillation decay gives convergence of the averages.** Let `α > 0` and `ρ > 0`. If `f`
is integrable on `closedBall x ρ` and its mean oscillation on `closedBall x r` is at most `M r^α`
for `0 < r ≤ ρ`, then the averages of `f` over the closed balls around `x` converge to the
precise representative of `f` at `x`. -/
theorem tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le
    (hα : 0 < α) (hρ : 0 < ρ) (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α) :
    Tendsto (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)) := by
  simpa using
    tendsto_setAverage_closedBall_restrict_preciseRepresentative_of_setAverage_norm_sub_le
      (Ω := univ) (c := 1) hα hρ one_pos (by simpa using hf) (fun _ _ _ ↦ by simp)
      (by simpa using hosc)

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
  have hc' : (0 : ℝ) < c := hc
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_closedBall_pos μ 0 one_pos).ne' measure_closedBall_lt_top.ne
  have hA : 0 ≤ A := average_nonneg fun _ ↦ norm_nonneg _
  have hrn : 0 < r ^ n := Real.rpow_pos_of_pos hr _
  -- Hölder's inequality on the ball.
  have h₁ : ENNReal.ofReal A ^ p ≤ (μ.restrict Ω (closedBall x r))⁻¹ *
      ∫⁻ y in closedBall x r, ‖f y - a‖ₑ ^ p ∂μ.restrict Ω := by
    have h := enorm_setAverage_rpow_le (mu := μ.restrict Ω) (s := closedBall x r)
      (f := fun y ↦ ‖f y - a‖) hp
    -- `A` abbreviates the average in `h`, which `set` did not abstract there.
    change ‖A‖ₑ ^ p ≤ _ at h
    simpa [Real.enorm_of_nonneg hA, enorm_norm] using h
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

end Characterization

end MeasureTheory

end TauCeti
