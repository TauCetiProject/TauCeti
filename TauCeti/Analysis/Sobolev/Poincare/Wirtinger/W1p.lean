/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.WeakDeriv
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Poincaré–Wirtinger inequality on `W^{1,p}(Ω)`

Let `Ω` be a bounded convex open subset of a finite-dimensional real inner product space `E` of
dimension `n`, let `μ` be an additive Haar measure, and let `S ⊆ Ω` have positive measure.  This
file specializes `TauCeti.HasWeakFDerivOn.eLpNorm_sub_setAverage_le_of_convex` and its
consequences from `TauCeti.Analysis.Sobolev.Poincare.Wirtinger.WeakDeriv` to elements of
`W^{1,p}(Ω)` for `1 ≤ p ≤ ∞`:

`‖u - ⨍_S u‖_{Lᵖ(Ω)} ≤ μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S) * ‖∇u‖_{Lᵖ(Ω)}`,

with no measurability assumption on `S`.

## Reduction to weak derivatives

Every `u ∈ W^{1,p}(Ω)` has weak Fréchet derivative `x ↦ innerSL ℝ (W1p.gradient u x)`
(`TauCeti.W1p.hasWeakFDerivOn`), and `innerSL ℝ` is a linear isometry so `‖∇u‖_{Lᵖ(Ω)}` coincides
with the `Lᵖ` seminorm of the weak Fréchet derivative.  For finite `p`, the convex and ball
inequalities follow directly from the `HasWeakFDerivOn` bounds; since the constant does not depend
on `p`, the case `p = ∞` follows by applying the finite case at exponents `q < ∞` and letting
`q → ∞` (`TauCeti.tendsto_eLpNorm_atTop`).

## Main declarations

* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex`: the inequality on `W^{1,p}(Ω)`.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball`: the constant on a ball of radius `R`
  is `2 ^ (n + 1) * R`.
* `TauCeti.W1p.setIntegral_value_sub_setAverage_sq_le_of_ball_subset`: the same bound in `L²`,
  for a ball contained in `Ω`, with both sides written as integrals over the ball.
* `TauCeti.W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset`: the same bound in `L¹`,
  for a ball contained in `Ω` and any `u ∈ W^{1,p}(Ω)`.
* `TauCeti.W1p.exists_value_ae_eq_const_of_gradient_eq_zero`: on a preconnected `Ω`, a Sobolev
  function with vanishing weak gradient is almost everywhere constant.
* `TauCeti.W1p.exists_value_ae_eq_add_const_of_gradient_ae_eq`: on a preconnected `Ω`, a Sobolev
  function whose weak gradient agrees almost everywhere with `∇ q` for a `C¹` function `q` equals
  `q + c` almost everywhere.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16.
* L. C. Evans, *Partial Differential Equations*, Section 5.8.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {S : Set E}

omit [FiniteDimensional ℝ E] in
private theorem eLpNorm_innerSL_gradient {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : W1p mu Omega q) :
    eLpNorm (fun x ↦ innerSL ℝ (W1p.gradient u x)) q (mu.restrict Omega) = ‖W1p.gradient u‖ₑ := by
  rw [Lp.eNorm_def]
  exact eLpNorm_congr_norm_ae
    ((innerSL ℝ).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
    (Lp.aestronglyMeasurable _) (.of_forall fun x ↦ innerSL_apply_norm ℝ (W1p.gradient u x))

/-! ### The inequality on the whole domain -/

/-- **The Poincaré–Wirtinger inequality on `W^{1,p}(Ω)`.**  Let `Ω` be a bounded convex open set
in a finite-dimensional real inner product space of dimension `n`, and let `S ⊆ Ω` have positive
measure.  For `1 ≤ p ≤ ∞`, every `u ∈ W^{1,p}(Ω)` deviates from its mean over `S` by at most
`μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` times the `Lᵖ` norm of its weak gradient.  The constant
does not depend on `p`, so the case `p = ∞` is the limit of the finite exponents. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_of_convex
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ (Omega : Set E)) (hS0 : mu S ≠ 0) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) p (mu.restrict Omega) ≤
      ENNReal.ofReal (mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) / mu.real S) *
        ‖W1p.gradient u‖ₑ := by
  set C := ENNReal.ofReal
    (mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) / mu.real S)
  -- The inequality at every finite exponent follows from the `HasWeakFDerivOn` bound.
  have hfin (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ∞) (v : W1p mu Omega q) :
      eLpNorm (fun x ↦ W1p.value v x - ⨍ y in S, W1p.value v y ∂mu) q (mu.restrict Omega) ≤
        C * ‖W1p.gradient v‖ₑ := by
    have h := (W1p.hasWeakFDerivOn v).eLpNorm_sub_setAverage_le_of_convex
      hconv hb hS hS0 Fact.out hq
    rwa [eLpNorm_innerSL_gradient v] at h
  rcases ne_or_eq p ∞ with hp | rfl
  · exact hfin p hp u
  -- At `p = ∞`, lower `u` to the finite exponents `q ≥ 1` and let `q → ∞`.
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hle : ∀ᶠ q : ℝ≥0 in atTop,
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) q (mu.restrict Omega) ≤
        C * eLpNorm (W1p.gradient u) q (mu.restrict Omega) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
    have hval : W1p.value (W1p.ofExponentLE le_top u) =ᵐ[mu.restrict Omega] W1p.value u :=
      (W1p.coeFn_value_ofExponentLE (le_top : (q : ℝ≥0∞) ≤ ∞) u).eventuallyEq
    have havg : ⨍ y in S, W1p.value (W1p.ofExponentLE le_top u) y ∂mu =
        ⨍ y in S, W1p.value u y ∂mu := average_congr (ae_restrict_of_ae_restrict_of_subset hS hval)
    have h := hfin q ENNReal.coe_ne_top (W1p.ofExponentLE le_top u)
    rw [havg, Lp.eNorm_def,
      eLpNorm_congr_ae (W1p.coeFn_gradient_ofExponentLE _ u).eventuallyEq] at h
    exact (eLpNorm_congr_ae (hval.mono fun x hx ↦ by simp only [hx])).symm.trans_le h
  rw [Lp.eNorm_def]
  exact le_of_tendsto_of_tendsto tendsto_eLpNorm_atTop
    (ENNReal.Tendsto.const_mul tendsto_eLpNorm_atTop (Or.inr ENNReal.ofReal_ne_top)) hle

/-- **The Poincaré–Wirtinger inequality on a ball.**  On a ball of radius `R` the constant of
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex` is `2 ^ (n + 1) * R`: the deviation of
`u ∈ W^{1,p}(B(c, R))` from its mean over the ball is at most `2 ^ (n + 1) * R` times the `Lᵖ`
norm of its weak gradient.  The constant is proportional to `R`, as the scaling of both sides
forces. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball {c : E} {R : ℝ}
    (hOmega : (Omega : Set E) = ball c R) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in (Omega : Set E), W1p.value u y ∂mu) p
        (mu.restrict Omega) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * R) * ‖W1p.gradient u‖ₑ := by
  rcases ne_or_eq p ∞ with hp | rfl
  · have h := (W1p.hasWeakFDerivOn u).eLpNorm_sub_setAverage_ball_le
      (x := c) (r := R) hOmega.symm.subset Fact.out hp
    rwa [← hOmega, eLpNorm_innerSL_gradient u] at h
  rcases le_or_gt R 0 with hR | hR
  · -- The ball is empty, so the measure vanishes.
    have h0 : mu.restrict (Omega : Set E) = 0 := by
      rw [hOmega, Metric.ball_eq_empty.2 hR, Measure.restrict_empty]
    simp [h0]
  have hpos : mu (Omega : Set E) ≠ 0 := by
    rw [hOmega]
    exact (measure_ball_pos mu c hR).ne'
  have hconst : mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) /
      mu.real (Omega : Set E) ≤ 2 ^ (finrank ℝ E + 1) * R := by
    rw [hOmega]
    exact mu.addHaar_real_ball_mul_diam_ball_pow_div_le c hR
  refine (W1p.eLpNorm_value_sub_setAverage_le_of_convex (hOmega ▸ convex_ball c R)
    (hOmega ▸ Metric.isBounded_ball (x := c) (r := R)) subset_rfl hpos u).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl)

/-- **The Poincaré–Wirtinger inequality on a ball inside the domain, in `L²`.**  If
`u ∈ H¹(Ω)` and `B(c, R) ⊆ Ω`, then `∫_{B(c, R)} |u - ⨍_{B(c, R)} u|²` is at most
`(2 ^ (n + 1) * R)²` times `∫_{B(c, R)} ‖∇u‖²`.  This is
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball` for the restriction of `u` to the ball,
with both sides written as integrals. -/
theorem W1p.setIntegral_value_sub_setAverage_sq_le_of_ball_subset {c : E} {R : ℝ}
    (hball : ball c R ⊆ (Omega : Set E)) (u : W1p mu Omega 2) :
    ∫ x in ball c R, (W1p.value u x - ⨍ y in ball c R, W1p.value u y ∂mu) ^ 2 ∂mu ≤
      (2 ^ (finrank ℝ E + 1) * R) ^ 2 * ∫ x in ball c R, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 hR]
  -- Restrict `u` to the ball `B = B(c, R)`, viewed as a domain of its own.
  set B : Opens E := ⟨ball c R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  set uB := W1p.restrictL hB u
  set m := ⨍ y in ball c R, W1p.value u y ∂mu
  have hval : W1p.value uB =ᵐ[mu.restrict (ball c R)] W1p.value u := W1p.value_restrictL_ae hB u
  have hP := W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball (p := 2)
    (rfl : (B : Set E) = ball c R) uB
  have havg : ⨍ y in (B : Set E), W1p.value uB y ∂mu = m := average_congr hval
  rw [havg] at hP
  have hcongr : (fun x ↦ W1p.value uB x - m) =ᵐ[mu.restrict (ball c R)]
      fun x ↦ W1p.value u x - m := hval.mono fun x hx ↦ congrArg (· - m) hx
  have : IsFiniteMeasure (mu.restrict (ball c R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmem : MemLp (fun x ↦ W1p.value uB x - m) 2 (mu.restrict (ball c R)) :=
    (Lp.memLp (W1p.value uB)).sub (memLp_const m)
  -- Convert the `eLpNorm` bound into a bound on integrals of squares.
  have hnorm : ‖hmem.toLp _‖ ≤ 2 ^ (finrank ℝ E + 1) * R * ‖W1p.gradient uB‖ := by
    rw [Lp.norm_toLp, ← toReal_eNorm (W1p.gradient uB),
      ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ (finrank ℝ E + 1) * R),
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (by finiteness) hP
  have hsq : ∫ x in ball c R, (W1p.value u x - m) ^ 2 ∂mu = ‖hmem.toLp _‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp, hcongr] with x hx hx'
    rw [hx, hx', Real.norm_eq_abs, sq_abs]
  have hgrad : ‖W1p.gradient uB‖ ^ 2 = ∫ x in ball c R, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_restrictL_ae hB u] with x hx
    rw [hx]
  rw [hsq, ← hgrad, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- **The Poincaré–Wirtinger inequality on a ball inside the domain, in `L¹`.**  If
`u ∈ W^{1,p}(Ω)` and `B(c, R) ⊆ Ω`, then `∫_{B(c, R)} |u - ⨍_{B(c, R)} u|` is at most
`2 ^ (n + 1) * R` times `∫_{B(c, R)} ‖∇u‖`.  This is
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball` at exponent one, for the restriction of
`u` to the ball, which lies in `W^{1,1}` because the ball has finite measure. -/
theorem W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset {c : E} {R : ℝ}
    (hball : ball c R ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    ∫ x in ball c R, |W1p.value u x - ⨍ y in ball c R, W1p.value u y ∂mu| ∂mu ≤
      2 ^ (finrank ℝ E + 1) * R * ∫ x in ball c R, ‖W1p.gradient u x‖ ∂mu := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 hR]
  -- Restrict `u` to the ball `B = B(c, R)`, viewed as a domain of its own, and lower the
  -- exponent to one.
  set B : Opens E := ⟨ball c R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict (B : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set uB : W1p mu B 1 := W1p.ofExponentLE (Fact.out : 1 ≤ p) (W1p.restrictL hB u)
  set m := ⨍ y in ball c R, W1p.value u y ∂mu
  have hval : W1p.value uB =ᵐ[mu.restrict (ball c R)] W1p.value u :=
    (W1p.coeFn_value_ofExponentLE _ _).eventuallyEq.trans (W1p.value_restrictL_ae hB u)
  have hgrad : W1p.gradient uB =ᵐ[mu.restrict (ball c R)] W1p.gradient u :=
    (W1p.coeFn_gradient_ofExponentLE _ _).eventuallyEq.trans (W1p.gradient_restrictL_ae hB u)
  have hP := W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball (p := 1)
    (rfl : (B : Set E) = ball c R) uB
  have havg : ⨍ y in (B : Set E), W1p.value uB y ∂mu = m := average_congr hval
  rw [havg] at hP
  have hle : mu.restrict (ball c R) ≤ mu.restrict Omega := Measure.restrict_mono hball le_rfl
  have hint : IntegrableOn (W1p.value u) (ball c R) mu :=
    ((Lp.memLp (W1p.value u)).mono_measure hle).integrable Fact.out
  have hgint : IntegrableOn (W1p.gradient u) (ball c R) mu :=
    ((Lp.memLp (W1p.gradient u)).mono_measure hle).integrable Fact.out
  -- Both sides of `hP` are the integrals in the statement.
  rw [eLpNorm_one_eq_lintegral_eNorm (f := fun x ↦ W1p.value uB x - m)
      ((Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const),
    Lp.eNorm_def, eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable _)] at hP
  simp_rw [← Real.norm_eq_abs]
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
    ofReal_integral_norm_eq_lintegral_eNorm (f := fun x ↦ W1p.value u x - m)
      (hint.sub (integrable_const m)), ofReal_integral_norm_eq_lintegral_eNorm hgint]
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hP.trans_eq ?_)
  · filter_upwards [hval] with x hx
    rw [hx]
  · congr 1
    exact lintegral_congr_ae (hgrad.mono fun x hx ↦ by simp only [hx])

/-! ### Functions with vanishing gradient -/

/-- **A Sobolev function with vanishing gradient on a connected domain is constant.** If `Ω` is
preconnected and the weak gradient of `u ∈ W^{1,p}(Ω)` vanishes, then `u` agrees almost everywhere
on `Ω` with a constant. -/
theorem W1p.exists_value_ae_eq_const_of_gradient_eq_zero
    (hconn : IsPreconnected (Omega : Set E)) {u : W1p mu Omega p} (hu : W1p.gradient u = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = c := by
  refine (W1p.hasWeakFDerivOn u).exists_ae_eq_const_of_deriv_ae_eq_zero hconn ?_
  filter_upwards [(Lp.ext_iff.1 hu).trans (Lp.coeFn_zero _ _ _)] with x hx
  simp [hx]

/-- **Integration up to a constant on a preconnected domain.** If `Ω` is preconnected and the weak
gradient of `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with the classical gradient `∇ q` of
a function `q` that is `C¹` on `Ω`, then `u` agrees almost everywhere on `Ω` with `q + c` for some
constant `c : ℝ`. Neither boundedness of `Ω` nor global `Lᵖ` integrability of `q` is needed. -/
theorem W1p.exists_value_ae_eq_add_const_of_gradient_ae_eq
    (hconn : IsPreconnected (Omega : Set E)) {u : W1p mu Omega p} {q : E → ℝ}
    (hq : ContDiffOn ℝ 1 q Omega)
    (hgrad : (W1p.gradient u : E → E) =ᵐ[mu.restrict Omega] ∇ q) :
    ∃ c : ℝ, (W1p.value u : E → ℝ) =ᵐ[mu.restrict Omega] fun x ↦ q x + c := by
  have hsub : HasWeakFDerivOn mu Omega (fun x ↦ W1p.value u x - q x)
      (fun x ↦ innerSL ℝ (W1p.gradient u x) - innerSL ℝ (∇ q x)) :=
    (W1p.hasWeakFDerivOn u).sub (hasWeakFDerivOn_gradient_of_contDiffOn hq)
  obtain ⟨c, hc⟩ := hsub.exists_ae_eq_const_of_deriv_ae_eq_zero hconn <| by
    filter_upwards [hgrad] with x hx
    simp [hx]
  refine ⟨c, hc.mono fun x hx ↦ ?_⟩
  linarith

end TauCeti
