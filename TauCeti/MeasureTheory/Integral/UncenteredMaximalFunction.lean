/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
-- `TauCeti.MeasureTheory.Integral.Average` is imported privately: it supplies
-- `TauCeti.setLAverage_le_div_mul_setLAverage_of_subset`, used only in a proof.
import TauCeti.MeasureTheory.Integral.Average

/-!
# The uncentred maximal function

The **uncentred Hardy–Littlewood maximal function** of `f` is

`M_u f x = sup_{B ∋ x} ⨍_B ‖f‖`,

the supremum of the averages of `‖f‖` over all open balls containing `x`, centred anywhere
(`TauCeti.uncenteredMaximalFunction`). It dominates the centred maximal function
`TauCeti.maximalFunction`, whose balls are centred at `x`, and for an additive Haar measure on a
real normed space of dimension `n` it is at most `2ⁿ` times it: a ball of radius `r` containing
`x` lies in the ball of radius `2r` about `x`, whose measure is `2ⁿ` times larger. So the two
maximal functions are pointwise comparable, and the weak type `(1, 1)` and strong type `(p, p)`
bounds of the centred maximal function transfer to the uncentred one with an extra factor `2ⁿ`.

The constant `2ⁿ` is the right order in dimension one: for `f = 1_{[0, 1]}` on `ℝ` and `x > 1`
the centred maximal function is `1 / (2x)`, while the balls `(0, x + ε)` give the uncentred one
the value `1 / x`.

## Main declarations

* `TauCeti.uncenteredMaximalFunction`: the uncentred maximal function, with
  `TauCeti.setLAverage_le_uncenteredMaximalFunction`, `TauCeti.uncenteredMaximalFunction_le` and
  `TauCeti.lt_uncenteredMaximalFunction_iff` as its interface.
* `TauCeti.lowerSemicontinuous_uncenteredMaximalFunction`,
  `TauCeti.measurable_uncenteredMaximalFunction`: the superlevel sets of `M_u f` are open, so it is
  Borel measurable.
* `TauCeti.maximalFunction_le_uncenteredMaximalFunction`: `M f ≤ M_u f`.
* `TauCeti.uncenteredMaximalFunction_le_two_pow_mul_maximalFunction`: `M_u f ≤ 2ⁿ M f` for an
  additive Haar measure.

## References

* E. Stein, *Harmonic Analysis*, Chapter I.
* L. Grafakos, *Classical Fourier Analysis*, Section 2.1.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module Set
open scoped ENNReal

section PseudoMetricSpace

variable {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [ENorm F] {μ : Measure X}
  {f : X → F} {x y : X} {r : ℝ} {a t : ℝ≥0∞}

/-- The **uncentred Hardy–Littlewood maximal function** of `f` with respect to `μ`: the supremum
of the averages of `‖f‖ₑ` over the open balls containing `x`. -/
noncomputable def uncenteredMaximalFunction (μ : Measure X) (f : X → F) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (r : ℝ) (_ : x ∈ ball y r), ⨍⁻ z in ball y r, ‖f z‖ₑ ∂μ

theorem uncenteredMaximalFunction_def (μ : Measure X) (f : X → F) (x : X) :
    uncenteredMaximalFunction μ f x = ⨆ (y : X) (r : ℝ) (_ : x ∈ ball y r),
      ⨍⁻ z in ball y r, ‖f z‖ₑ ∂μ :=
  (rfl)

/-- The average over a ball containing `x` is at most the uncentred maximal function at `x`. -/
theorem setLAverage_le_uncenteredMaximalFunction (μ : Measure X) (f : X → F) (hx : x ∈ ball y r) :
    ⨍⁻ z in ball y r, ‖f z‖ₑ ∂μ ≤ uncenteredMaximalFunction μ f x :=
  le_iSup₂_of_le y r (le_iSup (fun _ : x ∈ ball y r => ⨍⁻ z in ball y r, ‖f z‖ₑ ∂μ) hx)

/-- A bound for the averages over all balls containing `x` bounds the uncentred maximal function
at `x`. -/
theorem uncenteredMaximalFunction_le
    (h : ∀ y r, x ∈ ball y r → ⨍⁻ z in ball y r, ‖f z‖ₑ ∂μ ≤ a) :
    uncenteredMaximalFunction μ f x ≤ a :=
  iSup₂_le fun y r => iSup_le (h y r)

/-- The uncentred maximal function exceeds `t` at `x` exactly when the average over some ball
containing `x` does. -/
theorem lt_uncenteredMaximalFunction_iff :
    t < uncenteredMaximalFunction μ f x ↔
      ∃ y r, x ∈ ball y r ∧ t < ⨍⁻ z in ball y r, ‖f z‖ₑ ∂μ := by
  simp only [uncenteredMaximalFunction_def, lt_iSup_iff, exists_prop]

/-- The superlevel sets of the uncentred maximal function are open, each being a union of open
balls. No hypothesis on `μ` or `f` is needed. -/
theorem lowerSemicontinuous_uncenteredMaximalFunction (μ : Measure X) (f : X → F) :
    LowerSemicontinuous (uncenteredMaximalFunction μ f) := by
  intro x t ht
  obtain ⟨y, r, hx, hlt⟩ := lt_uncenteredMaximalFunction_iff.1 ht
  filter_upwards [isOpen_ball.mem_nhds hx] with z hz
  exact hlt.trans_le (setLAverage_le_uncenteredMaximalFunction μ f hz)

/-- The uncentred maximal function is Borel measurable, being lower semicontinuous. -/
@[fun_prop]
theorem measurable_uncenteredMaximalFunction [OpensMeasurableSpace X] (μ : Measure X)
    (f : X → F) : Measurable (uncenteredMaximalFunction μ f) :=
  (lowerSemicontinuous_uncenteredMaximalFunction μ f).measurable

/-- The centred maximal function is at most the uncentred one. -/
theorem maximalFunction_le_uncenteredMaximalFunction (μ : Measure X) (f : X → F) (x : X) :
    maximalFunction μ f x ≤ uncenteredMaximalFunction μ f x :=
  maximalFunction_le fun _ hr => setLAverage_le_uncenteredMaximalFunction μ f (mem_ball_self hr)

end PseudoMetricSpace

section Haar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [ENorm F]

/-- **The uncentred maximal function is at most `2ⁿ` times the centred one**, for an additive Haar
measure on a real normed space of dimension `n`: a ball of radius `r` containing `x` lies in the
ball of radius `2r` about `x`, whose measure is `2ⁿ` times larger. -/
theorem uncenteredMaximalFunction_le_two_pow_mul_maximalFunction (μ : Measure E)
    [μ.IsAddHaarMeasure] (f : E → F) (x : E) :
    uncenteredMaximalFunction μ f x ≤ 2 ^ finrank ℝ E * maximalFunction μ f x := by
  refine uncenteredMaximalFunction_le fun y r hx => ?_
  have hr : 0 < r := pos_of_mem_ball hx
  have hsub : ball y r ⊆ ball x (2 * r) := fun z hz => mem_ball.2 <| by
    calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < r + r := add_lt_add (mem_ball.1 hz) (mem_ball'.1 hx)
      _ = 2 * r := by ring
  have hvol : μ (ball x (2 * r)) = 2 ^ finrank ℝ E * μ (ball y r) := by
    rw [Measure.addHaar_ball_of_pos μ x (by positivity), Measure.addHaar_ball_of_pos μ y hr,
      mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, mul_assoc]
  calc ⨍⁻ z in ball y r, ‖f z‖ₑ ∂μ
      ≤ μ (ball x (2 * r)) / μ (ball y r) * ⨍⁻ z in ball x (2 * r), ‖f z‖ₑ ∂μ :=
        setLAverage_le_div_mul_setLAverage_of_subset hsub measure_ball_lt_top.ne
    _ ≤ 2 ^ finrank ℝ E * maximalFunction μ f x := by
        rw [hvol, ENNReal.mul_div_cancel_right (Metric.measure_ball_pos μ y hr).ne'
          measure_ball_lt_top.ne]
        gcongr
        exact setLAverage_le_maximalFunction μ f x (by positivity)

end Haar

end TauCeti
