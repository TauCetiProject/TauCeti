/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Semicontinuity.Defs
-- `TauCeti.MeasureTheory.Integral.Marcinkiewicz.Basic` is imported privately: its operator-level
-- interpolation API is used only to prove the strong maximal inequalities below.
import TauCeti.MeasureTheory.Integral.Marcinkiewicz.Basic
-- `Mathlib.MeasureTheory.Constructions.BorelSpace.Order` is imported privately: it is used only
-- for `LowerSemicontinuous.measurable`, inside the proof of `TauCeti.measurable_maximalFunction`.
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
-- `TauCeti.MeasureTheory.Covering.Vitali` is imported privately: its covering estimate
-- `TauCeti.mul_measure_le_lintegral_of_forall_exists_ball` is used only inside the proofs of the
-- weak-type inequalities.
import TauCeti.MeasureTheory.Covering.Vitali
-- `TauCeti.MeasureTheory.Integral.Lebesgue.Truncation` is imported privately: it supplies
-- `TauCeti.lintegral_rpow_le_of_forall_le` inside the proof of the vector-valued inequality.
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation
-- `TauCeti.Analysis.SpecialFunctions.Pow.NNReal` is imported privately: it supplies the
-- cancellation `ENNReal.rpow_one_sub_le_of_le_mul_rpow` inside the proof of the vector-valued
-- inequality.
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Hardy–Littlewood maximal function

The **centred Hardy–Littlewood maximal function** of `f` is

`M f x = ⨆ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ`,

the largest average of `‖f‖` over a ball centred at `x`. This file defines it, records the two
endpoint bounds it satisfies, and proves the **maximal inequality** in both of its forms: the weak
type `(1,1)` bound

`t * μ {x | t < M f x} ≤ 4 ^ n * ∫⁻ x, ‖f x‖ₑ ∂μ`

and, for `1 < p < ∞`, the strong type `(p, p)` bound `‖M f‖_p ≤ C(n, p) * ‖f‖_p`, for `μ` an
additive Haar measure on a real normed space of finite dimension `n`.

It also proves the two maximal inequalities of Fefferman and Stein: the **weighted** inequality

`∫⁻ (M f) ^ p * w ∂μ ≤ C(n, p) * ∫⁻ ‖f‖ₑ ^ p * M w ∂μ`

for every weight `w` and `1 < p < ∞`, and from it the **vector-valued** inequality

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ∂μ ≤ C(n, r, p) * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r) ∂μ`

for countable families and `1 < r ≤ p < ∞`. With `r = 2` the latter bounds the maximal functions of
the pieces of a square function, which is the form Littlewood–Paley theory uses.

The maximal inequality drives Calderón–Zygmund theory and, through it, the `Lᵖ` regularity
theory for elliptic equations.
It is also where the classical *asymmetric* pair of endpoints originates: `M` is bounded on `L^∞`
(`TauCeti.maximalFunction_le_eLpNormEssSup`) but, in positive dimension, not on `L¹` — a failure
not formalised here — so the correct `L¹` statement is the weak-type bound, and the strong `(p, p)`
bounds are obtained from those two ends by Marcinkiewicz interpolation. The qualification matters:
the `L¹` failure is a positive-dimensional phenomenon, since in dimension `0` every ball is the
whole space and the averages defining `M f` collapse to `‖f‖ₑ`.

## The proof

The weak-type bound is the Vitali covering argument, isolated as
`TauCeti.mul_measure_le_lintegral_of_forall_exists_ball` for two measures in
`TauCeti.MeasureTheory.Covering.Vitali` and specialised here as
`TauCeti.mul_measure_le_of_forall_exists_ball`: if every point of a set `S` is the centre of a ball
of radius at most `R` on which `∫⁻ g` is at least `t` times the measure of the ball, then
`t * μ S ≤ 4 ^ n * ∫⁻ g`. Mathlib's
`Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` extracts a pairwise disjoint
subfamily of those balls whose fourfold enlargements still cover `S`; the enlargement costs the
factor `4 ^ n` because a Haar measure scales a ball of radius `r` by `r ^ n`, and disjointness turns
the sum of the integrals over the selected balls into a single integral over their union.

Applying this to `S = {x | t < M f x}` needs a uniform bound on the radii it selects, and that is
where finiteness of `∫⁻ ‖f‖ₑ` enters: a ball whose average exceeds `t` has measure less than
`∫⁻ ‖f‖ₑ / t`, which in positive dimension bounds its radius. In dimension `0` it does not — every
ball is the whole space — and that degenerate case is proved separately.

The strong type `(p, p)` bound then comes from
`TauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup`, the operator-level diagonal
case of Marcinkiewicz interpolation. That theorem performs the reusable split at height `c * t`.
Here `c = d = 2⁻¹`, so the low part is bounded by `t / 2`, its maximal function never reaches
`t`, and the weak-type bound applied to the high part gives
`t * μ {M f > t} ≤ 2 * 4 ^ n * ∫⁻ x in {‖f‖ₑ > t / 2}, ‖f x‖ₑ ∂μ`.

The weighted weak type `(1, 1)` bound
`t * ∫⁻ x in {x | t < M f x}, w x ∂μ ≤ 5 ^ n * ∫⁻ ‖f‖ₑ * M w ∂μ` is the same covering argument
with the `w`-mass of the enlarged balls in place of their measure: the closed ball of radius `4 r`
around the centre of `ball x r` lies in the ball of radius `5 r` around any point `y` of `ball x r`,
so its `w`-mass is at most `5 ^ n * μ (ball x r) * M w y`. The radii are bounded by exhausting the
superlevel set with balls of radius at most `N`. Since `M w` vanishes nowhere unless `w = 0` almost
everywhere, `μ` and `μ.withDensity (M w)` then have the same null sets, the `L^∞` endpoint is the
unweighted one, and Marcinkiewicz interpolation from `μ.withDensity (M w)` to `μ.withDensity w`
gives the weighted strong bound.

For the vector-valued bound with `r < p`, write `q = p / r`, `F = ∑' i, (M fᵢ) ^ r` and
`G = ∑' i, ‖fᵢ‖ₑ ^ r`, and let `g ≤ F` be a truncation of `F` with `∫⁻ g ^ q` finite. Then
`∫⁻ g ^ q ≤ ∫⁻ F * g ^ (q - 1)`, the weighted inequality with the weight `g ^ (q - 1)` bounds this
by a multiple of `∫⁻ G * M (g ^ (q - 1))`, and Hölder's inequality together with the scalar maximal
inequality in `Lˢ`, `s` the exponent conjugate to `q`, bounds that by a multiple of
`(∫⁻ G ^ q) ^ (1 / q) * (∫⁻ g ^ q) ^ (1 / s)`. Dividing by the finite factor `(∫⁻ g ^ q) ^ (1 / s)`
and letting the truncations increase to `F` gives the bound for `∫⁻ F ^ q`.

## Main declarations

* `TauCeti.maximalFunction`: the centred Hardy–Littlewood maximal function, with
  `TauCeti.setLAverage_le_maximalFunction`, `TauCeti.maximalFunction_le` and
  `TauCeti.lt_maximalFunction_iff` as its interface.
* `TauCeti.maximalFunction_const`: the maximal function of a constant is that constant, so the
  normalisation is the intended one.
* `TauCeti.maximalFunction_mono_ae`, `TauCeti.maximalFunction_congr_ae`: `M` is monotone in `‖f‖ₑ`
  almost everywhere, so `M f` depends on `f` only through `‖f‖ₑ` and only up to a null set.
* `TauCeti.maximalFunction_enorm`: replacing a function by its extended norm leaves its maximal
  function unchanged.
* `TauCeti.maximalFunction_zero`, `TauCeti.maximalFunction_add_le`,
  `TauCeti.maximalFunction_const_smul`: `M` is sublinear. Subadditivity and the endpoint bounds
  feed directly into `TauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup`.
* `TauCeti.maximalFunction_le_eLpNormEssSup`: the `L^∞` endpoint.
* `TauCeti.ae_enorm_eq_zero_of_maximalFunction_eq_zero`: `M f` vanishes nowhere unless `f = 0`
  almost everywhere.
* `TauCeti.lowerSemicontinuous_maximalFunction`, `TauCeti.measurable_maximalFunction`: the
  superlevel sets `{x | t < M f x}` are open, so `M f` is Borel measurable.
* `TauCeti.mul_measure_le_of_forall_exists_ball`: the Vitali covering estimate for a Haar
  measure.
* `TauCeti.mul_measure_lt_maximalFunction_le`, `TauCeti.measure_lt_maximalFunction_le`: the
  **maximal inequality**, in product and in quotient form.
* `TauCeti.ae_maximalFunction_lt_top`: the maximal function of an `L¹` function is finite almost
  everywhere.
* `TauCeti.lintegral_rpow_maximalFunction_le`, `TauCeti.eLpNorm_maximalFunction_le`: the
  **strong type `(p, p)` maximal inequality** for `1 < p < ∞`, with an explicit constant.
* `TauCeti.mul_setLIntegral_lt_maximalFunction_le`,
  `TauCeti.lintegral_rpow_maximalFunction_mul_le`: the **weighted maximal inequality** of
  Fefferman and Stein, of weak type `(1, 1)` and of strong type `(p, p)` for `1 < p < ∞`.
* `TauCeti.lintegral_tsum_maximalFunction_rpow_le`,
  `TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le`: the **vector-valued maximal inequality**
  of Fefferman and Stein for `1 < r ≤ p < ∞`.
* `TauCeti.eLpNorm_maximalFunction_lt_top`,
  `TauCeti.ae_maximalFunction_lt_top_of_eLpNorm_ne_top`: a function with finite `Lᵖ` seminorm
  has a maximal function with finite `Lᵖ` seminorm for `1 < p ≤ ∞`, and the maximal function
  is finite almost everywhere for every `1 ≤ p ≤ ∞`.

The maximal function defined here is the *centred* one, whose averages are over the balls centred
at the point. The uncentred variant, over all balls containing the point, is comparable to it with
a dimensional constant and is not needed downstream.

## References

* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I.
* L. Grafakos, *Classical Fourier Analysis*, Sections 2.1 and 5.6.
* C. Fefferman, E. M. Stein, *Some maximal inequalities*, Amer. J. Math. **93** (1971), 107–115.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal Topology

section PseudoMetricSpace

variable {X F F' : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [ENorm F] [ENorm F']

/-- The **centred Hardy–Littlewood maximal function** of `f` with respect to `μ`: the supremum
over the radii `r > 0` of the average of `‖f‖ₑ` over the ball of radius `r` centred at `x`.

The averages are taken in `ℝ≥0∞`, so this is defined for every `f`, taking the value `∞` at the
points where the averages are unbounded. -/
noncomputable def maximalFunction (μ : Measure X) (f : X → F) (x : X) : ℝ≥0∞ :=
  ⨆ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ

variable {μ : Measure X} {f : X → F} {g : X → F'} {x : X} {r : ℝ} {a t : ℝ≥0∞}

theorem maximalFunction_def (μ : Measure X) (f : X → F) (x : X) :
    maximalFunction μ f x = ⨆ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ := (rfl)

/-- Every ball average is at most the maximal function: the introduction rule. -/
theorem setLAverage_le_maximalFunction (μ : Measure X) (f : X → F) (x : X) (hr : 0 < r) :
    ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ ≤ maximalFunction μ f x := by
  rw [maximalFunction_def]
  exact le_iSup₂ (f := fun r (_ : 0 < r) => ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ) r hr

/-- A bound holding for every ball average bounds the maximal function: the elimination rule. -/
theorem maximalFunction_le (h : ∀ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ ≤ a) :
    maximalFunction μ f x ≤ a := by
  rw [maximalFunction_def]
  exact iSup₂_le h

/-- The maximal function exceeds `t` exactly when some ball average does. -/
theorem lt_maximalFunction_iff :
    t < maximalFunction μ f x ↔ ∃ r > 0, t < ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ := by
  rw [maximalFunction_def]
  simp only [lt_iSup_iff, exists_prop]

/-- If `‖f‖ₑ ≤ ‖g‖ₑ` almost everywhere, then `M f ≤ M g`. -/
theorem maximalFunction_mono_ae (h : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ ‖g y‖ₑ) :
    maximalFunction μ f x ≤ maximalFunction μ g x :=
  maximalFunction_le fun _ hr =>
    (setLAverage_mono_ae _ h).trans (setLAverage_le_maximalFunction μ g x hr)

/-- Functions whose norms agree almost everywhere have the same maximal function. -/
theorem maximalFunction_congr_ae (h : ∀ᵐ y ∂μ, ‖f y‖ₑ = ‖g y‖ₑ) :
    maximalFunction μ f x = maximalFunction μ g x :=
  le_antisymm (maximalFunction_mono_ae (h.mono fun _ hy => hy.le))
    (maximalFunction_mono_ae (h.mono fun _ hy => hy.ge))

/-- Replacing a function by its extended norm leaves its maximal function unchanged. -/
@[simp]
theorem maximalFunction_enorm (μ : Measure X) (f : X → F) :
    maximalFunction μ (fun x => ‖f x‖ₑ) = maximalFunction μ f :=
  funext fun _ => maximalFunction_congr_ae (.of_forall fun _ => by simp)

/-- The `L^∞` endpoint of the maximal inequality: the maximal function of `f` is bounded by the
essential supremum of `‖f‖`, with constant `1`. -/
theorem maximalFunction_le_eLpNormEssSup (μ : Measure X) (f : X → F) (x : X) :
    maximalFunction μ f x ≤ eLpNormEssSup f μ := by
  rw [eLpNormEssSup_eq_essSup_enorm]
  exact maximalFunction_le fun r _ => setLAverage_le_essSup _ _

/-- The maximal function of a constant is its extended norm for any open positive, locally finite
measure. Local finiteness supplies a ball with positive finite measure at each point. -/
@[simp]
theorem maximalFunction_const (μ : Measure X) [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ]
    (c : F) (x : X) : maximalFunction μ (fun _ => c) x = ‖c‖ₑ := by
  refine le_antisymm ((maximalFunction_le_eLpNormEssSup μ _ x).trans
    (eLpNormEssSup_le_of_ae_enorm_bound (.of_forall fun _ => le_rfl))) ?_
  obtain ⟨r, hr, hfinite⟩ := (μ.finiteAt_nhds x).exists_mem_basis nhds_basis_ball
  exact (setLAverage_const (measure_ball_pos μ x hr).ne' hfinite.ne ‖c‖ₑ).ge.trans
    (setLAverage_le_maximalFunction μ _ x hr)

/-- The maximal inequality, with constant `1`, in the degenerate case of a space with at most one
point, where every positive-radius ball is the whole space. -/
private theorem mul_measure_lt_maximalFunction_le_of_subsingleton [Subsingleton X] (μ : Measure X)
    (f : X → F) (t : ℝ≥0∞) :
    t * μ {x | t < maximalFunction μ f x} ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rcases eq_empty_or_nonempty {x | t < maximalFunction μ f x} with hS | ⟨x, hx⟩
  · simp [hS]
  obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp hx
  have hball : ball x r = univ :=
    eq_univ_of_forall fun y => by simpa [Subsingleton.elim y x] using hr
  rw [setLAverage_eq, hball, Measure.restrict_univ] at hlt
  calc t * μ {x | t < maximalFunction μ f x}
      ≤ t * μ univ := by gcongr; exact subset_univ _
    _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := (ENNReal.mul_lt_of_lt_div hlt).le

section Sublinear

/-- The maximal function is positively homogeneous: scaling `f` by `c` scales `M f` by `‖c‖ₑ`.
This is the first half of the sublinearity of `M`, the second being
`TauCeti.maximalFunction_add_le`. -/
@[simp]
theorem maximalFunction_const_smul {𝕜 : Type*} [NNNorm 𝕜] [SMul 𝕜 F] [ENormSMulClass 𝕜 F]
    (μ : Measure X) (c : 𝕜) (f : X → F) (x : X) :
    maximalFunction μ (c • f) x = ‖c‖ₑ * maximalFunction μ f x := by
  rw [maximalFunction_def, maximalFunction_def]
  simp only [Pi.smul_apply, enorm_smul, ENNReal.mul_iSup]
  exact iSup_congr fun r => iSup_congr fun _ => by
    rw [laverage_eq', laverage_eq', lintegral_const_mul' _ _ enorm_ne_top]

variable {G : Type*} [TopologicalSpace G] [ESeminormedAddMonoid G] {f g : X → G}

/-- The maximal function of the zero function is zero. -/
@[simp]
theorem maximalFunction_zero (μ : Measure X) (x : X) : maximalFunction μ (0 : X → G) x = 0 := by
  simp [maximalFunction_def]

/-- The maximal function is subadditive, the second half of that sublinearity. Only the norm of the
first summand need be measurable. -/
theorem maximalFunction_add_le (hf : AEMeasurable (fun y => ‖f y‖ₑ) μ) (x : X) :
    maximalFunction μ (f + g) x ≤ maximalFunction μ f x + maximalFunction μ g x := by
  refine maximalFunction_le fun r hr => ?_
  calc ⨍⁻ y in ball x r, ‖(f + g) y‖ₑ ∂μ
      ≤ ⨍⁻ y in ball x r, (‖f y‖ₑ + ‖g y‖ₑ) ∂μ :=
        setLAverage_mono_ae _ (.of_forall fun y => enorm_add_le (f y) (g y))
    _ = ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ + ⨍⁻ y in ball x r, ‖g y‖ₑ ∂μ := by
        rw [setLAverage_eq, setLAverage_eq, setLAverage_eq, lintegral_add_left' hf.restrict,
          ENNReal.add_div]
    _ ≤ maximalFunction μ f x + maximalFunction μ g x :=
        add_le_add (setLAverage_le_maximalFunction μ f x hr)
          (setLAverage_le_maximalFunction μ g x hr)

end Sublinear

end PseudoMetricSpace

section Haar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [ENorm F] {μ : Measure E} [μ.IsAddHaarMeasure] {t : ℝ≥0∞}

/-- Enlarging a ball by the factor `4` multiplies its measure by `4 ^ n`: the dimensional cost of
the Vitali enlargement. -/
private theorem addHaar_closedBall_four_mul (μ : Measure E) [μ.IsAddHaarMeasure] (x : E) {r : ℝ}
    (hr : 0 < r) : μ (closedBall x (4 * r)) = 4 ^ finrank ℝ E * μ (ball x r) := by
  rw [Measure.addHaar_closedBall μ x (by linarith : (0 : ℝ) ≤ 4 * r),
    Measure.addHaar_ball_of_pos μ x hr, ← mul_assoc, mul_pow,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 ^ finrank ℝ E),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- **The Vitali covering estimate.** If every point of `S` is the centre of a ball of radius at
most `R` on which `∫⁻ g` is at least `t` times the measure of the ball, then
`t * μ S ≤ 4 ^ n * ∫⁻ g`, with `n` the dimension of the space.

The factor `4 ^ n` is the cost of passing from a pairwise disjoint subfamily of those balls to its
fourfold enlargement, which still covers `S`. -/
theorem mul_measure_le_of_forall_exists_ball {S : Set E} {R : ℝ} {g : E → ℝ≥0∞}
    (hS : ∀ x ∈ S, ∃ r ∈ Ioc 0 R, t * μ (ball x r) ≤ ∫⁻ y in ball x r, g y ∂μ) :
    t * μ S ≤ 4 ^ finrank ℝ E * ∫⁻ y, g y ∂μ := by
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine mul_measure_le_lintegral_of_forall_exists_ball (R := R) fun x hx => ?_
  obtain ⟨r, hr, hle⟩ := hS x hx
  refine ⟨r, hr, ?_⟩
  rw [addHaar_closedBall_four_mul μ x hr.1, mul_left_comm, lintegral_const_mul' _ _ (by simp)]
  gcongr

/-- The superlevel sets of the maximal function are open: enlarging the radius slightly keeps the
average of `‖f‖ₑ` above `t`, at every nearby centre. -/
theorem lowerSemicontinuous_maximalFunction (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) :
    LowerSemicontinuous (maximalFunction μ f) := by
  intro x t ht
  obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp ht
  have hc₀ : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hc_top : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hpos : ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1) ≠ 0 := fun s hs =>
    mul_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos hs _)).ne' hc₀
  have hne : ∀ s : ℝ, ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1) ≠ ∞ := fun _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc_top
  rw [setLAverage_eq] at hlt
  have hmul : t * (ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball (0 : E) 1)) <
      ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ := by
    rw [← Measure.addHaar_ball_of_pos μ x hr]
    exact ENNReal.mul_lt_of_lt_div hlt
  -- A slightly larger radius still works, by continuity of `s ↦ t * (s ^ n * μ (ball 0 1))`.
  have hcont : Tendsto
      (fun s : ℝ => t * (ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1))) (𝓝 r)
      (𝓝 (t * (ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball (0 : E) 1)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul_const
        ((ENNReal.continuous_ofReal.tendsto _).comp ((continuous_pow _).tendsto r)) (.inr hc_top))
      (.inl (hpos r hr))
  have hev : ∀ᶠ s : ℝ in 𝓝[>] r,
      t * (ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1)) <
        ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ :=
    (hcont.mono_left nhdsWithin_le_nhds).eventually_lt_const hmul
  obtain ⟨s, hs, hrs⟩ := (hev.and self_mem_nhdsWithin).exists
  have hrs' : r < s := hrs
  have hs_pos : 0 < s := hr.trans hrs'
  -- Every centre within `s - r` of `x` then has a ball average exceeding `t`.
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrs')] with y hy
  refine lt_of_lt_of_le ?_ (setLAverage_le_maximalFunction μ f y hs_pos)
  rw [setLAverage_eq, Measure.addHaar_ball_of_pos μ y hs_pos,
    ENNReal.lt_div_iff_mul_lt (.inl (hpos s hs_pos)) (.inl (hne s))]
  refine hs.trans_le (lintegral_mono_set (ball_subset_ball' ?_))
  rw [dist_comm]
  linarith [mem_ball.mp hy]

/-- The maximal function is Borel measurable, being lower semicontinuous. No hypothesis on `f` is
needed: the supremum defining `M f` is over balls, not over values of `f`. -/
@[fun_prop]
theorem measurable_maximalFunction (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) :
    Measurable (maximalFunction μ f) :=
  (lowerSemicontinuous_maximalFunction μ f).measurable

/-- **The Hardy–Littlewood maximal inequality**, the weak-type `(1,1)` bound: the measure of the
set where the maximal function exceeds `t`, multiplied by `t`, is at most `4 ^ n` times the `L¹`
norm of `f`, with `n` the dimension of the space.

No integrability hypothesis is needed: the bound is vacuous when `∫⁻ x, ‖f x‖ₑ ∂μ = ∞`. -/
theorem mul_measure_lt_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F)
    (t : ℝ≥0∞) :
    t * μ {x | t < maximalFunction μ f x} ≤ 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rcases eq_or_ne (∫⁻ x, ‖f x‖ₑ ∂μ) ∞ with hI | hI
  · rw [hI, ENNReal.mul_top (pow_ne_zero _ (by norm_num))]
    exact le_top
  rcases eq_or_ne t 0 with rfl | ht₀
  · simp
  rcases eq_or_ne t ∞ with rfl | ht_top
  · -- the superlevel set at `∞` is empty
    simp
  rcases subsingleton_or_nontrivial E with _ | _
  · exact (mul_measure_lt_maximalFunction_le_of_subsingleton μ f t).trans
      (le_mul_of_one_le_left' (one_le_pow₀ (by norm_num)))
  have hc₀ : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hc_top : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have htc₀ : t * μ (ball (0 : E) 1) ≠ 0 := mul_ne_zero ht₀ hc₀
  have htc_top : t * μ (ball (0 : E) 1) ≠ ∞ := ENNReal.mul_ne_top ht_top hc_top
  -- Every point of the superlevel set is the centre of a ball whose average exceeds `t`.
  have hex : ∀ x ∈ {x | t < maximalFunction μ f x},
      ∃ r : ℝ, 0 < r ∧ t * μ (ball x r) < ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ := by
    intro x hx
    obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp hx
    rw [setLAverage_eq] at hlt
    exact ⟨r, hr, ENNReal.mul_lt_of_lt_div hlt⟩
  choose! r hr₀ hrlt using hex
  -- Those radii are bounded, because `∫⁻ ‖f‖ₑ ∂μ` is finite and the dimension is positive.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ {x | t < maximalFunction μ f x}, r x ∈ Ioc 0 R := by
    refine ⟨max 1 ((∫⁻ x, ‖f x‖ₑ ∂μ) / (t * μ (ball (0 : E) 1))).toReal,
      fun x hx => ⟨hr₀ x hx, ?_⟩⟩
    have hlt : ENNReal.ofReal (r x ^ finrank ℝ E) * (t * μ (ball (0 : E) 1)) <
        ∫⁻ y, ‖f y‖ₑ ∂μ := by
      rw [mul_left_comm, ← Measure.addHaar_ball_of_pos μ x (hr₀ x hx)]
      exact (hrlt x hx).trans_le (setLIntegral_le_lintegral _ _)
    rw [← ENNReal.lt_div_iff_mul_lt (.inl htc₀) (.inl htc_top),
      ENNReal.ofReal_lt_iff_lt_toReal (pow_nonneg (hr₀ x hx).le _)
        (ENNReal.div_ne_top hI htc₀)] at hlt
    by_contra! hcon
    have h₁ : (1 : ℝ) ≤ r x := le_trans (le_max_left _ _) hcon.le
    have h₂ : r x ≤ r x ^ finrank ℝ E := le_self_pow₀ h₁ Module.finrank_pos.ne'
    linarith [le_max_right (1 : ℝ) ((∫⁻ x, ‖f x‖ₑ ∂μ) / (t * μ (ball (0 : E) 1))).toReal]
  exact mul_measure_le_of_forall_exists_ball fun x hx => ⟨r x, hR x hx, (hrlt x hx).le⟩

/-- **The Hardy–Littlewood maximal inequality**, in quotient form. -/
theorem measure_lt_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F)
    (ht : t ≠ 0) :
    μ {x | t < maximalFunction μ f x} ≤ 4 ^ finrank ℝ E * (∫⁻ x, ‖f x‖ₑ ∂μ) / t := by
  rcases eq_or_ne t ∞ with rfl | ht_top
  · -- the superlevel set at `∞` is empty
    simp
  refine (ENNReal.le_div_iff_mul_le (.inl ht) (.inl ht_top)).2 ?_
  rw [mul_comm]
  exact mul_measure_lt_maximalFunction_le μ f t

/-- The maximal function of an `L¹` function is finite almost everywhere: the maximal inequality
with `t → ∞`. -/
theorem ae_maximalFunction_lt_top (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F)
    (hf : ∫⁻ x, ‖f x‖ₑ ∂μ ≠ ∞) : ∀ᵐ x ∂μ, maximalFunction μ f x < ∞ := by
  have hC : 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) hf
  have hsub : ∀ t : ℝ≥0∞, t ≠ ∞ →
      t * μ {x | maximalFunction μ f x = ∞} ≤ 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ := by
    refine fun t ht => le_trans (mul_le_mul_right (measure_mono fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact lt_of_lt_of_le (lt_top_iff_ne_top.2 ht) hx.ge) t)
      (mul_measure_lt_maximalFunction_le μ f t)
  have hm : μ {x | maximalFunction μ f x = ∞} = 0 := by
    by_contra hm'
    rcases eq_or_ne (μ {x | maximalFunction μ f x = ∞}) ∞ with hm_top | hm_top
    · exact hC (top_le_iff.1 (by simpa [hm_top] using hsub 1 ENNReal.one_ne_top))
    · have hle := hsub ((4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ + 1) /
        μ {x | maximalFunction μ f x = ∞}) (ENNReal.div_ne_top (by simp [hC]) hm')
      rw [ENNReal.div_mul_cancel hm' hm_top] at hle
      exact absurd hle (not_le.2 (ENNReal.lt_add_right hC one_ne_zero))
  rw [ae_iff]
  simpa only [not_lt, top_le_iff] using hm

section StrongType

/-- The constant that Marcinkiewicz interpolation at the height `2⁻¹ * t` produces from a weak-type
`(1, 1)` constant `A` and the `L^∞` constant `1`. -/
private theorem ofReal_mul_two_mul_eq (p : ℝ) (A : ℝ≥0∞) :
    ENNReal.ofReal (p * (2 : ℝ)⁻¹ ^ (1 - p) / (p - 1)) * (2 * A) =
      ENNReal.ofReal (2 * p * 2 ^ (p - 1) / (p - 1)) * A := by
  have hinv : ((2 : ℝ))⁻¹ ^ (1 - p) = 2 ^ (p - 1) := by
    rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_sub]
  have hsplit : 2 * p * 2 ^ (p - 1) / (p - 1) = 2 * (p * 2 ^ (p - 1) / (p - 1)) := by ring
  rw [hinv, hsplit, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  ring

/-- **The Hardy–Littlewood maximal inequality**, the strong-type `(p, p)` bound for `1 < p < ∞`,
as an inequality between the integrals `∫⁻ ‖·‖ₑ ^ p`:

`∫⁻ (M f) ^ p ∂μ ≤ (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ n * ∫⁻ ‖f‖ₑ ^ p ∂μ`.

The constant degenerates as `p → 1`, as it must in positive dimension, where `M` is not bounded on
`L¹`. -/
theorem lintegral_rpow_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F}
    (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, maximalFunction μ f x ^ p ∂μ ≤
      ENNReal.ofReal (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ finrank ℝ E *
        ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [← ofReal_mul_two_mul_eq, ← maximalFunction_enorm μ f]
  simpa only [inv_inv, ENNReal.ofReal_ofNat, enorm_eq_self] using
    lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup
      (T := fun g => maximalFunction μ g) (A := 4 ^ finrank ℝ E) (b := 1)
      (c := 2⁻¹) (d := 2⁻¹) hf
      (measurable_maximalFunction μ fun x => ‖f x‖ₑ).aemeasurable hp
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun g h hg _hh => .of_forall fun y => maximalFunction_add_le
        (by simpa only [enorm_eq_self] using hg) y)
      (fun g _hg s => by
        simpa only [enorm_eq_self] using mul_measure_lt_maximalFunction_le μ g s)
      (fun (g : E → ℝ≥0∞) (_hg : AEMeasurable g μ) =>
        .of_forall fun y : E => by simpa only [ENNReal.ofReal_one, one_mul] using
          maximalFunction_le_eLpNormEssSup μ g y)

/-- **The Hardy–Littlewood maximal inequality**, the strong-type `(p, p)` bound for `1 < p < ∞`,
in terms of representative-level `Lᵖ` seminorms.

Together with `TauCeti.maximalFunction_le_eLpNormEssSup` (the case `p = ∞`) and
`TauCeti.mul_measure_lt_maximalFunction_le` (the weak-type substitute at `p = 1`), this gives the
representative-level strong estimate for the maximal function. The resulting finiteness statement
is recorded by
`TauCeti.eLpNorm_maximalFunction_lt_top` below. -/
theorem eLpNorm_maximalFunction_le [TopologicalSpace F] (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → F} (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (maximalFunction μ f) p μ ≤
      (ENNReal.ofReal (2 * p.toReal * 2 ^ (p.toReal - 1) / (p.toReal - 1)) *
        4 ^ finrank ℝ E) ^ (1 / p.toReal) * eLpNorm f p μ := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  -- `f` itself need not be a.e. strongly measurable; if it is not, its `Lᵖ` seminorm is `∞`.
  have hfle : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
    by_cases hfm : AEStronglyMeasurable f μ
    · exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top hfm).ge
    · simp [eLpNorm_of_not_aestronglyMeasurable hfm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top
    (measurable_maximalFunction μ f).aestronglyMeasurable]
  calc (∫⁻ x, ‖maximalFunction μ f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal (2 * p.toReal * 2 ^ (p.toReal - 1) / (p.toReal - 1)) *
          4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        simpa only [enorm_eq_self] using lintegral_rpow_maximalFunction_le μ hf hpr
    _ = (ENNReal.ofReal (2 * p.toReal * 2 ^ (p.toReal - 1) / (p.toReal - 1)) *
          4 ^ finrank ℝ E) ^ (1 / p.toReal) * (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ _ := by gcongr

end StrongType

section Finiteness

variable [TopologicalSpace F] {p : ℝ≥0∞} {f : E → F}

/-- The maximal function of an `Lᵖ` function has finite `Lᵖ` seminorm when `1 < p ≤ ∞`. -/
theorem eLpNorm_maximalFunction_lt_top (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) (hf_top : eLpNorm f p μ ≠ ∞)
    (hp : 1 < p) : eLpNorm (maximalFunction μ f) p μ < ∞ := by
  have hfm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_eLpNorm_ne_top hf_top
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [eLpNorm_exponent_top (measurable_maximalFunction μ f).aestronglyMeasurable]
    refine (eLpNormEssSup_le_of_ae_enorm_bound (.of_forall fun x => ?_)).trans_lt (by
        simpa only [eLpNorm_exponent_top hfm] using hf_top.lt_top)
    rw [enorm_eq_self]
    exact maximalFunction_le_eLpNormEssSup μ f x
  · exact (eLpNorm_maximalFunction_le μ hf hp hp_top).trans_lt
      (ENNReal.mul_lt_top (by finiteness) hf_top.lt_top)

/-- The maximal function of a function with finite `Lᵖ` seminorm is finite almost everywhere
when `1 ≤ p`, including both endpoints. -/
theorem ae_maximalFunction_lt_top_of_eLpNorm_ne_top (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → F) (hf_top : eLpNorm f p μ ≠ ∞)
    (hp : 1 ≤ p) : ∀ᵐ x ∂μ, maximalFunction μ f x < ∞ := by
  have hfm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_eLpNorm_ne_top hf_top
  rcases eq_or_ne p ∞ with rfl | hp_top
  · exact .of_forall fun x => (maximalFunction_le_eLpNormEssSup μ f x).trans_lt
      (by simpa only [eLpNorm_exponent_top hfm] using hf_top.lt_top)
  rcases hp.eq_or_lt with rfl | hp
  · exact ae_maximalFunction_lt_top μ f (by
      simpa only [eLpNorm_one_eq_lintegral_enorm hfm] using hf_top)
  · have hp₀ : p ≠ 0 := (zero_lt_one.trans hp).ne'
    have hpr : 1 < p.toReal := by
      simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
    let g : E → ℝ≥0∞ := fun x => if 1 < ‖f x‖ₑ then ‖f x‖ₑ else 0
    have hg_le (x : E) : g x ≤ ‖f x‖ₑ ^ p.toReal := by
      simp only [g]
      split_ifs with hx
      · exact ENNReal.le_rpow_self_of_one_le hx.le hpr.le
      · exact bot_le
    have hfp : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ < ∞ :=
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp_top hfm).mp hf_top.lt_top
    have hg_int : ∫⁻ x, ‖g x‖ₑ ∂μ ≠ ∞ := by
      simpa only [enorm_eq_self] using (lt_of_le_of_lt (lintegral_mono hg_le) hfp).ne
    have hfg (x : E) : ‖f x‖ₑ ≤ 1 + g x := by
      simp only [g]
      split_ifs with hx
      · exact le_add_left le_rfl
      · simpa only [add_zero] using le_of_not_gt hx
    have hM (x : E) : maximalFunction μ f x ≤ 1 + maximalFunction μ g x := by
      calc
        maximalFunction μ f x ≤
            maximalFunction μ ((fun _ : E => (1 : ℝ≥0∞)) + g) x :=
          maximalFunction_mono_ae (.of_forall fun y => by
            simpa only [Pi.add_apply, enorm_eq_self] using hfg y)
        _ ≤ maximalFunction μ (fun _ : E => (1 : ℝ≥0∞)) x + maximalFunction μ g x :=
          maximalFunction_add_le aemeasurable_const x
        _ = 1 + maximalFunction μ g x := by
          rw [maximalFunction_const]
          simp only [enorm_eq_self]
    exact (ae_maximalFunction_lt_top μ g hg_int).mono fun x hx =>
      (hM x).trans_lt (ENNReal.add_lt_top.2 ⟨by finiteness, hx⟩)

end Finiteness

omit [BorelSpace E] in
/-- If the maximal function of `f` vanishes at a single point, then `f` vanishes almost everywhere:
every ball around that point has average `0`. -/
theorem ae_enorm_eq_zero_of_maximalFunction_eq_zero {f : E → F}
    (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) {x₀ : E} (hx₀ : maximalFunction μ f x₀ = 0) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ = 0 := by
  rw [← Measure.restrict_univ (μ := μ), ← iUnion_ball_nat_succ x₀, ae_restrict_iUnion_iff]
  intro n
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hav : ⨍⁻ y in ball x₀ (n + 1), ‖f y‖ₑ ∂μ = 0 :=
    le_antisymm (hx₀ ▸ setLAverage_le_maximalFunction μ f x₀ hn) bot_le
  rw [setLAverage_eq, ENNReal.div_eq_zero_iff] at hav
  exact (lintegral_eq_zero_iff' hf.restrict).1 (hav.resolve_right measure_ball_lt_top.ne)

section Weighted

/-- The `w`-mass of the closed ball `closedBall x (4 * r)` is at most `5 ^ n` times the measure of
`ball x r` times the maximal function of `w` at any point `y` of `ball x r`: the enlarged ball lies
in `ball y (5 * r)`, on which the average of `w` is at most `M w y`. -/
private theorem setLIntegral_closedBall_four_mul_le (w : E → ℝ≥0∞) {x y : E} {r : ℝ}
    (hr : 0 < r) (hy : y ∈ ball x r) :
    ∫⁻ z in closedBall x (4 * r), w z ∂μ ≤
      5 ^ finrank ℝ E * μ (ball x r) * maximalFunction μ w y := by
  have h5 : 0 < 5 * r := by positivity
  have hsub : closedBall x (4 * r) ⊆ ball y (5 * r) := fun z hz => by
    rw [mem_closedBall] at hz
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle z x y, dist_comm x y]
  have hμ : μ (ball y (5 * r)) = 5 ^ finrank ℝ E * μ (ball x r) := by
    rw [Measure.addHaar_ball_of_pos μ y h5, Measure.addHaar_ball_of_pos μ x hr, mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      mul_assoc]
  calc ∫⁻ z in closedBall x (4 * r), w z ∂μ ≤ ∫⁻ z in ball y (5 * r), w z ∂μ :=
        lintegral_mono_set hsub
    _ = μ (ball y (5 * r)) * ⨍⁻ z in ball y (5 * r), w z ∂μ :=
        (measure_mul_setLAverage _ measure_ball_lt_top.ne).symm
    _ ≤ μ (ball y (5 * r)) * maximalFunction μ w y := by
        gcongr
        simpa only [enorm_eq_self] using setLAverage_le_maximalFunction μ w y h5
    _ = 5 ^ finrank ℝ E * μ (ball x r) * maximalFunction μ w y := by rw [hμ]

/-- **The weighted maximal inequality of Fefferman and Stein**, weak type `(1, 1)`: for every weight
`w`, the `w`-mass of the set where the maximal function of `f` exceeds `t`, multiplied by `t`, is at
most `5 ^ n` times the integral of `‖f‖` against the maximal function of `w`:

`t * ∫⁻ x in {x | t < M f x}, w x ∂μ ≤ 5 ^ n * ∫⁻ x, ‖f x‖ₑ * M w x ∂μ`.

No hypothesis is needed on `f` or on `w`. -/
theorem mul_setLIntegral_lt_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F)
    (w : E → ℝ≥0∞) (t : ℝ≥0∞) :
    t * ∫⁻ x in {x | t < maximalFunction μ f x}, w x ∂μ ≤
      5 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ * maximalFunction μ w x ∂μ := by
  -- The superlevel set is the increasing union of the sets `S N` of centres of balls of radius at
  -- most `N` whose average of `‖f‖ₑ` exceeds `t`; the Vitali covering estimate applies to each.
  let S : ℕ → Set E := fun N =>
    {x | ∃ r ∈ Ioc 0 (N : ℝ), t * μ (ball x r) < ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ}
  have hS : {x | t < maximalFunction μ f x} = ⋃ N, S N := by
    ext x
    simp only [S, mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp hx
      obtain ⟨N, hN⟩ := exists_nat_ge r
      rw [setLAverage_eq] at hlt
      exact ⟨N, r, ⟨hr, hN⟩, ENNReal.mul_lt_of_lt_div hlt⟩
    · rintro ⟨N, r, hr, hlt⟩
      refine lt_maximalFunction_iff.mpr ⟨r, hr.1, ?_⟩
      rw [setLAverage_eq]
      exact (ENNReal.lt_div_iff_mul_lt (.inl (measure_ball_pos μ x hr.1).ne')
        (.inl measure_ball_lt_top.ne)).2 hlt
  have hmono : Monotone S := fun N N' h x ⟨r, hr, hlt⟩ =>
    ⟨r, ⟨hr.1, hr.2.trans (by exact_mod_cast h)⟩, hlt⟩
  rw [← withDensity_apply' w, hS, hmono.measure_iUnion, ENNReal.mul_iSup,
    ← lintegral_const_mul' _ _ (by simp)]
  refine iSup_le fun N => mul_measure_le_lintegral_of_forall_exists_ball fun x ⟨r, hr, hlt⟩ =>
    ⟨r, hr, ?_⟩
  -- Multiply by `μ (ball x r)`, bound `t * μ (ball x r)` by `∫⁻ ‖f‖ₑ` and the `w`-mass of the
  -- enlarged ball pointwise on `ball x r`, then cancel `μ (ball x r)`.
  have hB0 : μ (ball x r) ≠ 0 := (measure_ball_pos μ x hr.1).ne'
  have hBtop : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  rw [withDensity_apply' w, ← ENNReal.mul_le_mul_iff_left hB0 hBtop]
  calc t * (∫⁻ z in closedBall x (4 * r), w z ∂μ) * μ (ball x r)
      = t * μ (ball x r) * ∫⁻ z in closedBall x (4 * r), w z ∂μ := by ring
    _ ≤ (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) * ∫⁻ z in closedBall x (4 * r), w z ∂μ := by
        gcongr
    _ ≤ ∫⁻ y in ball x r, ‖f y‖ₑ * ∫⁻ z in closedBall x (4 * r), w z ∂μ ∂μ :=
        lintegral_mul_const_le _ _
    _ ≤ ∫⁻ y in ball x r, μ (ball x r) *
          (5 ^ finrank ℝ E * (‖f y‖ₑ * maximalFunction μ w y)) ∂μ := by
        refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
        calc ‖f y‖ₑ * ∫⁻ z in closedBall x (4 * r), w z ∂μ
            ≤ ‖f y‖ₑ * (5 ^ finrank ℝ E * μ (ball x r) * maximalFunction μ w y) := by
              gcongr
              exact setLIntegral_closedBall_four_mul_le w hr.1 hy
          _ = μ (ball x r) * (5 ^ finrank ℝ E * (‖f y‖ₑ * maximalFunction μ w y)) := by ring
    _ = (∫⁻ y in ball x r, 5 ^ finrank ℝ E * (‖f y‖ₑ * maximalFunction μ w y) ∂μ) *
          μ (ball x r) := by
        rw [lintegral_const_mul' _ _ hBtop, mul_comm]

/-- **The weighted maximal inequality of Fefferman and Stein**, strong type `(p, p)` for
`1 < p < ∞`: for every weight `w`,

`∫⁻ (M f) ^ p * w ∂μ ≤ (2 * p * 2 ^ (p - 1) / (p - 1)) * 5 ^ n * ∫⁻ ‖f‖ₑ ^ p * M w ∂μ`.

With `w = 1` this recovers the unweighted bound `TauCeti.lintegral_rpow_maximalFunction_le`, with
`5 ^ n` in place of `4 ^ n`. Applied to `w = g ^ (q - 1)` it controls the pairing of `(M f) ^ p`
with an `Lᵠ'` function, which is how `TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le` reaches
the vector-valued maximal inequality. -/
theorem lintegral_rpow_maximalFunction_mul_le (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F}
    (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) {w : E → ℝ≥0∞} (hw : AEMeasurable w μ) {p : ℝ}
    (hp : 1 < p) :
    ∫⁻ x, maximalFunction μ f x ^ p * w x ∂μ ≤
      ENNReal.ofReal (2 * p * 2 ^ (p - 1) / (p - 1)) * 5 ^ finrank ℝ E *
        ∫⁻ x, ‖f x‖ₑ ^ p * maximalFunction μ w x ∂μ := by
  by_cases hpos : ∃ x₀, maximalFunction μ w x₀ = 0
  · -- If `M w` vanishes somewhere, then `w = 0` almost everywhere and the left side vanishes.
    obtain ⟨x₀, hx₀⟩ := hpos
    refine le_of_eq_of_le ?_ zero_le
    rw [← lintegral_zero]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_enorm_eq_zero_of_maximalFunction_eq_zero (f := w) hw hx₀] with x hx
    rw [enorm_eq_self] at hx
    simp [hx]
  simp only [not_exists] at hpos
  -- Otherwise `μ` and `μ.withDensity (M w)` have the same null sets, so the `L^∞` endpoint is the
  -- unweighted one, and Marcinkiewicz interpolation runs from `μ.withDensity (M w)` to
  -- `μ.withDensity w`.
  have hMw : Measurable (maximalFunction μ w) := measurable_maximalFunction μ w
  have hac : μ ≪ μ.withDensity (maximalFunction μ w) := fun s hs => by
    rw [withDensity_apply_eq_zero' hMw.aemeasurable] at hs
    simpa [hpos] using hs
  have hac' := withDensity_absolutelyContinuous μ (maximalFunction μ w)
  have hT := lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup
    (μ := μ.withDensity (maximalFunction μ w)) (ν := μ.withDensity w)
    (T := fun g => maximalFunction μ g) (A := 5 ^ finrank ℝ E) (b := 1) (c := 2⁻¹) (d := 2⁻¹)
    (v := fun x => ‖f x‖ₑ) (hf.mono_ac hac') (measurable_maximalFunction μ _).aemeasurable hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun g h hg _hh => .of_forall fun y => maximalFunction_add_le
      (by simpa only [enorm_eq_self] using hg.mono_ac hac) y)
    (fun g hg s => by
      rw [withDensity_apply' w, lintegral_withDensity_eq_lintegral_mul₀ hMw.aemeasurable
        (hg.mono_ac hac).enorm]
      simpa only [Pi.mul_apply, mul_comm (maximalFunction μ w _)] using
        mul_setLIntegral_lt_maximalFunction_le μ g w s)
    (fun g _hg => .of_forall fun y => by
      simpa only [ENNReal.ofReal_one, one_mul] using
        (maximalFunction_le_eLpNormEssSup μ g y).trans (eLpNormEssSup_mono_measure g hac))
  simp only [enorm_eq_self, maximalFunction_enorm] at hT
  rw [lintegral_withDensity_eq_lintegral_mul₀ hw
      ((measurable_maximalFunction μ f).pow_const p).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ hMw.aemeasurable (hf.pow_const p)] at hT
  simpa only [inv_inv, ENNReal.ofReal_ofNat, enorm_eq_self, maximalFunction_enorm,
    ofReal_mul_two_mul_eq, Pi.mul_apply, mul_comm (w _), mul_comm (maximalFunction μ w _)] using hT

end Weighted

section VectorValued

variable {ι : Type*} [Countable ι]

/-- **The vector-valued maximal inequality** for `1 < p < ∞` on the diagonal: the `ℓᵖ`-valued
maximal function is bounded on `Lᵖ(ℓᵖ)`, with the constant of the scalar inequality
`TauCeti.lintegral_rpow_maximalFunction_le`:

`∫⁻ ∑' i, (M fᵢ) ^ p ∂μ ≤ (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ n * ∫⁻ ∑' i, ‖fᵢ‖ₑ ^ p ∂μ`. -/
theorem lintegral_tsum_maximalFunction_rpow_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : ι → E → F} (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ) μ) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, ∑' i, maximalFunction μ (f i) x ^ p ∂μ ≤
      ENNReal.ofReal (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ finrank ℝ E *
        ∫⁻ x, ∑' i, ‖f i x‖ₑ ^ p ∂μ := by
  rw [lintegral_tsum fun i => ((measurable_maximalFunction μ (f i)).pow_const p).aemeasurable,
    lintegral_tsum fun i => (hf i).pow_const p, ← ENNReal.tsum_mul_left]
  exact tsum_le_tsum fun i => lintegral_rpow_maximalFunction_le μ (hf i) hp

/-- The core of the vector-valued maximal inequality: for conjugate exponents `q` and `s` and a
measurable `φ ≤ ∑' i, (M fᵢ) ^ r` with `∫⁻ φ ^ q` finite, `∫⁻ φ ^ q` is bounded by a constant
multiple of `∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ q`. -/
private theorem lintegral_rpow_le_of_le_tsum_maximalFunction_rpow {f : ι → E → F}
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ) μ) {r q s : ℝ} (hr : 1 < r)
    (hqs : q.HolderConjugate s) {φ : E → ℝ≥0∞} (hφ : Measurable φ)
    (hφF : ∀ x, φ x ≤ ∑' i, maximalFunction μ (f i) x ^ r) (hfin : ∫⁻ x, φ x ^ q ∂μ ≠ ∞) :
    ∫⁻ x, φ x ^ q ∂μ ≤
      (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 5 ^ finrank ℝ E *
        (ENNReal.ofReal (2 * s * 2 ^ (s - 1) / (s - 1)) * 4 ^ finrank ℝ E) ^ (1 / s)) ^ q *
        ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ q ∂μ := by
  set cw := ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 5 ^ finrank ℝ E
  set cM := ENNReal.ofReal (2 * s * 2 ^ (s - 1) / (s - 1)) * 4 ^ finrank ℝ E
  set G : E → ℝ≥0∞ := fun x => ∑' i, ‖f i x‖ₑ ^ r with hG_def
  set ψ : E → ℝ≥0∞ := fun x => φ x ^ (q - 1) with hψ_def
  have hq1 : 1 < q := hqs.lt
  have hψ : Measurable ψ := hφ.pow_const _
  have hMψ := measurable_maximalFunction μ ψ
  -- Test `φ ^ q ≤ (∑' i, (M fᵢ) ^ r) * ψ` against the weighted inequality with the weight `ψ`.
  have h1 : ∫⁻ x, φ x ^ q ∂μ ≤ cw * ∫⁻ x, G x * maximalFunction μ ψ x ∂μ := by
    calc ∫⁻ x, φ x ^ q ∂μ
        ≤ ∫⁻ x, ∑' i, maximalFunction μ (f i) x ^ r * ψ x ∂μ := lintegral_mono fun x => by
          calc φ x ^ q = φ x ^ ((1 : ℝ) + (q - 1)) := by ring_nf
            _ = φ x * ψ x := by
                rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
            _ ≤ ∑' i, maximalFunction μ (f i) x ^ r * ψ x := by
                rw [ENNReal.tsum_mul_right]
                gcongr
                exact hφF x
      _ = ∑' i, ∫⁻ x, maximalFunction μ (f i) x ^ r * ψ x ∂μ :=
          lintegral_tsum fun i =>
            (((measurable_maximalFunction μ (f i)).pow_const r).mul hψ).aemeasurable
      _ ≤ ∑' i, cw * ∫⁻ x, ‖f i x‖ₑ ^ r * maximalFunction μ ψ x ∂μ :=
          tsum_le_tsum fun i => lintegral_rpow_maximalFunction_mul_le μ (hf i) hψ.aemeasurable hr
      _ = cw * ∫⁻ x, G x * maximalFunction μ ψ x ∂μ := by
          rw [ENNReal.tsum_mul_left, ← lintegral_tsum (f := fun i x => ‖f i x‖ₑ ^ r *
            maximalFunction μ ψ x) fun i => ((hf i).pow_const r).mul hMψ.aemeasurable]
          simp_rw [hG_def, ENNReal.tsum_mul_right]
  -- The scalar maximal inequality in `Lˢ`, with `ψ ^ s = φ ^ q`.
  have h2 : ∫⁻ x, maximalFunction μ ψ x ^ s ∂μ ≤ cM * ∫⁻ x, φ x ^ q ∂μ := by
    have := lintegral_rpow_maximalFunction_le μ (f := ψ)
      (by simpa only [enorm_eq_self] using hψ.aemeasurable) hqs.symm.lt
    simpa only [hψ_def, enorm_eq_self, ← ENNReal.rpow_mul, hqs.sub_one_mul_conj] using this
  -- Hölder's inequality, then cancel the finite factor `(∫⁻ φ ^ q) ^ (1 / s)`.
  have hs0 : 0 ≤ 1 / s := hqs.symm.one_div_pos.le
  have h3 : ∫⁻ x, φ x ^ q ∂μ ≤ cw * cM ^ (1 / s) * (∫⁻ x, G x ^ q ∂μ) ^ (1 / q) *
      (∫⁻ x, φ x ^ q ∂μ) ^ (1 / s) := by
    calc ∫⁻ x, φ x ^ q ∂μ
        ≤ cw * ((∫⁻ x, G x ^ q ∂μ) ^ (1 / q) * (cM * ∫⁻ x, φ x ^ q ∂μ) ^ (1 / s)) := by
          refine h1.trans ?_
          gcongr
          exact (ENNReal.lintegral_mul_le_Lp_mul_Lq μ hqs (AEMeasurable.tsum fun i =>
            (hf i).pow_const r) hMψ.aemeasurable).trans (by gcongr)
      _ = cw * cM ^ (1 / s) * (∫⁻ x, G x ^ q ∂μ) ^ (1 / q) * (∫⁻ x, φ x ^ q ∂μ) ^ (1 / s) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hs0]
          ring
  have h4 := ENNReal.rpow_one_sub_le_of_le_mul_rpow
    (by rw [one_div]; exact inv_lt_one_of_one_lt₀ hqs.symm.lt) hfin h3
  rw [one_div s, hqs.symm.one_sub_inv, ← one_div, ← one_div] at h4
  calc ∫⁻ x, φ x ^ q ∂μ = ((∫⁻ x, φ x ^ q ∂μ) ^ (1 / q)) ^ q := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hqs.pos.ne', ENNReal.rpow_one]
    _ ≤ (cw * cM ^ (1 / s) * (∫⁻ x, G x ^ q ∂μ) ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow h4 hqs.pos.le
    _ = (cw * cM ^ (1 / s)) ^ q * ∫⁻ x, G x ^ q ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hqs.pos.le, ← ENNReal.rpow_mul,
          one_div_mul_cancel hqs.pos.ne', ENNReal.rpow_one]

/-- **The vector-valued maximal inequality of Fefferman and Stein** for `1 < r < p < ∞`: the
`ℓʳ`-valued maximal function is bounded on `Lᵖ(ℓʳ)`,

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ∂μ ≤ C * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r) ∂μ`,

with `C = (c(r) * 5 ^ n * (c(s) * 4 ^ n) ^ (1 / s)) ^ (p / r)`, where
`c(t) = 2 t 2 ^ (t - 1) / (t - 1)`, `n` is the dimension and `s = p / (p - r)` is the exponent
conjugate to `p / r`; it depends only on `n`, `r` and `p`. The family is indexed by any countable
type, so this covers sequences. For `r = 2` this is the square-function form
`‖(∑' i, (M fᵢ) ^ 2) ^ (1 / 2)‖_p ≤ C' ‖(∑' i, ‖fᵢ‖ ^ 2) ^ (1 / 2)‖_p` for `2 < p < ∞`; the diagonal
case `p = r` is `TauCeti.lintegral_tsum_maximalFunction_rpow_le`. -/
theorem lintegral_rpow_tsum_maximalFunction_rpow_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : ι → E → F} (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ) μ) {r p : ℝ} (hr : 1 < r)
    (hrp : r < p) :
    ∫⁻ x, (∑' i, maximalFunction μ (f i) x ^ r) ^ (p / r) ∂μ ≤
      (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 5 ^ finrank ℝ E *
        (ENNReal.ofReal (2 * (p / (p - r)) * 2 ^ (p / (p - r) - 1) / (p / (p - r) - 1)) *
          4 ^ finrank ℝ E) ^ ((p - r) / p)) ^ (p / r) *
        ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (p / r) ∂μ := by
  have hr0 : 0 < r := by linarith
  -- `p / r` and `p / (p - r)` are conjugate exponents.
  have hqs : (p / r).HolderConjugate (p / (p - r)) := by
    rw [Real.holderConjugate_iff_eq_conjExponent ((one_lt_div hr0).2 hrp)]
    field_simp
  rw [← one_div_div p (p - r)]
  exact lintegral_rpow_le_of_forall_le
    (Measurable.tsum fun i => (measurable_maximalFunction μ (f i)).pow_const r) hqs.pos
    fun φ hφ hφF hfin => lintegral_rpow_le_of_le_tsum_maximalFunction_rpow hf hr hqs hφ hφF hfin

end VectorValued

end Haar

end TauCeti
