/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stieltjes functions

A Stieltjes function on `(0, ∞)` is a function with a representation

`f(t) = a / t + b + ∫ x, 1 / (t + x) ∂μ`,

where `a` and `b` are nonnegative and `μ` is a positive measure on `ℝ≥0` satisfying
`μ {0} = 0` and `∫ (1 + x)⁻¹ ∂μ < ∞`.  Removing the atom at zero makes the singular coefficient
`a` canonical.  The weighted integrability condition is the standard sharp condition: the
representing measure need not be finite, but it makes the transform finite at every positive
parameter.  Values outside `(0, ∞)` are deliberately unconstrained.

This file introduces the representation predicate and the function class, proves that the
defining integral is genuinely integrable at every positive parameter, and develops the basic
cone API and the elementary reciprocal examples.  These are the foundations for the
Stieltjes/Bernstein-function correspondences.

## Main declarations

* `TauCeti.RepresentsStieltjes`: a measure and two nonnegative coefficients represent a function
  by the Stieltjes formula on `(0, ∞)`.
* `TauCeti.IsStieltjesFunction`: existence of a Stieltjes representation.
* `TauCeti.measurable_stieltjesWeight` and `TauCeti.integrable_stieltjesWeight`: the weight is
  measurable, and every finite measure satisfies the weight condition.
* `TauCeti.lintegral_inv_le_of_eventually_integral_inv_add_le`: a bound on the Stieltjes
  transform of a Stieltjes measure on `ℝ≥0` near the origin, tending to `c`, bounds
  `∫ y, y⁻¹ ∂ν` by `c`.
* `TauCeti.IsStieltjesFunction.add`, `TauCeti.IsStieltjesFunction.smul`: Stieltjes functions form
  a convex cone.
* `TauCeti.isStieltjesFunction_const`, `TauCeti.isStieltjesFunction_inv`,
  `TauCeti.isStieltjesFunction_inv_const_add`: the basic examples.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Definition 2.1 and Theorem 2.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-- The weight controlling a Stieltjes representing measure. -/
def stieltjesWeight (x : ℝ≥0) : ℝ := (1 + x)⁻¹

/-- Evaluation of the standard Stieltjes weight. -/
@[simp]
lemma stieltjesWeight_apply (x : ℝ≥0) : stieltjesWeight x = (1 + (x : ℝ))⁻¹ :=
  (rfl)

/-- A measure `μ` with coefficients `a, b ≥ 0` represents `f` as a Stieltjes function if its
standard weight is integrable and the Stieltjes formula holds on `(0, ∞)`. -/
def RepresentsStieltjes (μ : Measure ℝ≥0) (a b : ℝ≥0) (f : ℝ → ℝ) : Prop :=
  μ {0} = 0 ∧ Integrable stieltjesWeight μ ∧
      ∀ t : ℝ, 0 < t → f t = (a : ℝ) / t + (b : ℝ) + ∫ x, (t + (x : ℝ))⁻¹ ∂μ

/-- Characterization of `RepresentsStieltjes` without unfolding its body. -/
theorem representsStieltjes_iff {μ : Measure ℝ≥0} {a b : ℝ≥0} {f : ℝ → ℝ} :
    RepresentsStieltjes μ a b f ↔
      μ {0} = 0 ∧ Integrable stieltjesWeight μ ∧
        ∀ t : ℝ, 0 < t → f t = (a : ℝ) / t + (b : ℝ) + ∫ x, (t + (x : ℝ))⁻¹ ∂μ :=
  Iff.rfl

/-- The standard Stieltjes weight is measurable. -/
@[fun_prop]
theorem measurable_stieltjesWeight : Measurable stieltjesWeight := by
  rw [funext stieltjesWeight_apply]
  fun_prop

/-- The standard Stieltjes weight is bounded by `1`, so it is integrable against every finite
measure. -/
theorem integrable_stieltjesWeight (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    Integrable stieltjesWeight μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (.of_forall fun x => ?_)
  rw [stieltjesWeight_apply, norm_inv, Real.norm_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (by simp)

/-- The Stieltjes kernel is integrable at every positive parameter when its standard weight is. -/
theorem integrable_inv_add {μ : Measure ℝ≥0} (hμ : Integrable stieltjesWeight μ)
    {t : ℝ} (ht : 0 < t) : Integrable (fun x : ℝ≥0 => (t + (x : ℝ))⁻¹) μ := by
  refine (hμ.const_mul (max 1 t⁻¹)).mono' (by fun_prop) (.of_forall fun x => ?_)
  have hx := x.coe_nonneg
  rw [Real.norm_of_nonneg (by positivity), stieltjesWeight_apply, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (le_max_right 1 t⁻¹) ht.le,
    mul_le_mul_of_nonneg_left (le_max_left 1 t⁻¹) hx, mul_inv_cancel₀ ht.ne']

/-- If the Stieltjes transform of a measure on `ℝ≥0` satisfying the standard weighted
integrability condition is bounded near `0⁺` by a function `g` tending to `c` there, then
`∫ y, y⁻¹ ∂ν ≤ c`.  The bound is stated as a lower Lebesgue integral because `y ↦ y⁻¹` is
unbounded, and the conclusion carries in particular the finiteness of that integral. -/
theorem lintegral_inv_le_of_eventually_integral_inv_add_le {ν : Measure ℝ≥0}
    (hν : Integrable stieltjesWeight ν) {g : ℝ → ℝ} {c : ℝ} (hg : Tendsto g (𝓝[>] 0) (𝓝 c))
    (h : ∀ᶠ t in 𝓝[>] 0, (∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν) ≤ g t) :
    ∫⁻ y : ℝ≥0, (y : ℝ≥0∞)⁻¹ ∂ν ≤ ENNReal.ofReal c := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hlim (y : ℝ≥0) : Tendsto (fun t : ℝ => ENNReal.ofReal (t + y)⁻¹) (𝓝[>] 0)
      (𝓝 (y : ℝ≥0∞)⁻¹) := by
    refine (tendsto_inv_iff.2 ?_).congr' <| hpos.mono fun t ht =>
      (ENNReal.ofReal_inv_of_pos (by positivity)).symm
    simpa using ENNReal.tendsto_ofReal
      ((tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).add_const (y : ℝ))
  -- Fatou's lemma as the parameter tends to `0⁺`.
  calc ∫⁻ y : ℝ≥0, (y : ℝ≥0∞)⁻¹ ∂ν
      = ∫⁻ y, liminf (fun t : ℝ => ENNReal.ofReal (t + y)⁻¹) (𝓝[>] 0) ∂ν :=
        lintegral_congr fun y => (hlim y).liminf_eq.symm
    _ ≤ liminf (fun t : ℝ => ∫⁻ y, ENNReal.ofReal (t + y)⁻¹ ∂ν) (𝓝[>] 0) :=
        lintegral_liminf_le fun t => by fun_prop
    _ ≤ liminf (fun t => ENNReal.ofReal (g t)) (𝓝[>] 0) := by
        refine liminf_le_liminf ((h.and hpos).mono fun t ⟨hle, ht⟩ => ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inv_add hν ht)
          (.of_forall fun y => by positivity)]
        exact ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal c := (ENNReal.tendsto_ofReal hg).liminf_eq

namespace RepresentsStieltjes

variable {μ ν : Measure ℝ≥0} {a b c d : ℝ≥0} {f g : ℝ → ℝ}

/-- A Stieltjes representing measure has no atom at zero. -/
lemma measure_singleton_zero (h : RepresentsStieltjes μ a b f) : μ {0} = 0 := h.1

/-- The weighted integrability condition on a Stieltjes representing measure. -/
lemma integrable_weight (h : RepresentsStieltjes μ a b f) : Integrable stieltjesWeight μ := h.2.1

/-- Evaluation of a Stieltjes representation at a positive parameter. -/
lemma eq_div_add_add_integral_inv_add (h : RepresentsStieltjes μ a b f) {t : ℝ} (ht : 0 < t) :
    f t = (a : ℝ) / t + (b : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ :=
  h.2.2 t ht

/-- A represented Stieltjes function is nonnegative on `(0, ∞)`. -/
lemma nonneg (h : RepresentsStieltjes μ a b f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  rw [h.eq_div_add_add_integral_inv_add ht]
  positivity

/-- A Stieltjes representation depends only on the represented function's values on `(0, ∞)`. -/
lemma congr (h : RepresentsStieltjes μ a b f) (hfg : EqOn g f (Ioi 0)) :
    RepresentsStieltjes μ a b g := by
  refine ⟨h.measure_singleton_zero, h.integrable_weight, fun t ht => ?_⟩
  rw [hfg ht, h.eq_div_add_add_integral_inv_add ht]

/-- The sum of two Stieltjes representations is represented by the sum of their coefficients and
measures. -/
lemma add (hf : RepresentsStieltjes μ a b f) (hg : RepresentsStieltjes ν c d g) :
    RepresentsStieltjes (μ + ν) (a + c) (b + d) (f + g) := by
  refine ⟨by simp [hf.measure_singleton_zero, hg.measure_singleton_zero],
    hf.integrable_weight.add_measure hg.integrable_weight, fun t ht => ?_⟩
  rw [Pi.add_apply, hf.eq_div_add_add_integral_inv_add ht,
    hg.eq_div_add_add_integral_inv_add ht,
    integral_add_measure (integrable_inv_add hf.integrable_weight ht)
      (integrable_inv_add hg.integrable_weight ht)]
  push_cast
  ring

/-- A nonnegative scalar multiple of a Stieltjes representation is represented by scaling its
coefficients and measure. -/
lemma smul (h : RepresentsStieltjes μ a b f) {r : ℝ} (hr : 0 ≤ r) :
    RepresentsStieltjes ((ENNReal.ofReal r) • μ) (r.toNNReal * a) (r.toNNReal * b) (r • f) := by
  refine ⟨by simp [h.measure_singleton_zero],
    h.integrable_weight.smul_measure ENNReal.ofReal_ne_top, fun t ht => ?_⟩
  rw [Pi.smul_apply, h.eq_div_add_add_integral_inv_add ht, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal hr, smul_eq_mul, NNReal.coe_mul, Real.coe_toNNReal r hr]
  ring

end RepresentsStieltjes

/-- A real function is a Stieltjes function if it has a standard Stieltjes representation on
`(0, ∞)`. -/
def IsStieltjesFunction (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ≥0, ∃ μ : Measure ℝ≥0, RepresentsStieltjes μ a b f

/-- Characterization of a Stieltjes function by its representing data. -/
theorem isStieltjesFunction_iff {f : ℝ → ℝ} :
    IsStieltjesFunction f ↔
      ∃ a b : ℝ≥0, ∃ μ : Measure ℝ≥0, RepresentsStieltjes μ a b f :=
  Iff.rfl

namespace IsStieltjesFunction

variable {f g : ℝ → ℝ}

/-- A Stieltjes function is nonnegative on `(0, ∞)`. -/
@[grind =>]
lemma nonneg (hf : IsStieltjesFunction f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact hμ.nonneg ht

/-- The Stieltjes property depends only on values on `(0, ∞)`. -/
lemma congr (hf : IsStieltjesFunction f) (hfg : EqOn g f (Ioi 0)) : IsStieltjesFunction g := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact ⟨a, b, μ, hμ.congr hfg⟩

/-- Stieltjes functions are closed under addition. -/
lemma add (hf : IsStieltjesFunction f) (hg : IsStieltjesFunction g) :
    IsStieltjesFunction (f + g) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  obtain ⟨c, d, ν, hν⟩ := hg
  exact ⟨a + c, b + d, μ + ν, hμ.add hν⟩

/-- Stieltjes functions are closed under multiplication by a nonnegative scalar. -/
lemma smul (hf : IsStieltjesFunction f) {r : ℝ} (hr : 0 ≤ r) :
    IsStieltjesFunction (r • f) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact ⟨r.toNNReal * a, r.toNNReal * b, ENNReal.ofReal r • μ, hμ.smul hr⟩

end IsStieltjesFunction

/-- Every nonnegative constant function is Stieltjes. -/
theorem isStieltjesFunction_const {b : ℝ} (hb : 0 ≤ b) :
    IsStieltjesFunction (fun _ : ℝ => b) := by
  refine ⟨0, b.toNNReal, 0, ?_⟩
  refine ⟨by simp, integrable_zero_measure, fun t _ => ?_⟩
  simp [Real.coe_toNNReal b hb]

/-- The zero function is Stieltjes. -/
theorem isStieltjesFunction_zero : IsStieltjesFunction (fun _ : ℝ => 0) := by
  simpa using isStieltjesFunction_const le_rfl

/-- The reciprocal `t ↦ t⁻¹` is Stieltjes; it is the singular coefficient with zero measure. -/
theorem isStieltjesFunction_inv : IsStieltjesFunction (fun t : ℝ => t⁻¹) := by
  refine ⟨1, 0, 0, ?_⟩
  refine ⟨by simp, integrable_zero_measure, fun t _ => ?_⟩
  simp [div_eq_mul_inv]

/-- For `x ≥ 0`, the shifted reciprocal `t ↦ (t + x)⁻¹` is Stieltjes.  At `x = 0` it is the
singular term; for `0 < x` it is represented by the Dirac mass at `x`. -/
theorem isStieltjesFunction_inv_const_add {x : ℝ} (hx : 0 ≤ x) :
    IsStieltjesFunction (fun t : ℝ => (x + t)⁻¹) := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simpa using isStieltjesFunction_inv
  · refine ⟨0, 0, Measure.dirac x.toNNReal, by simp [hxpos], integrable_dirac (by simp),
      fun t _ => ?_⟩
    simp [Real.coe_toNNReal x hx, add_comm]

end TauCeti

end

end
