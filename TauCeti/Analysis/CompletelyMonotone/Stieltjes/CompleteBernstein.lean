/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Bernstein

/-!
# Complete Bernstein functions and Stieltjes functions

A complete Bernstein function has a representation

`g(t) = a + b t + ∫ x, t / (t + x) ∂μ`,

where `a, b ≥ 0`, the positive measure `μ` has no atom at zero, and
`∫ (1 + x)⁻¹ ∂μ < ∞`.  The normalization `μ {0} = 0` stops an atom at zero from making the
integral term jump — such an atom contributes `1` at every positive parameter and `0` at zero —
so the integral term vanishes at zero and the representation is the intended continuous extension.
This file packages that standard representation and proves the first fundamental correspondence:
`f` is Stieltjes exactly when `t ↦ t f(t)` on `(0, ∞)` has a complete Bernstein extension to
`[0, ∞)`.

The extension is necessary when the Stieltjes representation has a nonzero `a / t` term: its
value at zero must be `a`, whereas the literal product `0 * f(0)` is zero.  Values of a Stieltjes
function outside `(0, ∞)` remain irrelevant, and values of a complete Bernstein function outside
`[0, ∞)` remain irrelevant.

## Main declarations

* `TauCeti.RepresentsCompleteBernstein`: complete-Bernstein representing data.
* `TauCeti.IsCompleteBernsteinFunction`: the representation-based predicate.
* `TauCeti.IsCompleteBernsteinFunction.isBernsteinFunction`: a complete Bernstein function is a
  Bernstein function.
* `TauCeti.isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_mul`: the
  Stieltjes--complete-Bernstein correspondence.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Theorems 6.2 and 7.3.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- A measure `μ` and coefficients `a, b ≥ 0` represent a complete Bernstein function when
`μ` satisfies the standard Stieltjes integrability condition and the function agrees on
`[0, ∞)` with `a + b t + ∫ x, t / (t + x) ∂μ`.  Requiring `μ {0} = 0` stops an atom at zero from
making the integral term jump between zero and the positive parameters. -/
def RepresentsCompleteBernstein (μ : Measure ℝ≥0) (a b : ℝ≥0) (f : ℝ → ℝ) : Prop :=
  μ {0} = 0 ∧ Integrable stieltjesWeight μ ∧
    EqOn f (stieltjesBernsteinTransform μ a b) (Ici 0)

/-- Characterization of complete-Bernstein representing data without unfolding the predicate. -/
theorem representsCompleteBernstein_iff {μ : Measure ℝ≥0} {a b : ℝ≥0} {f : ℝ → ℝ} :
    RepresentsCompleteBernstein μ a b f ↔
      μ {0} = 0 ∧ Integrable stieltjesWeight μ ∧
        EqOn f (stieltjesBernsteinTransform μ a b) (Ici 0) :=
  Iff.rfl

namespace RepresentsCompleteBernstein

variable {μ ν : Measure ℝ≥0} {a b c d : ℝ≥0} {f g : ℝ → ℝ}

/-- A complete-Bernstein representing measure has no atom at zero. -/
lemma measure_singleton_zero (h : RepresentsCompleteBernstein μ a b f) : μ {0} = 0 :=
  h.1

/-- A complete-Bernstein representing measure satisfies the Stieltjes weight condition. -/
lemma integrable_weight (h : RepresentsCompleteBernstein μ a b f) :
    Integrable stieltjesWeight μ :=
  h.2.1

/-- Evaluation of a complete-Bernstein representation at a nonnegative parameter. -/
lemma eq_stieltjesBernsteinTransform (h : RepresentsCompleteBernstein μ a b f)
    {t : ℝ} (ht : 0 ≤ t) : f t = stieltjesBernsteinTransform μ a b t :=
  h.2.2 ht

/-- A complete-Bernstein representation depends only on the represented function's values on
`[0, ∞)`. -/
lemma congr (h : RepresentsCompleteBernstein μ a b f) (hgf : EqOn g f (Ici 0)) :
    RepresentsCompleteBernstein μ a b g :=
  ⟨h.measure_singleton_zero, h.integrable_weight, hgf.trans h.2.2⟩

private lemma integrable_div_add (hμ : Integrable stieltjesWeight μ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : ℝ≥0 => t / (t + x)) μ := by
  rcases ht.eq_or_lt with rfl | ht
  · have hz : Integrable (fun _ : ℝ≥0 => (0 : ℝ)) μ := integrable_zero ℝ≥0 ℝ μ
    simpa only [zero_div] using hz
  · simpa only [div_eq_mul_inv] using (integrable_inv_add hμ ht).const_mul t

/-- The sum of two complete-Bernstein representations is represented by the sum of their
coefficients and measures. -/
lemma add (hf : RepresentsCompleteBernstein μ a b f)
    (hg : RepresentsCompleteBernstein ν c d g) :
    RepresentsCompleteBernstein (μ + ν) (a + c) (b + d) (f + g) := by
  refine ⟨by simp [hf.measure_singleton_zero, hg.measure_singleton_zero],
    hf.integrable_weight.add_measure hg.integrable_weight, fun t ht => ?_⟩
  rw [Pi.add_apply, hf.eq_stieltjesBernsteinTransform ht,
    hg.eq_stieltjesBernsteinTransform ht]
  simp only [stieltjesBernsteinTransform_apply]
  rw [integral_add_measure
      (integrable_div_add hf.integrable_weight ht)
      (integrable_div_add hg.integrable_weight ht)]
  push_cast
  ring

/-- A nonnegative scalar multiple of a complete-Bernstein representation is represented by
scaling its coefficients and measure. -/
lemma smul (h : RepresentsCompleteBernstein μ a b f) {r : ℝ} (hr : 0 ≤ r) :
    RepresentsCompleteBernstein ((ENNReal.ofReal r) • μ)
      (r.toNNReal * a) (r.toNNReal * b) (r • f) := by
  refine ⟨by simp [h.measure_singleton_zero],
    h.integrable_weight.smul_measure ENNReal.ofReal_ne_top, fun t ht => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, h.eq_stieltjesBernsteinTransform ht]
  simp only [stieltjesBernsteinTransform_apply]
  rw [integral_smul_measure]
  · simp only [ENNReal.toReal_ofReal hr, smul_eq_mul]
    push_cast
    rw [Real.coe_toNNReal r hr]
    ring

/-- A function with a complete-Bernstein representation is a Bernstein function. -/
theorem isBernsteinFunction (h : RepresentsCompleteBernstein μ a b f) :
    IsBernsteinFunction f :=
  (isBernsteinFunction_stieltjesBernsteinTransform h.measure_singleton_zero
    h.integrable_weight).congr h.2.2

/-- Dividing a complete Bernstein function by its parameter on `(0, ∞)` gives the Stieltjes
function with the same representing data. -/
theorem representsStieltjes_div (h : RepresentsCompleteBernstein μ a b f) :
    RepresentsStieltjes μ a b (fun t => f t / t) := by
  rw [representsStieltjes_iff]
  refine ⟨h.measure_singleton_zero, h.integrable_weight, fun t ht => ?_⟩
  rw [h.eq_stieltjesBernsteinTransform ht.le, stieltjesBernsteinTransform_apply,
    stieltjesBernsteinIntegral_eq_mul_integral_inv_add]
  field_simp

end RepresentsCompleteBernstein

/-- A real function is a complete Bernstein function if it has the standard Stieltjes-type
representation on `[0, ∞)`. -/
def IsCompleteBernsteinFunction (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ≥0, ∃ μ : Measure ℝ≥0, RepresentsCompleteBernstein μ a b f

/-- Characterization of a complete Bernstein function by its representing data. -/
theorem isCompleteBernsteinFunction_iff {f : ℝ → ℝ} :
    IsCompleteBernsteinFunction f ↔
      ∃ a b : ℝ≥0, ∃ μ : Measure ℝ≥0, RepresentsCompleteBernstein μ a b f :=
  Iff.rfl

namespace IsCompleteBernsteinFunction

variable {f g : ℝ → ℝ}

/-- Every complete Bernstein function is a Bernstein function. -/
@[grind =>]
theorem isBernsteinFunction (hf : IsCompleteBernsteinFunction f) : IsBernsteinFunction f := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact hμ.isBernsteinFunction

/-- The complete Bernstein property depends only on values on `[0, ∞)`. -/
theorem congr (hf : IsCompleteBernsteinFunction f) (hgf : EqOn g f (Ici 0)) :
    IsCompleteBernsteinFunction g := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact ⟨a, b, μ, hμ.congr hgf⟩

/-- Complete Bernstein functions are closed under addition. -/
lemma add (hf : IsCompleteBernsteinFunction f) (hg : IsCompleteBernsteinFunction g) :
    IsCompleteBernsteinFunction (f + g) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  obtain ⟨c, d, ν, hν⟩ := hg
  exact ⟨a + c, b + d, μ + ν, hμ.add hν⟩

/-- Complete Bernstein functions are closed under multiplication by a nonnegative scalar. -/
lemma smul (hf : IsCompleteBernsteinFunction f) {r : ℝ} (hr : 0 ≤ r) :
    IsCompleteBernsteinFunction (r • f) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact ⟨r.toNNReal * a, r.toNNReal * b, ENNReal.ofReal r • μ, hμ.smul hr⟩

/-- Dividing a complete Bernstein function by its parameter gives a Stieltjes function. -/
theorem isStieltjesFunction_div (hf : IsCompleteBernsteinFunction f) :
    IsStieltjesFunction (fun t => f t / t) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  rw [isStieltjesFunction_iff]
  exact ⟨a, b, μ, hμ.representsStieltjes_div⟩

end IsCompleteBernsteinFunction

/-- The Stieltjes--Bernstein transform of normalized, integrable measure data has a complete
Bernstein representation with the given measure and coefficients. -/
theorem representsCompleteBernstein_stieltjesBernsteinTransform
    {μ : Measure ℝ≥0} {a b : ℝ≥0} (hzero : μ {0} = 0)
    (hμ : Integrable stieltjesWeight μ) :
    RepresentsCompleteBernstein μ a b (stieltjesBernsteinTransform μ a b) :=
  ⟨hzero, hμ, fun _ _ => rfl⟩

/-- The Stieltjes--Bernstein transform of normalized, integrable measure data is a complete
Bernstein function. -/
theorem isCompleteBernsteinFunction_stieltjesBernsteinTransform
    {μ : Measure ℝ≥0} {a b : ℝ≥0} (hzero : μ {0} = 0)
    (hμ : Integrable stieltjesWeight μ) :
    IsCompleteBernsteinFunction (stieltjesBernsteinTransform μ a b) :=
  ⟨a, b, μ, representsCompleteBernstein_stieltjesBernsteinTransform hzero hμ⟩

/-- **Stieltjes--complete-Bernstein correspondence.** A function `f` is Stieltjes exactly when
its product `t ↦ t * f t` on `(0, ∞)` extends to a complete Bernstein function on `[0, ∞)`.
The extension's value at zero records the coefficient of the possible `t⁻¹` singularity. -/
theorem isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_mul
    {f : ℝ → ℝ} :
    IsStieltjesFunction f ↔
      ∃ g : ℝ → ℝ, IsCompleteBernsteinFunction g ∧
        EqOn g (fun t => t * f t) (Ioi 0) := by
  constructor
  · intro hf
    rw [isStieltjesFunction_iff] at hf
    obtain ⟨a, b, μ, hμ⟩ := hf
    exact ⟨stieltjesBernsteinTransform μ a b,
      isCompleteBernsteinFunction_stieltjesBernsteinTransform hμ.measure_singleton_zero
        hμ.integrable_weight,
      fun _ ht => hμ.stieltjesBernsteinTransform_eq_mul ht⟩
  · rintro ⟨g, ⟨a, b, μ, hμ⟩, hgf⟩
    rw [isStieltjesFunction_iff]
    refine ⟨a, b, μ, hμ.representsStieltjes_div.congr fun t ht => ?_⟩
    calc
      f t = t * f t / t := (mul_div_cancel_left₀ (f t) (ne_of_gt ht)).symm
      _ = g t / t := congrArg (fun y : ℝ => y / t) (hgf ht).symm

/-- Nonnegative constant functions are complete Bernstein functions. -/
theorem isCompleteBernsteinFunction_const {c : ℝ} (hc : 0 ≤ c) :
    IsCompleteBernsteinFunction (fun _ : ℝ => c) := by
  rw [isCompleteBernsteinFunction_iff]
  refine ⟨c.toNNReal, 0, 0, ?_⟩
  rw [representsCompleteBernstein_iff]
  refine ⟨by simp, integrable_zero_measure, fun t _ => ?_⟩
  simp [stieltjesBernsteinTransform_apply, Real.coe_toNNReal c hc]

/-- The identity function is a complete Bernstein function. -/
theorem isCompleteBernsteinFunction_id : IsCompleteBernsteinFunction id := by
  rw [isCompleteBernsteinFunction_iff]
  refine ⟨0, 1, 0, ?_⟩
  rw [representsCompleteBernstein_iff]
  refine ⟨by simp, integrable_zero_measure, fun t _ => ?_⟩
  simp [stieltjesBernsteinTransform_apply]

/-- For `x > 0`, the basic function `t ↦ t / (t + x)` is complete Bernstein, represented by
the unit point mass at `x`. -/
theorem isCompleteBernsteinFunction_div_add {x : ℝ} (hx : 0 < x) :
    IsCompleteBernsteinFunction (fun t : ℝ => t / (t + x)) := by
  let xₙ := x.toNNReal
  have hxₙ : xₙ ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hx)
  rw [isCompleteBernsteinFunction_iff]
  refine ⟨0, 0, Measure.dirac xₙ, ?_⟩
  rw [representsCompleteBernstein_iff]
  refine ⟨by simp [hxₙ], integrable_dirac (by simp), fun t _ => ?_⟩
  rw [stieltjesBernsteinTransform_apply, integral_dirac]
  simp [xₙ, Real.coe_toNNReal x hx.le]

end TauCeti

end

end
