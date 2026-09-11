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

The predicate defined here *is* the integral representation, that is, the representing clause of
the cited theorem, and it carries exactly the data `μ, a, b` of `TauCeti.RepresentsStieltjes`.
The correspondence below is therefore the change of normalization `f ↦ t f(t)` performed on that
shared data.  The equivalence of the representation with the analytic characterizations of a
complete Bernstein function — extension to a Pick function on `ℂ ∖ (-∞, 0]`, or operator
monotonicity — is not formalized here.

The extension is necessary when the Stieltjes representation has a nonzero `a / t` term: its
value at zero must be `a`, whereas the literal product `0 * f(0)` is zero.  Values of a Stieltjes
function outside `(0, ∞)` remain irrelevant, and values of a complete Bernstein function outside
`[0, ∞)` remain irrelevant.

## Main declarations

* `TauCeti.RepresentsCompleteBernstein`: complete-Bernstein representing data, with the accessors
  `measure_singleton_zero`, `integrable_weight`, `eq_stieltjesBernsteinTransform`, `apply_zero`
  and `congr`.
* `TauCeti.IsCompleteBernsteinFunction`: the representation-based predicate.
* `TauCeti.representsCompleteBernstein_stieltjesBernsteinTransform` and
  `TauCeti.isCompleteBernsteinFunction_stieltjesBernsteinTransform`: the transform of normalized,
  integrable representing data carries the representation.
* `TauCeti.RepresentsCompleteBernstein.add`, `TauCeti.RepresentsCompleteBernstein.smul`,
  `TauCeti.IsCompleteBernsteinFunction.add` and `TauCeti.IsCompleteBernsteinFunction.smul`:
  complete Bernstein functions are closed under sums and nonnegative scalar multiples.
* `TauCeti.IsCompleteBernsteinFunction.isBernsteinFunction`: a complete Bernstein function is a
  Bernstein function.
* `TauCeti.RepresentsCompleteBernstein.representsStieltjes_div` and
  `TauCeti.IsCompleteBernsteinFunction.isStieltjesFunction_div`: dividing a complete Bernstein
  function by its parameter gives a Stieltjes function.
* `TauCeti.isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_mul`: the
  Stieltjes--complete-Bernstein correspondence.
* `TauCeti.isCompleteBernsteinFunction_affine`, `TauCeti.isCompleteBernsteinFunction_const`,
  `TauCeti.isCompleteBernsteinFunction_id` and `TauCeti.isCompleteBernsteinFunction_div_add`:
  the affine, constant, identity and point-mass witnesses.

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

/-- A represented complete Bernstein function takes the value `a` at zero: the boundary value
records the coefficient of the `a / t` term of the associated Stieltjes function. -/
lemma apply_zero (h : RepresentsCompleteBernstein μ a b f) : f 0 = a := by
  simp [h.eq_stieltjesBernsteinTransform le_rfl]

/-- A complete-Bernstein representation depends only on the represented function's values on
`[0, ∞)`. -/
lemma congr (h : RepresentsCompleteBernstein μ a b f) (hgf : EqOn g f (Ici 0)) :
    RepresentsCompleteBernstein μ a b g :=
  ⟨h.measure_singleton_zero, h.integrable_weight, hgf.trans h.2.2⟩

/-- Dividing a complete Bernstein function by its parameter on `(0, ∞)` gives the Stieltjes
function with the same representing data. -/
theorem representsStieltjes_div (h : RepresentsCompleteBernstein μ a b f) :
    RepresentsStieltjes μ a b (fun t => f t / t) := by
  have hcanon : RepresentsStieltjes μ a b
      (fun t => (a : ℝ) / t + (b : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ) :=
    representsStieltjes_iff.mpr ⟨h.measure_singleton_zero, h.integrable_weight, fun _ _ => rfl⟩
  refine hcanon.congr fun t ht => ?_
  rw [h.eq_stieltjesBernsteinTransform (mem_Ioi.mp ht).le,
    hcanon.stieltjesBernsteinTransform_eq_mul (mem_Ioi.mp ht),
    mul_div_cancel_left₀ _ (mem_Ioi.mp ht).ne']

/-- The sum of two complete-Bernstein representations is represented by the sum of their
coefficients and measures. -/
lemma add (hf : RepresentsCompleteBernstein μ a b f)
    (hg : RepresentsCompleteBernstein ν c d g) :
    RepresentsCompleteBernstein (μ + ν) (a + c) (b + d) (f + g) := by
  refine ⟨by simp [hf.measure_singleton_zero, hg.measure_singleton_zero],
    hf.integrable_weight.add_measure hg.integrable_weight, fun t ht => ?_⟩
  rcases (mem_Ici.mp ht).eq_or_lt with rfl | htpos
  · simp [hf.apply_zero, hg.apply_zero]
  · rw [(hf.representsStieltjes_div.add
      hg.representsStieltjes_div).stieltjesBernsteinTransform_eq_mul htpos]
    simp only [Pi.add_apply]
    field_simp [htpos.ne']

/-- A nonnegative scalar multiple of a complete-Bernstein representation is represented by
scaling its coefficients and measure. -/
lemma smul (h : RepresentsCompleteBernstein μ a b f) {r : ℝ} (hr : 0 ≤ r) :
    RepresentsCompleteBernstein ((ENNReal.ofReal r) • μ)
      (r.toNNReal * a) (r.toNNReal * b) (r • f) := by
  refine ⟨by simp [h.measure_singleton_zero],
    h.integrable_weight.smul_measure ENNReal.ofReal_ne_top, fun t ht => ?_⟩
  rcases (mem_Ici.mp ht).eq_or_lt with rfl | htpos
  · simp [h.apply_zero, Real.coe_toNNReal r hr]
  · rw [(h.representsStieltjes_div.smul hr).stieltjesBernsteinTransform_eq_mul htpos]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [htpos.ne']

/-- A function with a complete-Bernstein representation is a Bernstein function. -/
theorem isBernsteinFunction (h : RepresentsCompleteBernstein μ a b f) :
    IsBernsteinFunction f :=
  (isBernsteinFunction_stieltjesBernsteinTransform h.measure_singleton_zero
    h.integrable_weight).congr h.2.2

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
The extension's value at zero records the coefficient of the possible `t⁻¹` singularity.  Both
sides are the same representing data `μ, a, b`, so the content is the change of normalization
`f ↦ t f(t)` and the continuous extension of the product across zero. -/
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

/-- Nonnegative affine functions are complete Bernstein functions. -/
theorem isCompleteBernsteinFunction_affine {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsCompleteBernsteinFunction (fun t : ℝ => c + d * t) := by
  rw [isCompleteBernsteinFunction_iff]
  refine ⟨c.toNNReal, d.toNNReal, 0, ?_⟩
  rw [representsCompleteBernstein_iff]
  refine ⟨by simp, integrable_zero_measure, fun t _ => ?_⟩
  simp [stieltjesBernsteinTransform_apply, Real.coe_toNNReal c hc, Real.coe_toNNReal d hd]

/-- Nonnegative constant functions are complete Bernstein functions. -/
theorem isCompleteBernsteinFunction_const {c : ℝ} (hc : 0 ≤ c) :
    IsCompleteBernsteinFunction (fun _ : ℝ => c) :=
  (isCompleteBernsteinFunction_affine hc le_rfl).congr fun t _ => by simp

/-- The identity function is a complete Bernstein function. -/
theorem isCompleteBernsteinFunction_id : IsCompleteBernsteinFunction (fun t : ℝ => t) :=
  (isCompleteBernsteinFunction_affine le_rfl zero_le_one).congr fun t _ => by simp

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
