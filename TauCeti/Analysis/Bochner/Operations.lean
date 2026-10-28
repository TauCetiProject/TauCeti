/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Group.Convolution
public import TauCeti.Analysis.Bochner.BochnerTheorem
import TauCeti.Analysis.Bochner.Fourier.Convention

/-!
# Operations on Bochner measures

Bochner's theorem (`TauCeti.bochner`) identifies a continuous positive-definite function
`F : V → ℂ` on a finite-dimensional real inner-product space with its representing finite
measure `TauCeti.bochnerMeasure F`, through `F v = ∫ q, fourierAtom v q ∂(bochnerMeasure F)`.
This file records how the standard operations on positive-definite functions act on the
representing measure:

* a product of continuous positive-definite functions is represented by the **convolution** of
  their measures;
* the **Fourier atom** `v ↦ fourierAtom v ξ` is represented by the Dirac mass at `ξ`, and the
  constant function `1` by the Dirac mass at `0`;
* **modulating** `F` by the atom `v ↦ fourierAtom v ξ` **translates** its measure by `ξ`;
* **reflecting** `F` through `v ↦ -v`, or **conjugating** it, reflects its measure;
* **pulling `F` back** along a continuous linear map `T` pushes its measure forward along the
  adjoint `T†`.

The atom, translation, reflection and conjugation rules need no hypothesis on `F`: each
operation is invertible and preserves continuity and positive definiteness, so outside the
hypotheses of Bochner's theorem both sides are `0`. The product and pullback rules need the
hypotheses, since a product or a pullback can be positive definite without its factors being so.

## Main declarations

* `TauCeti.bochnerMeasure_mul`: the Bochner measure of a product is the convolution of the
  Bochner measures.
* `TauCeti.bochnerMeasure_fourierAtom` and `TauCeti.bochnerMeasure_one`: Dirac masses.
* `TauCeti.bochnerMeasure_fourierAtom_mul`: modulation translates the Bochner measure.
* `TauCeti.bochnerMeasure_comp_neg` and `TauCeti.bochnerMeasure_conj`: reflection and
  conjugation reflect the Bochner measure.
* `TauCeti.bochnerMeasure_comp_continuousLinearMap`: pullback along `T` pushes the Bochner
  measure forward along `T†`.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), §1.3 (the Fourier–Stieltjes transform of
  convolutions and translates of measures) and §1.4 (Bochner's theorem).
-/

public section

open MeasureTheory ComplexConjugate
open scoped InnerProduct

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

variable {F H : V → ℂ}

/-- **Products become convolutions.** The Bochner measure of the product of two continuous
positive-definite functions is the convolution of their Bochner measures. -/
theorem bochnerMeasure_mul (hFcont : Continuous F) (hFpd : IsPositiveDefiniteSub F)
    (hHcont : Continuous H) (hHpd : IsPositiveDefiniteSub H) :
    bochnerMeasure (fun v => F v * H v) = bochnerMeasure F ∗ bochnerMeasure H := by
  refine (eq_bochnerMeasure (F := fun v => F v * H v) _ fun v => ?_).symm
  rw [integral_fourierAtom_conv, integral_fourierAtom_bochnerMeasure hFcont hFpd,
    integral_fourierAtom_bochnerMeasure hHcont hHpd]

/-- The Fourier atom `v ↦ fourierAtom v ξ` is represented by the Dirac mass at `ξ`.

Not a `@[simp]` lemma: `simp` rewrites the atom through `fourierAtom_apply` first, so the
left-hand side is not in simp normal form. -/
theorem bochnerMeasure_fourierAtom (ξ : V) :
    bochnerMeasure (fun v => fourierAtom v ξ) = Measure.dirac ξ :=
  (eq_bochnerMeasure _ fun v => by rw [integral_dirac]).symm

/-- The constant function `1` is represented by the Dirac mass at `0`. -/
@[simp]
theorem bochnerMeasure_one : bochnerMeasure (fun _ : V => (1 : ℂ)) = Measure.dirac 0 := by
  simpa only [fourierAtom_zero_right] using bochnerMeasure_fourierAtom (0 : V)

/-- The Fourier atom `v ↦ fourierAtom v ξ` is continuous and positive definite, being the
transform of the Dirac mass at `ξ`. -/
theorem continuous_and_isPositiveDefiniteSub_fourierAtom (ξ : V) :
    Continuous (fun v => fourierAtom v ξ) ∧ IsPositiveDefiniteSub (fun v => fourierAtom v ξ) :=
  continuous_and_isPositiveDefiniteSub_of_integral_fourierAtom_eq (Measure.dirac ξ)
    fun v => by rw [integral_dirac]

/-- **Modulation translates the Bochner measure.** Multiplying a function by the Fourier atom
`v ↦ fourierAtom v ξ` translates its Bochner measure by `ξ`. No hypothesis on `F` is needed:
multiplication by the atom is undone by multiplication by the atom at `-ξ`, so both sides are
`0` outside the hypotheses of Bochner's theorem. -/
theorem bochnerMeasure_fourierAtom_mul (ξ : V) (F : V → ℂ) :
    bochnerMeasure (fun v => fourierAtom v ξ * F v) = (bochnerMeasure F).map (· + ξ) := by
  by_cases h : Continuous F ∧ IsPositiveDefiniteSub F
  · refine (eq_bochnerMeasure (F := fun v => fourierAtom v ξ * F v) _ fun v => ?_).symm
    rw [integral_map (measurable_add_const ξ).aemeasurable
        (continuous_fourierAtom v).aestronglyMeasurable]
    simp_rw [fourierAtom_add_right]
    rw [integral_mul_const, integral_fourierAtom_bochnerMeasure h.1 h.2, mul_comm]
  · rw [bochnerMeasure_eq_zero_of_not h, Measure.map_zero, bochnerMeasure_eq_zero_of_not]
    rintro ⟨hcont, hpd⟩
    obtain ⟨hξcont, hξpd⟩ := continuous_and_isPositiveDefiniteSub_fourierAtom (-ξ)
    have hF : (fun v => fourierAtom v (-ξ) * (fourierAtom v ξ * F v)) = F := by
      funext v
      rw [← mul_assoc, ← fourierAtom_add_right, neg_add_cancel, fourierAtom_zero_right, one_mul]
    rw [← hF] at h
    exact h ⟨hξcont.mul hcont, hξpd.mul hpd⟩

/-- **Reflection reflects the Bochner measure.** The Bochner measure of `v ↦ F (-v)` is the
image of the Bochner measure of `F` under negation. No hypothesis on `F` is needed: reflection is
an involution preserving continuity and positive definiteness. -/
@[simp]
theorem bochnerMeasure_comp_neg (F : V → ℂ) :
    bochnerMeasure (fun v => F (-v)) = (bochnerMeasure F).map Neg.neg := by
  by_cases h : Continuous F ∧ IsPositiveDefiniteSub F
  · refine (eq_bochnerMeasure (F := fun v => F (-v)) _ fun v => ?_).symm
    rw [integral_map measurable_neg.aemeasurable (continuous_fourierAtom v).aestronglyMeasurable,
      ← integral_fourierAtom_bochnerMeasure h.1 h.2 (-v)]
    simp only [fourierAtom_apply, inner_neg_left, inner_neg_right]
  · rw [bochnerMeasure_eq_zero_of_not h, Measure.map_zero, bochnerMeasure_eq_zero_of_not]
    rintro ⟨hcont, hpd⟩
    refine h ⟨?_, ?_⟩
    · simpa only [Function.comp_def, neg_neg] using hcont.comp continuous_neg
    · simpa only [neg_neg] using hpd.comp_neg

/-- **Conjugation reflects the Bochner measure.** The Bochner measure of `v ↦ conj (F v)` is the
image of the Bochner measure of `F` under negation. No hypothesis on `F` is needed: conjugation
is an involution preserving continuity and positive definiteness. -/
@[simp]
theorem bochnerMeasure_conj (F : V → ℂ) :
    bochnerMeasure (fun v => conj (F v)) = (bochnerMeasure F).map Neg.neg := by
  by_cases h : Continuous F ∧ IsPositiveDefiniteSub F
  · have hF : (fun v => conj (F v)) = fun v => F (-v) := funext fun v => (h.2.map_neg v).symm
    rw [hF, bochnerMeasure_comp_neg]
  · rw [bochnerMeasure_eq_zero_of_not h, Measure.map_zero, bochnerMeasure_eq_zero_of_not]
    rintro ⟨hcont, hpd⟩
    -- the conjugate of `F` is positive definite, so its reflection, which is `F`, is too
    have hF : (fun v => conj (F (-v))) = F := funext fun v => by
      rw [hpd.map_neg v, Complex.conj_conj]
    rw [← hF] at h
    exact h ⟨hcont.comp continuous_neg, hpd.comp_neg⟩

section Pullback

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

/-- **Pullback pushes the Bochner measure forward along the adjoint.** For a continuous
positive-definite `F` on `V` and a continuous linear map `T : W →L[ℝ] V`, the Bochner measure of
`w ↦ F (T w)` is the image of the Bochner measure of `F` under the adjoint `T†`. -/
theorem bochnerMeasure_comp_continuousLinearMap (T : W →L[ℝ] V) (hcont : Continuous F)
    (hpd : IsPositiveDefiniteSub F) :
    bochnerMeasure (fun w => F (T w)) = (bochnerMeasure F).map (T†) := by
  refine (eq_bochnerMeasure (F := fun w => F (T w)) _ fun w => ?_).symm
  rw [integral_map (T†).continuous.aemeasurable (continuous_fourierAtom w).aestronglyMeasurable,
    ← integral_fourierAtom_bochnerMeasure hcont hpd (T w)]
  simp only [fourierAtom_apply, ContinuousLinearMap.adjoint_inner_left]

end Pullback

end TauCeti
