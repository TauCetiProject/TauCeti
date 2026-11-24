/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation

/-!
# Translation of first-order Sobolev fields on the whole space

For an additive Haar measure on a finite-dimensional real normed space `E`, translation by a
vector `h` acts on the first-order weak-derivative graph
`W^{1,p}(E, F) = TauCeti.WeakDerivStep mu ⊤ p (id)` over `Lᵖ(E, F)`: it sends `u` to
`x ↦ u (x + h)` and its weak derivative `Du` to `x ↦ Du (x + h)`
(`TauCeti.HasWeakFDerivOn.translateLp`). Since both components are translated by the same `Lᵖ`
isometry, the result is a linear isometric equivalence of the graph space
(`TauCeti.WeakDerivStep.translateLIE`), with inverse translation by `-h`.

On the line, translation moves the coefficient of a first-order operator along with the field, so
it identifies operators that agree after a shift of the variable, as in the splicing of operators
along a long neck.

## Main declarations

* `TauCeti.WeakDerivStep.translateLIE`: translation by `h` on `W^{1,p}(E, F)`.
* `TauCeti.WeakDerivStep.prev_translateLIE`, `TauCeti.WeakDerivStep.weakFDeriv_translateLIE`:
  it translates the field and its weak derivative in `Lᵖ`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.3.1 (translation of Sobolev functions).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti.WeakDerivStep

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance graphStepTranslation_isAddHaarMeasure :
    (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/-- Translation by `h` on `W^{1,p}(E, F)` as a bounded linear map; it is packaged as the linear
isometric equivalence `TauCeti.WeakDerivStep.translateLIE`. -/
private def translateL (h : E) :
    WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))
      →L[ℝ] WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E)))) :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      (((((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h :
          Lp F p _ ≃ₗᵢ[ℝ] Lp F p _).toContinuousLinearEquiv.toContinuousLinearMap).comp
          (prevL _)).prod
        ((((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h :
          Lp (E →L[ℝ] F) p _ ≃ₗᵢ[ℝ] Lp (E →L[ℝ] F) p _
            ).toContinuousLinearEquiv.toContinuousLinearMap).comp (weakFDerivL _))))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr (by
      simpa [-Opens.coe_top] using (hasWeakFDerivOn_base_prev _ u).translateLp h)

private theorem prev_translateL (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    prev _ (translateL h u) = (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (prev _ u) := by
  simp [-Opens.coe_top, prev_coe, translateL]

private theorem weakFDeriv_translateL (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    weakFDeriv _ (translateL h u) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (weakFDeriv _ u) := by
  simp [-Opens.coe_top, weakFDeriv_coe, translateL]

private theorem translateL_neg_translateL (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    translateL (-h) (translateL h u) = u := by
  refine ext_prev_weakFDeriv ?_ ?_
  · rw [prev_translateL, prev_translateL, ← Measure.translateLp_symm,
      LinearIsometryEquiv.symm_apply_apply]
  · rw [weakFDeriv_translateL, weakFDeriv_translateL, ← Measure.translateLp_symm,
      LinearIsometryEquiv.symm_apply_apply]

private theorem norm_translateL (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    ‖translateL h u‖ = ‖u‖ := by
  have h₁ : ‖prev _ (translateL h u)‖ = ‖prev _ u‖ := by
    rw [prev_translateL]
    exact LinearIsometryEquiv.norm_map _ _
  have h₂ : ‖weakFDeriv _ (translateL h u)‖ = ‖weakFDeriv _ u‖ := by
    rw [weakFDeriv_translateL]
    exact LinearIsometryEquiv.norm_map _ _
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq,
    norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, h₁, h₂]

/-- **Translation on `W^{1,p}(E, F)`.** Translation by `h` sends a field `u` with weak derivative
`Du` to `x ↦ u (x + h)`, with weak derivative `x ↦ Du (x + h)`. It is a linear isometric
equivalence of the graph space, with inverse translation by `-h`
(`TauCeti.WeakDerivStep.translateLIE_symm`). -/
def translateLIE (h : E) :
    WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))
      ≃ₗᵢ[ℝ] WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E)))) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (translateL h).toLinearMap
      norm_map' := norm_translateL h }
    fun u ↦ ⟨translateL (-h) u, by simpa using translateL_neg_translateL (-h) u⟩

private theorem translateLIE_apply (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    translateLIE h u = translateL h u :=
  rfl

/-- Translation translates the field in `Lᵖ`. -/
theorem prev_translateLIE (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    prev _ (translateLIE h u) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (prev _ u) :=
  prev_translateL h u

/-- Translation translates the weak derivative in `Lᵖ`. -/
theorem weakFDeriv_translateLIE (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    weakFDeriv _ (translateLIE h u) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (weakFDeriv _ u) :=
  weakFDeriv_translateL h u

/-- The translated field is represented almost everywhere by `x ↦ u (x + h)`. -/
theorem prev_translateLIE_ae (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    ⇑(prev _ (translateLIE h u)) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      fun x ↦ prev _ u (x + h) := by
  rw [prev_translateLIE]
  exact Measure.coeFn_translateLp h _

/-- The translated weak derivative is represented almost everywhere by `x ↦ Du (x + h)`. -/
theorem weakFDeriv_translateLIE_ae (h : E)
    (u : WeakDerivStep mu ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict ((⊤ : Opens E) : Set E))))) :
    ⇑(weakFDeriv _ (translateLIE h u)) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      fun x ↦ weakFDeriv _ u (x + h) := by
  rw [weakFDeriv_translateLIE]
  exact Measure.coeFn_translateLp h _

/-- The inverse of translation by `h` is translation by `-h`. -/
@[simp]
theorem translateLIE_symm (h : E) :
    (translateLIE (F := F) (mu := mu) (p := p) h).symm = translateLIE (-h) :=
  LinearIsometryEquiv.ext fun u ↦ by
    refine (translateLIE (F := F) (mu := mu) (p := p) h).injective ?_
    rw [LinearIsometryEquiv.apply_symm_apply, translateLIE_apply, translateLIE_apply]
    simpa using (translateL_neg_translateL (-h) u).symm

end TauCeti.WeakDerivStep
