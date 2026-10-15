/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation of weak derivatives

Weak differentiability is invariant under translations that stay inside the domain. If `u` has
weak Fréchet derivative `U` on `Ω`, and `x + h ∈ Ω` for every `x ∈ V`, then `x ↦ u (x + h)` has
weak derivative `x ↦ U (x + h)` on `V`. Consequently the difference quotient

`x ↦ t⁻¹ • (u (x + t • w) - u x)`

has weak derivative `x ↦ t⁻¹ • (U (x + t • w) - U x)` wherever both terms are defined. This is
the local translation rule used by difference-quotient proofs of interior Sobolev regularity.

The proof translates each compactly supported test function in the opposite direction and uses
translation invariance of the additive Haar measure. No regularity of the boundary of either
domain is needed.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.comp_add_right`: translation of a weak directional derivative.
* `TauCeti.HasWeakFDerivOn.comp_add_right`: translation of a weak Fréchet derivative.
* `TauCeti.HasWeakFDerivOn.translateLp`: whole-space translation of an `Lᵖ` weak derivative.
* `TauCeti.HasWeakFDerivOn.differenceQuotient`: the weak derivative of a difference quotient.

## References

* L. C. Evans, *Partial Differential Equations*, §5.8.2 and §6.3.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.23 and §8.8.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped Distributions

namespace TauCeti

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega V : Opens E}
  {u u' : E → F} {U : E → E →L[ℝ] F} {v h : E}

local instance weakDerivTranslation_isAddHaarMeasure :
    (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/-- A translated function has the translated weak directional derivative on every open set whose
translate lies in the original domain. -/
theorem HasWeakLineDerivOn.comp_add_right
    (hu : HasWeakLineDerivOn mu Omega u u' v) (hVO : MapsTo (· + h) V Omega) :
    HasWeakLineDerivOn mu V (fun x => u (x + h)) (fun x => u' (x + h)) v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨hu.completeSpace,
    MeasureTheory.LocallyIntegrableOn.comp_add_right_of_mapsTo hu.locallyIntegrableOn hVO,
    MeasureTheory.LocallyIntegrableOn.comp_add_right_of_mapsTo
      hu.locallyIntegrableOn_deriv hVO,
    fun phi => ?_⟩
  let psi := translateTestFunction hVO phi
  have hleft :
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • u (x + h) ∂mu) =
        ∫ y, lineDeriv ℝ (psi : E → ℝ) y v • u y ∂mu := by
    simpa only [psi, lineDeriv_translateTestFunction, add_sub_cancel_right] using
      integral_add_right_eq_self
        (fun y => lineDeriv ℝ (psi : E → ℝ) y v • u y) h
  have hright :
      (∫ x, (phi : E → ℝ) x • u' (x + h) ∂mu) =
        ∫ y, (psi : E → ℝ) y • u' y ∂mu := by
    simpa only [psi, translateTestFunction_apply, add_sub_cancel_right] using
      integral_add_right_eq_self (fun y => (psi : E → ℝ) y • u' y) h
  rw [hleft, hright]
  exact hu.integral_lineDeriv_smul_eq_neg_integral_smul psi

/-- A translated function has the translated weak Fréchet derivative on every open set whose
translate lies in the original domain. -/
theorem HasWeakFDerivOn.comp_add_right
    (hu : HasWeakFDerivOn mu Omega u U) (hVO : MapsTo (· + h) V Omega) :
    HasWeakFDerivOn mu V (fun x => u (x + h)) (fun x => U (x + h)) := by
  rw [hasWeakFDerivOn_iff]
  intro w
  exact (hu.hasWeakLineDerivOn w).comp_add_right hVO

/-- On the whole space, translating an `Lᵖ` function and its weak Fréchet derivative by the
same vector preserves the weak-derivative identity. -/
theorem HasWeakFDerivOn.translateLp {p : ENNReal} [Fact (1 ≤ p)]
    {f : Lp F p (mu.restrict ((⊤ : Opens E) : Set E))}
    {D : Lp (E →L[ℝ] F) p (mu.restrict ((⊤ : Opens E) : Set E))}
    (hf : HasWeakFDerivOn mu ⊤ f D) (h : E) :
    HasWeakFDerivOn mu ⊤
      ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h f)
      ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h D) := by
  let nu := mu.restrict ((⊤ : Opens E) : Set E)
  have htrans := hf.comp_add_right (V := (⊤ : Opens E)) (h := h) (fun _ _ => by simp)
  exact (htrans.congr_ae (Measure.coeFn_translateLp (mu := nu) h f).symm).congr_ae_deriv
    (Measure.coeFn_translateLp (mu := nu) h D).symm

/-- The weak derivative of the difference quotient of `u` in direction `w` with step `t` is the
corresponding difference quotient of its weak derivative. Both `V ⊆ Ω` and
`V + t • w ⊆ Ω` are explicit because both values occur in the quotient. -/
theorem HasWeakFDerivOn.differenceQuotient
    (hu : HasWeakFDerivOn mu Omega u U) (hV : V ≤ Omega) {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) V Omega) :
    HasWeakFDerivOn mu V (fun x => t⁻¹ • (u (x + t • w) - u x))
      (fun x => t⁻¹ • (U (x + t • w) - U x)) := by
  exact ((hu.comp_add_right hVO).sub (hu.mono hV)).const_smul t⁻¹

end TauCeti
