/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.SpecialFunctions.CantorFunction
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval

/-!
# The Cantor function is not an interval Sobolev function

The Cantor–Lebesgue function is continuous and has classical derivative zero almost
everywhere, but has no locally integrable weak derivative on `(0,1)`. In particular it
cannot represent an element of `W^{1,p}(0,1)` for any `1 ≤ p ≤ ∞`. This distinguishes the
weak-derivative definition from mere almost-everywhere classical differentiability.

We also obtain a smooth test function supported compactly inside `(0,1)` for which
`∫ φ' C ≠ 0`: the zero classical derivative fails the defining weak-derivative identity.

## References

* G. Leoni, *A First Course in Sobolev Spaces*, Chapter 7, for the distinction between
  absolutely continuous and almost-everywhere differentiable representatives.
* O. Dovgoshey, O. Martio, V. Ryazanov, M. Vuorinen, *The Cantor function*,
  Expositiones Mathematicae **24** (2006), 1–37.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace TauCeti

/-- The Cantor function has no weak derivative on `(0,1)`, even if only local integrability
is required of the candidate derivative. Its almost-everywhere classical derivative therefore
does not supply a weak derivative. -/
theorem not_hasWeakLineDerivOn_cantorFunction (g : ℝ → ℝ) :
    ¬ HasWeakLineDerivOn volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ cantorFunction g 1 := by
  intro h
  have hg : g =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun _ ↦ 0 := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [h.ae_hasDerivAt continuous_cantorFunction.continuousOn
      Filter.EventuallyEq.rfl (by norm_num), ae_hasDerivAt_cantorFunction] with x hx hC hmem
    exact (hx (by simpa using Ioo_subset_Ioc_self hmem)).unique hC
  have hzero := h.congr_ae_deriv hg
  exact not_absolutelyContinuousOnInterval_cantorFunction
    (hzero.absolutelyContinuousOnInterval (integrableOn_zero)
      continuous_cantorFunction.continuousOn Filter.EventuallyEq.rfl (by norm_num))

/-- Some smooth test function compactly supported in `(0,1)` detects the nonzero
distributional derivative of the Cantor function. In particular, the candidate weak
derivative zero fails the test-function identity. -/
theorem exists_testFunction_integral_lineDeriv_mul_cantorFunction_ne_zero :
    ∃ φ : 𝓓((⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ : Opens ℝ), ℝ),
      (∫ x, lineDeriv ℝ (φ : ℝ → ℝ) x 1 * cantorFunction x) ≠ 0 := by
  classical
  by_contra! h
  apply not_hasWeakLineDerivOn_cantorFunction (fun _ ↦ 0)
  apply hasWeakLineDerivOn_iff_testFunction.2
  refine ⟨inferInstance, continuous_cantorFunction.continuousOn.locallyIntegrableOn
    measurableSet_Ioo, locallyIntegrableOn_zero, fun φ ↦ ?_⟩
  simpa only [smul_eq_mul, mul_zero, integral_zero, neg_zero] using h φ

/-- No Sobolev class in `W^{1,p}(0,1)` has the Cantor function as an almost-everywhere
representative, for any `1 ≤ p ≤ ∞`. -/
theorem W1p.value_not_ae_eq_cantorFunction {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p) :
    ¬ value u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] cantorFunction := by
  intro hu
  have h := ((hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)).congr_ae hu
  exact not_hasWeakLineDerivOn_cantorFunction _ h

end TauCeti
