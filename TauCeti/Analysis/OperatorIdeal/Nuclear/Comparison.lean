/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Nuclear.Basic
public import TauCeti.Analysis.Normed.Operator.Nuclear

/-!
# Trace-class gauge bounded by the nuclear norm

On Hilbert spaces, the sum of the approximation numbers is at most the projective nuclear
norm. Consequently every nuclear operator between Hilbert spaces has summable approximation
numbers, so it belongs to the trace-class ideal.

The comparison uses the rank-one formula and the Fatou inequality for the approximation-number
gauge on an operator-norm convergent nuclear series. It does not require a Schmidt decomposition.
The reverse inequality, and hence the isometric identification of the two operator ideals,
requires that additional decomposition and is not asserted here.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Chapter 2.
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The sum of the approximation numbers of an operator between Hilbert spaces is bounded by
its projective nuclear norm. Both sides are extended-valued, so this also applies to operators
which are not nuclear. -/
theorem nuclearENorm_le_nuclearGauge (T : E →L[𝕜] F) :
    T.nuclearENorm ≤ TauCeti.nuclearGauge 𝕜 E F T := by
  apply le_of_forall_gt
  intro c hc
  obtain ⟨f, y, hsum, -, hcost⟩ :=
    TauCeti.exists_hasSum_smulRight_of_nuclearGauge_lt hc
  have hbound : T.nuclearENorm ≤ ∑' n, ‖f n‖ₑ * ‖y n‖ₑ := by
    simpa using nuclearENorm_le_tsum_of_hasSum hsum
  exact hbound.trans_lt hcost

/-- A nuclear operator between Hilbert spaces has summable approximation numbers. -/
theorem summable_singularValue_of_mem_nuclearOperators {T : E →L[𝕜] F}
    (hT : T ∈ TauCeti.nuclearOperators 𝕜 E F) : Summable T.singularValue := by
  apply T.nuclearENorm_ne_top_iff_summable.mp
  exact ((T.nuclearENorm_le_nuclearGauge).trans_lt
    (TauCeti.nuclearGauge_lt_top_iff.mpr hT)).ne

end ContinuousLinearMap
