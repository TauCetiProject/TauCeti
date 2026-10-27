/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.OperatorNorm
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# The Ky Fan operator-ideal families

For each positive integer `k`, the sum of the first `k` approximation numbers defines
an operator-ideal family on real or complex Hilbert spaces. Every bounded operator has
finite gauge, so the ideal is the whole space of bounded operators, equipped with its
Ky Fan norm. These carriers are complete. At `k = 1` the family is the operator-norm family.

The construction uses `ContinuousLinearMap.kyFanGauge` and its triangle and ideal
inequalities. Completeness follows from continuity of this gauge and the general
lower-semicontinuous-gauge criterion for operator-ideal carriers.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press, 1987, Chapter 2.
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

noncomputable section

open scoped ENNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable (𝕜 : Type u) [RCLike 𝕜]

/-- The operator-ideal family given by the sum of the first `k` approximation numbers.
The positivity assumption ensures that the gauge dominates the operator norm. -/
def kyFan (k : ℕ) (hk : 0 < k) : OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge A := A.kyFanGauge k
  gauge_add_le A B := by exact_mod_cast A.kyFanGauge_add_le B k
  gauge_smul c A := by
    simp [ContinuousLinearMap.kyFanGauge_smul, enorm_eq_nnnorm]
  enorm_le_gauge A := by
    simpa only [enorm_eq_nnnorm, ENNReal.coe_le_coe] using A.nnnorm_le_kyFanGauge hk
  gauge_comp_le L A R := by
    simpa only [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using
      L.kyFanGauge_comp_comp_le A R k

variable {𝕜}
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

@[simp]
theorem gauge_kyFan (k : ℕ) (hk : 0 < k) (A : E →L[𝕜] F) :
    (kyFan 𝕜 k hk).gauge A = (A.kyFanGauge k : ℝ≥0∞) := (rfl)

variable (E F) in
/-- Every bounded operator lies in each finite Ky Fan ideal. -/
@[simp]
theorem finiteSubmodule_kyFan (k : ℕ) (hk : 0 < k) :
    ((kyFan 𝕜 k hk).operatorGauge E F).finiteSubmodule = ⊤ :=
  eq_top_iff.2 fun A _ ↦ by simp

/-- Every finite Ky Fan operator-ideal family has complete normed carriers. -/
instance kyFan_isComplete (k : ℕ) (hk : 0 < k) :
    (kyFan.{u, v, w} 𝕜 k hk).IsComplete :=
  isComplete_of_lowerSemicontinuous fun _ _ _ _ _ _ _ _ ↦
    (ENNReal.continuous_coe.comp
      (ContinuousLinearMap.continuous_kyFanGauge k)).lowerSemicontinuous

/-- The first Ky Fan family is the operator-norm family. -/
@[simp]
theorem kyFan_one : kyFan.{u, v, w} 𝕜 1 (by decide) = opNorm 𝕜 := by
  ext
  simp [enorm_eq_nnnorm]

end OperatorIdealFamily

end TauCeti
