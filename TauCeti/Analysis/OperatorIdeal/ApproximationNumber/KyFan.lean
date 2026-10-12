/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.KyFan
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# The Ky Fan triangle inequality for approximation numbers

The Ky Fan gauge `Kₖ(T) = a₀(T) + ⋯ + aₖ₋₁(T)` of a bounded linear map `T : E →L[𝕜] F` is the sum
of its first `k` approximation numbers. Between finite-dimensional inner product spaces it is the
Ky Fan `k`-sum of singular values `LinearMap.kyFanSum`, by Eckart–Young, and so satisfies Ky Fan's
triangle inequality `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`.

This file carries the triangle inequality to inner product spaces of arbitrary dimension, on every
pair `E`, `F` with the converse min–max localization property `TauCeti.HasMinMaxLowerBound`. On such
a pair the first `k` approximation numbers of `S + T` are, up to any `ε > 0`, those of a compression
of `S + T` to finite-dimensional subspaces `V ≤ E` and `W ≤ F`
(`TauCeti.HasMinMaxLowerBound.exists_singularValue_le_compression`). Compressing `S` and `T` in the
same way does not increase their approximation numbers, and the finite-dimensional Ky Fan
inequality applies to the compressions.

## Main declarations

* `ContinuousLinearMap.kyFanGauge_eq_kyFanSum`: between finite-dimensional inner product spaces,
  `Kₖ(T)` is the Ky Fan `k`-sum of the singular values of `T`.
* `TauCeti.HasMinMaxLowerBound.kyFanGauge_add_le`: on a pair with the converse min–max
  localization property, `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II, §4.
-/

public section

open scoped NNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- **Eckart–Young for Ky Fan gauges.** Between finite-dimensional inner product spaces, the Ky Fan
gauge `Kₖ(T)` of a bounded linear map is the Ky Fan `k`-sum `σ₀(T) + ⋯ + σₖ₋₁(T)` of its singular
values. -/
theorem kyFanGauge_eq_kyFanSum (T : E →L[𝕜] F) (k : ℕ) :
    (T.kyFanGauge k : ℝ) = (T : E →ₗ[𝕜] F).kyFanSum k := by
  simp [kyFanGauge_def, LinearMap.kyFanSum_def, singularValue_eq_linearMap_singularValues]

end ContinuousLinearMap

namespace TauCeti

open ContinuousLinearMap

/-- **Ky Fan triangle inequality from the converse min–max localization.** On a pair of inner
product spaces with the property `HasMinMaxLowerBound`, the Ky Fan gauges are subadditive:
`Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`. -/
theorem HasMinMaxLowerBound.kyFanGauge_add_le (h : HasMinMaxLowerBound 𝕜 E F)
    (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨V, _, hV⟩ := h.exists_singularValue_le_compression (S + T) k
    (δ := ε / (k + 1)) (by positivity)
  set P := (V.map (S + T : E →ₗ[𝕜] F)).orthogonalProjectionOnto
  -- Compressing by `P` and the inclusion of `V`, both of norm at most one, does not increase
  -- approximation numbers.
  have hcomp : ∀ X : E →L[𝕜] F,
      (P.comp (X.comp V.subtypeL)).kyFanGauge k ≤ X.kyFanGauge k := fun X ↦
    calc (P.comp (X.comp V.subtypeL)).kyFanGauge k
        ≤ ‖P‖₊ * X.kyFanGauge k * ‖V.subtypeL‖₊ := kyFanGauge_comp_comp_le _ _ _ k
      _ ≤ 1 * X.kyFanGauge k * 1 := by
        gcongr
        · exact_mod_cast Submodule.orthogonalProjectionOnto_norm_le _
        · exact_mod_cast V.norm_subtypeL_le
      _ = X.kyFanGauge k := by rw [one_mul, mul_one]
  -- The finite-dimensional Ky Fan inequality for the compressions.
  have hfin : ((P.comp ((S + T).comp V.subtypeL)).kyFanGauge k : ℝ) ≤
      (P.comp (S.comp V.subtypeL)).kyFanGauge k + (P.comp (T.comp V.subtypeL)).kyFanGauge k := by
    rw [add_comp, comp_add, kyFanGauge_eq_kyFanSum, kyFanGauge_eq_kyFanSum, kyFanGauge_eq_kyFanSum,
      toLinearMap_add]
    exact LinearMap.kyFanSum_add_le _ _ k
  calc ((S + T).kyFanGauge k : ℝ)
      ≤ ∑ n ∈ Finset.range k,
          ((P.comp ((S + T).comp V.subtypeL)).singularValue n + ε / (k + 1)) := by
        rw [kyFanGauge_def, NNReal.coe_sum]
        exact Finset.sum_le_sum fun n hn ↦ hV n (Finset.mem_range.mp hn)
    _ = (P.comp ((S + T).comp V.subtypeL)).kyFanGauge k + k * (ε / (k + 1)) := by
        simp [Finset.sum_add_distrib, kyFanGauge_def]
    _ ≤ S.kyFanGauge k + T.kyFanGauge k + ε := by
        gcongr
        · exact hfin.trans (add_le_add (by exact_mod_cast hcomp S) (by exact_mod_cast hcomp T))
        · rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith

end TauCeti
