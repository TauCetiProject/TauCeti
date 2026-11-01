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
inequality applies to the compressions. Every pair whose source space is complete has the
localization property (`TauCeti.HasMinMaxLowerBound.of_completeSpace`), so the triangle
inequality holds for bounded linear maps from a Hilbert space to an inner product space.

## Main declarations

* `ContinuousLinearMap.kyFanGauge_eq_kyFanSum`: between finite-dimensional inner product spaces,
  `Kₖ(T)` is the Ky Fan `k`-sum of the singular values of `T`.
* `ContinuousLinearMap.kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le`: compressing a map
  to subspaces of its source and target does not increase its Ky Fan gauges.
* `TauCeti.HasMinMaxLowerBound.kyFanGauge_le_of_forall_compression`: on a pair with the converse
  min–max localization property, a bound on the Ky Fan gauges of all finite-dimensional
  compressions of `T` bounds those of `T`.
* `TauCeti.HasMinMaxLowerBound.kyFanGauge_add_le`: on a pair with the converse min–max
  localization property, `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`.
* `ContinuousLinearMap.kyFanGauge_add_le`: **Ky Fan triangle inequality**,
  `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` for bounded linear maps on a complete inner product space.

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

/-- Compressing `T` to subspaces `V ≤ E` and `W ≤ F`, by the inclusion of `V` and the orthogonal
projection onto `W`, does not increase its Ky Fan gauges. -/
theorem kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le (T : E →L[𝕜] F)
    (V : Submodule 𝕜 E) (W : Submodule 𝕜 F) [W.HasOrthogonalProjection] (k : ℕ) :
    (W.orthogonalProjectionOnto.comp (T.comp V.subtypeL)).kyFanGauge k ≤ T.kyFanGauge k := by
  simp only [kyFanGauge_def]
  exact Finset.sum_le_sum fun n _ ↦
    T.singularValue_orthogonalProjectionOnto_comp_comp_subtypeL_le V W n

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

/-- **Ky Fan gauges from finite-dimensional compressions.** On a pair with the converse min–max
localization property, `Kₖ(T) ≤ c` as soon as `Kₖ(C) ≤ c` for the compression `C : V → T(V)` of `T`
to every finite-dimensional subspace `V ≤ E`, followed by the orthogonal projection onto `T(V)`. -/
theorem HasMinMaxLowerBound.kyFanGauge_le_of_forall_compression (h : HasMinMaxLowerBound 𝕜 E F)
    (T : E →L[𝕜] F) {k : ℕ} {c : ℝ}
    (hc : ∀ (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V],
      (((V.map (T : E →ₗ[𝕜] F)).orthogonalProjectionOnto.comp
        (T.comp V.subtypeL)).kyFanGauge k : ℝ) ≤ c) :
    (T.kyFanGauge k : ℝ) ≤ c := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨V, _, hV⟩ := h.exists_singularValue_le_compression T k (δ := ε / (k + 1))
    (by positivity)
  set C := (V.map (T : E →ₗ[𝕜] F)).orthogonalProjectionOnto.comp (T.comp V.subtypeL)
  calc (T.kyFanGauge k : ℝ)
      ≤ ∑ n ∈ Finset.range k, ((C.singularValue n : ℝ) + ε / (k + 1)) := by
        rw [kyFanGauge_def, NNReal.coe_sum]
        exact Finset.sum_le_sum fun n hn ↦ hV n (Finset.mem_range.mp hn)
    _ = C.kyFanGauge k + k * (ε / (k + 1)) := by
        simp [Finset.sum_add_distrib, kyFanGauge_def]
    _ ≤ c + ε := by
        gcongr
        · exact hc V
        · rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith

/-- **Ky Fan triangle inequality from the converse min–max localization.** On a pair of inner
product spaces with the property `HasMinMaxLowerBound`, the Ky Fan gauges are subadditive:
`Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`. -/
theorem HasMinMaxLowerBound.kyFanGauge_add_le (h : HasMinMaxLowerBound 𝕜 E F)
    (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add]
  refine h.kyFanGauge_le_of_forall_compression (S + T) fun V _ ↦ ?_
  set P := (V.map (S + T : E →ₗ[𝕜] F)).orthogonalProjectionOnto
  calc ((P.comp ((S + T).comp V.subtypeL)).kyFanGauge k : ℝ)
      ≤ (P.comp (S.comp V.subtypeL)).kyFanGauge k + (P.comp (T.comp V.subtypeL)).kyFanGauge k := by
        -- The finite-dimensional Ky Fan inequality for the compressions.
        rw [add_comp, comp_add, kyFanGauge_eq_kyFanSum, kyFanGauge_eq_kyFanSum,
          kyFanGauge_eq_kyFanSum, toLinearMap_add]
        exact LinearMap.kyFanSum_add_le _ _ k
    _ ≤ S.kyFanGauge k + T.kyFanGauge k := by
        gcongr <;> exact_mod_cast kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le _ V _ k

end TauCeti

namespace ContinuousLinearMap

/-- **Ky Fan triangle inequality.** For bounded linear maps from a complete inner product space to
an inner product space, the Ky Fan gauges are subadditive: `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`. -/
theorem kyFanGauge_add_le [CompleteSpace E] (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  TauCeti.HasMinMaxLowerBound.of_completeSpace.kyFanGauge_add_le S T k

end ContinuousLinearMap
