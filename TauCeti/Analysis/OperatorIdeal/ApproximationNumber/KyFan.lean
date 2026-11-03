/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.KyFan
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Ky Fan's maximum principle and triangle inequality for approximation numbers

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

Ky Fan's maximum principle `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ Kₖ(T)`, for orthonormal families `(uᵢ)` and `(vᵢ)`
with `k` members, needs no localization: compressing `T` to the spans of the two families reduces
it to the finite-dimensional principle `LinearMap.norm_sum_inner_le_kyFanSum`.

## Main declarations

* `ContinuousLinearMap.kyFanGauge_eq_kyFanSum`: between finite-dimensional inner product spaces,
  `Kₖ(T)` is the Ky Fan `k`-sum of the singular values of `T`.
* `ContinuousLinearMap.norm_sum_inner_le_kyFanGauge`: **Ky Fan's maximum principle**,
  `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ Kₖ(T)` for orthonormal families `(uᵢ)`, `(vᵢ)` with `k` members.
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

open scoped InnerProductSpace NNReal

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

namespace ContinuousLinearMap

/-- Compressing a bounded linear map to subspaces of the source and target does not increase its
Ky Fan gauges. -/
theorem kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le (W : Submodule 𝕜 F)
    [W.HasOrthogonalProjection] (V : Submodule 𝕜 E) (T : E →L[𝕜] F) (k : ℕ) :
    (W.orthogonalProjectionOnto ∘L T ∘L V.subtypeL).kyFanGauge k ≤ T.kyFanGauge k :=
  calc (W.orthogonalProjectionOnto ∘L T ∘L V.subtypeL).kyFanGauge k
      ≤ ‖W.orthogonalProjectionOnto‖₊ * T.kyFanGauge k * ‖V.subtypeL‖₊ :=
        kyFanGauge_comp_comp_le _ _ _ k
    _ ≤ 1 * T.kyFanGauge k * 1 := by
        gcongr
        · exact_mod_cast Submodule.orthogonalProjectionOnto_norm_le _
        · exact_mod_cast V.norm_subtypeL_le
    _ = T.kyFanGauge k := by rw [one_mul, mul_one]

/-- **Ky Fan's maximum principle.** For a bounded linear map `T` between inner product spaces and
orthonormal families `(uᵢ)` in `F` and `(vᵢ)` in `E` with `k` members,
`‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ a₀(T) + ⋯ + aₖ₋₁(T)`. -/
theorem norm_sum_inner_le_kyFanGauge {ι : Type*} [Fintype ι] (T : E →L[𝕜] F) {u : ι → F}
    {v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ ≤ T.kyFanGauge (Fintype.card ι) := by
  -- Compress `T` to the finite-dimensional spans of the two families.
  set V := Submodule.span 𝕜 (Set.range v)
  set W := Submodule.span 𝕜 (Set.range u)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  set v' : ι → V := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  set u' : ι → W := fun i ↦ ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hv' : Orthonormal 𝕜 v' := orthonormal_span hv
  have hu' : Orthonormal 𝕜 u' := orthonormal_span hu
  set C := W.orthogonalProjectionOnto ∘L T ∘L V.subtypeL
  have hsum : ∑ i, ⟪u' i, (C : V →ₗ[𝕜] W) (v' i)⟫_𝕜 = ∑ i, ⟪u i, T (v i)⟫_𝕜 := by
    simp [C, u', v']
  calc ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ = ‖∑ i, ⟪u' i, (C : V →ₗ[𝕜] W) (v' i)⟫_𝕜‖ := by rw [hsum]
    _ ≤ (C : V →ₗ[𝕜] W).kyFanSum (Fintype.card ι) := LinearMap.norm_sum_inner_le_kyFanSum _ hu' hv'
    _ = C.kyFanGauge (Fintype.card ι) := (kyFanGauge_eq_kyFanSum C _).symm
    _ ≤ T.kyFanGauge (Fintype.card ι) := by
        exact_mod_cast kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le W V T _

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
  have hcomp (X : E →L[𝕜] F) : (P.comp (X.comp V.subtypeL)).kyFanGauge k ≤ X.kyFanGauge k :=
    kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le _ V X k
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

namespace ContinuousLinearMap

/-- **Ky Fan triangle inequality.** For bounded linear maps from a complete inner product space to
an inner product space, the Ky Fan gauges are subadditive: `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`. -/
theorem kyFanGauge_add_le [CompleteSpace E] (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  TauCeti.HasMinMaxLowerBound.of_completeSpace.kyFanGauge_add_le S T k

end ContinuousLinearMap
