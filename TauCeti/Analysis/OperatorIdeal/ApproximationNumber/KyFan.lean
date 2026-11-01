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
* `ContinuousLinearMap.kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le`: compressing a map
  to subspaces of its source and target does not increase its Ky Fan gauges.
* `ContinuousLinearMap.norm_sum_inner_le_kyFanGauge`: **Ky Fan's maximum principle**,
  `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ Kₖ(T)` for orthonormal families `(uᵢ)`, `(vᵢ)` with `k` members.
* `TauCeti.HasMinMaxLowerBound.kyFanGauge_le_of_forall_compression`: on a pair with the converse
  min–max localization property, a bound on the Ky Fan gauges of all finite-dimensional
  compressions of `T` bounds those of `T`.
* `TauCeti.HasMinMaxLowerBound.kyFanGauge_add_le`: on a pair with the converse min–max
  localization property, `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`.
* `TauCeti.HasMinMaxLowerBound.kyFanGauge_le_iff`: on a pair with the converse min–max
  localization property, the variational characterization of `Kₖ(T)` by sums
  `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖` over pairs of orthonormal families.
* `ContinuousLinearMap.kyFanGauge_add_le`: **Ky Fan triangle inequality**,
  `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` for bounded linear maps on a complete inner product space.
* `ContinuousLinearMap.kyFanGauge_le_iff`: the variational characterization of `Kₖ(T)` by sums
  `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖` over pairs of orthonormal families, for a complete source space.

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

/-- The **variational characterization of Ky Fan gauges from the converse min–max localization.**
On a pair with the property `HasMinMaxLowerBound`, `Kₖ(T) ≤ c` exactly when
`‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ c` for all orthonormal families `(uᵢ)` in `F` and `(vᵢ)` in `E` with at most
`k` members. -/
theorem HasMinMaxLowerBound.kyFanGauge_le_iff (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F)
    {k : ℕ} {c : ℝ} :
    (T.kyFanGauge k : ℝ) ≤ c ↔ ∀ m ≤ k, ∀ (u : Fin m → F) (v : Fin m → E), Orthonormal 𝕜 u →
      Orthonormal 𝕜 v → ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ ≤ c := by
  refine ⟨fun hc m hm u v hu hv ↦ ?_, fun hc ↦ ?_⟩
  · have := T.norm_sum_inner_le_kyFanGauge hu hv
    rw [Fintype.card_fin] at this
    exact this.trans ((NNReal.coe_le_coe.mpr (T.monotone_kyFanGauge hm)).trans hc)
  refine h.kyFanGauge_le_of_forall_compression T fun V _ ↦ ?_
  -- The finite-dimensional variational characterization bounds the compression to `V`.
  rw [kyFanGauge_eq_kyFanSum]
  refine (LinearMap.kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_
  simpa using hc m hm _ _ (hu.comp_linearIsometry (Submodule.subtypeₗᵢ _))
    (hv.comp_linearIsometry V.subtypeₗᵢ)

end TauCeti

namespace ContinuousLinearMap

/-- **Ky Fan triangle inequality.** For bounded linear maps from a complete inner product space to
an inner product space, the Ky Fan gauges are subadditive: `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`. -/
theorem kyFanGauge_add_le [CompleteSpace E] (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  TauCeti.HasMinMaxLowerBound.of_completeSpace.kyFanGauge_add_le S T k

/-- The **variational characterization** of the Ky Fan gauges: on a complete source space,
`Kₖ(T) ≤ c` exactly when `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ c` for all orthonormal families `(uᵢ)` in `F` and
`(vᵢ)` in `E` with at most `k` members. -/
theorem kyFanGauge_le_iff [CompleteSpace E] (T : E →L[𝕜] F) {k : ℕ} {c : ℝ} :
    (T.kyFanGauge k : ℝ) ≤ c ↔ ∀ m ≤ k, ∀ (u : Fin m → F) (v : Fin m → E), Orthonormal 𝕜 u →
      Orthonormal 𝕜 v → ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ ≤ c :=
  TauCeti.HasMinMaxLowerBound.of_completeSpace.kyFanGauge_le_iff T

end ContinuousLinearMap
