/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# Ky Fan gauges of positive operators

For a positive operator `T` on a Hilbert space, the Ky Fan gauge
`Kₖ(T) = a₀(T) + ⋯ + aₖ₋₁(T)` is the supremum of the diagonal sums `∑ᵢ re ⟪vᵢ, T vᵢ⟫` along
orthonormal families of at most `k` vectors (`ContinuousLinearMap.IsPositive.kyFanGauge_le_iff`).
This is Ky Fan's maximum principle for positive operators: one orthonormal family does the work of
the two families in the general principle `ContinuousLinearMap.norm_sum_inner_le_kyFanGauge`.

The upper bound is the general principle. For the lower bound, the converse min–max
localization `TauCeti.HasMinMaxLowerBound.exists_singularValue_le_compression_endomorphism`
approximates the first `k` approximation numbers of `T` by those of a compression of `T` to a
finite-dimensional subspace `U`, and the compression is again positive. On `U` the leading
singular pairs attain the Ky Fan sum as `∑ᵢ ⟪uᵢ, T vᵢ⟫`, and positivity of the quadratic form,
`2 re ⟪u, T v⟫ ≤ re ⟪u, T u⟫ + re ⟪v, T v⟫`, shows that the diagonal sum along `(vᵢ)` attains it
too (`LinearMap.IsPositive.exists_orthonormal_sum_re_inner_eq_kyFanSum`).

The variational description gives the converse of the Ky Fan triangle inequality for positive
operators, `Kₖ(S) + Kₗ(T) ≤ Kₖ₊ₗ(S + T)`
(`ContinuousLinearMap.IsPositive.kyFanGauge_add_kyFanGauge_le`): two nearly maximizing families span
a subspace of dimension at most `k + l`, and the diagonal sums of `S` and `T` along each family
are at most their traces on that subspace. Combined with `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`, this is the
estimate making the logarithmic means `Kₙ(T) / log (1 + n)` additive in the limit on positive
operators, and hence Dixmier traces additive on the positive part of the logarithmic ideal.

## Main declarations

* `ContinuousLinearMap.IsPositive.exists_orthonormal_kyFanGauge_le_sum_re_inner_add`: up to any
  `ε > 0`, some orthonormal family of at most `k` vectors attains `Kₖ(T)` on the diagonal.
* `ContinuousLinearMap.IsPositive.kyFanGauge_le_iff`: Ky Fan's maximum principle for positive
  operators.
* `ContinuousLinearMap.IsPositive.kyFanGauge_add_kyFanGauge_le`: `Kₖ(S) + Kₗ(T) ≤ Kₖ₊ₗ(S + T)`
  for positive `S` and `T`.

## References

* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §2.β.
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 1.
-/

public section

open scoped InnerProductSpace NNReal
open Module

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace ContinuousLinearMap

/-- **Ky Fan's maximum principle for positive operators**, approximate attainment: for a positive
operator `T` on a Hilbert space and `ε > 0`, some orthonormal family of at most `k` vectors has
`a₀(T) + ⋯ + aₖ₋₁(T) ≤ ∑ᵢ re ⟪vᵢ, T vᵢ⟫ + ε`. -/
theorem IsPositive.exists_orthonormal_kyFanGauge_le_sum_re_inner_add
    {T : E →L[𝕜] E} (hT : T.IsPositive) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (v : Fin m → E), m ≤ k ∧ Orthonormal 𝕜 v ∧
      (T.kyFanGauge k : ℝ) ≤ ∑ i, RCLike.re ⟪v i, T (v i)⟫_𝕜 + ε := by
  obtain ⟨U, _, hU⟩ := (TauCeti.HasMinMaxLowerBound.of_completeSpace (𝕜 := 𝕜) (E := E)
    (F := E)).exists_singularValue_le_compression_endomorphism T k (δ := ε / (k + 1))
    (by positivity)
  -- The compression `C` of `T` to `U` is positive, so a single orthonormal family in `U` attains
  -- its Ky Fan sum on the diagonal.
  set C := U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL
  set m := min k (finrank 𝕜 (LinearMap.range (C : U →ₗ[𝕜] U)))
  have hm : m ≤ finrank 𝕜 U := (min_le_right _ _).trans (Submodule.finrank_le _)
  obtain ⟨v, hv, hsum⟩ :=
    (hT.orthogonalProjectionOnto_comp U).toLinearMap.exists_orthonormal_sum_re_inner_eq_kyFanSum hm
  refine ⟨m, fun i ↦ v i, min_le_left _ _, hv.comp_linearIsometry U.subtypeₗᵢ, ?_⟩
  have hsum' : ∑ i, RCLike.re ⟪(v i : E), T (v i)⟫_𝕜 = C.kyFanGauge k := by
    rw [kyFanGauge_eq_kyFanSum, ← LinearMap.kyFanSum_min_finrank_range, ← hsum]
    simp
  calc (T.kyFanGauge k : ℝ)
      ≤ ∑ n ∈ Finset.range k, ((C.singularValue n : ℝ) + ε / (k + 1)) := by
        rw [kyFanGauge_def, NNReal.coe_sum]
        exact Finset.sum_le_sum fun n hn ↦ hU n (Finset.mem_range.1 hn)
    _ = C.kyFanGauge k + k * (ε / (k + 1)) := by
        simp [Finset.sum_add_distrib, kyFanGauge_def]
    _ ≤ ∑ i, RCLike.re ⟪(v i : E), T (v i)⟫_𝕜 + ε := by
        rw [hsum']
        gcongr
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **Ky Fan's maximum principle for positive operators.** For a positive operator `T` on a Hilbert
space, `a₀(T) + ⋯ + aₖ₋₁(T) ≤ c` exactly when `∑ᵢ re ⟪vᵢ, T vᵢ⟫ ≤ c` for every orthonormal family
`(vᵢ)` of at most `k` vectors. -/
theorem IsPositive.kyFanGauge_le_iff {T : E →L[𝕜] E} (hT : T.IsPositive)
    {k : ℕ} {c : ℝ} :
    (T.kyFanGauge k : ℝ) ≤ c ↔ ∀ m ≤ k, ∀ v : Fin m → E, Orthonormal 𝕜 v →
      ∑ i, RCLike.re ⟪v i, T (v i)⟫_𝕜 ≤ c := by
  refine ⟨fun h m hm v hv ↦ ?_, fun h ↦ le_of_forall_pos_le_add fun ε hε ↦ ?_⟩
  · calc ∑ i, RCLike.re ⟪v i, T (v i)⟫_𝕜 ≤ ‖∑ i, ⟪v i, T (v i)⟫_𝕜‖ := by
          simpa [map_sum] using RCLike.re_le_norm (∑ i, ⟪v i, T (v i)⟫_𝕜)
      _ ≤ T.kyFanGauge m := by simpa using T.norm_sum_inner_le_kyFanGauge hv hv
      _ ≤ T.kyFanGauge k := by exact_mod_cast T.monotone_kyFanGauge hm
      _ ≤ c := h
  · obtain ⟨m, v, hm, hv, hle⟩ := hT.exists_orthonormal_kyFanGauge_le_sum_re_inner_add k hε
    linarith [h m hm v hv]

/-- **Ky Fan superadditivity for positive operators.** For positive operators `S` and `T` on a
Hilbert space, `Kₖ(S) + Kₗ(T) ≤ Kₖ₊ₗ(S + T)`, where `Kₖ` is the sum of the first `k` approximation
numbers. Together with the triangle inequality `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` this gives
`Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T) ≤ K₂ₖ(S + T)`. -/
theorem IsPositive.kyFanGauge_add_kyFanGauge_le {S T : E →L[𝕜] E}
    (hS : S.IsPositive) (hT : T.IsPositive) (k l : ℕ) :
    S.kyFanGauge k + T.kyFanGauge l ≤ (S + T).kyFanGauge (k + l) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨m, v, hm, hv, hSv⟩ := hS.exists_orthonormal_kyFanGauge_le_sum_re_inner_add k
    (half_pos hε)
  obtain ⟨m', w, hm', hw, hTw⟩ := hT.exists_orthonormal_kyFanGauge_le_sum_re_inner_add l
    (half_pos hε)
  -- Both families lie in the span `U` of their union, of dimension at most `k + l`.
  set U := Submodule.span 𝕜 (Set.range (Sum.elim v w))
  have : FiniteDimensional 𝕜 U :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  have hU : finrank 𝕜 U ≤ k + l :=
    (finrank_range_le_card (R := 𝕜) (Sum.elim v w)).trans (by simpa using add_le_add hm hm')
  -- The diagonal sums along `v` and `w` are bounded by the traces of the compressions to `U`.
  set comp : (E →L[𝕜] E) → U →L[𝕜] U := fun X ↦ U.orthogonalProjectionOnto ∘L X ∘L U.subtypeL
  have hdiag {X : E →L[𝕜] E} (hX : X.IsPositive) {n : ℕ} {x : Fin n → E} (hx : Orthonormal 𝕜 x)
      (hxU : ∀ i, x i ∈ U) :
      ∑ i, RCLike.re ⟪x i, X (x i)⟫_𝕜 ≤ RCLike.re ((comp X : U →ₗ[𝕜] U).trace 𝕜 U) := by
    have := (hX.orthogonalProjectionOnto_comp U).toLinearMap.sum_re_inner_le_re_trace
      (hx.codRestrict U hxU)
    simpa [comp] using this
  have hvS := hdiag hS hv fun i ↦ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hwT := hdiag hT hw fun i ↦ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  -- The trace of the compression of `S + T` is a diagonal sum along an orthonormal basis of `U`.
  set b := stdOrthonormalBasis 𝕜 U
  have htr : RCLike.re ((comp S : U →ₗ[𝕜] U).trace 𝕜 U) +
      RCLike.re ((comp T : U →ₗ[𝕜] U).trace 𝕜 U) ≤ (S + T).kyFanGauge (k + l) := by
    rw [← map_add, ← map_add, ← toLinearMap_add]
    have hcomp : comp S + comp T = comp (S + T) := by simp [comp, add_comp, comp_add]
    have hinner (X : E →L[𝕜] E) (x : U) :
        ⟪x, (comp X : U →ₗ[𝕜] U) x⟫_𝕜 = ⟪(x : E), X x⟫_𝕜 := by
      simp [comp]
    rw [hcomp, LinearMap.trace_eq_sum_inner _ b]
    simp only [hinner]
    calc RCLike.re (∑ i, ⟪(b i : E), (S + T) (b i)⟫_𝕜)
        ≤ ‖∑ i, ⟪(b i : E), (S + T) (b i)⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ (S + T).kyFanGauge (Fintype.card (Fin (finrank 𝕜 U))) :=
          (S + T).norm_sum_inner_le_kyFanGauge (b.orthonormal.comp_linearIsometry U.subtypeₗᵢ)
            (b.orthonormal.comp_linearIsometry U.subtypeₗᵢ)
      _ ≤ (S + T).kyFanGauge (k + l) := by
          exact_mod_cast (S + T).monotone_kyFanGauge (by simpa using hU)
  linarith

end ContinuousLinearMap
