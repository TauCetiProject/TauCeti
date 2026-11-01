/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# Ky Fan's maximum principle for approximation numbers

For a bounded linear map `T : E →L[𝕜] F` between inner product spaces, the Ky Fan gauge
`Kₖ(T) = a₀(T) + ⋯ + aₖ₋₁(T)` is the sum of its first `k` approximation numbers. This file proves
Ky Fan's maximum principle in arbitrary dimension: for orthonormal families `(uᵢ)` in `F` and
`(vᵢ)` in `E` with `k` members,

  `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ Kₖ(T)`,

and, when `E` is complete, `Kₖ(T)` is the supremum of these sums over families with at most `k`
members. The upper bound compresses `T` to the finite-dimensional spans of the two families, where
it is the finite-dimensional maximum principle `LinearMap.norm_sum_inner_le_kyFanSum`. The
supremum uses the finite-dimensional compressions of `T` which keep its first `k` approximation
numbers up to any `ε > 0` (`TauCeti.HasMinMaxLowerBound.exists_singularValue_le_compression`).

For a positive operator `T` on a Hilbert space it suffices to take `u = v`: `Kₖ(T)` is the
supremum of the diagonal sums `∑ᵢ re ⟪T wᵢ, wᵢ⟫` over orthonormal families with at most `k`
members. The bound `2 ‖⟪x, T y⟫‖ ≤ re ⟪T x, x⟫ + re ⟪T y, y⟫`
(`ContinuousLinearMap.IsPositive.two_mul_norm_inner_le_add`) bounds a mixed sum by the average of
two diagonal sums.

The diagonal form gives the **superadditivity** of the Ky Fan gauges on positive operators,

  `Kₖ(S) + Kₗ(T) ≤ Kₖ₊ₗ(S + T)`,

which reverses the Ky Fan triangle inequality `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` at the cost of doubling
the index when `k = l`. Two orthonormal families with `k` and `l` members span a space of
dimension at most `k + l`, and on it the diagonal sums of the positive compressions of `S` and `T`
are at most their traces. The two inequalities together are what make Dixmier traces, which are
generalized limits of the logarithmic means `Kₙ(T) / log n`, additive on positive operators.

## Main declarations

* `ContinuousLinearMap.norm_sum_inner_le_kyFanGauge`: Ky Fan's maximum principle, the upper bound.
* `ContinuousLinearMap.kyFanGauge_le_iff`: the variational characterization of `Kₖ(T)` by sums
  over pairs of orthonormal families, for a complete source space.
* `ContinuousLinearMap.IsPositive.kyFanGauge_le_iff`: the variational characterization of `Kₖ(T)`
  by diagonal sums, for a positive operator on a Hilbert space.
* `ContinuousLinearMap.IsPositive.kyFanGauge_add_kyFanGauge_le`: superadditivity
  `Kₖ(S) + Kₗ(T) ≤ Kₖ₊ₗ(S + T)` for positive operators on a Hilbert space.

## References

* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II, §4.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §2.β.
-/

public section

open Module Finset

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace ContinuousLinearMap

/-- **Ky Fan's maximum principle**, the upper bound: for orthonormal families `(uᵢ)` in `F` and
`(vᵢ)` in `E` with `k` members, `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖` is at most the Ky Fan gauge `Kₖ(T)`. -/
theorem norm_sum_inner_le_kyFanGauge (T : E →L[𝕜] F) {ι : Type*} [Fintype ι] {u : ι → F}
    {v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ‖∑ i, ⟪u i, T (v i)⟫‖ ≤ T.kyFanGauge (Fintype.card ι) := by
  set V := Submodule.span 𝕜 (Set.range v)
  set W := Submodule.span 𝕜 (Set.range u)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  have hvV (i : ι) : v i ∈ V := Submodule.subset_span ⟨i, rfl⟩
  have huW (i : ι) : u i ∈ W := Submodule.subset_span ⟨i, rfl⟩
  -- The compression `V → W` of `T`, between finite-dimensional spaces.
  set C : V →L[𝕜] W := W.orthogonalProjectionOnto.comp (T.comp V.subtypeL)
  have hC : C.kyFanGauge (Fintype.card ι) ≤ T.kyFanGauge (Fintype.card ι) :=
    T.kyFanGauge_orthogonalProjectionOnto_comp_comp_subtypeL_le V W _
  -- The two families as orthonormal families in `W` and `V`.
  set u' : ι → W := fun i ↦ ⟨u i, huW i⟩
  set v' : ι → V := fun i ↦ ⟨v i, hvV i⟩
  have hsum : ∑ i, ⟪u i, T (v i)⟫ = ∑ i, ⟪u' i, C (v' i)⟫ := by
    simp [u', v', C]
  rw [hsum]
  refine le_trans ?_ (NNReal.coe_le_coe.mpr hC)
  rw [kyFanGauge_eq_kyFanSum]
  exact (C : V →ₗ[𝕜] W).norm_sum_inner_le_kyFanSum (hu.codRestrict W huW) (hv.codRestrict V hvV)

/-- The **variational characterization** of the Ky Fan gauges: on a complete source space,
`Kₖ(T) ≤ c` exactly when `‖∑ᵢ ⟪uᵢ, T vᵢ⟫‖ ≤ c` for all orthonormal families `(uᵢ)` in `F` and
`(vᵢ)` in `E` with at most `k` members. -/
theorem kyFanGauge_le_iff [CompleteSpace E] (T : E →L[𝕜] F) {k : ℕ} {c : ℝ} :
    (T.kyFanGauge k : ℝ) ≤ c ↔ ∀ m ≤ k, ∀ (u : Fin m → F) (v : Fin m → E), Orthonormal 𝕜 u →
      Orthonormal 𝕜 v → ‖∑ i, ⟪u i, T (v i)⟫‖ ≤ c := by
  refine ⟨fun h m hm u v hu hv ↦ ?_, fun h ↦ ?_⟩
  · have := T.norm_sum_inner_le_kyFanGauge hu hv
    rw [Fintype.card_fin] at this
    exact this.trans ((NNReal.coe_le_coe.mpr (T.monotone_kyFanGauge hm)).trans h)
  refine TauCeti.HasMinMaxLowerBound.of_completeSpace.kyFanGauge_le_of_forall_compression T
    fun V _ ↦ ?_
  -- The finite-dimensional variational characterization bounds the compression to `V`.
  rw [kyFanGauge_eq_kyFanSum]
  refine (LinearMap.kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_
  simpa using h m hm _ _ (hu.comp_linearIsometry (Submodule.subtypeₗᵢ _))
    (hv.comp_linearIsometry V.subtypeₗᵢ)

namespace IsPositive

/-- **Ky Fan's maximum principle for positive operators**: for a positive operator `T` on a
Hilbert space, `Kₖ(T) ≤ c` exactly when `∑ᵢ re ⟪T wᵢ, wᵢ⟫ ≤ c` for every orthonormal family
`(wᵢ)` with at most `k` members. -/
theorem kyFanGauge_le_iff [CompleteSpace E] {T : E →L[𝕜] E} (hT : T.IsPositive) {k : ℕ}
    {c : ℝ} :
    (T.kyFanGauge k : ℝ) ≤ c ↔
      ∀ m ≤ k, ∀ w : Fin m → E, Orthonormal 𝕜 w → ∑ i, RCLike.re ⟪T (w i), w i⟫ ≤ c := by
  refine ⟨fun h m hm w hw ↦ ?_, fun h ↦ T.kyFanGauge_le_iff.mpr fun m hm u v hu hv ↦ ?_⟩
  · refine le_trans ?_ (T.kyFanGauge_le_iff.mp h m hm w w hw hw)
    simp_rw [hT.inner_left_eq_inner_right, ← map_sum]
    exact RCLike.re_le_norm _
  calc ‖∑ i, ⟪u i, T (v i)⟫‖
      ≤ ∑ i, (RCLike.re ⟪T (u i), u i⟫ + RCLike.re ⟪T (v i), v i⟫) / 2 :=
        (norm_sum_le _ _).trans <| sum_le_sum fun i _ ↦ by
          linarith [hT.two_mul_norm_inner_le_add (u i) (v i)]
    _ ≤ c := by
        rw [← sum_div, sum_add_distrib]
        linarith [h m hm u hu, h m hm v hv]

variable {S T : E →L[𝕜] E}

/-- On the span of two orthonormal families with `m` and `m'` members, the diagonal sums of
positive `S` and `T` are at most the traces of their compressions, whose sum is a diagonal sum of
`S + T` over an orthonormal basis with at most `m + m'` members. -/
private theorem sum_re_inner_add_sum_re_inner_le_kyFanGauge (hS : S.IsPositive)
    (hT : T.IsPositive) {m m' : ℕ} {w : Fin m → E} {w' : Fin m' → E} (hw : Orthonormal 𝕜 w)
    (hw' : Orthonormal 𝕜 w') :
    ∑ i, RCLike.re ⟪S (w i), w i⟫ + ∑ j, RCLike.re ⟪T (w' j), w' j⟫ ≤
      (S + T).kyFanGauge (m + m') := by
  set U := Submodule.span 𝕜 (Set.range (Sum.elim w w'))
  have : FiniteDimensional 𝕜 U := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  have hU : finrank 𝕜 U ≤ m + m' := (finrank_range_le_card _).trans (by simp)
  -- `C X` is the compression of `X` to `U`.
  set C : (E →L[𝕜] E) → U →L[𝕜] U := fun X ↦ U.orthogonalProjectionOnto.comp (X.comp U.subtypeL)
  have hdiag {X : E →L[𝕜] E} (hX : X.IsPositive) {n : ℕ} {x : Fin n → E} (hx : Orthonormal 𝕜 x)
      (hxU : ∀ i, x i ∈ U) :
      ∑ i, RCLike.re ⟪X (x i), x i⟫ ≤ RCLike.re (LinearMap.trace 𝕜 U (C X)) := by
    have hCX : (C X : U →ₗ[𝕜] U).IsPositive :=
      (isPositive_toLinearMap_iff _).mpr (hX.orthogonalProjectionOnto_comp U)
    simpa [C] using hCX.sum_re_inner_apply_self_le_re_trace (hx.codRestrict U hxU)
  set b := stdOrthonormalBasis 𝕜 U
  have hb := b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  calc ∑ i, RCLike.re ⟪S (w i), w i⟫ + ∑ j, RCLike.re ⟪T (w' j), w' j⟫
      ≤ RCLike.re (LinearMap.trace 𝕜 U (C S)) + RCLike.re (LinearMap.trace 𝕜 U (C T)) :=
        add_le_add (hdiag hS hw fun i ↦ Submodule.subset_span ⟨.inl i, rfl⟩)
          (hdiag hT hw' fun j ↦ Submodule.subset_span ⟨.inr j, rfl⟩)
    _ = RCLike.re (∑ l, ⟪(b l : E), (S + T) (b l)⟫) := by
        rw [← map_add, ← map_add, LinearMap.trace_eq_sum_inner _ b]
        simp [C, inner_add_right, sum_add_distrib]
    _ ≤ (S + T).kyFanGauge (Fintype.card (Fin (finrank 𝕜 U))) :=
        (RCLike.re_le_norm _).trans ((S + T).norm_sum_inner_le_kyFanGauge hb hb)
    _ ≤ (S + T).kyFanGauge (m + m') := by
        rw [Fintype.card_fin]
        exact_mod_cast (S + T).monotone_kyFanGauge hU

/-- **Superadditivity of the Ky Fan gauges** on positive operators: for positive `S` and `T` on a
Hilbert space, `Kₖ(S) + Kₗ(T) ≤ Kₖ₊ₗ(S + T)`. -/
theorem kyFanGauge_add_kyFanGauge_le [CompleteSpace E] (hS : S.IsPositive) (hT : T.IsPositive)
    (k l : ℕ) : S.kyFanGauge k + T.kyFanGauge l ≤ (S + T).kyFanGauge (k + l) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add, ← le_sub_iff_add_le]
  refine hS.kyFanGauge_le_iff.mpr fun m hm w hw ↦ ?_
  rw [le_sub_comm]
  refine hT.kyFanGauge_le_iff.mpr fun m' hm' w' hw' ↦ ?_
  rw [le_sub_iff_add_le']
  exact (sum_re_inner_add_sum_re_inner_le_kyFanGauge hS hT hw hw').trans
    (by exact_mod_cast (S + T).monotone_kyFanGauge (add_le_add hm hm'))

end IsPositive

end ContinuousLinearMap
