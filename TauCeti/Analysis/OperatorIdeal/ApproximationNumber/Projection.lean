/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import TauCeti.Analysis.Normed.Module.Quotient

import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Approximation numbers of projections and projection bounds

An orthogonal projection onto a subspace of dimension `r` has approximation numbers equal to
`1` at indices below `r`, and `0` thereafter. This gives an exact finite-rank model for the
zero-based indexing of approximation numbers. For an infinite-dimensional subspace all the
approximation numbers are `1`. The formula uses cardinal dimension and only assumes that the
subspace admits an orthogonal projection; neither the ambient space nor the subspace is required
to be finite-dimensional, and the ambient space need not be complete.

More generally, over any nontrivially normed field and between arbitrary seminormed spaces,
bounded operators and projections of rank at most `n` convert subspace restrictions and quotient
compositions into finite-rank approximants of `T : E →L[𝕜] F`:

* If `P : E →L[𝕜] E` has rank at most `n` and `id - P` maps into `M ≤ E`, then `T ∘L P`
  approximates `T` with error `aₙ(T) ≤ ‖id - P‖ ‖T|_M‖ ≤ (1 + ‖P‖) ‖T|_M‖`
  (`ContinuousLinearMap.singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL`,
  `ContinuousLinearMap.singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL`), specializing to
  bounded idempotents with kernel `M` of codimension at most `n`.
* Dually, if `P : F →L[𝕜] F` has rank at most `n` and fixes `V ≤ F` pointwise, then `P ∘L T`
  approximates `T` with error `aₙ(T) ≤ ‖id - P‖ ‖V.mkQL ∘L T‖ ≤ (1 + ‖P‖) ‖V.mkQL ∘L T‖`
  (`ContinuousLinearMap.singularValue_le_nnnorm_id_sub_mul_nnnorm_mkQL_comp`,
  `ContinuousLinearMap.singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp`), specializing both
  to bounded idempotents whose range contains `V` and to projections `P : F →L[𝕜] V` onto `V`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Inequalities.lean`.
-/

public section

open scoped NNReal

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The approximation numbers of an orthogonal projection are `1` below the dimension of
its range and `0` at every other index. This also applies to infinite-dimensional ranges. -/
@[simp]
theorem singularValue_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (n : ℕ) :
    U.starProjection.singularValue n = if (n : Cardinal) < Module.rank 𝕜 U then 1 else 0 := by
  split_ifs with hn
  · apply le_antisymm
    · exact (U.starProjection.singularValue_le_nnnorm n).trans
        (by exact_mod_cast U.starProjection_norm_le)
    · exact_mod_cast U.starProjection.le_singularValue_of_lt_rank hn
        (c := 1) (fun x hx ↦ by simp [U.norm_starProjection_apply hx])
  · apply ContinuousLinearMap.singularValue_eq_zero_of_rank_le
    rw [LinearMap.rank, range_starProjection]
    exact le_of_not_gt hn

end Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `P : E →L[𝕜] E` has rank at most `n` and `id - P` maps into a submodule `M ≤ E`, then
`aₙ(T) ≤ ‖id - P‖ ‖T|_M‖`. -/
theorem singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL (T : E →L[𝕜] F)
    {M : Submodule 𝕜 E} {P : E →L[𝕜] E} {n : ℕ} (hP : P.rank ≤ n)
    (hM : ∀ x, x - P x ∈ M) :
    T.singularValue n ≤ ‖ContinuousLinearMap.id 𝕜 E - P‖₊ * ‖T ∘L M.subtypeL‖₊ := by
  have hTP : (T ∘L P).rank ≤ n := by
    have h := (LinearMap.lift_rank_comp_le_right P.toLinearMap T.toLinearMap).trans
      (Cardinal.lift_le.mpr hP)
    rwa [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at h
  let Q : E →L[𝕜] M := (ContinuousLinearMap.id 𝕜 E - P).codRestrict M hM
  have hQ : ‖Q‖₊ ≤ ‖ContinuousLinearMap.id 𝕜 E - P‖₊ :=
    opNNNorm_le_bound _ _ fun x ↦ (ContinuousLinearMap.id 𝕜 E - P).le_opNNNorm x
  have hMQ : M.subtypeL ∘L Q = ContinuousLinearMap.id 𝕜 E - P :=
    subtypeL_comp_codRestrict _ _ _
  have hsub : T - T ∘L P = (T ∘L M.subtypeL) ∘L Q := by
    rw [comp_assoc, hMQ, comp_sub, comp_id]
  calc
    T.singularValue n ≤ ‖T - T ∘L P‖₊ := T.singularValue_le_nnnorm_sub hTP
    _ = ‖(T ∘L M.subtypeL) ∘L Q‖₊ := by rw [hsub]
    _ ≤ ‖T ∘L M.subtypeL‖₊ * ‖Q‖₊ := opNNNorm_comp_le _ _
    _ ≤ ‖T ∘L M.subtypeL‖₊ * ‖ContinuousLinearMap.id 𝕜 E - P‖₊ := by gcongr
    _ = ‖ContinuousLinearMap.id 𝕜 E - P‖₊ * ‖T ∘L M.subtypeL‖₊ := mul_comm _ _

/-- If `P : E →L[𝕜] E` has rank at most `n` and `id - P` maps into a submodule `M ≤ E`, then
`aₙ(T) ≤ (1 + ‖P‖) ‖T|_M‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL (T : E →L[𝕜] F)
    {M : Submodule 𝕜 E} {P : E →L[𝕜] E} {n : ℕ} (hP : P.rank ≤ n)
    (hM : ∀ x, x - P x ∈ M) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖T ∘L M.subtypeL‖₊ := by
  refine (T.singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL hP hM).trans ?_
  gcongr
  exact nnnorm_id_sub_le_one_add P

/-- If `P : E →L[𝕜] E` is a bounded idempotent with kernel `M` of codimension at most `n`, then
`aₙ(T) ≤ ‖id - P‖ ‖T|_M‖`. -/
theorem singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL_of_isIdempotentElem
    (T : E →L[𝕜] F) {M : Submodule 𝕜 E} {P : E →L[𝕜] E} {n : ℕ}
    (hP : IsIdempotentElem P) (hker : P.ker = M) (hrank : Module.rank 𝕜 (E ⧸ M) ≤ n) :
    T.singularValue n ≤ ‖ContinuousLinearMap.id 𝕜 E - P‖₊ * ‖T ∘L M.subtypeL‖₊ := by
  have hPrank : P.rank ≤ n := by
    rw [← hker] at hrank
    have h := P.toLinearMap.quotKerEquivRange.symm.lift_rank_eq
    exact Cardinal.lift_le_nat_iff.mp (h.trans_le (Cardinal.lift_le_nat_iff.mpr hrank))
  refine T.singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL hPrank fun x ↦ ?_
  rw [← hker, LinearMap.mem_ker, coe_coe, map_sub, ← mul_apply_eq_comp, hP.eq, sub_self]

/-- If `P : E →L[𝕜] E` is a bounded idempotent with kernel `M` of codimension at most `n`, then
`aₙ(T) ≤ (1 + ‖P‖) ‖T|_M‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL_of_isIdempotentElem
    (T : E →L[𝕜] F) {M : Submodule 𝕜 E} {P : E →L[𝕜] E} {n : ℕ}
    (hP : IsIdempotentElem P) (hker : P.ker = M) (hrank : Module.rank 𝕜 (E ⧸ M) ≤ n) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖T ∘L M.subtypeL‖₊ := by
  refine (T.singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL_of_isIdempotentElem
    hP hker hrank).trans ?_
  gcongr
  exact nnnorm_id_sub_le_one_add P

/-- If `P : F →L[𝕜] F` has rank at most `n` and fixes a submodule `V ≤ F` pointwise, then
`aₙ(T) ≤ ‖id - P‖ ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_nnnorm_id_sub_mul_nnnorm_mkQL_comp (T : E →L[𝕜] F)
    {V : Submodule 𝕜 F} {P : F →L[𝕜] F} {n : ℕ} (hP : P.rank ≤ n)
    (hV : ∀ y ∈ V, P y = y) :
    T.singularValue n ≤ ‖ContinuousLinearMap.id 𝕜 F - P‖₊ * ‖V.mkQL ∘L T‖₊ := by
  let R : E →L[𝕜] F := P ∘L T
  have hR : R.rank ≤ n :=
    (Submodule.rank_mono (LinearMap.range_comp_le_range _ _)).trans hP
  let S : F →L[𝕜] F := ContinuousLinearMap.id 𝕜 F - P
  have hker : V ≤ S.ker := fun y hy ↦ by simp [S, hV y hy]
  let D : F ⧸ V →L[𝕜] F := V.liftQL S hker
  have hD : ‖D‖₊ ≤ ‖S‖₊ := by exact_mod_cast V.norm_liftQL_le S hker
  have hsub : T - R = D ∘L (V.mkQL ∘L T) := by
    ext x
    simp [R, S, D]
  calc
    T.singularValue n ≤ ‖T - R‖₊ := T.singularValue_le_nnnorm_sub hR
    _ = ‖D ∘L (V.mkQL ∘L T)‖₊ := by rw [hsub]
    _ ≤ ‖D‖₊ * ‖V.mkQL ∘L T‖₊ := opNNNorm_comp_le _ _
    _ ≤ ‖S‖₊ * ‖V.mkQL ∘L T‖₊ := by gcongr

/-- If `P : F →L[𝕜] F` has rank at most `n` and fixes a submodule `V ≤ F` pointwise, then
`aₙ(T) ≤ (1 + ‖P‖) ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp (T : E →L[𝕜] F)
    {V : Submodule 𝕜 F} {P : F →L[𝕜] F} {n : ℕ} (hP : P.rank ≤ n)
    (hV : ∀ y ∈ V, P y = y) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖V.mkQL ∘L T‖₊ := by
  refine (T.singularValue_le_nnnorm_id_sub_mul_nnnorm_mkQL_comp hP hV).trans ?_
  gcongr
  exact nnnorm_id_sub_le_one_add P

/-- If `P : F →L[𝕜] F` is a bounded idempotent of rank at most `n` whose range contains `V ≤ F`,
then `aₙ(T) ≤ ‖id - P‖ ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_nnnorm_id_sub_mul_nnnorm_mkQL_comp_of_isIdempotentElem
    (T : E →L[𝕜] F) {V : Submodule 𝕜 F} {P : F →L[𝕜] F} {n : ℕ}
    (hP : IsIdempotentElem P) (hPrank : P.rank ≤ n) (hrange : V ≤ P.range) :
    T.singularValue n ≤ ‖ContinuousLinearMap.id 𝕜 F - P‖₊ * ‖V.mkQL ∘L T‖₊ := by
  refine T.singularValue_le_nnnorm_id_sub_mul_nnnorm_mkQL_comp hPrank fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := hrange hy
  rw [coe_coe, ← mul_apply_eq_comp, hP.eq]

/-- If `P : F →L[𝕜] F` is a bounded idempotent of rank at most `n` whose range contains `V ≤ F`,
then `aₙ(T) ≤ (1 + ‖P‖) ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp_of_isIdempotentElem
    (T : E →L[𝕜] F) {V : Submodule 𝕜 F} {P : F →L[𝕜] F} {n : ℕ}
    (hP : IsIdempotentElem P) (hPrank : P.rank ≤ n) (hrange : V ≤ P.range) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖V.mkQL ∘L T‖₊ := by
  refine (T.singularValue_le_nnnorm_id_sub_mul_nnnorm_mkQL_comp_of_isIdempotentElem
    hP hPrank hrange).trans ?_
  gcongr
  exact nnnorm_id_sub_le_one_add P

/-- If `V ≤ F` has dimension at most `n` and `P : F →L[𝕜] V` restricts to the identity on `V`, then
`aₙ(T) ≤ ‖id - V.subtypeL ∘L P‖ ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_nnnorm_id_sub_subtypeL_comp_mul_nnnorm_mkQL_comp (T : E →L[𝕜] F)
    {V : Submodule 𝕜 F} {P : F →L[𝕜] V} {n : ℕ} (hV : Module.rank 𝕜 V ≤ n)
    (hP : ∀ v : V, P v = v) :
    T.singularValue n ≤
      ‖ContinuousLinearMap.id 𝕜 F - V.subtypeL ∘L P‖₊ * ‖V.mkQL ∘L T‖₊ :=
  T.singularValue_le_nnnorm_id_sub_mul_nnnorm_mkQL_comp
    ((Submodule.rank_mono (LinearMap.range_comp_le_range _ V.subtype)).trans
      ((Submodule.range_subtype V).symm ▸ hV))
    fun y hy ↦ congrArg Subtype.val (hP ⟨y, hy⟩)

/-- If `V ≤ F` has dimension at most `n` and `P : F →L[𝕜] V` restricts to the identity on `V`, then
`aₙ(T) ≤ (1 + ‖P‖) ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp_of_proj (T : E →L[𝕜] F)
    {V : Submodule 𝕜 F} {P : F →L[𝕜] V} {n : ℕ} (hV : Module.rank 𝕜 V ≤ n)
    (hP : ∀ v : V, P v = v) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖V.mkQL ∘L T‖₊ := by
  refine (T.singularValue_le_nnnorm_id_sub_subtypeL_comp_mul_nnnorm_mkQL_comp hV hP).trans ?_
  gcongr
  refine (nnnorm_id_sub_le_one_add _).trans ?_
  gcongr
  exact (opNNNorm_comp_le _ _).trans
    (mul_le_of_le_one_left' (by exact_mod_cast V.norm_subtypeL_le))

end ContinuousLinearMap
