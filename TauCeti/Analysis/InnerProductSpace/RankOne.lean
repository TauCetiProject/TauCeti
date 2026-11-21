/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Rank-one operators normalized at a vector

`rankOneDivNormSq 𝕜 y x` is the native rank-one operator `v ↦ ⟪x,v⟫ • y`, divided by `‖x‖²`.
It sends a nonzero `x` to `y` and is zero when `x = 0`. Its exact operator norm is `‖y‖ / ‖x‖`,
using total division also at zero.

In particular, for a bounded real-linear map `C`, the `𝕜`-linear operator
`rankOneDivNormSq 𝕜 (C x) x` agrees with `C` on `x` and has norm at most `‖C‖`. At `x = 0`,
linearity gives `C x = 0`, so the agreement holds without excluding the zero set. This is the
pointwise coefficient reduction used in vector similarity principles. It follows the replacement
of a real-linear coefficient by a complex-linear one along the solution in Step 2 of the proof
of McDuff–Salamon's Theorem 2.3.5.

Every rank-one operator `InnerProductSpace.rankOne 𝕜 x y` and every normalized rank-one operator
`TauCeti.rankOneDivNormSq 𝕜 y x` is compact (`InnerProductSpace.isCompactOperator_rankOne`,
`TauCeti.isCompactOperator_rankOneDivNormSq`), and sandwiching any continuous linear map `T` with
`T x ≠ 0` between `rankOneDivNormSq 𝕜 u (T x)` and `rankOne 𝕜 x v` recovers `rankOne 𝕜 u v`
(`ContinuousLinearMap.rankOneDivNormSq_comp_comp_rankOne`).

Over the reals, the symmetric operator `u ↦ ⟪a, u⟫ b + ⟪b, u⟫ a` sends a nonzero `a` to a vector
pairing positively with a nonzero `b` (`TauCeti.inner_rankOne_add_rankOne_apply_pos`). This
is the symmetric operator used to build metric variations pairing positively with a given vector.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5, proof, Step 2 (coefficient reduction).
-/

public noncomputable section

namespace InnerProductSpace

/-- Every rank-one operator is compact. -/
theorem isCompactOperator_rankOne {𝕜 E F : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : E) (y : F) :
    IsCompactOperator (rankOne 𝕜 x y) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton 𝕜 x)).comp_clm _

end InnerProductSpace

namespace TauCeti

open InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- The native rank-one operator divided by the squared norm of its input vector.
The inverse is total, so this operator is zero at the zero input vector. -/
def rankOneDivNormSq (y : F) (x : E) : E →L[𝕜] F :=
  ((‖x‖ : 𝕜) ^ 2)⁻¹ • rankOne 𝕜 y x

/-- The defining normalization of the native rank-one operator. -/
theorem rankOneDivNormSq_def (y : F) (x : E) :
    rankOneDivNormSq 𝕜 y x = ((‖x‖ : 𝕜) ^ 2)⁻¹ • rankOne 𝕜 y x := by
  rfl

/-- Evaluate the normalized rank-one operator using the inner-product formula. -/
theorem rankOneDivNormSq_apply (y : F) (x v : E) :
    rankOneDivNormSq 𝕜 y x v = (((‖x‖ : 𝕜) ^ 2)⁻¹ * inner 𝕜 x v) • y := by
  simp [rankOneDivNormSq, smul_smul]

@[simp]
theorem rankOneDivNormSq_zero_right (y : F) : rankOneDivNormSq 𝕜 y (0 : E) = 0 := by
  simp [rankOneDivNormSq]

@[simp]
theorem rankOneDivNormSq_zero_left (x : E) : rankOneDivNormSq 𝕜 (0 : F) x = 0 := by
  simp [rankOneDivNormSq]

/-- A nonzero input vector is sent to the prescribed output vector. -/
@[simp]
theorem rankOneDivNormSq_apply_self (y : F) {x : E} (hx : x ≠ 0) :
    rankOneDivNormSq 𝕜 y x x = y := by
  rw [rankOneDivNormSq_apply, inner_self_eq_norm_sq_to_K]
  simp [norm_ne_zero_iff.mpr hx]

/-- The exact norm formula includes the zero input case by total division. -/
@[simp]
theorem norm_rankOneDivNormSq (y : F) (x : E) :
    ‖rankOneDivNormSq 𝕜 y x‖ = ‖y‖ / ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  rw [rankOneDivNormSq, norm_smul, norm_inv, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg x), norm_rankOne]
  field_simp [norm_ne_zero_iff.mpr hx]

/-- Every normalized rank-one operator `TauCeti.rankOneDivNormSq 𝕜 y x` is compact. -/
theorem isCompactOperator_rankOneDivNormSq (y : F) (x : E) :
    IsCompactOperator (rankOneDivNormSq 𝕜 y x) := by
  rw [rankOneDivNormSq_def]
  exact (InnerProductSpace.isCompactOperator_rankOne y x).smul _

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {𝕜 𝕜' E F : Type*} [RCLike 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' E] [NormedSpace 𝕜' F]

/-- Normalizing the output of a linear map over an independent scalar field preserves its action,
including at zero. The resulting operator is linear over `𝕜`. -/
@[simp]
theorem rankOneDivNormSq_apply_map (C : E →L[𝕜'] F) (x : E) :
    rankOneDivNormSq 𝕜 (C x) x x = C x := by
  by_cases hx : x = 0
  · simp [hx]
  exact rankOneDivNormSq_apply_self _ hx

/-- The linear operator matching a linear map on a chosen vector has no larger norm. -/
theorem norm_rankOneDivNormSq_map_le (C : E →L[𝕜'] F) (x : E) :
    ‖rankOneDivNormSq 𝕜 (C x) x‖ ≤ ‖C‖ := by
  rw [norm_rankOneDivNormSq]
  exact C.ratio_le_opNorm x

/-- Sandwiching a continuous linear map `T` with `T x ≠ 0` between
`rankOneDivNormSq 𝕜 u (T x)` and `InnerProductSpace.rankOne 𝕜 x v` produces
`InnerProductSpace.rankOne 𝕜 u v`. -/
theorem rankOneDivNormSq_comp_comp_rankOne {𝕜 E₁ E₂ E₃ E₄ : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
    [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
    {T : E₂ →L[𝕜] E₃} {x : E₂} (hx : T x ≠ 0) (u : E₄) (v : E₁) :
    (rankOneDivNormSq 𝕜 u (T x)).comp (T.comp (InnerProductSpace.rankOne 𝕜 x v)) =
      InnerProductSpace.rankOne 𝕜 u v := by
  ext w
  simp [map_smul, rankOneDivNormSq_apply_self u hx]

end ContinuousLinearMap

namespace TauCeti

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The symmetric operator `u ↦ ⟪a, u⟫ b + ⟪b, u⟫ a` carries `a` to a vector pairing positively
with `b`, for nonzero `a` and `b`: the pairing is `‖a‖² ‖b‖² + ⟪a, b⟫²`. -/
theorem inner_rankOne_add_rankOne_apply_pos {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < ⟪(rankOne ℝ b a + rankOne ℝ a b) a, b⟫ := by
  simp only [add_apply, rankOne_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_comm a b]
  have := mul_pos (pow_pos (norm_pos_iff.2 ha) 2) (pow_pos (norm_pos_iff.2 hb) 2)
  nlinarith [sq_nonneg ⟪b, a⟫]

end TauCeti
