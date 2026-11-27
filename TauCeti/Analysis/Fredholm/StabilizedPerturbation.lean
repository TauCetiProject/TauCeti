/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Fredholm.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.Fredholm.Parametric
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.Analysis.Normed.Operator.Surjective

/-!
# Small perturbations of stabilized Fredholm operators

A Fredholm operator `T : E → F` between Banach spaces is stable under small perturbations:
every operator close enough to `T` is Fredholm with the same index
(`ContinuousLinearMap.IsFredholm.exists_pos_isFredholm_and_index_eq_of_norm_sub_lt`). That
statement gives no information on how close is close enough, so it cannot be applied uniformly to
a family of operators, such as the operators `D_R` glued along necks of length `R → ∞`.

This file gives an explicit radius. Stabilize `T` by a finite-dimensional space `S`, by a map
`B : S → F` such that `(x, σ) ↦ T x + B σ` has a bounded linear right inverse `Q`, as every
Fredholm operator admits
(`ContinuousLinearMap.IsFredholm.exists_le_isTopCompl_rightInverse_coprod_of_dense`).
Then every operator `T'` with `‖T' - T‖ ‖Q‖ < 1 / 2` is Fredholm with the index of `T`
(`ContinuousLinearMap.IsFredholm.isFredholm_and_index_eq_of_norm_sub_mul_lt`). The radius
`1 / (2 ‖Q‖)` depends on `T` only through `‖Q‖`, so it is uniform over a family of operators whose
stabilizations have uniformly bounded right inverses.

The proof perturbs the stabilization. The operator `(x, σ) ↦ T' x + B σ` is within `‖T' - T‖` of
`(x, σ) ↦ T x + B σ`, so `Q` is an approximate right inverse of it, which a Neumann series
corrects to a right inverse `Q'` with `‖Q'‖ ≤ 2 ‖Q‖`. Both stabilizations are thus onto, and
`ξ ↦ ξ - Q (A ξ)` and `ξ ↦ ξ - Q' (A' ξ)` embed their kernels into each other, so the kernels have
the same dimension (`ContinuousLinearMap.exists_injective_ker_of_norm_mul_norm_sub_lt_one`). For a
surjective stabilization the index is the dimension of the kernel minus `dim S`
(`ContinuousLinearMap.index_eq_finrank_ker_coprod_sub_of_surjective`).

## Main results

* `ContinuousLinearMap.IsFredholm.isFredholm_and_index_eq_of_norm_sub_mul_lt`: the Fredholm
  property and the index are stable under perturbations smaller than `1 / (2 ‖Q‖)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix A.1 (stability of Fredholm operators and of their index).
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Small perturbations of a stabilized Fredholm operator.** Let `T` be Fredholm and let
`B : S → F`, with `S` finite-dimensional, stabilize it: the operator `(x, σ) ↦ T x + B σ` has a
bounded linear right inverse `Q`. Then every operator `T'` with `‖T' - T‖ ‖Q‖ < 1 / 2` is
Fredholm, with the same index as `T`.

The radius `1 / (2 ‖Q‖)` depends on `T` only through the norm of a right inverse of its
stabilization. Unlike the radius of
`ContinuousLinearMap.IsFredholm.exists_pos_isFredholm_and_index_eq_of_norm_sub_lt`, it is therefore
uniform over families of operators whose stabilizations have uniformly bounded right inverses. -/
theorem _root_.ContinuousLinearMap.IsFredholm.isFredholm_and_index_eq_of_norm_sub_mul_lt
    {S : Type*} [NormedAddCommGroup S] [NormedSpace 𝕜 S] [FiniteDimensional 𝕜 S]
    {T : E →L[𝕜] F} (hT : T.IsFredholm) {B : S →L[𝕜] F} {Q : F →L[𝕜] E × S}
    (hQ : (T.coprod B).comp Q = ContinuousLinearMap.id 𝕜 F) {T' : E →L[𝕜] F}
    (h : ‖T' - T‖ * ‖Q‖ < 1 / 2) : T'.IsFredholm ∧ T'.index = T.index := by
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  -- The stabilizations differ by `T' - T` on the first factor.
  have hδ : ‖T'.coprod B - T.coprod B‖ ≤ ‖T' - T‖ := by
    have hAA : T'.coprod B - T.coprod B = (T' - T).comp (ContinuousLinearMap.fst 𝕜 E S) := by
      ext <;> simp
    rw [hAA]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le 𝕜 E S))
  have hθ : ‖Q‖ * ‖T'.coprod B - T.coprod B‖ < 1 / 2 := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hδ (norm_nonneg _)).trans_lt h
  -- `Q` is an approximate right inverse of the perturbed stabilization, and corrects to one.
  have happrox : ‖(T'.coprod B).comp Q - ContinuousLinearMap.id 𝕜 F‖ ≤ 1 / 2 := by
    rw [← hQ, ← ContinuousLinearMap.sub_comp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by linarith)
  obtain ⟨Q', hQ', hQ'n⟩ :=
    (T'.coprod B).exists_rightInverse_of_norm_comp_sub_id_le_half Q happrox
  -- The kernels of the two stabilizations embed into each other.
  have : FiniteDimensional 𝕜 T.ker := hT.finite_ker
  have : FiniteDimensional 𝕜 (T.coprod B).ker := (hT.coprod_of_finiteDimensional B).finite_ker
  obtain ⟨g, hg⟩ :=
    ContinuousLinearMap.exists_injective_ker_of_norm_mul_norm_sub_lt_one hQ (by linarith)
  obtain ⟨f, hf⟩ :=
    ContinuousLinearMap.exists_injective_ker_of_norm_mul_norm_sub_lt_one hQ' (by
      rw [norm_sub_rev]
      calc ‖Q'‖ * ‖T'.coprod B - T.coprod B‖ ≤ 2 * ‖Q‖ * ‖T'.coprod B - T.coprod B‖ :=
            mul_le_mul_of_nonneg_right hQ'n (norm_nonneg _)
        _ < 1 := by linarith)
  have : FiniteDimensional 𝕜 (T'.coprod B).ker := Module.Finite.of_injective g hg
  have hsurj : Function.Surjective (T.coprod B) :=
    (ContinuousLinearMap.rightInverse_of_comp hQ).surjective
  have hsurj' : Function.Surjective (T'.coprod B) :=
    (ContinuousLinearMap.rightInverse_of_comp hQ').surjective
  have hF := ContinuousLinearMap.IsFredholm.of_surjective_coprod T' B hsurj' inferInstance
  have : FiniteDimensional 𝕜 T'.ker := hF.finite_ker
  refine ⟨hF, ?_⟩
  rw [ContinuousLinearMap.index_eq_finrank_ker_coprod_sub_of_surjective _ _ hsurj',
    ContinuousLinearMap.index_eq_finrank_ker_coprod_sub_of_surjective _ _ hsurj,
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hg)
      (LinearMap.finrank_le_finrank_of_injective hf)]

end TauCeti
