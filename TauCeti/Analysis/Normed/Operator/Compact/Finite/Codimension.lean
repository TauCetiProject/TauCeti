/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Compact operators are small on subspaces of finite codimension

Given a compact operator and a positive tolerance, there is a closed subspace of finite
codimension on which the operator norm is at most that tolerance. Neither space needs to
have the approximation property, and the operator need not be approximated by finite-rank
operators. The proof takes a finite net of the image of the unit ball and intersects the
kernels of norming functionals for the centres of the net: if the net is an `ε`-cover with `k`
centres, the result has codimension at most `k` and the restricted operator has norm at most `2ε`.

This is a functional-analytic input to finite-cover finiteness arguments for analytic
cohomology: compact restrictions can be made uniformly small after finitely many linear
conditions. The analytic construction of those restriction operators and their comparison
with sheaf cohomology are separate inputs.

## Main declarations

* `ContinuousLinearMap.exists_norm_comp_subtypeL_le_two_mul_of_isCover`: a finite `ε`-cover of
  the image of the unit ball gives a closed subspace of codimension at most the size of the cover
  on which the operator has norm at most `2ε`.
* `IsCompactOperator.exists_finiteDimensional_quotient_norm_comp_subtype_le`: a compact operator
  becomes arbitrarily small on a closed subspace of finite codimension.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, compact operators.
-/

public noncomputable section

open Metric Set

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If the image of the closed unit ball under `T` is covered by the closed `ε`-balls centred at
the points of `N`, then `T` has norm at most `2ε` on a closed subspace of codimension at most
`|N|`. The subspace is the common kernel of the functionals `φ_y ∘ T`, where `φ_y` norms the
centre `y`: every `T x` with `‖x‖ ≤ 1` in it lies within `ε` of a centre `y` of norm
`φ_y (y - T x) ≤ ε`. -/
theorem exists_norm_comp_subtypeL_le_two_mul_of_isCover (T : E →L[𝕜] F) {ε : ℝ≥0}
    {N : Finset F} (hN : IsCover ε ((T : E → F) '' closedBall 0 1) N) :
    ∃ M : Submodule 𝕜 E, IsClosed (M : Set E) ∧ Module.rank 𝕜 (E ⧸ M) ≤ N.card ∧
      ‖T ∘L M.subtypeL‖ ≤ 2 * ε := by
  choose φ hφ hφy using fun y : F ↦ exists_dual_vector'' 𝕜 y
  let A : E →L[𝕜] (N → 𝕜) := pi fun y ↦ (φ y).comp T
  refine ⟨LinearMap.ker (A : E →ₗ[𝕜] N → 𝕜), A.isClosed_ker, ?_, ?_⟩
  · -- The codimension is the rank of the range of `A`, at most `|N|`.
    have hrange : Module.rank 𝕜 (LinearMap.range (A : E →ₗ[𝕜] N → 𝕜)) ≤ N.card :=
      (Submodule.rank_le _).trans (by simp)
    have h := (LinearMap.quotKerEquivRange (A : E →ₗ[𝕜] N → 𝕜)).lift_rank_eq
    exact Cardinal.lift_le_nat_iff.mp (h.trans_le (Cardinal.lift_le_nat_iff.mpr hrange))
  refine opNorm_le_of_unit_norm (by positivity) fun x hx ↦ ?_
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 <| hN.subset_iUnion_closedBall <|
    mem_image_of_mem T (mem_closedBall_zero_iff.2 hx.le)
  have hxy' : ‖y - T x‖ ≤ ε := by rw [← dist_eq_norm, dist_comm]; exact mem_closedBall.1 hxy
  -- The centre `y` has norm `φ y (y - T x) ≤ ε`, since `φ y` vanishes at `T x`.
  have hφx : φ y (T x) = 0 := congr_fun (LinearMap.mem_ker.1 x.property) ⟨y, hy⟩
  have hy' : ‖y‖ ≤ ε := by
    have h : φ y (y - T x) = ‖y‖ := by rw [map_sub, hφx, sub_zero, hφy]
    calc ‖y‖ = ‖φ y (y - T x)‖ := by rw [h, RCLike.norm_ofReal, abs_norm]
      _ ≤ ‖φ y‖ * ‖y - T x‖ := le_opNorm _ _
      _ ≤ 1 * ε := by gcongr; exact hφ y
      _ = ε := one_mul _
  calc ‖(T ∘L (LinearMap.ker (A : E →ₗ[𝕜] N → 𝕜)).subtypeL) x‖ = ‖T x‖ := by
        rw [comp_apply, Submodule.subtypeL_apply]
    _ ≤ ‖y‖ + ‖T x - y‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ε + ε := by rw [norm_sub_rev]; gcongr
    _ = 2 * ε := by ring

end ContinuousLinearMap

namespace IsCompactOperator

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {T : E →L[𝕜] F}

/-- A compact operator becomes arbitrarily small on a closed subspace of finite codimension.
The conclusion controls the actual restricted operator in its native subspace norm. -/
theorem exists_finiteDimensional_quotient_norm_comp_subtype_le (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Submodule 𝕜 E, IsClosed (K : Set E) ∧ FiniteDimensional 𝕜 (E ⧸ K) ∧
      ‖T.comp K.subtypeL‖ ≤ ε := by
  -- Apply the covering estimate to a finite `ε / 2`-cover of the image of the unit ball.
  obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_totallyBounded
    (Real.toNNReal_pos.2 (half_pos hε)).ne'
    (hT.totallyBounded_image_closedBall (f := T.toLinearMap) 1)
  obtain ⟨K, hKc, hK, hTK⟩ :=
    T.exists_norm_comp_subtypeL_le_two_mul_of_isCover (N := hNfin.toFinset) (by simpa using hN)
  refine ⟨K, hKc, Module.rank_lt_aleph0_iff.mp (hK.trans_lt Cardinal.natCast_lt_aleph0), ?_⟩
  rwa [Real.coe_toNNReal _ (half_pos hε).le, mul_div_cancel₀ _ two_ne_zero] at hTK

end IsCompactOperator
