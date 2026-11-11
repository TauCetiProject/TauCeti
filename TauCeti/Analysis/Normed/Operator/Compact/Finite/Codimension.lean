/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Compact operators are small on subspaces of finite codimension

Given a compact operator and a positive tolerance, there is a closed subspace of finite
codimension on which the operator norm is at most that tolerance. Neither space needs to
have the approximation property, and the operator need not be approximated by finite-rank
operators. The proof takes a finite net of the image of the unit ball and intersects the
kernels of norming functionals for the centres of the net.

This is a functional-analytic input to finite-cover finiteness arguments for analytic
cohomology: compact restrictions can be made uniformly small after finitely many linear
conditions. The analytic construction of those restriction operators and their comparison
with sheaf cohomology are separate inputs.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, compact operators.
-/

public noncomputable section

open Metric Set

namespace IsCompactOperator

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {T : E →L[𝕜] F}

/-- A compact operator becomes arbitrarily small on a closed subspace of finite codimension.
The conclusion controls the actual restricted operator in its native subspace norm. -/
theorem exists_finiteDimensional_quotient_norm_comp_subtype_le (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Submodule 𝕜 E, IsClosed (K : Set E) ∧ FiniteDimensional 𝕜 (E ⧸ K) ∧
      ‖T.comp K.subtypeL‖ ≤ ε := by
  classical
  obtain ⟨s, _, hs, hcover⟩ :=
    (hT.isCompact_closure_image_closedBall (f := T.toLinearMap) 1).finite_cover_balls
      (half_pos hε)
  let : Fintype s := hs.fintype
  choose φ hφ hφ_apply using fun y : s ↦ exists_dual_vector'' 𝕜 (y : F)
  let A : E →L[𝕜] (s → 𝕜) := ContinuousLinearMap.pi fun y ↦ (φ y).comp T
  let K := A.ker
  have hfinite : FiniteDimensional 𝕜 (E ⧸ K) :=
    FiniteDimensional.of_injective A.toLinearMap.quotKerEquivRange.toLinearMap
      A.toLinearMap.quotKerEquivRange.injective
  refine ⟨K, A.isClosed_ker, hfinite, ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  have hTx : T (x : E) ∈ closure (T '' closedBall 0 1) :=
    subset_closure ⟨x, by simpa [mem_closedBall_zero_iff] using hx.le, rfl⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hTx)
  let j : s := ⟨y, hy⟩
  have hzero : φ j (T (x : E)) = 0 := congrFun (A.mem_ker.mp x.property) j
  have hnormy : ‖y‖ ≤ ‖T (x : E) - y‖ := by
    calc
      ‖y‖ = ‖φ j (y - T (x : E))‖ := by rw [map_sub, hzero, sub_zero, hφ_apply]; simp [j]
      _ ≤ ‖φ j‖ * ‖y - T (x : E)‖ := (φ j).le_opNorm _
      _ ≤ ‖y - T (x : E)‖ := mul_le_of_le_one_left (norm_nonneg _) (hφ j)
      _ = ‖T (x : E) - y‖ := norm_sub_rev _ _
  have hdist : ‖T (x : E) - y‖ < ε / 2 := by simpa [dist_eq_norm] using hxy
  rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  calc
    ‖T (x : E)‖ ≤ ‖T (x : E) - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (T (x : E) - y) y
    _ ≤ ε := by linarith

end IsCompactOperator
