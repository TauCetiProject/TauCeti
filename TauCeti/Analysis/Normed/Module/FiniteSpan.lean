/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Distances to finite spans

Distance to a span is the infimum of the errors of its finitely supported linear combinations.
As the family and the point vary, this distance is upper semicontinuous, hence measurable.
Continuity need not hold when the rank drops. For any finite linear combination, `‖c i‖` times
the distance of `v i` from the span of the remaining vectors is bounded by `‖∑ j, c j • v j‖`.
-/

public section

open Finset Metric Set

namespace TauCeti

variable {𝕜 E ι : Type*} [SeminormedAddCommGroup E]

section Semiring

variable [Semiring 𝕜] [Module 𝕜 E]

/-- Distance to a span is the infimum of the finitely supported linear-combination errors. -/
theorem infDist_span_range_eq_iInf_finsupp (v : ι → E) (x : E) :
    infDist x (Submodule.span 𝕜 (range v) : Set E) =
      ⨅ c : ι →₀ 𝕜, ‖x - c.sum fun i r ↦ r • v i‖ := by
  rw [← Finsupp.range_linearCombination, LinearMap.coe_range, infDist_eq_iInf, iInf_range']
  simp only [dist_eq_norm, Finsupp.linearCombination_apply]

/-- Distance to a finite span is the infimum of the linear-combination errors. -/
theorem infDist_span_range_eq_iInf [Fintype ι] (v : ι → E) (x : E) :
    infDist x (Submodule.span 𝕜 (range v) : Set E) =
      ⨅ c : ι → 𝕜, ‖x - ∑ i, c i • v i‖ := by
  rw [← Fintype.range_linearCombination, LinearMap.coe_range, infDist_eq_iInf, iInf_range']
  simp only [dist_eq_norm, Fintype.linearCombination_apply]

/-- Distance to the span of a varying family is upper semicontinuous, including at
rank drops. The point and the family may vary together. -/
theorem upperSemicontinuous_infDist_span_range [ContinuousConstSMul 𝕜 E]
    {α : Type*} [TopologicalSpace α]
    {v : α → ι → E} {x : α → E} (hv : ∀ i, Continuous fun a ↦ v a i)
    (hx : Continuous x) :
    UpperSemicontinuous fun a ↦ infDist (x a) (Submodule.span 𝕜 (range (v a)) : Set E) := by
  simp_rw [infDist_span_range_eq_iInf_finsupp]
  apply upperSemicontinuous_ciInf (fun _ ↦ ⟨0, by rintro _ ⟨c, rfl⟩; positivity⟩)
  intro c
  exact (hx.sub (continuous_finsetSum c.support fun i _ ↦
    (hv i).const_smul (c i))).norm.upperSemicontinuous

end Semiring

variable [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- The norm of a coefficient times the distance of its vector from the span of the remaining
vectors is bounded by the norm of the full linear combination. No independence or closedness is
needed. -/
theorem norm_mul_infDist_span_range_ne_le_finsupp (v : ι → E) (c : ι →₀ 𝕜) (i : ι) :
    ‖c i‖ * infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) ≤
      ‖c.sum fun j r ↦ r • v j‖ := by
  classical
  let W := Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j)
  have hzero (j : ι) (hj : j ≠ i) : W.mkQ (v j) = 0 :=
    (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  have hsum : W.mkQ (c.sum fun j r ↦ r • v j) = c i • W.mkQ (v i) := by
    rw [map_finsuppSum]
    exact c.sum_eq_single i (fun j _ hj ↦ by simp [hzero j hj]) (by simp)
  calc
    _ = ‖c i • W.mkQ (v i)‖ := by
      rw [norm_smul, Submodule.mkQ_apply]
      exact congrArg (fun t : ℝ ↦ ‖c i‖ * t)
        (QuotientAddGroup.norm_mk (S := W.toAddSubgroup) (v i)).symm
    _ = ‖W.mkQ (c.sum fun j r ↦ r • v j)‖ := congrArg norm hsum.symm
    _ ≤ _ := Submodule.Quotient.norm_mk_le W _

/-- The norm of a coefficient times the distance of its vector from the span of the remaining
vectors is bounded by the norm of the full finite linear combination. -/
theorem norm_mul_infDist_span_range_ne_le [Fintype ι] (v : ι → E) (c : ι → 𝕜) (i : ι) :
    ‖c i‖ * infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) ≤
      ‖∑ j, c j • v j‖ := by
  classical
  simpa [Finsupp.sum_fintype] using
    norm_mul_infDist_span_range_ne_le_finsupp v (Finsupp.equivFunOnFinite.symm c) i

end TauCeti
