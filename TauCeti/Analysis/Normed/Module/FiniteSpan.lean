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

Distance to the span of a finite family is the infimum of the errors of its linear combinations.
As the family and the point vary, this distance is upper semicontinuous, hence measurable.
Continuity need not hold when the rank drops. Quotient norms also bound the distance of one
member from the span of the others by the norm of any linear combination containing it.
-/

public section

open Finset Metric Set

namespace TauCeti

variable {𝕜 E ι : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι]

/-- Distance to a finite span is the infimum of the linear-combination errors. -/
theorem infDist_span_range_eq_iInf (v : ι → E) (x : E) :
    infDist x (Submodule.span 𝕜 (range v) : Set E) =
      ⨅ c : ι → 𝕜, ‖x - ∑ i, c i • v i‖ := by
  apply le_antisymm
  · apply le_ciInf
    intro c
    simpa only [dist_eq_norm] using infDist_le_dist_of_mem
      ((Submodule.mem_span_range_iff_exists_fun 𝕜).mpr ⟨c, rfl⟩ :
        (∑ i, c i • v i) ∈ Submodule.span 𝕜 (range v))
  · apply (le_infDist ⟨0, Submodule.zero_mem _⟩).mpr
    intro y hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hy
    simpa only [dist_eq_norm] using
      (ciInf_le (f := fun c : ι → 𝕜 ↦ ‖x - ∑ i, c i • v i‖)
        ⟨0, by rintro _ ⟨d, rfl⟩; positivity⟩ c)

omit [Fintype ι] in
/-- Distance to the span of a varying finite family is upper semicontinuous, including at
rank drops. The point and the family may vary together. -/
theorem upperSemicontinuous_infDist_span_range [Finite ι] {α : Type*} [TopologicalSpace α]
    {v : α → ι → E} {x : α → E} (hv : ∀ i, Continuous fun a ↦ v a i)
    (hx : Continuous x) :
    UpperSemicontinuous fun a ↦ infDist (x a) (Submodule.span 𝕜 (range (v a)) : Set E) := by
  let _ := Fintype.ofFinite ι
  simp_rw [infDist_span_range_eq_iInf]
  apply upperSemicontinuous_ciInf (fun _ ↦ ⟨0, by rintro _ ⟨c, rfl⟩; positivity⟩)
  intro c
  exact (hx.sub (continuous_finsetSum _ fun i _ ↦ (hv i).const_smul (c i))).norm.upperSemicontinuous

/-- A coefficient times the distance of its vector from the span of the remaining vectors is
bounded by the norm of the full linear combination. No independence or closedness is needed. -/
theorem norm_mul_infDist_span_other_le (v : ι → E) (c : ι → 𝕜) (i : ι) :
    ‖c i‖ * infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) ≤
      ‖∑ j, c j • v j‖ := by
  classical
  let W := Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j)
  have hzero (j : ι) (hj : j ≠ i) : W.mkQ (v j) = 0 :=
    (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  have hsum : W.mkQ (∑ j, c j • v j) = c i • W.mkQ (v i) := by
    rw [map_sum, sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hzero j hj]
    · simp
  calc
    _ = ‖c i • W.mkQ (v i)‖ := by
      rw [norm_smul, Submodule.mkQ_apply]
      exact congrArg (fun t : ℝ ↦ ‖c i‖ * t)
        (QuotientAddGroup.norm_mk (S := W.toAddSubgroup) (v i)).symm
    _ = ‖W.mkQ (∑ j, c j • v j)‖ := congrArg norm hsum.symm
    _ ≤ _ := Submodule.Quotient.norm_mk_le W _

end TauCeti
