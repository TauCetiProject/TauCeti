/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.Semicontinuity.Basic

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Distances to finite spans and closedness of finite-dimensional subspaces

Distance to a span is the infimum of the errors of its finitely supported linear combinations.
As the family and the point vary, this distance is upper semicontinuous, hence measurable.
Continuity need not hold when the rank drops. For any finite linear combination, `‖c i‖` times
the distance of `v i` from the span of the remaining vectors is bounded by `‖∑ j, c j • v j‖`.

Over any complete normed field (trivially normed or not), the supremum of a closed subspace and a
finite-dimensional subspace of a seminormed space is closed
(`Submodule.isClosed_sup_finiteDimensional'`). In particular, every finite-dimensional subspace of
a `T0Space` seminormed space (such as a normed space) is closed
(`Submodule.isClosed_of_finiteDimensional'`).
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

namespace Submodule

/-- Over a trivially normed field (`[DiscreteTopology 𝕜]`), adding a vector `v` to a closed
subspace `W` of a seminormed space gives a closed subspace. -/
private theorem isClosed_sup_span_singleton_of_discreteTopology {𝕜 E : Type*} [NormedField 𝕜]
    [DiscreteTopology 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {W : Submodule 𝕜 E}
    (hW : IsClosed (W : Set E)) (v : E) : IsClosed ((W ⊔ 𝕜 ∙ v : Submodule 𝕜 E) : Set E) := by
  by_cases hv : v ∈ W
  · rwa [sup_eq_left.2 ((span_singleton_le_iff_mem v W).2 hv)]
  have hδ : 0 < infDist v W := (hW.notMem_iff_infDist_pos ⟨0, W.zero_mem⟩).1 hv
  -- A vector of `W ⊔ 𝕜 ∙ v` of norm less than `infDist v W` lies in `W`, because a nonzero
  -- coefficient `d` of `v` has norm `1`, so `‖w + d • v‖ = ‖v + d⁻¹ • w‖`.
  have hsmall {u : E} (hu : u ∈ W ⊔ 𝕜 ∙ v) (hlt : ‖u‖ < infDist v W) : u ∈ W := by
    obtain ⟨w, hw, _, hd, rfl⟩ := mem_sup.1 hu
    obtain ⟨d, rfl⟩ := mem_span_singleton.1 hd
    rcases eq_or_ne d 0 with rfl | hd
    · simpa using hw
    refine absurd hlt (not_lt.2 ?_)
    calc infDist v W ≤ dist v (-(d⁻¹ • w)) :=
          infDist_le_dist_of_mem (W.neg_mem (W.smul_mem _ hw))
      _ = ‖d‖ * ‖v + d⁻¹ • w‖ := by
          rw [NormedDivisionRing.norm_eq_one_iff_ne_zero_of_discrete.2 hd, one_mul, dist_eq_norm,
            sub_neg_eq_add]
      _ = ‖w + d • v‖ := by rw [← norm_smul, smul_add, smul_inv_smul₀ hd, add_comm]
  -- On `ball 0 (infDist v W)`, `W ⊔ 𝕜 ∙ v` agrees with the closed set `W`, so it is locally closed
  -- at `0`, hence closed as an additive subgroup.
  refine (W ⊔ 𝕜 ∙ v).toAddSubgroup.isClosed_of_isLocallyClosedAt (zero_mem _)
    ⟨ball 0 (infDist v W), Metric.ball_mem_nhds 0 hδ, W, hW, ?_⟩
  ext u
  simp only [mem_inter_iff, Metric.mem_ball, dist_zero_right, SetLike.mem_coe,
    Submodule.mem_toAddSubgroup]
  exact ⟨fun ⟨hlt, hu⟩ ↦ ⟨hlt, hsmall hu hlt⟩, fun ⟨hlt, hu⟩ ↦ ⟨hlt, mem_sup_left hu⟩⟩

/-- Over any complete normed field (trivially normed or not), the supremum of a closed subspace
and a finite-dimensional subspace of a seminormed space is closed.

Unlike Mathlib's `Submodule.isClosed_sup_finiteDimensional`, this does not require
`NontriviallyNormedField 𝕜`; in exchange, it requires a `NormedSpace` structure (over a trivially
normed field, a general topological vector space does not suffice). -/
theorem isClosed_sup_finiteDimensional' {𝕜 E : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s t : Submodule 𝕜 E) (hs : IsClosed (s : Set E)) [FiniteDimensional 𝕜 t] :
    IsClosed ((s ⊔ t : Submodule 𝕜 E) : Set E) := by
  -- Over a trivially normed field, induct over a finite generating set using
  -- `isClosed_sup_span_singleton_of_discreteTopology`; over a nontrivially normed field, apply
  -- Mathlib's `Submodule.isClosed_sup_finiteDimensional`.
  rcases NormedField.discreteTopology_or_nontriviallyNormedField 𝕜 with _ | ⟨⟨_, rfl⟩⟩
  · classical
    obtain ⟨S, rfl⟩ := t.fg_iff_finiteDimensional.2 ‹FiniteDimensional 𝕜 t›
    induction S using Finset.induction_on with
    | empty => simpa using hs
    | insert v S _ ih =>
      rw [Finset.coe_insert, span_insert, sup_left_comm, sup_comm (𝕜 ∙ v)]
      exact isClosed_sup_span_singleton_of_discreteTopology ih v
  · exact s.isClosed_sup_finiteDimensional t hs

/-- Over any complete normed field (trivially normed or not), every finite-dimensional subspace of
a `T0Space` seminormed space (in particular, of a normed space) is closed.

Unlike Mathlib's `Submodule.isClosed_of_finiteDimensional`, this does not require
`NontriviallyNormedField 𝕜`; in exchange, it requires a `NormedSpace` structure. -/
theorem isClosed_of_finiteDimensional' {𝕜 E : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    [SeminormedAddCommGroup E] [T0Space E] [NormedSpace 𝕜 E]
    (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) := by
  simpa using (⊥ : Submodule 𝕜 E).isClosed_sup_finiteDimensional' s isClosed_singleton

end Submodule
