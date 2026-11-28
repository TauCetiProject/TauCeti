/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Closedness of finite-dimensional subspaces of normed spaces

Over a complete nontrivially normed field, Mathlib shows that the supremum of a closed subspace
and a finite-dimensional subspace is closed (`Submodule.isClosed_sup_finiteDimensional`), and in
particular that every finite-dimensional subspace of a `T0Space` topological vector space is
closed (`Submodule.isClosed_of_finiteDimensional`).

For normed spaces, the same closedness results hold over a trivially normed field
(`[DiscreteTopology 𝕜]`): adding a single vector to a closed subspace preserves closedness because
the enlarged subspace agrees with `W` on the open ball of radius `infDist v W` around zero, so the
enlarged subspace is locally closed at zero. Combining the discrete and nontrivial cases yields
closedness over any complete normed field.

## Main results

* `Submodule.isClosed_sup_finiteDimensional_of_discreteTopology`: over a trivially normed field,
  the supremum of a closed subspace and a finite-dimensional subspace of a seminormed space is
  closed.
* `Submodule.isClosed_sup_finiteDimensional'`: over any complete normed field (trivially normed
  or not), the supremum of a closed subspace and a finite-dimensional subspace of a seminormed
  space is closed.
* `Submodule.isClosed_of_finiteDimensional'`: over any complete normed field (trivially normed
  or not), every finite-dimensional subspace of a `T0Space` seminormed space (in particular, of a
  normed space) is closed.
* `Submodule.infDist_pos_of_notMem`: over any complete normed field, a point outside a
  finite-dimensional subspace of a normed space has positive distance to it.
-/

public section

open Metric Set

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

/-- Over a trivially normed field (`[DiscreteTopology 𝕜]`), the supremum of a closed subspace and
a finite-dimensional subspace of a seminormed space is closed. -/
theorem isClosed_sup_finiteDimensional_of_discreteTopology {𝕜 E : Type*} [NormedField 𝕜]
    [DiscreteTopology 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s t : Submodule 𝕜 E) (hs : IsClosed (s : Set E)) [FiniteDimensional 𝕜 t] :
    IsClosed ((s ⊔ t : Submodule 𝕜 E) : Set E) := by
  classical
  obtain ⟨S, rfl⟩ := t.fg_iff_finiteDimensional.2 ‹FiniteDimensional 𝕜 t›
  induction S using Finset.induction_on with
  | empty => simpa using hs
  | insert v S _ ih =>
    rw [Finset.coe_insert, span_insert, sup_left_comm, sup_comm (𝕜 ∙ v)]
    exact isClosed_sup_span_singleton_of_discreteTopology ih v

/-- Over any complete normed field (trivially normed or not), the supremum of a closed subspace
and a finite-dimensional subspace of a seminormed space is closed.

Unlike Mathlib's `Submodule.isClosed_sup_finiteDimensional`, this does not require
`NontriviallyNormedField 𝕜`; in exchange, it requires a `NormedSpace` structure (over a trivially
normed field, a general topological vector space does not suffice). -/
theorem isClosed_sup_finiteDimensional' {𝕜 E : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s t : Submodule 𝕜 E) (hs : IsClosed (s : Set E)) [FiniteDimensional 𝕜 t] :
    IsClosed ((s ⊔ t : Submodule 𝕜 E) : Set E) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField 𝕜 with _ | ⟨⟨_, rfl⟩⟩
  · exact s.isClosed_sup_finiteDimensional_of_discreteTopology t hs
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

/-- **A point outside a finite-dimensional subspace has positive distance to it**, over any
complete normed field, since the subspace is closed. -/
theorem infDist_pos_of_notMem {𝕜 E : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {P : Submodule 𝕜 E} [FiniteDimensional 𝕜 P] {x : E}
    (hx : x ∉ P) : 0 < infDist x (P : Set E) :=
  (P.isClosed_of_finiteDimensional'.notMem_iff_infDist_pos ⟨0, P.zero_mem⟩).mp hx

end Submodule
