/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Extreme
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Tangent cones of finite polyhedra

At a point of a polyhedron cut out by finitely many continuous linear inequalities, the positive
(Bouligand) tangent cone consists exactly of the directions nonnegative on the active constraints.
Locally, the polyhedron itself agrees with the translate of this cone: inactive constraints remain
strict near the point. This supplies local corner models without a full-dimensionality assumption.

The scalar restriction in `posTangentConeAt` matters: `tangentConeAt ℝ` also allows negative
rescalings and would not describe the inward directions at a boundary point.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Section 23
  (tangent cones and feasible directions of polyhedra).
-/

public section

open Set Filter
open scoped Topology NNReal

namespace TauCeti

section

variable {𝕜 E ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [Finite ι]
  {f : ι → Module.Dual 𝕜 E} {c : ι → 𝕜} {x : E}

/-- Near a point of a finite polyhedron, only its active inequalities constrain membership. -/
theorem eventually_mem_polyhedron_iff (hf : ∀ j, Continuous (f j))
    (hx : x ∈ polyhedron f c) :
    ∀ᶠ y in 𝓝 x, y ∈ polyhedron f c ↔
      ∀ j ∈ activeSet f c x, 0 ≤ f j (y - x) := by
  have hslack : ∀ᶠ y in 𝓝 x, ∀ j, j ∉ activeSet f c x → c j < f j y := by
    rw [eventually_all]
    intro j
    by_cases hj : j ∈ activeSet f c x
    · exact Eventually.of_forall fun _ h ↦ (h hj).elim
    · have hlt : c j < f j x :=
        (mem_polyhedron.1 hx j).lt_of_ne (Ne.symm (fun h ↦ hj (mem_activeSet.2 h)))
      exact ((hf j).continuousAt.eventually (Ioi_mem_nhds hlt)).mono fun _ h _ ↦ h
  filter_upwards [hslack] with y hy
  constructor
  · intro hyP j hj
    rw [map_sub, mem_activeSet.1 hj]
    exact sub_nonneg.2 (mem_polyhedron.1 hyP j)
  · intro hyP
    apply mem_polyhedron.2
    intro j
    by_cases hj : j ∈ activeSet f c x
    · have h := hyP j hj
      rw [map_sub, mem_activeSet.1 hj] at h
      linarith
    · exact (hy j hj).le

end

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [Finite ι] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {f : ι → Module.Dual ℝ E} {c : ι → ℝ} {x : E}

/-- The positive tangent cone of a finite polyhedron is cut out by the homogeneous active
inequalities. This holds in any real topological vector space, provided the defining functionals are
continuous. -/
theorem posTangentConeAt_polyhedron (hf : ∀ j, Continuous (f j))
    (hx : x ∈ polyhedron f c) :
    posTangentConeAt (polyhedron f c) x =
      {v | ∀ j ∈ activeSet f c x, 0 ≤ f j v} := by
  ext v
  constructor
  · intro hv j hj
    obtain ⟨α, l, hl, a, d, -, hdP, had⟩ := exists_fun_of_mem_tangentConeAt hv
    have hlim : Tendsto (fun n ↦ f j (a n • d n)) l (𝓝 (f j v)) :=
      ((hf j).tendsto v).comp had
    refine ge_of_tendsto hlim ?_
    filter_upwards [hdP] with n hn
    have h : 0 ≤ f j (d n) := by
      have := mem_polyhedron.1 hn j
      rw [map_add, mem_activeSet.1 hj] at this
      linarith
    simpa only [NNReal.smul_def, map_smul, smul_eq_mul] using mul_nonneg (a n).coe_nonneg h
  · intro hv
    have hpath : Tendsto (fun t : ℝ≥0 ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
      have hcont : Continuous (fun t : ℝ≥0 ↦ x + t • v) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply mem_tangentConeAt_of_add_smul_mem (tendsto_id'.mpr (nhdsGT_le_nhdsNE 0))
    filter_upwards [hpath.eventually (eventually_mem_polyhedron_iff hf hx)] with t ht
    apply ht.2
    intro j hj
    simpa only [add_sub_cancel_left, NNReal.smul_def, map_smul, smul_eq_mul] using
      mul_nonneg t.coe_nonneg (hv j hj)

end TauCeti
