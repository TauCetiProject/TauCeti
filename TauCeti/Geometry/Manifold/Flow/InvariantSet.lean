/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Geometry.Manifold.IntegralCurve.Flow

/-!
# The flow of a vector field on an invariant set

A `C¹` vector field `v` on a boundaryless manifold need not be complete, yet its maximal integral
curves through the points of a set `K` may all be defined for all time and stay in `K`. These
curves then form a flow of `ℝ` on `K` (`TauCeti.globalFlowOn`), to which the topological dynamics
of Mathlib's `Flow` applies. When `K` is the whole manifold this is the flow
`TauCeti.globalFlow` of a complete field, read on the subtype.

A typical use is a compact invariant region of a field that blows up elsewhere, such as the slab
`M × [0, 1]` of a continuation field on `M × ℝ`.

## Main declarations

* `TauCeti.globalFlowOn`: the flow on `K`.
* `TauCeti.coe_globalFlowOn_apply`: it is the maximal integral curve, read in `K`.
* `TauCeti.isMIntegralCurve_coe_globalFlowOn`: its orbits are integral curves of the field.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {K : Set M}

/-- **The flow of a vector field on an invariant set.** Let `v` be a `C¹` vector field and `K` a
set such that the maximal integral curve of `v` through each point of `K` is defined for all time
and stays in `K`. These curves form a flow of `ℝ` on `K`: `globalFlowOn v hv K hK hKv t x` is the
value at time `t` of the maximal integral curve through `x`. -/
noncomputable def globalFlowOn (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (K : Set M)
    (hK : ∀ x ∈ K, maximalIntegralCurveInterval v x = univ)
    (hKv : ∀ x ∈ K, ∀ t, maximalIntegralCurve v x t ∈ K) : Flow ℝ K where
  toFun t x := ⟨maximalIntegralCurve v x t, hKv x x.2 t⟩
  cont' := by
    refine Continuous.subtype_mk ?_ _
    refine (contMDiffOn_maximalIntegralCurve (n := 1) le_rfl hv).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst) fun p ↦ ?_
    simp [hK p.2 p.2.2]
  map_add' t₁ t₂ x := by
    refine Subtype.ext ?_
    simp only
    rw [add_comm, maximalIntegralCurve_add hv (by simp [hK x x.2]) (by simp [hK x x.2])]
  map_zero' x := Subtype.ext maximalIntegralCurve_zero

variable (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hK : ∀ x ∈ K, maximalIntegralCurveInterval v x = univ)
  (hKv : ∀ x ∈ K, ∀ t, maximalIntegralCurve v x t ∈ K)

/-- The flow on an invariant set is the maximal integral curve. -/
@[simp]
theorem coe_globalFlowOn_apply (t : ℝ) (x : K) :
    (globalFlowOn v hv K hK hKv t x : M) = maximalIntegralCurve v x t :=
  (rfl)

/-- The orbits of the flow on an invariant set are integral curves of the field. -/
theorem isMIntegralCurve_coe_globalFlowOn (x : K) :
    IsMIntegralCurve (fun t ↦ (globalFlowOn v hv K hK hKv t x : M)) v := by
  simp only [coe_globalFlowOn_apply]
  exact isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv (hK x x.2)

end TauCeti
