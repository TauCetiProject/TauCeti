/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Topology.MetricSpace.Holder

/-!
# A smooth boundary chart of the unit ball

At a point `ν` of the unit sphere of a real inner product space `E`, the rigid coordinates
`TauCeti.unitSphereChart ν` send `ν` to the origin and the inward normal `-ν` to the first axis
of `ℝ × (ℝ ∙ ν)ᗮ`, so that `(unitSphereChart ν).symm (t, v) = ν - t ν + v`. In these coordinates
the lower boundary of the unit ball is the graph of `v ↦ 1 - √(1 - ‖v‖²)`. Cut off by a bump
function, this is the smooth compactly supported function `TauCeti.unitSphereGraph`, whose
derivative is Hölder continuous for every exponent at most one. Inside the cylinder of
half-height and radius `1/4`, the unit ball is exactly the region above this graph
(`TauCeti.unitSphereChart_symm_mem_ball_iff`). This is the boundary chart that the
`C^{1,β}` estimates up to the boundary take as input. The Lipschitz charts of balls are in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Graph`.

## Main declarations

* `TauCeti.unitSphereGraph`: the cut-off lower boundary of the unit ball over the tangent space,
  with `TauCeti.contDiff_unitSphereGraph` and `TauCeti.exists_holderWith_fderiv_unitSphereGraph`.
* `TauCeti.unitSphereChart`: the rigid coordinates at a point of the unit sphere, with
  `TauCeti.unitSphereChart_symm_apply` and `TauCeti.norm_unitSphereChart_symm_sq`.
* `TauCeti.unitSphereChart_symm_mem_ball_iff`: near the chart centre the unit ball is the region
  above `TauCeti.unitSphereGraph`.
-/

public section

noncomputable section

open Metric Set
open scoped NNReal InnerProductSpace

namespace TauCeti

section Graph

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The bump function equal to one on `closedBall 0 (1/4)` and supported in `ball 0 (1/2)`. -/
private def unitSphereBump : ContDiffBump (0 : K) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The lower boundary of the unit ball seen from the tangent space at a point of the unit sphere,
`v ↦ 1 - √(1 - ‖v‖²)`, cut off by a bump function supported in `ball 0 (1/2)` and equal to one on
`closedBall 0 (1/4)`, so that it is smooth with compact support. -/
def unitSphereGraph (v : K) : ℝ :=
  unitSphereBump (K := K) v * (1 - √(1 - ‖v‖ ^ 2))

/-- The cut-off sphere graph is smooth. -/
theorem contDiff_unitSphereGraph {k : ℕ∞} : ContDiff ℝ k (unitSphereGraph (K := K)) := by
  refine contDiff_iff_contDiffAt.2 fun v => ?_
  by_cases hv : ‖v‖ < 1
  · refine (unitSphereBump (K := K)).contDiff.contDiffAt.mul (contDiffAt_const.sub ?_)
    refine ContDiffAt.sqrt (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt) ?_
    nlinarith [norm_nonneg v]
  · -- Off `closedBall 0 (1/2)` the bump function, hence the graph, vanishes nearby.
    have hout : v ∉ closedBall (0 : K) (unitSphereBump (K := K)).rOut := by
      rw [mem_closedBall, dist_zero_right]
      -- The outer radius of `unitSphereBump` is `1/2` by definition.
      change ¬ ‖v‖ ≤ 1 / 2
      linarith
    have hev : unitSphereGraph (K := K) =ᶠ[nhds v] fun _ => 0 := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hout] with w hw
      rw [unitSphereGraph, image_eq_zero_of_notMem_tsupport (f := ⇑(unitSphereBump (K := K)))
        (by rwa [ContDiffBump.tsupport_eq]), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The cut-off sphere graph has a Hölder continuous derivative, for every exponent at most one. -/
theorem exists_holderWith_fderiv_unitSphereGraph [FiniteDimensional ℝ K] {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α (fderiv ℝ (unitSphereGraph (K := K))) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ (unitSphereGraph (K := K))) :=
    (contDiff_unitSphereGraph (k := 2)).fderiv_right (by norm_num)
  have hs : HasCompactSupport (fderiv ℝ (unitSphereGraph (K := K))) := by
    have h : unitSphereGraph (K := K) =
        ⇑(unitSphereBump (K := K)) * fun v : K => 1 - √(1 - ‖v‖ ^ 2) :=
      rfl
    rw [h]
    exact (unitSphereBump (K := K)).hasCompactSupport.mul_right.fderiv ℝ
  obtain ⟨L, hL⟩ := hd.lipschitzWith_of_hasCompactSupport hs one_ne_zero
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hd.continuous
  exact ⟨_, (holderWith_one.2 hL).of_le_of_norm_le (D := M.toNNReal)
    (fun x => (hM x).trans (Real.le_coe_toNNReal M)) hα one_pos⟩

/-- The cut-off sphere graph vanishes at the origin. -/
@[simp]
theorem unitSphereGraph_zero : unitSphereGraph (0 : K) = 0 := by
  simp [unitSphereGraph]

/-- On `closedBall 0 (1/4)` the cut-off sphere graph is `1 - √(1 - ‖v‖²)`. -/
theorem unitSphereGraph_of_norm_le {v : K} (hv : ‖v‖ ≤ 1 / 4) :
    unitSphereGraph v = 1 - √(1 - ‖v‖ ^ 2) := by
  rw [unitSphereGraph,
    (unitSphereBump (K := K)).one_of_mem_closedBall (by simpa [unitSphereBump] using hv), one_mul]

end Graph

section Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal splitting `x ↦ (-⟪x, ν⟫, x - ⟪x, ν⟫ ν)` along a unit vector `ν`. -/
private def unitSplitting (ν : E) (hν : ‖ν‖ = 1) : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ) :=
  (ℝ ∙ ν).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2
      ((LinearIsometryEquiv.toSpanUnitSingleton ν hν).symm.trans (LinearIsometryEquiv.neg ℝ))
      (LinearIsometryEquiv.refl ℝ (ℝ ∙ ν)ᗮ))

private theorem unitSplitting_symm_apply (ν : E) (hν : ‖ν‖ = 1) (z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)) :
    (unitSplitting ν hν).symm z = (-z.fst) • ν + (z.snd : E) := by
  obtain ⟨⟨t, v⟩⟩ := z
  simp [unitSplitting, LinearIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.coe_refl]

/-- The rigid coordinates at a point `ν` of the unit sphere: `ν` goes to the origin and the inward
normal `-ν` to the first axis, `(unitSphereChart ν hν).symm (t, v) = ν - t ν + v`. -/
def unitSphereChart (ν : E) (hν : ‖ν‖ = 1) : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ) :=
  (AffineIsometryEquiv.vaddConst ℝ ν).symm.trans (unitSplitting ν hν).toAffineIsometryEquiv

/-- The inverse of the rigid coordinates at `ν` is `(t, v) ↦ ν - t ν + v`. -/
@[simp]
theorem unitSphereChart_symm_apply (ν : E) (hν : ‖ν‖ = 1) (z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)) :
    (unitSphereChart ν hν).symm z = ν - z.fst • ν + (z.snd : E) := by
  rw [AffineIsometryEquiv.symm_apply_eq]
  have h : ν - z.fst • ν + (z.snd : E) -ᵥ ν = (unitSplitting ν hν).symm z := by
    rw [unitSplitting_symm_apply, vsub_eq_sub, neg_smul]
    abel
  simp only [unitSphereChart, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.coe_vaddConst_symm, LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  rw [h, LinearIsometryEquiv.apply_symm_apply]

/-- The rigid coordinates at `ν` send `ν` to the origin. -/
@[simp]
theorem unitSphereChart_apply_self (ν : E) (hν : ‖ν‖ = 1) : unitSphereChart ν hν ν = 0 := by
  simp [unitSphereChart]

/-- The squared norm of the point with coordinates `(t, v)` at `ν` is `(1 - t)² + ‖v‖²`. -/
theorem norm_unitSphereChart_symm_sq (ν : E) (hν : ‖ν‖ = 1) (z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)) :
    ‖(unitSphereChart ν hν).symm z‖ ^ 2 = (1 - z.fst) ^ 2 + ‖z.snd‖ ^ 2 := by
  have hinner : ⟪ν, (z.snd : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 z.snd.property
  have h1 : ν - z.fst • ν + (z.snd : E) = (1 - z.fst) • ν + (z.snd : E) := by
    rw [sub_smul, one_smul]
  rw [unitSphereChart_symm_apply, h1, norm_add_sq_real, norm_smul, inner_smul_left, hinner, hν,
    Real.norm_eq_abs, Submodule.norm_coe]
  simp [sq_abs]

/-- **The unit ball in the chart.** In the cylinder of half-height and radius `1/4` about the
centre of the rigid coordinates at a point `ν` of the unit sphere, the unit ball is the region
above the cut-off sphere graph. -/
theorem unitSphereChart_symm_mem_ball_iff (ν : E) (hν : ‖ν‖ = 1)
    {z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)} (hz : z ∈ normalCylinder (1 / 4) (1 / 4)) :
    (unitSphereChart ν hν).symm z ∈ ball 0 1 ↔ unitSphereGraph z.snd < z.fst := by
  rw [mem_normalCylinder] at hz
  obtain ⟨-, ht2, hv⟩ := hz
  have hsq := norm_unitSphereChart_symm_sq ν hν z
  rw [mem_ball_zero_iff, unitSphereGraph_of_norm_le hv.le]
  have hn0 := norm_nonneg ((unitSphereChart ν hν).symm z)
  constructor
  · intro h
    have hlt : (1 - z.fst) ^ 2 < 1 - ‖z.snd‖ ^ 2 := by nlinarith
    have := (Real.lt_sqrt (by linarith)).2 hlt
    linarith
  · intro h
    have hlt : 1 - z.fst < √(1 - ‖z.snd‖ ^ 2) := by linarith
    have hsq' := (Real.lt_sqrt (by linarith)).1 hlt
    nlinarith

end Chart

end TauCeti
