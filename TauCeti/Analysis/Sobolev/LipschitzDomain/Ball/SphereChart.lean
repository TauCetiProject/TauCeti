/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Smooth boundary charts of balls

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

The global `C^{1,β}` estimates take one chart at every boundary point, all with the same model
space. When `E` has dimension `n + 1`, every point of the sphere of radius `r` about `c` has rigid
coordinates in `ℝ × ℝⁿ`, `ℝⁿ = EuclideanSpace ℝ (Fin n)`, in which the ball of radius `r` about `c`
(`TauCeti.exists_affineIsometryEquiv_graph_ball`) or the complement of the closed ball
(`TauCeti.exists_affineIsometryEquiv_graph_compl_closedBall`) is, inside a cylinder of size `r / 4`,
the region above the graph of the rescaled sphere graph `v ↦ ± r g(v / r)`, which is of class
`C^{1,α}` for every `α ≤ 1`. So an annulus, for instance, has a `C^{1,α}` boundary in the sense of
these estimates.

## Main declarations

* `TauCeti.unitSphereGraph`: the cut-off lower boundary of the unit ball over the tangent space,
  with `TauCeti.contDiff_unitSphereGraph` and `TauCeti.exists_holderWith_fderiv_unitSphereGraph`.
* `TauCeti.unitSphereChart`: the rigid coordinates at a point of the unit sphere, with
  `TauCeti.unitSphereChart_symm_apply` and `TauCeti.norm_unitSphereChart_symm_sq`.
* `TauCeti.unitSphereChart_symm_mem_ball_iff`: near the chart centre the unit ball is the region
  above `TauCeti.unitSphereGraph`.
* `TauCeti.exists_affineIsometryEquiv_unitSphereGraph_chart`: such charts at every point of the
  unit sphere, all with values in one model space.
* `TauCeti.exists_affineIsometryEquiv_graph_ball` and
  `TauCeti.exists_affineIsometryEquiv_graph_compl_closedBall`: `C^{1,α}` boundary charts in the
  model `ℝ × ℝⁿ` of a ball and of the exterior of a closed ball, at every point of their sphere.
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

/-- The cut-off sphere graph is compactly supported. -/
theorem hasCompactSupport_unitSphereGraph [FiniteDimensional ℝ K] :
    HasCompactSupport (unitSphereGraph (K := K)) := by
  have h : unitSphereGraph (K := K) =
      ⇑(unitSphereBump (K := K)) * fun v : K => 1 - √(1 - ‖v‖ ^ 2) :=
    rfl
  rw [h]
  exact (unitSphereBump (K := K)).hasCompactSupport.mul_right

/-- The cut-off sphere graph has a Hölder continuous derivative, for every exponent at most one. -/
theorem exists_holderWith_fderiv_unitSphereGraph [FiniteDimensional ℝ K] {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α (fderiv ℝ (unitSphereGraph (K := K))) := by
  obtain ⟨C, hC, -⟩ := ((contDiff_unitSphereGraph (k := 2)).fderiv_right (m := 1) (by norm_num)
    ).exists_holderWith_and_norm_le_of_hasCompactSupport
      ((hasCompactSupport_unitSphereGraph (K := K)).fderiv (𝕜 := ℝ)) hα
  exact ⟨C, hC⟩

/-- The cut-off sphere graph vanishes at the origin. -/
@[simp]
theorem unitSphereGraph_zero : unitSphereGraph (0 : K) = 0 := by
  simp [unitSphereGraph]

/-- On `closedBall 0 (1/4)` the cut-off sphere graph is `1 - √(1 - ‖v‖²)`. -/
theorem unitSphereGraph_of_norm_le {v : K} (hv : ‖v‖ ≤ 1 / 4) :
    unitSphereGraph v = 1 - √(1 - ‖v‖ ^ 2) := by
  rw [unitSphereGraph,
    (unitSphereBump (K := K)).one_of_mem_closedBall (by simpa [unitSphereBump] using hv), one_mul]

/-- Near the centre of the chart, `ν`-coordinate `r - s` and tangential coordinate `v` describe a
point of the open ball of radius `r` exactly when `s` lies strictly above the sphere graph
`r (1 - √(1 - ‖v / r‖²))`, and a point of the closed ball exactly when `s` lies above it. -/
private theorem sq_add_sq_lt_iff {r s : ℝ} (hr : 0 < r) {v : K}
    (hs : s < r) (hv : ‖v‖ ≤ r / 4) :
    ((r - s) ^ 2 + ‖v‖ ^ 2 < r ^ 2 ↔ r * unitSphereGraph (r⁻¹ • v) < s) ∧
      ((r - s) ^ 2 + ‖v‖ ^ 2 ≤ r ^ 2 ↔ r * unitSphereGraph (r⁻¹ • v) ≤ s) := by
  have hv' : ‖r⁻¹ • v‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]
    linarith
  have hvr : ‖r⁻¹ • v‖ ^ 2 = ‖v‖ ^ 2 / r ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
    field_simp
  have hq : 0 ≤ 1 - ‖r⁻¹ • v‖ ^ 2 := by nlinarith [norm_nonneg (r⁻¹ • v)]
  rw [unitSphereGraph_of_norm_le hv']
  set q := √(1 - ‖r⁻¹ • v‖ ^ 2)
  have hq2 : q ^ 2 = 1 - ‖v‖ ^ 2 / r ^ 2 := by rw [Real.sq_sqrt hq, hvr]
  have hrq : (r * q) ^ 2 = r ^ 2 - ‖v‖ ^ 2 := by
    rw [mul_pow, hq2]
    field_simp
  have hlt : r * (1 - q) < s ↔ (r - s) ^ 2 < (r * q) ^ 2 := by
    rw [sq_lt_sq₀ (by linarith) (by positivity)]
    constructor <;> intro h <;> linarith
  have hle : r * (1 - q) ≤ s ↔ (r - s) ^ 2 ≤ (r * q) ^ 2 := by
    rw [sq_le_sq₀ (by linarith) (by positivity)]
    constructor <;> intro h <;> linarith
  rw [hlt, hle, hrq]
  exact ⟨by constructor <;> intro h <;> linarith, by constructor <;> intro h <;> linarith⟩

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
  have h := (sq_add_sq_lt_iff one_pos (s := z.fst) (by linarith) (v := z.snd) (by linarith)).1
  rwa [inv_one, one_smul, one_mul, one_pow, ← norm_unitSphereChart_symm_sq ν hν,
    sq_lt_one_iff₀ (norm_nonneg _), ← mem_ball_zero_iff] at h

/-- **Charts of the unit ball with one model space.** Fix a unit vector `e₀`. At every point `x`
of the unit sphere there are rigid coordinates with values in `ℝ × (ℝ ∙ e₀)ᗮ`, sending `x` to the
origin, in which the unit ball is the region above the cut-off sphere graph inside the cylinder of
half-height and radius `1/4`: the coordinates `TauCeti.unitSphereChart e₀` after the reflection
exchanging `x` and `e₀`. So the unit ball is a bounded open set with smooth boundary, in the form
that the global estimates up to the boundary take as input, with charts sharing one model space. -/
theorem exists_affineIsometryEquiv_unitSphereGraph_chart {e₀ x : E} (he₀ : ‖e₀‖ = 1)
    (hx : ‖x‖ = 1) :
    ∃ e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × (ℝ ∙ e₀)ᗮ), e x = 0 ∧
      ∀ z ∈ normalCylinder (1 / 4) (1 / 4),
        (e.symm z ∈ ball 0 1 ↔ unitSphereGraph z.snd < z.fst) := by
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (x - e₀))ᗮ.reflection
  refine ⟨R.toAffineIsometryEquiv.trans (unitSphereChart e₀ he₀), ?_, fun z hz => ?_⟩
  · simp [R, Submodule.reflection_sub (hx.trans he₀.symm)]
  · rw [← unitSphereChart_symm_mem_ball_iff e₀ he₀ hz, mem_ball_zero_iff, mem_ball_zero_iff,
      AffineIsometryEquiv.coe_symm_trans, Function.comp_apply]
    have h0 : R.toAffineIsometryEquiv.symm (0 : E) = 0 := by
      rw [AffineIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
        map_zero]
    rw [← dist_zero_right, ← h0, AffineIsometryEquiv.dist_map, dist_zero_right]

end Chart

/-! ### Boundary charts of balls and of their exteriors, in a fixed model -/

section GraphChart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]

/-- The rigid coordinates at the point `r • ν` of the sphere of radius `r`, with the orthogonal
complement of `ν` identified with `EuclideanSpace ℝ (Fin n)` by an orthonormal basis `L` and the
first axis turned by `σ`: `(t, v) ↦ (r - σ⁻¹ t) ν + L⁻¹ v`. -/
private def sphereChart (σ : ℝ ≃ₗᵢ[ℝ] ℝ) (r : ℝ) (ν : E) (hν : ‖ν‖ = 1) :
    E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)) :=
  ((AffineIsometryEquiv.vaddConst ℝ ((r - 1) • ν)).symm.trans (unitSphereChart ν hν)).trans
    (LinearIsometryEquiv.withLpProdCongr 2 σ
      (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
        (norm_ne_zero_iff.1 (hν ▸ one_ne_zero))).repr).toAffineIsometryEquiv

private theorem sphereChart_apply_smul (σ : ℝ ≃ₗᵢ[ℝ] ℝ) (r : ℝ) (ν : E) (hν : ‖ν‖ = 1) :
    sphereChart (n := n) σ r ν hν (r • ν) = 0 := by
  have h : r • ν - (r - 1) • ν = ν := by rw [← sub_smul, sub_sub_cancel, one_smul]
  simp [sphereChart, h]

/-- The inverse of `sphereChart`: undo `σ` and the orthonormal basis, then the unit-sphere chart,
then translate by `(r - 1) • ν`. -/
@[simp]
private theorem sphereChart_symm_apply (σ : ℝ ≃ₗᵢ[ℝ] ℝ) (r : ℝ) (ν : E) (hν : ‖ν‖ = 1)
    (z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) :
    (sphereChart σ r ν hν).symm z = (unitSphereChart ν hν).symm (WithLp.toLp 2 (σ.symm z.fst,
      (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
        (norm_ne_zero_iff.1 (hν ▸ one_ne_zero))).repr.symm z.snd)) + (r - 1) • ν := by
  simp [sphereChart]

/-- The squared norm of the point with coordinates `z` is `(r - σ⁻¹ z.fst)² + ‖z.snd‖²`. -/
private theorem norm_sphereChart_symm_sq (σ : ℝ ≃ₗᵢ[ℝ] ℝ) (r : ℝ) (ν : E) (hν : ‖ν‖ = 1)
    (z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) :
    ‖(sphereChart σ r ν hν).symm z‖ ^ 2 = (r - σ.symm z.fst) ^ 2 + ‖z.snd‖ ^ 2 := by
  set L := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (norm_ne_zero_iff.1 (hν ▸ one_ne_zero))).repr
  have hinner : ⟪ν, ((L.symm z.snd : (ℝ ∙ ν)ᗮ) : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (L.symm z.snd).property
  have h1 : (sphereChart σ r ν hν).symm z =
      (r - σ.symm z.fst) • ν + ((L.symm z.snd : (ℝ ∙ ν)ᗮ) : E) := by
    rw [sphereChart_symm_apply, unitSphereChart_symm_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    module
  rw [h1, norm_add_sq_real, norm_smul, inner_smul_left, hinner, hν, Real.norm_eq_abs,
    Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  simp [sq_abs]

/-- The cut-off sphere graph rescaled to radius `r`, `v ↦ r g(v / r)`, is smooth, vanishes at the
origin, is compactly supported, and has an `α`-Hölder derivative for every `α ≤ 1`. -/
private theorem sphereGraph_scaled {r : ℝ} (hr : 0 < r) (s : ℝ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ Kγ : ℝ≥0, (fun v : EuclideanSpace ℝ (Fin n) => s * (r * unitSphereGraph (r⁻¹ • v))) 0 = 0 ∧
      ContDiff ℝ 1 (fun v : EuclideanSpace ℝ (Fin n) => s * (r * unitSphereGraph (r⁻¹ • v))) ∧
      HolderWith Kγ α
        (fderiv ℝ fun v : EuclideanSpace ℝ (Fin n) => s * (r * unitSphereGraph (r⁻¹ • v))) := by
  set γ : EuclideanSpace ℝ (Fin n) → ℝ := fun v => s * (r * unitSphereGraph (r⁻¹ • v))
  have hγ : ∀ k : ℕ∞, ContDiff ℝ k γ := fun k =>
    contDiff_const.mul (contDiff_const.mul
      ((contDiff_unitSphereGraph (k := k)).comp (contDiff_id.const_smul r⁻¹)))
  have hc : HasCompactSupport γ :=
    ((hasCompactSupport_unitSphereGraph.comp_smul (inv_ne_zero hr.ne')).mul_left
      (f := fun _ => r)).mul_left (f := fun _ => s)
  obtain ⟨K, hK, -⟩ := ((hγ 2).fderiv_right (m := 1) (by norm_num)
    ).exists_holderWith_and_norm_le_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ)) hα
  exact ⟨K, by simp [γ], hγ 1, hK⟩

/-- The chart of `sphereChart`, read on the cylinder of half-height and radius `r / 4`: with `σ`
the identity it puts the ball of radius `r` above the graph of `v ↦ r g(v / r)`, and with `σ = -1`
it puts the complement of the closed ball above the graph of `v ↦ -r g(v / r)`. -/
private theorem sphereChart_symm_mem_iff {r : ℝ} (hr : 0 < r) (ν : E) (hν : ‖ν‖ = 1)
    {z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))} (hz : z ∈ normalCylinder (r / 4) (r / 4)) :
    ((sphereChart (LinearIsometryEquiv.refl ℝ ℝ) r ν hν).symm z ∈ ball (0 : E) r ↔
        r * unitSphereGraph (r⁻¹ • z.snd) < z.fst) ∧
      ((sphereChart (LinearIsometryEquiv.neg ℝ) r ν hν).symm z ∈ (closedBall (0 : E) r)ᶜ ↔
        -1 * (r * unitSphereGraph (r⁻¹ • z.snd)) < z.fst) := by
  rw [mem_normalCylinder] at hz
  obtain ⟨ht1, ht2, hv⟩ := hz
  have hrefl : (LinearIsometryEquiv.refl ℝ ℝ).symm z.fst = z.fst := by
    rw [LinearIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.coe_refl, id]
  have hneg : (LinearIsometryEquiv.neg ℝ).symm z.fst = -z.fst := by
    rw [LinearIsometryEquiv.symm_neg, LinearIsometryEquiv.coe_neg]
  constructor
  · rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) hr.le, norm_sphereChart_symm_sq, hrefl]
    exact (sq_add_sq_lt_iff hr (by linarith) hv.le).1
  · rw [mem_compl_iff, mem_closedBall_zero_iff, ← sq_le_sq₀ (norm_nonneg _) hr.le,
      norm_sphereChart_symm_sq, hneg, (sq_add_sq_lt_iff hr (by linarith) hv.le).2, not_le,
      neg_one_mul]
    constructor <;> intro h <;> linarith

/-- Translating the chart of `sphereChart` to the centre `c`. -/
private theorem sphereChart_translate {σ : ℝ ≃ₗᵢ[ℝ] ℝ} {c x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ sphere c r) :
    ∃ (ν : E) (hν : ‖ν‖ = 1),
      ((AffineIsometryEquiv.vaddConst ℝ c).symm.trans (sphereChart (n := n) σ r ν hν)) x = 0 ∧
      ∀ z, ((AffineIsometryEquiv.vaddConst ℝ c).symm.trans (sphereChart (n := n) σ r ν hν)).symm z =
        (sphereChart (n := n) σ r ν hν).symm z + c := by
  have hxc : ‖x - c‖ = r := by rwa [mem_sphere_iff_norm] at hx
  have hν : ‖r⁻¹ • (x - c)‖ = 1 := by
    rw [norm_smul, hxc, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']
  have hxν : r • r⁻¹ • (x - c) = x - c := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  refine ⟨_, hν, ?_, fun z => by
    simp only [AffineIsometryEquiv.coe_symm_trans, Function.comp_apply,
      AffineIsometryEquiv.symm_symm, AffineIsometryEquiv.coe_vaddConst, vadd_eq_add]⟩
  simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.coe_vaddConst_symm, vsub_eq_sub]
  have h := sphereChart_apply_smul (n := n) σ r _ hν
  rwa [hxν] at h

/-- **A `C^{1,α}` boundary chart of a ball.** Let `E` have dimension `n + 1` and let `x` lie on the
sphere of radius `r > 0` about `c`. There are rigid coordinates `e : E ≃ᵃⁱ[ℝ] ℝ × ℝⁿ` sending `x` to
the origin and a `C¹` function `γ` vanishing at the origin, whose derivative is `α`-Hölder for a
given `α ≤ 1`, such that inside the cylinder of half-height and radius `r / 4` the ball of radius
`r` about `c` is the region above the graph of `γ`. The model space `ℝⁿ` does not depend on `x`. -/
theorem exists_affineIsometryEquiv_graph_ball {c x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ sphere c r) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ (e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)))
      (γ : EuclideanSpace ℝ (Fin n) → ℝ) (Kγ : ℝ≥0), e x = 0 ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
      HolderWith Kγ α (fderiv ℝ γ) ∧
      ∀ z ∈ normalCylinder (r / 4) (r / 4), (e.symm z ∈ ball c r ↔ γ z.snd < z.fst) := by
  obtain ⟨ν, hν, he, hsymm⟩ := sphereChart_translate (n := n)
    (σ := LinearIsometryEquiv.refl ℝ ℝ) hr hx
  obtain ⟨Kγ, h0, hγ, hK⟩ := sphereGraph_scaled (n := n) hr 1 hα
  refine ⟨_, _, Kγ, he, h0, hγ, hK, fun z hz => ?_⟩
  rw [hsymm, mem_ball, dist_eq_norm, add_sub_cancel_right, ← mem_ball_zero_iff, one_mul]
  exact (sphereChart_symm_mem_iff hr ν hν hz).1

/-- **A `C^{1,α}` boundary chart of the exterior of a ball.** Let `E` have dimension `n + 1` and let
`x` lie on the sphere of radius `r > 0` about `c`. There are rigid coordinates `e : E ≃ᵃⁱ[ℝ] ℝ × ℝⁿ`
sending `x` to the origin and a `C¹` function `γ` vanishing at the origin, whose derivative is
`α`-Hölder for a given `α ≤ 1`, such that inside the cylinder of half-height and radius `r / 4` the
complement of the closed ball of radius `r` about `c` is the region above the graph of `γ`. -/
theorem exists_affineIsometryEquiv_graph_compl_closedBall {c x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ sphere c r) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ (e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)))
      (γ : EuclideanSpace ℝ (Fin n) → ℝ) (Kγ : ℝ≥0), e x = 0 ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
      HolderWith Kγ α (fderiv ℝ γ) ∧
      ∀ z ∈ normalCylinder (r / 4) (r / 4), (e.symm z ∈ (closedBall c r)ᶜ ↔ γ z.snd < z.fst) := by
  obtain ⟨ν, hν, he, hsymm⟩ := sphereChart_translate (n := n)
    (σ := LinearIsometryEquiv.neg ℝ) hr hx
  obtain ⟨Kγ, h0, hγ, hK⟩ := sphereGraph_scaled (n := n) hr (-1) hα
  refine ⟨_, _, Kγ, he, h0, hγ, hK, fun z hz => ?_⟩
  rw [hsymm, mem_compl_iff, mem_closedBall, dist_eq_norm, add_sub_cancel_right,
    ← mem_closedBall_zero_iff, ← mem_compl_iff]
  exact (sphereChart_symm_mem_iff hr ν hν hz).2

end GraphChart

end TauCeti
