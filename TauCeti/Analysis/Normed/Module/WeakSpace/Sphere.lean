/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

/-!
# Weak neighborhoods, weak-to-norm continuity, and weak closures of spheres

If a linear map `J : E →ₗ[𝕜] F` has infinite-dimensional range, then the common kernel of any
finite family of continuous linear functionals on `E` contains a vector `v` with `J v ≠ 0`.
Consequently every weak neighborhood of `x : E` contains an entire affine line `x + 𝕜 • v` with
`J v ≠ 0` (`TauCeti.exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace`).

This yields two sharp characterizations in infinite dimensions:

* Over a nontrivially normed field, `w ↦ J ((toWeakSpace 𝕜 E).symm w)` is discontinuous at every
  point whenever `J` has infinite-dimensional range
  (`TauCeti.not_continuousAt_comp_toWeakSpace_symm`). Over a complete nontrivially normed field
  with Hausdorff target weak topology, a continuous linear map `J : E →L[𝕜] F` is globally
  weak-to-norm continuous if and only if its range is finite-dimensional
  (`ContinuousLinearMap.continuous_comp_toWeakSpace_symm_iff`); in particular,
  `(toWeakSpace 𝕜 E).symm` is continuous if and only if `E` is finite-dimensional
  (`TauCeti.continuous_toWeakSpace_symm_iff`).
* Over `ℝ` or `ℂ`, for a continuous linear map `J : E →L[𝕜] F` into a normed space with
  infinite-dimensional range, the weak closure of the preimage of any sphere `J ⁻¹' sphere y r`
  is the preimage of the closed ball `J ⁻¹' closedBall y r`
  (`ContinuousLinearMap.closure_toWeakSpace_preimage_sphere`). In particular, the weak closure of
  `{u | ‖J u‖ = r}` is `{u | ‖J u‖ ≤ r}`
  (`ContinuousLinearMap.closure_toWeakSpace_setOf_norm_apply_eq`), the weak closure of a sphere
  `Metric.sphere x r` in an infinite-dimensional normed space is `Metric.closedBall x r`
  (`TauCeti.closure_toWeakSpace_sphere`), and for `r > 0` these spheres are weakly closed if and
  only if the range (respectively the space) is finite-dimensional
  (`ContinuousLinearMap.isClosed_toWeakSpace_preimage_sphere_iff`,
  `ContinuousLinearMap.isClosed_toWeakSpace_setOf_norm_apply_eq_iff`,
  `TauCeti.isClosed_toWeakSpace_sphere_iff`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, §3.2, Proposition 3.5 and Example 1.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.5.
-/

public section

open Filter Metric Set Topology

section WeakNeighborhoods

namespace TauCeti

variable {𝕜 E F : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F]

/-- If `J : E →ₗ[𝕜] F` has infinite-dimensional range, every weak neighborhood of `x : E`
contains an entire affine line `x + 𝕜 • v` along which `J v ≠ 0`. -/
theorem exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace (J : E →ₗ[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 (LinearMap.range J)) (x : E) {U : Set (WeakSpace 𝕜 E)}
    (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ v : E, J v ≠ 0 ∧ ∀ k : 𝕜, toWeakSpace 𝕜 E (x + k • v) ∈ U := by
  have hind : IsInducing
      (fun (w : WeakSpace 𝕜 E) (f : StrongDual 𝕜 E) ↦ f ((toWeakSpace 𝕜 E).symm w)) := ⟨rfl⟩
  rw [hind.nhds_eq_comap] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.1 hU
  rw [nhds_pi] at hW
  obtain ⟨S, t, ht, hSt⟩ := Filter.mem_pi'.1 hW
  -- The evaluation map on the finite set `S` has finite-dimensional image, so its kernel cannot
  -- be contained in `ker J`.
  let Φ : E →ₗ[𝕜] (S → 𝕜) := LinearMap.pi fun f : S ↦ f.1.toLinearMap
  have hv : ∃ v : E, Φ v = 0 ∧ J v ≠ 0 := by
    by_contra h
    push Not at h
    have hker : LinearMap.ker Φ ≤ LinearMap.ker J := fun v hv ↦ h v hv
    have hfinQ : FiniteDimensional 𝕜 (E ⧸ LinearMap.ker Φ) :=
      Φ.quotKerEquivRange.symm.finiteDimensional
    have hrange : LinearMap.range ((LinearMap.ker Φ).liftQ J hker) = LinearMap.range J :=
      Submodule.range_liftQ (LinearMap.ker Φ) J hker
    exact hJ (hrange ▸ Module.Finite.range ((LinearMap.ker Φ).liftQ J hker))
  obtain ⟨v, hvΦ, hJv⟩ := hv
  refine ⟨v, hJv, fun k ↦ hWU (hSt fun f hf ↦ ?_)⟩
  have hfv : f v = 0 := congr_fun hvΦ ⟨f, hf⟩
  have hfx : f x ∈ t f := by simpa using mem_of_mem_nhds (ht f)
  simpa [hfv] using hfx

/-- In an infinite-dimensional topological vector space, every weak neighborhood of `x` contains
a nontrivial affine line `x + 𝕜 • v` (`v ≠ 0`). -/
theorem exists_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace
    (hE : ¬ FiniteDimensional 𝕜 E) (x : E) {U : Set (WeakSpace 𝕜 E)}
    (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ v : E, v ≠ 0 ∧ ∀ k : 𝕜, toWeakSpace 𝕜 E (x + k • v) ∈ U := by
  have hrange : ¬ FiniteDimensional 𝕜 (LinearMap.range (LinearMap.id (R := 𝕜) (M := E))) := by
    rw [LinearMap.range_id]
    exact fun h ↦ hE (Submodule.topEquiv (R := 𝕜) (M := E)).finiteDimensional
  exact exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace LinearMap.id hrange x hU

end TauCeti

end WeakNeighborhoods

section Continuity

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A linear map with infinite-dimensional range into a normed space is discontinuous from the
weak topology to the norm topology at every point. -/
theorem not_continuousAt_comp_toWeakSpace_symm (J : E →ₗ[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 (LinearMap.range J)) (w : WeakSpace 𝕜 E) :
    ¬ ContinuousAt (fun u : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm u)) w := by
  intro hc
  set x : E := (toWeakSpace 𝕜 E).symm w
  have hw : toWeakSpace 𝕜 E x = w := (toWeakSpace 𝕜 E).apply_symm_apply w
  have hpre : (fun u : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm u)) ⁻¹' ball (J x) 1 ∈
      𝓝 (toWeakSpace 𝕜 E x) := by
    rw [hw]
    exact hc.preimage_mem_nhds (ball_mem_nhds _ one_pos)
  obtain ⟨v, hJv, hline⟩ := exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace J hJ x hpre
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 (1 / ‖J v‖)
  have hlt : dist (J (x + k • v)) (J x) < 1 := by
    simpa [mem_preimage, mem_ball] using hline k
  rw [map_add, map_smul, dist_eq_norm, add_sub_cancel_left, norm_smul] at hlt
  have hgt : 1 < ‖k‖ * ‖J v‖ := (div_lt_iff₀ (norm_pos_iff.2 hJv)).1 hk
  exact hlt.not_gt hgt

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [T2Space (WeakSpace 𝕜 F)]

/-- Over a complete nontrivially normed field, a continuous linear map into a normed space with
Hausdorff weak topology is globally weak-to-norm continuous if and only if its range is
finite-dimensional. -/
theorem continuous_comp_toWeakSpace_symm_iff (J : E →L[𝕜] F) :
    Continuous (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) ↔
      FiniteDimensional 𝕜 J.range := by
  refine ⟨fun h ↦ ?_, fun hfin ↦ ?_⟩
  · by_contra hJ
    exact TauCeti.not_continuousAt_comp_toWeakSpace_symm J.toLinearMap hJ 0 h.continuousAt
  · -- Factor through the finite-dimensional range inside `WeakSpace 𝕜 F`, where every linear
    -- map is continuous.
    let R : Submodule 𝕜 (WeakSpace 𝕜 F) := J.range.map (toWeakSpace 𝕜 F).toLinearMap
    have : FiniteDimensional 𝕜 R :=
      ((toWeakSpace 𝕜 F).submoduleMap J.range).finiteDimensional
    let g : R →ₗ[𝕜] F := ((toWeakSpace 𝕜 F).symm : WeakSpace 𝕜 F →ₗ[𝕜] F).comp R.subtype
    have hg : Continuous g := LinearMap.continuous_of_finiteDimensional (E := R) (F' := F) g
    have hφ : Continuous (fun w : WeakSpace 𝕜 E ↦
        (⟨WeakSpace.map J w, ⟨J ((toWeakSpace 𝕜 E).symm w), ⟨(toWeakSpace 𝕜 E).symm w, rfl⟩,
          rfl⟩⟩ : R)) :=
      (WeakSpace.map J).continuous.subtype_mk _
    exact hg.comp hφ

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [T2Space (WeakSpace 𝕜 E)]

/-- Over a complete nontrivially normed field, the identity from the weak topology to the norm
topology is continuous if and only if the space is finite-dimensional. -/
theorem continuous_toWeakSpace_symm_iff :
    Continuous (toWeakSpace 𝕜 E).symm ↔ FiniteDimensional 𝕜 E := by
  have h := (ContinuousLinearMap.id 𝕜 E).continuous_comp_toWeakSpace_symm_iff
  have hrange : (ContinuousLinearMap.id 𝕜 E).range = ⊤ := LinearMap.range_id
  rw [hrange] at h
  exact h.trans ⟨fun _ ↦ (Submodule.topEquiv (R := 𝕜) (M := E)).finiteDimensional,
    fun _ ↦ (Submodule.topEquiv (R := 𝕜) (M := E)).symm.finiteDimensional⟩

end TauCeti

end Continuity

section WeakClosureOfSpheres

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `J : E →L[𝕜] F` has infinite-dimensional range, the weak closure of the preimage of any
sphere `J ⁻¹' Metric.sphere y r` is the preimage of the closed ball `J ⁻¹' Metric.closedBall y r`.
This holds for every real radius `r`, including `r ≤ 0`. -/
theorem closure_toWeakSpace_preimage_sphere (J : E →L[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 J.range) (y : F) (r : ℝ) :
    closure (toWeakSpace 𝕜 E '' (J ⁻¹' sphere y r)) =
      toWeakSpace 𝕜 E '' (J ⁻¹' closedBall y r) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let : IsScalarTower ℝ 𝕜 F := .of_algebraMap_smul fun _ _ ↦ rfl
  have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  apply subset_antisymm
  · -- `J ⁻¹' closedBall y r` is norm-closed and convex, hence weakly closed.
    have hclosed : IsClosed (toWeakSpace 𝕜 E '' (J ⁻¹' closedBall y r)) := by
      have hconv : Convex ℝ (J ⁻¹' closedBall y r) :=
        (convex_closedBall y r).linear_preimage (J.toLinearMap.restrictScalars ℝ)
      have hnorm : IsClosed (J ⁻¹' closedBall y r) := isClosed_closedBall.preimage J.continuous
      rw [← hnorm.closure_eq, hconv.toWeakSpace_closure 𝕜]
      exact isClosed_closure
    exact closure_minimal (image_mono (preimage_mono sphere_subset_closedBall)) hclosed
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_preimage, mem_closedBall] at hx
    rcases hx.eq_or_lt with hxeq | hxlt
    · exact subset_closure ⟨x, hxeq, rfl⟩
    · -- Any weak neighborhood of `x` contains a line `x + 𝕜 • v` with `J v ≠ 0`; the
      -- intermediate value theorem finds a point on the ray at distance `r` from `y`.
      rw [mem_closure_iff_nhds]
      intro U hU
      obtain ⟨v, hJv, hline⟩ :=
        TauCeti.exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace J.toLinearMap hJ x hU
      have hJv_pos : 0 < ‖J v‖ := norm_pos_iff.2 hJv
      have hr_nonneg : 0 ≤ r := dist_nonneg.trans hxlt.le
      set T : ℝ := (r + dist (J x) y) / ‖J v‖
      have hT : 0 ≤ T := div_nonneg (add_nonneg hr_nonneg dist_nonneg) hJv_pos.le
      let φ : ℝ → ℝ := fun t ↦ dist (J (x + (t : 𝕜) • v)) y
      have hφ_cont : ContinuousOn φ (Icc 0 T) := by
        refine Continuous.continuousOn ?_
        have hray : Continuous (fun t : ℝ ↦ x + (t : 𝕜) • v) :=
          continuous_const.add (RCLike.continuous_ofReal.smul continuous_const)
        exact (J.continuous.comp hray).dist continuous_const
      have hφ0 : φ 0 ≤ r := by simpa [φ] using hxlt.le
      have hφT : r ≤ φ T := by
        have htri : ‖(T : 𝕜) • J v‖ - ‖J x - y‖ ≤ ‖(J x - y) + (T : 𝕜) • J v‖ := by
          simpa only [sub_neg_eq_add, norm_neg, add_comm] using
            norm_sub_norm_le ((T : 𝕜) • J v) (-(J x - y))
        have hnormT : ‖(T : 𝕜) • J v‖ = r + dist (J x) y := by
          rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hT,
            div_mul_cancel₀ _ hJv_pos.ne']
        have hrew : φ T = ‖(J x - y) + (T : 𝕜) • J v‖ := by
          simp only [φ, dist_eq_norm, map_add, map_smul]
          abel_nf
        rw [hrew]
        linarith [hnormT, dist_eq_norm (J x) y]
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc hT hφ_cont ⟨hφ0, hφT⟩
      exact ⟨toWeakSpace 𝕜 E (x + (t : 𝕜) • v), hline (t : 𝕜), ⟨x + (t : 𝕜) • v, ht, rfl⟩⟩

/-- For `r > 0` and `x : E`, the preimage `J ⁻¹' Metric.sphere (J x) r` is weakly closed if and
only if `J` has finite-dimensional range. -/
theorem isClosed_toWeakSpace_preimage_sphere_iff (J : E →L[𝕜] F) (x : E) {r : ℝ} (hr : 0 < r) :
    IsClosed (toWeakSpace 𝕜 E '' (J ⁻¹' sphere (J x) r)) ↔
      FiniteDimensional 𝕜 J.range := by
  refine ⟨fun hclosed ↦ ?_, fun hfin ↦ ?_⟩
  · by_contra hJ
    have hx : toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' (J ⁻¹' sphere (J x) r)) := by
      rw [J.closure_toWeakSpace_preimage_sphere hJ (J x) r]
      exact ⟨x, mem_closedBall_self hr.le, rfl⟩
    rw [hclosed.closure_eq] at hx
    obtain ⟨u, hu, hux⟩ := hx
    have heq : u = x := (toWeakSpace 𝕜 E).injective hux
    rw [mem_preimage, heq, mem_sphere_iff_norm, sub_self, norm_zero] at hu
    exact hr.ne hu
  · have hcont : Continuous (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) :=
      J.continuous_comp_toWeakSpace_symm_iff.2 hfin
    have hset : toWeakSpace 𝕜 E '' (J ⁻¹' sphere (J x) r) =
        (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) ⁻¹' sphere (J x) r := by
      ext w
      simp [(toWeakSpace 𝕜 E).image_eq_preimage_symm]
    rw [hset]
    exact isClosed_sphere.preimage hcont

/-- If `J : E →L[𝕜] F` has infinite-dimensional range, the weak closure of `{u | ‖J u‖ = r}` is
`{u | ‖J u‖ ≤ r}` for every real `r`. -/
theorem closure_toWeakSpace_setOf_norm_apply_eq (J : E →L[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 J.range) (r : ℝ) :
    closure (toWeakSpace 𝕜 E '' {u : E | ‖J u‖ = r}) =
      toWeakSpace 𝕜 E '' {u : E | ‖J u‖ ≤ r} := by
  have hs : J ⁻¹' sphere 0 r = {u : E | ‖J u‖ = r} := by ext u; simp
  have hb : J ⁻¹' closedBall 0 r = {u : E | ‖J u‖ ≤ r} := by ext u; simp
  simpa only [hs, hb] using J.closure_toWeakSpace_preimage_sphere hJ 0 r

/-- For `r > 0`, the level sphere `{u | ‖J u‖ = r}` is weakly closed if and only if `J` has
finite-dimensional range. -/
theorem isClosed_toWeakSpace_setOf_norm_apply_eq_iff (J : E →L[𝕜] F) {r : ℝ} (hr : 0 < r) :
    IsClosed (toWeakSpace 𝕜 E '' {u : E | ‖J u‖ = r}) ↔
      FiniteDimensional 𝕜 J.range := by
  have hs : J ⁻¹' sphere (J 0) r = {u : E | ‖J u‖ = r} := by ext u; simp
  simpa only [hs] using J.isClosed_toWeakSpace_preimage_sphere_iff 0 hr

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In an infinite-dimensional real or complex normed space, the weak closure of any sphere
`Metric.sphere x r` is the closed ball `Metric.closedBall x r`. -/
theorem closure_toWeakSpace_sphere (hE : ¬ FiniteDimensional 𝕜 E) (x : E) (r : ℝ) :
    closure (toWeakSpace 𝕜 E '' sphere x r) = toWeakSpace 𝕜 E '' closedBall x r := by
  have hrange : ¬ FiniteDimensional 𝕜 (ContinuousLinearMap.id 𝕜 E).range := by
    have hid : (ContinuousLinearMap.id 𝕜 E).range = ⊤ := LinearMap.range_id
    rw [hid]
    exact fun h ↦ hE (Submodule.topEquiv (R := 𝕜) (M := E)).finiteDimensional
  simpa only [ContinuousLinearMap.coe_id', preimage_id] using
    (ContinuousLinearMap.id 𝕜 E).closure_toWeakSpace_preimage_sphere hrange x r

/-- For `r > 0`, a sphere `Metric.sphere x r` in a real or complex normed space is weakly closed
if and only if the space is finite-dimensional. -/
theorem isClosed_toWeakSpace_sphere_iff (x : E) {r : ℝ} (hr : 0 < r) :
    IsClosed (toWeakSpace 𝕜 E '' sphere x r) ↔ FiniteDimensional 𝕜 E := by
  have h := (ContinuousLinearMap.id 𝕜 E).isClosed_toWeakSpace_preimage_sphere_iff x hr
  have hid : (ContinuousLinearMap.id 𝕜 E).range = ⊤ := LinearMap.range_id
  rw [hid] at h
  simpa only [ContinuousLinearMap.coe_id', preimage_id, id_eq] using
    h.trans ⟨fun _ ↦ (Submodule.topEquiv (R := 𝕜) (M := E)).finiteDimensional,
      fun _ ↦ (Submodule.topEquiv (R := 𝕜) (M := E)).symm.finiteDimensional⟩

end TauCeti

end WeakClosureOfSpheres
