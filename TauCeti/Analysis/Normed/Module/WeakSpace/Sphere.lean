/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Topology.Algebra.Module.WeakSpace
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Weak-to-norm continuity and weak closures of spheres

Using `LinearMap.exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace` (every weak
neighborhood of `x` contains an affine line `x + 𝕜 • v` along which an infinite-rank linear map
`J : E →ₗ[𝕜] F` is nonconstant, with `J v ≠ 0`) and
`TauCeti.exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero`, this file
establishes sharp characterizations of weak-to-norm continuity and weak closures of spheres in
infinite dimensions:

* Over a nontrivially normed field, `w ↦ J ((toWeakSpace 𝕜 E).symm w)` is discontinuous at every
  point whenever `J` has infinite-dimensional range
  (`LinearMap.not_continuousAt_comp_toWeakSpace_symm`). Over a nontrivially normed field with
  Hausdorff target weak topology, a continuous linear map `J : E →L[𝕜] F` is globally
  weak-to-norm continuous if and only if its range is finite-dimensional
  (`ContinuousLinearMap.continuous_comp_toWeakSpace_symm_iff`); in particular,
  `(toWeakSpace 𝕜 E).symm` is continuous if and only if `E` is finite-dimensional
  (`TauCeti.continuous_toWeakSpace_symm_iff`).
* Over `ℝ` or `ℂ`, every closed ball is weakly closed (`TauCeti.isClosed_toWeakSpace_closedBall`).
  For a continuous linear map `J : E →L[𝕜] F` into a normed space with infinite-dimensional range,
  the weak closure of the preimage of any sphere `J ⁻¹' sphere y r` is the preimage of the closed
  ball `J ⁻¹' closedBall y r` (`ContinuousLinearMap.closure_toWeakSpace_preimage_sphere`). In
  particular, the weak closure of `{u | ‖J u‖ = r}` is `{u | ‖J u‖ ≤ r}`
  (`ContinuousLinearMap.closure_toWeakSpace_setOf_norm_apply_eq`), the weak closure of a sphere
  `Metric.sphere x r` in an infinite-dimensional normed space is `Metric.closedBall x r`
  (`TauCeti.closure_toWeakSpace_sphere`), and for `r > 0`, preimages of spheres centered in the
  range (`J ⁻¹' sphere (J x) r`), level spheres `{u | ‖J u‖ = r}`, and spheres `Metric.sphere x r`
  are weakly closed if and only if the range (respectively the space) is finite-dimensional
  (`ContinuousLinearMap.isClosed_toWeakSpace_preimage_sphere_iff`,
  `ContinuousLinearMap.isClosed_toWeakSpace_setOf_norm_apply_eq_iff`,
  `TauCeti.isClosed_toWeakSpace_sphere_iff`).
* For any injective `LinearMapClass` map `j : G` from an infinite-dimensional topological vector
  space into a normed space over `ℝ` or `ℂ`, `0` lies in the weak closure of `{u | ‖j u‖ = r}` for
  `r ≥ 0` (`TauCeti.zero_mem_closure_toWeakSpace_setOf_norm_eq`), `{u | ‖j u‖ = r}` is not weakly
  closed for `r > 0` (`TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq`), and `j` is not
  weak-to-norm continuous (`TauCeti.not_continuous_comp_toWeakSpace_symm`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, §3.2, Proposition 3.5 and Example 1 (weak closure of the unit sphere).
* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.5.
-/

public section

open Filter Metric Set Topology

section Continuity

namespace LinearMap

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
  obtain ⟨v, hJv, hline⟩ := J.exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace hJ x hpre
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 (1 / ‖J v‖)
  have hlt : dist (J (x + k • v)) (J x) < 1 := by
    simpa [mem_preimage, mem_ball] using hline k
  rw [map_add, map_smul, dist_eq_norm, add_sub_cancel_left, norm_smul] at hlt
  have hgt : 1 < ‖k‖ * ‖J v‖ := (div_lt_iff₀ (norm_pos_iff.2 hJv)).1 hk
  exact hlt.not_gt hgt

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [T2Space (WeakSpace 𝕜 F)]

/-- Over a nontrivially normed field, a continuous linear map into a normed space with Hausdorff
weak topology is globally weak-to-norm continuous if and only if its range is
finite-dimensional. -/
theorem continuous_comp_toWeakSpace_symm_iff (J : E →L[𝕜] F) :
    Continuous (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) ↔
      FiniteDimensional 𝕜 J.range := by
  refine ⟨fun h ↦ ?_, fun hfin ↦ ?_⟩
  · by_contra hJ
    exact J.toLinearMap.not_continuousAt_comp_toWeakSpace_symm hJ 0 h.continuousAt
  · -- Deduce dual separation from `T2Space (WeakSpace 𝕜 F)`, extend basis coordinates on the
    -- finite-dimensional range to `StrongDual 𝕜 F`, and reconstruct `J` as a finite sum.
    have : SeparatingDual 𝕜 F := ⟨fun y hy ↦ by
      by_contra! h
      have hinsep : Inseparable (toWeakSpace 𝕜 F y) 0 := by
        have hind : IsInducing
            (fun (w : WeakSpace 𝕜 F) (f : StrongDual 𝕜 F) ↦ f ((toWeakSpace 𝕜 F).symm w)) :=
          ⟨rfl⟩
        rw [← hind.inseparable_iff]
        simp [h]
      exact hy ((toWeakSpace 𝕜 F).injective (by simpa using hinsep.eq))⟩
    have := hfin
    let b := Module.finBasis 𝕜 J.range
    have hsurj : Function.Surjective
        (J.range.subtype.dualMap ∘ ContinuousLinearMap.toLinearMap) :=
      SeparatingDual.dualMap_surjective_iff.2 Subtype.val_injective
    choose φ hφ using fun i ↦ hsurj (b.coord i)
    have hsum : (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) =
        fun w : WeakSpace 𝕜 E ↦
          ∑ i, ((φ i ∘L J) ((toWeakSpace 𝕜 E).symm w)) • (b i : F) := by
      ext w
      set x : E := (toWeakSpace 𝕜 E).symm w
      have hrepr := congrArg Subtype.val (b.sum_repr ⟨J x, LinearMap.mem_range_self _ x⟩)
      simp only [Submodule.coe_sum, SetLike.val_smul] at hrepr
      rw [← hrepr]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      exact (LinearMap.congr_fun (hφ i) ⟨J x, LinearMap.mem_range_self _ x⟩).symm
    rw [hsum]
    refine continuous_finsetSum _ fun i _ ↦ ?_
    have heval : Continuous (fun w : WeakSpace 𝕜 E ↦ (φ i ∘L J) ((toWeakSpace 𝕜 E).symm w)) :=
      WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (φ i ∘L J)
    exact heval.smul continuous_const

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [T2Space (WeakSpace 𝕜 E)]

/-- Over a nontrivially normed field, for a normed space with Hausdorff weak topology, the identity
from the weak topology to the norm topology is continuous if and only if the space is
finite-dimensional. -/
theorem continuous_toWeakSpace_symm_iff :
    Continuous (toWeakSpace 𝕜 E).symm ↔ FiniteDimensional 𝕜 E :=
  (ContinuousLinearMap.id 𝕜 E).continuous_comp_toWeakSpace_symm_iff.trans
    LinearMap.finite_range_id_iff

end TauCeti

end Continuity

section WeakClosureOfSpheres

namespace TauCeti

/-- Every closed ball in a real or complex seminormed space is weakly closed. -/
theorem isClosed_toWeakSpace_closedBall (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) (r : ℝ) :
    IsClosed (toWeakSpace 𝕜 E '' closedBall x r) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  exact isClosed_closedBall.isClosed_toWeakSpace_image_of_convex 𝕜 (convex_closedBall x r)

end TauCeti

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
  apply subset_antisymm
  · -- `J ⁻¹' closedBall y r` is the weak preimage of a weakly closed ball, hence weakly closed.
    have hclosed : IsClosed (toWeakSpace 𝕜 E '' (J ⁻¹' closedBall y r)) := by
      have heq : toWeakSpace 𝕜 E '' (J ⁻¹' closedBall y r) =
          WeakSpace.map J ⁻¹' (toWeakSpace 𝕜 F '' closedBall y r) := by
        ext w
        obtain ⟨x, rfl⟩ := (toWeakSpace 𝕜 E).surjective w
        -- `WeakSpace.map_apply` relies on `WeakSpace 𝕜 E = E` definitionally; keep explicit
        -- `toWeakSpace` casts so `rw` does not produce an ill-typed `J (toWeakSpace 𝕜 E x)`.
        have hmap : WeakSpace.map J (toWeakSpace 𝕜 E x) = toWeakSpace 𝕜 F (J x) :=
          WeakSpace.map_apply J x
        rw [(toWeakSpace 𝕜 E).injective.mem_set_image, mem_preimage, mem_preimage, hmap,
          (toWeakSpace 𝕜 F).injective.mem_set_image]
      rw [heq]
      exact (TauCeti.isClosed_toWeakSpace_closedBall 𝕜 y r).preimage (WeakSpace.map J).continuous
    exact closure_minimal (image_mono (preimage_mono sphere_subset_closedBall)) hclosed
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨v, hJv, hline⟩ :=
      J.toLinearMap.exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace hJ x hU
    let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
    have : IsScalarTower ℝ 𝕜 F := .restrictScalars ℝ 𝕜 F
    obtain ⟨t, -, ht⟩ := TauCeti.exists_dist_add_smul_eq (norm_ne_zero_iff.2 hJv) hx
    refine ⟨toWeakSpace 𝕜 E (x + (t : 𝕜) • v), hline (t : 𝕜), ⟨x + (t : 𝕜) • v, ?_, rfl⟩⟩
    simpa only [mem_preimage, mem_sphere, map_add, map_smul, ContinuousLinearMap.coe_coe,
      ← RCLike.algebraMap_eq_ofReal, algebraMap_smul] using ht

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
  · rw [(toWeakSpace 𝕜 E).image_eq_preimage_symm]
    exact isClosed_sphere.preimage (J.continuous_comp_toWeakSpace_symm_iff.2 hfin)

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
  simpa only [ContinuousLinearMap.coe_id', preimage_id] using
    (ContinuousLinearMap.id 𝕜 E).closure_toWeakSpace_preimage_sphere
      (mt LinearMap.finite_range_id_iff.1 hE) x r

/-- For `r > 0`, a sphere `Metric.sphere x r` in a real or complex normed space is weakly closed
if and only if the space is finite-dimensional. -/
theorem isClosed_toWeakSpace_sphere_iff (x : E) {r : ℝ} (hr : 0 < r) :
    IsClosed (toWeakSpace 𝕜 E '' sphere x r) ↔ FiniteDimensional 𝕜 E := by
  simpa only [ContinuousLinearMap.coe_id', preimage_id, id_eq] using
    ((ContinuousLinearMap.id 𝕜 E).isClosed_toWeakSpace_preimage_sphere_iff x hr).trans
      LinearMap.finite_range_id_iff

section Sphere

variable {𝕜 V F G : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FunLike G V F] [LinearMapClass G 𝕜 V F] {j : G}

/-- In an infinite-dimensional space, `0` lies in the weak closure of every sphere
`{u | ‖j u‖ = r}` of an injective linear map `j` into a normed space. -/
theorem zero_mem_closure_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) {r : ℝ} (hr : 0 ≤ r) :
    (0 : WeakSpace 𝕜 V) ∈ closure (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := by
  refine mem_closure_iff_nhds.2 fun U hU ↦ ?_
  obtain ⟨x, hx, hxU⟩ := exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero hV hU
  have hjx : ‖j x‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero_iff j hj).2 hx)
  -- Rescale `x` so that its image has norm `r`.
  refine ⟨_, hxU ((r / ‖j x‖ : ℝ) : 𝕜), mem_image_of_mem _ ?_⟩
  simp [map_smul, norm_smul, abs_of_nonneg hr, hjx]

/-- In an infinite-dimensional space, a sphere `{u | ‖j u‖ = r}` of positive radius of an
injective linear map `j` into a normed space is not weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := fun hclosed ↦ by
  obtain ⟨u, hu, hu0⟩ :=
    hclosed.closure_subset (zero_mem_closure_toWeakSpace_setOf_norm_eq hV hj hr.le)
  rw [map_eq_zero_iff _ (toWeakSpace 𝕜 V).injective] at hu0
  subst hu0
  simp only [mem_ofPred_eq, map_zero, norm_zero] at hu
  exact hr.ne hu

/-- In an infinite-dimensional space, an injective linear map into a normed space is not
continuous from the weak topology to the norm topology. -/
theorem not_continuous_comp_toWeakSpace_symm (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) :
    ¬ Continuous fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w) := fun hcont ↦ by
  refine not_isClosed_toWeakSpace_setOf_norm_eq hV hj one_pos ?_
  rw [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  exact isClosed_eq (continuous_norm.comp hcont) continuous_const

end Sphere

end TauCeti

end WeakClosureOfSpheres
