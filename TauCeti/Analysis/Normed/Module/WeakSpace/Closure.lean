/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Weak closures of balls, subspaces, and level spheres in infinite dimensions

By geometric Hahn–Banach (`Convex.isClosed_toWeakSpace`), closed balls and norm-closed subspaces of
a seminormed space over `ℝ` or `ℂ` remain closed in the weak topology
(`TauCeti.isClosed_toWeakSpace_closedBall`, `Submodule.isClosed_toWeakSpace_iff`).

Norm spheres and level sets `J ⁻¹' Metric.sphere y r` behave completely differently when `J` has
infinite-dimensional range. Every weak neighbourhood of a point in a topological vector space
contains a finite-codimensional affine subspace
(`TauCeti.exists_submodule_finiteDimensional_quotient_forall_toWeakSpace_add_mem_of_mem_nhds`), and
therefore an entire affine line in a direction not killed by `J` whenever `LinearMap.range J` is
infinite-dimensional
(`LinearMap.exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds`). In particular:

* every norm-bounded set in an infinite-dimensional normed space has empty weak interior
  (`TauCeti.interior_toWeakSpace_eq_empty_of_isBounded`);
* any continuous linear map `J : V →L[𝕜] F` with infinite-dimensional range into a normed space is
  discontinuous for the weak topology on `V` and the norm topology on `F` at every point
  (`ContinuousLinearMap.not_continuousAt_toWeakSpace_symm`, complementing global discontinuity in
  `TauCeti.Analysis.Normed.Module.WeakSpace.Sphere`);
* over `ℝ` or `ℂ`, for any continuous linear map `J : V →L[𝕜] F` with infinite-dimensional range,
  any center `y : F`, and any `r : ℝ`, the weak closure of `J ⁻¹' Metric.sphere y r` is
  `J ⁻¹' Metric.closedBall y r` (`ContinuousLinearMap.closure_toWeakSpace_preimage_sphere`,
  `ContinuousLinearMap.closure_toWeakSpace_setOf_norm_eq` for `{u | ‖J u‖ = r}`, and
  `TauCeti.closure_toWeakSpace_sphere` for `J = id`), so `J ⁻¹' Metric.sphere y r` is not weakly
  closed whenever `J ⁻¹' Metric.ball y r` is nonempty
  (`ContinuousLinearMap.not_isClosed_toWeakSpace_preimage_sphere`).

This shows that weak-to-norm continuity of a compact operator on bounded sets cannot hold globally
for any operator of infinite rank, and that norm sphere constraints are not weakly closed even when
they are weakly sequentially closed.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Section 3.3, Example 1 and Remark 3.
-/

public section

open Bornology Filter Metric Set Topology

namespace TauCeti

section ConvexClosed

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Closed balls in a seminormed space over `ℝ` or `ℂ` are closed in the weak topology. -/
theorem isClosed_toWeakSpace_closedBall (x : V) (r : ℝ) :
    IsClosed (toWeakSpace 𝕜 V '' closedBall x r) := by
  let : NormedSpace ℝ V := .restrictScalars ℝ 𝕜 V
  let : Module ℝ V := .restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := .restrictScalars ℝ 𝕜 V
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace
  exact (convex_closedBall x r).isClosed_toWeakSpace isClosed_closedBall

end ConvexClosed

section Submodule

/-- A submodule of a seminormed space over `ℝ` or `ℂ` is weakly closed if and only if it is closed
in the norm topology. -/
@[simp]
theorem _root_.Submodule.isClosed_toWeakSpace_iff {𝕜 V : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (L : Submodule 𝕜 V) :
    IsClosed (toWeakSpace 𝕜 V '' (L : Set V)) ↔ IsClosed (L : Set V) := by
  let : NormedSpace ℝ V := .restrictScalars ℝ 𝕜 V
  let : Module ℝ V := .restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := .restrictScalars ℝ 𝕜 V
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace
  exact (L.restrictScalars ℝ).convex.isClosed_toWeakSpace_iff

/-- A norm-closed submodule of a seminormed space over `ℝ` or `ℂ` is closed in the weak topology. -/
theorem _root_.Submodule.isClosed_toWeakSpace {𝕜 V : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (L : Submodule 𝕜 V)
    (hL : IsClosed (L : Set V)) :
    IsClosed (toWeakSpace 𝕜 V '' (L : Set V)) :=
  L.isClosed_toWeakSpace_iff.2 hL

end Submodule

section InfiniteDimensionalLines

/-- In an infinite-dimensional normed space over a nontrivially normed field, every norm-bounded set
has empty interior in the weak topology. -/
theorem interior_toWeakSpace_eq_empty_of_isBounded {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] (hV : ¬ FiniteDimensional 𝕜 V) {s : Set V}
    (hs : IsBounded s) :
    interior (toWeakSpace 𝕜 V '' s) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun w hw ↦ ?_
  obtain ⟨x, rfl⟩ := (toWeakSpace 𝕜 V).surjective w
  obtain ⟨v, hv, hline⟩ :=
    exists_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds hV (mem_interior_iff_mem_nhds.1 hw)
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall x).1 hs
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (R / ‖v‖)
  have hx_mem : x + c • v ∈ s := (toWeakSpace 𝕜 V).injective.mem_set_image.1 (hline c)
  have hdist : ‖c‖ * ‖v‖ ≤ R := by
    have h := mem_closedBall.1 (hR hx_mem)
    rwa [dist_eq_norm, add_sub_cancel_left, norm_smul] at h
  exact ((div_lt_iff₀ hv_pos).1 hc).not_ge hdist

end InfiniteDimensionalLines

end TauCeti

namespace ContinuousLinearMap

section GlobalDiscontinuity

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear map with infinite-dimensional range from a topological vector space into a
normed space is discontinuous at every point when the domain carries its weak topology and the
codomain carries its norm topology. -/
theorem not_continuousAt_toWeakSpace_symm (J : V →L[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 (LinearMap.range J.toLinearMap)) (x : V) :
    ¬ ContinuousAt (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V x) := by
  intro hc
  have hU : (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w)) ⁻¹' ball (J x) 1 ∈
      𝓝 (toWeakSpace 𝕜 V x) :=
    hc.preimage_mem_nhds (ball_mem_nhds _ one_pos)
  obtain ⟨v, hv, hline⟩ :=
    J.toLinearMap.exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds hJ hU
  have hJv : 0 < ‖J v‖ := norm_pos_iff.2 hv
  obtain ⟨c, hc_norm⟩ := NormedField.exists_lt_norm 𝕜 (1 / ‖J v‖)
  have hlt : ‖c‖ * ‖J v‖ < 1 := by
    have h : J (x + c • v) ∈ ball (J x) 1 := by
      simpa only [mem_preimage, LinearEquiv.symm_apply_apply] using hline c
    rw [mem_ball, dist_eq_norm, map_add, map_smul, add_sub_cancel_left, norm_smul] at h
    exact h
  exact ((div_lt_iff₀ hJv).1 hc_norm).not_ge hlt.le

end GlobalDiscontinuity

section WeakClosureSphere

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Weak closure of a level sphere.** For a continuous linear map `J : V →L[𝕜] F` with
infinite-dimensional range into a normed space over `ℝ` or `ℂ`, and for any center `y : F` and
radius `r : ℝ`, the weak closure of `J ⁻¹' Metric.sphere y r` is `J ⁻¹' Metric.closedBall y r`. -/
theorem closure_toWeakSpace_preimage_sphere (J : V →L[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 (LinearMap.range J.toLinearMap)) (y : F) (r : ℝ) :
    closure (toWeakSpace 𝕜 V '' (J ⁻¹' sphere y r)) =
      toWeakSpace 𝕜 V '' (J ⁻¹' closedBall y r) := by
  refine Subset.antisymm ?_ ?_
  · -- The sublevel ball is the weak preimage under `WeakSpace.map J` of the closed ball in `F`,
    -- which is weakly closed by geometric Hahn–Banach.
    have hpre : toWeakSpace 𝕜 V '' (J ⁻¹' closedBall y r) =
        WeakSpace.map J ⁻¹' (toWeakSpace 𝕜 F '' closedBall y r) := by
      -- `toWeakSpace` is `LinearEquiv.refl`, so `WeakSpace.map_apply` gives the commutation.
      have hcomp : (toWeakSpace 𝕜 F).symm ∘ WeakSpace.map J = J ∘ (toWeakSpace 𝕜 V).symm :=
        funext (WeakSpace.map_apply J)
      rw [(toWeakSpace 𝕜 V).image_eq_preimage_symm, (toWeakSpace 𝕜 F).image_eq_preimage_symm,
        ← preimage_comp, ← preimage_comp, hcomp]
    refine closure_minimal (image_mono (preimage_mono sphere_subset_closedBall)) ?_
    rw [hpre]
    exact (TauCeti.isClosed_toWeakSpace_closedBall y r).preimage (WeakSpace.map J).continuous
  · -- Every weak neighbourhood of `u` contains a real line `u + t • v` (`J v ≠ 0`), along which
    -- `t ↦ dist (J (u + t • v)) y` starts at `≤ r`, grows unboundedly, and hits `r` by IVT.
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨v, hv, hline⟩ :=
      J.toLinearMap.exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds hJ hU
    have hJv : 0 < ‖J v‖ := norm_pos_iff.2 hv
    let φ : ℝ → ℝ := fun t ↦ ‖(J u - y) + (t : 𝕜) • J v‖
    have hφ_cont : Continuous φ := by fun_prop
    have hφ0 : φ 0 ≤ r := by
      simpa only [φ, RCLike.ofReal_zero, zero_smul, add_zero, ← dist_eq_norm]
        using mem_closedBall.1 hu
    have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.1 hu)
    set T : ℝ := (r + ‖J u - y‖) / ‖J v‖
    have hT : 0 ≤ T := div_nonneg (add_nonneg hr (norm_nonneg _)) hJv.le
    have hT_norm : ‖(T : 𝕜) • J v‖ = r + ‖J u - y‖ := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hT, div_mul_cancel₀ _ hJv.ne']
    have hφT : r ≤ φ T := by
      have htri : ‖(T : 𝕜) • J v‖ ≤ φ T + ‖J u - y‖ := by
        simpa only [φ, add_sub_cancel_left] using
          norm_sub_le ((J u - y) + (T : 𝕜) • J v) (J u - y)
      linarith
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc hT hφ_cont.continuousOn ⟨hφ0, hφT⟩
    refine ⟨toWeakSpace 𝕜 V (u + (t : 𝕜) • v), hline (t : 𝕜), u + (t : 𝕜) • v, ?_, rfl⟩
    rw [mem_preimage, mem_sphere, dist_eq_norm, map_add, map_smul, add_sub_right_comm]
    exact ht

/-- For a continuous linear map `J : V →L[𝕜] F` with infinite-dimensional range into a normed space
over `ℝ` or `ℂ`, `J ⁻¹' Metric.sphere y r` is not weakly closed whenever `J ⁻¹' Metric.ball y r` is
nonempty. -/
theorem not_isClosed_toWeakSpace_preimage_sphere (J : V →L[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 (LinearMap.range J.toLinearMap)) {y : F} {r : ℝ}
    (hne : (J ⁻¹' ball y r).Nonempty) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' (J ⁻¹' sphere y r)) := by
  intro hclosed
  obtain ⟨u, hu⟩ := hne
  have hmem : toWeakSpace 𝕜 V u ∈ toWeakSpace 𝕜 V '' (J ⁻¹' sphere y r) := by
    rw [← hclosed.closure_eq, J.closure_toWeakSpace_preimage_sphere hJ y r]
    exact mem_image_of_mem _ (ball_subset_closedBall hu)
  have hu_sph : dist (J u) y = r :=
    mem_sphere.1 ((toWeakSpace 𝕜 V).injective.mem_set_image.1 hmem)
  exact (mem_ball.1 hu).ne hu_sph

/-- For a continuous linear map `J : V →L[𝕜] F` with infinite-dimensional range into a normed space
over `ℝ` or `ℂ`, and any `r : ℝ`, the weak closure of `{u : V | ‖J u‖ = r}` is
`{u : V | ‖J u‖ ≤ r}`. -/
theorem closure_toWeakSpace_setOf_norm_eq (J : V →L[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 (LinearMap.range J.toLinearMap)) (r : ℝ) :
    closure (toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r}) =
      toWeakSpace 𝕜 V '' {u : V | ‖J u‖ ≤ r} := by
  have hsphere : {u : V | ‖J u‖ = r} = J ⁻¹' sphere (0 : F) r := by
    ext u
    simp
  have hball : {u : V | ‖J u‖ ≤ r} = J ⁻¹' closedBall (0 : F) r := by
    ext u
    simp
  rw [hsphere, hball]
  exact J.closure_toWeakSpace_preimage_sphere hJ 0 r

end WeakClosureSphere

end ContinuousLinearMap

namespace TauCeti

section NormSphere

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Weak closure of the sphere.** In an infinite-dimensional normed space over `ℝ` or `ℂ`, the
weak closure of `Metric.sphere x r` is `Metric.closedBall x r` for every `x : V` and `r : ℝ`. -/
theorem closure_toWeakSpace_sphere (hV : ¬ FiniteDimensional 𝕜 V) (x : V) (r : ℝ) :
    closure (toWeakSpace 𝕜 V '' sphere x r) = toWeakSpace 𝕜 V '' closedBall x r := by
  have hid : ¬ FiniteDimensional 𝕜 (LinearMap.range (ContinuousLinearMap.id 𝕜 V).toLinearMap) := by
    rw [ContinuousLinearMap.coe_id, LinearMap.range_id]
    exact fun h ↦ hV (Module.Finite.equiv Submodule.topEquiv)
  simpa using (ContinuousLinearMap.id 𝕜 V).closure_toWeakSpace_preimage_sphere hid x r

/-- In an infinite-dimensional normed space over `ℝ` or `ℂ`, a sphere of positive radius is not
closed in the weak topology. -/
theorem not_isClosed_toWeakSpace_sphere (hV : ¬ FiniteDimensional 𝕜 V) (x : V) {r : ℝ}
    (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' sphere x r) := by
  have hid : ¬ FiniteDimensional 𝕜 (LinearMap.range (ContinuousLinearMap.id 𝕜 V).toLinearMap) := by
    rw [ContinuousLinearMap.coe_id, LinearMap.range_id]
    exact fun h ↦ hV (Module.Finite.equiv Submodule.topEquiv)
  simpa using (ContinuousLinearMap.id 𝕜 V).not_isClosed_toWeakSpace_preimage_sphere hid
    ⟨x, by simpa using hr⟩

end NormSphere

end TauCeti
