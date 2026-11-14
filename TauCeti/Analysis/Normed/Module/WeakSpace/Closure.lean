/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.LocallyConvex.WeakSpace
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Weak closures of balls, subspaces, and level spheres in infinite dimensions

By geometric Hahn–Banach (`Convex.isClosed_toWeakSpace`), closed balls and norm-closed subspaces of
a seminormed space over `ℝ` or `ℂ` remain closed in the weak topology
(`TauCeti.isClosed_toWeakSpace_closedBall`, `Submodule.isClosed_toWeakSpace`).

Norm spheres and level sets `{u : V | ‖J u‖ = r}` behave completely differently when `V` is
infinite-dimensional. Every weak neighbourhood of a point in an infinite-dimensional vector space
is defined by finitely many continuous linear functionals, whose common kernel is nontrivial, so
every weak neighbourhood contains an entire affine line
(`TauCeti.exists_ne_zero_forall_add_smul_mem_of_mem_nhds`). In particular:

* every norm-bounded set in an infinite-dimensional normed space has empty weak interior
  (`TauCeti.interior_toWeakSpace_eq_empty_of_isBounded`);
* for any injective continuous linear map `J : V →L[𝕜] F` into a normed space, `J` is discontinuous
  for the weak topology on `V` and the norm topology on `F` at every point
  (`ContinuousLinearMap.not_continuousAt_toWeakSpace_symm`,
  `ContinuousLinearMap.not_continuous_toWeakSpace_symm`);
* over `ℝ` or `ℂ`, the weak closure of the level sphere `J ⁻¹' Metric.sphere (J x) r` (`0 ≤ r`) is
  the entire sublevel ball `J ⁻¹' Metric.closedBall (J x) r`
  (`ContinuousLinearMap.closure_toWeakSpace_preimage_sphere`, and
  `TauCeti.closure_toWeakSpace_sphere` for `J = id`), so `{u : V | ‖J u‖ = r}` contains `0` in its
  weak closure and is never weakly closed for `0 < r`
  (`ContinuousLinearMap.not_isClosed_toWeakSpace_setOf_norm_eq`).

This shows that weak-to-norm continuity of a compact operator on bounded sets cannot hold globally
on an infinite-dimensional domain, even when the operator is compact and injective, and that norm
sphere constraints are not weakly closed even when they are weakly sequentially closed.

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

/-- A norm-closed submodule of a seminormed space over `ℝ` or `ℂ` is closed in the weak topology. -/
theorem _root_.Submodule.isClosed_toWeakSpace {𝕜 V : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (L : Submodule 𝕜 V)
    (hL : IsClosed (L : Set V)) :
    IsClosed (toWeakSpace 𝕜 V '' (L : Set V)) := by
  let : NormedSpace ℝ V := .restrictScalars ℝ 𝕜 V
  let : Module ℝ V := .restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := .restrictScalars ℝ 𝕜 V
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace
  exact (L.restrictScalars ℝ).convex.isClosed_toWeakSpace hL

/-- A submodule of a seminormed space over `ℝ` or `ℂ` is weakly closed if and only if it is closed
in the norm topology. -/
theorem _root_.Submodule.isClosed_toWeakSpace_iff {𝕜 V : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (L : Submodule 𝕜 V) :
    IsClosed (toWeakSpace 𝕜 V '' (L : Set V)) ↔ IsClosed (L : Set V) := by
  let : NormedSpace ℝ V := .restrictScalars ℝ 𝕜 V
  let : Module ℝ V := .restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := .restrictScalars ℝ 𝕜 V
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace
  exact (L.restrictScalars ℝ).convex.isClosed_toWeakSpace_iff

end Submodule

section InfiniteDimensionalLines

/-- **Affine lines in weak neighbourhoods.** Every neighbourhood of `toWeakSpace 𝕜 E x` in an
infinite-dimensional topological vector space contains the entire affine line
`{toWeakSpace 𝕜 E (x + c • v) | c : 𝕜}` in some nonzero direction `v`. -/
theorem exists_ne_zero_forall_add_smul_mem_of_mem_nhds {𝕜 E : Type*} [Field 𝕜]
    [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) {x : E} {U : Set (WeakSpace 𝕜 E)}
    (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ v : E, v ≠ 0 ∧ ∀ c : 𝕜, toWeakSpace 𝕜 E (x + c • v) ∈ U := by
  let eval : E → StrongDual 𝕜 E → 𝕜 := fun y f ↦ f y
  have htend : Tendsto (toWeakSpace 𝕜 E) (comap eval (𝓝 (eval x))) (𝓝 (toWeakSpace 𝕜 E x)) :=
    tendsto_toWeakSpace_iff_forall_eval_tendsto.2 fun f ↦
      ((continuous_apply f).tendsto (eval x)).comp tendsto_comap
  obtain ⟨W, hW, hWU⟩ := mem_comap.1 (htend hU)
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hIW⟩ := hW
  -- Finitely many linear functionals on an infinite-dimensional space have a nontrivial common
  -- kernel, since otherwise `E` would embed into `I → 𝕜`.
  let Φ : E →ₗ[𝕜] (I → 𝕜) := LinearMap.pi fun i : I ↦ (i : StrongDual 𝕜 E).toLinearMap
  have hker : LinearMap.ker Φ ≠ ⊥ := fun hbot ↦
    hE (FiniteDimensional.of_injective Φ (LinearMap.ker_eq_bot.1 hbot))
  obtain ⟨v, hv_ker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hv0, fun c ↦ ?_⟩
  have hmem : eval (x + c • v) ∈ W := hIW fun f hf ↦ by
    have hfv : f v = 0 := congrFun (LinearMap.mem_ker.1 hv_ker) ⟨f, hf⟩
    simpa only [eval, map_add, map_smul, smul_eq_mul, hfv, mul_zero, add_zero] using
      mem_of_mem_nhds (ht f)
  exact hWU hmem

/-- In an infinite-dimensional normed space over a nontrivially normed field, every norm-bounded set
has empty interior in the weak topology. -/
theorem interior_toWeakSpace_eq_empty_of_isBounded {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] (hV : ¬ FiniteDimensional 𝕜 V) {s : Set V}
    (hs : IsBounded s) :
    interior (toWeakSpace 𝕜 V '' s) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun w hw ↦ ?_
  obtain ⟨x, rfl⟩ := (toWeakSpace 𝕜 V).surjective w
  obtain ⟨v, hv, hline⟩ :=
    exists_ne_zero_forall_add_smul_mem_of_mem_nhds hV (mem_interior_iff_mem_nhds.1 hw)
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

/-- An injective continuous linear map on an infinite-dimensional topological vector space into a
normed space is discontinuous at every point when the domain carries its weak topology and the
codomain carries its norm topology. -/
theorem not_continuousAt_toWeakSpace_symm (hV : ¬ FiniteDimensional 𝕜 V) (J : V →L[𝕜] F)
    (hJ : Function.Injective J) (x : V) :
    ¬ ContinuousAt (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V x) := by
  intro hc
  have hU : (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w)) ⁻¹' ball (J x) 1 ∈
      𝓝 (toWeakSpace 𝕜 V x) :=
    hc.preimage_mem_nhds (ball_mem_nhds _ one_pos)
  obtain ⟨v, hv, hline⟩ := TauCeti.exists_ne_zero_forall_add_smul_mem_of_mem_nhds hV hU
  have hJv : 0 < ‖J v‖ := norm_pos_iff.2 (map_ne_zero_iff J hJ |>.2 hv)
  obtain ⟨c, hc_norm⟩ := NormedField.exists_lt_norm 𝕜 (1 / ‖J v‖)
  have hlt : ‖c‖ * ‖J v‖ < 1 := by
    have h : J (x + c • v) ∈ ball (J x) 1 := by
      simpa only [mem_preimage, LinearEquiv.symm_apply_apply] using hline c
    rw [mem_ball, dist_eq_norm, map_add, map_smul, add_sub_cancel_left, norm_smul] at h
    exact h
  exact ((div_lt_iff₀ hJv).1 hc_norm).not_ge hlt.le

/-- An injective continuous linear map on an infinite-dimensional topological vector space into a
normed space is never globally continuous from the weak topology to the norm topology. -/
theorem not_continuous_toWeakSpace_symm (hV : ¬ FiniteDimensional 𝕜 V) (J : V →L[𝕜] F)
    (hJ : Function.Injective J) :
    ¬ Continuous (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w)) :=
  fun hc ↦ J.not_continuousAt_toWeakSpace_symm hV hJ 0 hc.continuousAt

end GlobalDiscontinuity

section WeakClosureSphere

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Weak closure of a level sphere.** For an injective continuous linear map `J : V →L[𝕜] F` on an
infinite-dimensional vector space into a normed space over `ℝ` or `ℂ`, the weak closure of
`J ⁻¹' Metric.sphere (J x) r` (`0 ≤ r`) is the entire sublevel ball
`J ⁻¹' Metric.closedBall (J x) r`. -/
theorem closure_toWeakSpace_preimage_sphere (hV : ¬ FiniteDimensional 𝕜 V) (J : V →L[𝕜] F)
    (hJ : Function.Injective J) (x : V) {r : ℝ} (hr : 0 ≤ r) :
    closure (toWeakSpace 𝕜 V '' (J ⁻¹' sphere (J x) r)) =
      toWeakSpace 𝕜 V '' (J ⁻¹' closedBall (J x) r) := by
  refine Subset.antisymm ?_ ?_
  · -- The sublevel ball is the weak preimage under `WeakSpace.map J` of the closed ball in `F`,
    -- which is weakly closed by geometric Hahn–Banach.
    have hpre : toWeakSpace 𝕜 V '' (J ⁻¹' closedBall (J x) r) =
        WeakSpace.map J ⁻¹' (toWeakSpace 𝕜 F '' closedBall (J x) r) := by
      ext w
      simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm,
        (toWeakSpace 𝕜 F).image_eq_preimage_symm, mem_preimage, WeakSpace.toWeakSpace_symm_map]
    refine closure_minimal (image_mono (preimage_mono sphere_subset_closedBall)) ?_
    rw [hpre]
    exact (TauCeti.isClosed_toWeakSpace_closedBall (J x) r).preimage (WeakSpace.map J).continuous
  · -- Every weak neighbourhood of `u` contains a real line `u + t • v` (`v ≠ 0`), along which
    -- `t ↦ dist (J (u + t • v)) (J x)` starts at `≤ r`, grows unboundedly, and hits `r` by IVT.
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨v, hv, hline⟩ := TauCeti.exists_ne_zero_forall_add_smul_mem_of_mem_nhds hV hU
    have hJv : 0 < ‖J v‖ := norm_pos_iff.2 (map_ne_zero_iff J hJ |>.2 hv)
    let φ : ℝ → ℝ := fun t ↦ ‖(J u - J x) + (t : 𝕜) • J v‖
    have hφ_cont : Continuous φ := by fun_prop
    have hφ0 : φ 0 ≤ r := by
      simpa only [φ, RCLike.ofReal_zero, zero_smul, add_zero, ← dist_eq_norm]
        using mem_closedBall.1 hu
    set T : ℝ := (r + ‖J u - J x‖) / ‖J v‖
    have hT : 0 ≤ T := div_nonneg (add_nonneg hr (norm_nonneg _)) hJv.le
    have hT_norm : ‖(T : 𝕜) • J v‖ = r + ‖J u - J x‖ := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hT, div_mul_cancel₀ _ hJv.ne']
    have hφT : r ≤ φ T := by
      have htri : ‖(T : 𝕜) • J v‖ ≤ φ T + ‖J u - J x‖ := by
        simpa only [φ, add_sub_cancel_left] using
          norm_sub_le ((J u - J x) + (T : 𝕜) • J v) (J u - J x)
      linarith
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc hT hφ_cont.continuousOn ⟨hφ0, hφT⟩
    refine ⟨toWeakSpace 𝕜 V (u + (t : 𝕜) • v), hline (t : 𝕜), u + (t : 𝕜) • v, ?_, rfl⟩
    rw [mem_preimage, mem_sphere, dist_eq_norm, map_add, map_smul, add_sub_right_comm]
    exact ht

/-- For an injective continuous linear map `J : V →L[𝕜] F` on an infinite-dimensional vector space
into a normed space over `ℝ` or `ℂ`, the weak closure of `{u : V | ‖J u‖ = r}` (`0 ≤ r`) is
`{u : V | ‖J u‖ ≤ r}`. -/
theorem closure_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V) (J : V →L[𝕜] F)
    (hJ : Function.Injective J) {r : ℝ} (hr : 0 ≤ r) :
    closure (toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r}) =
      toWeakSpace 𝕜 V '' {u : V | ‖J u‖ ≤ r} := by
  have hsphere : {u : V | ‖J u‖ = r} = J ⁻¹' sphere (J 0) r := by
    ext u
    simp
  have hball : {u : V | ‖J u‖ ≤ r} = J ⁻¹' closedBall (J 0) r := by
    ext u
    simp
  rw [hsphere, hball]
  exact J.closure_toWeakSpace_preimage_sphere hV hJ 0 hr

/-- For an injective continuous linear map `J : V →L[𝕜] F` on an infinite-dimensional vector space
into a normed space over `ℝ` or `ℂ`, `0` belongs to the weak closure of `{u : V | ‖J u‖ = r}` for
every `0 ≤ r`. -/
theorem mem_closure_toWeakSpace_setOf_norm_eq_zero (hV : ¬ FiniteDimensional 𝕜 V) (J : V →L[𝕜] F)
    (hJ : Function.Injective J) {r : ℝ} (hr : 0 ≤ r) :
    toWeakSpace 𝕜 V 0 ∈ closure (toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r}) := by
  rw [J.closure_toWeakSpace_setOf_norm_eq hV hJ hr]
  exact ⟨0, by simpa only [mem_ofPred_eq, map_zero, norm_zero] using hr, rfl⟩

/-- For `0 < r` and an injective continuous linear map `J : V →L[𝕜] F` on an infinite-dimensional
vector space into a normed space over `ℝ` or `ℂ`, `{u : V | ‖J u‖ = r}` is not weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V) (J : V →L[𝕜] F)
    (hJ : Function.Injective J) {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r}) := by
  intro hclosed
  have h0 : toWeakSpace 𝕜 V 0 ∈ toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r} :=
    hclosed.closure_eq ▸ J.mem_closure_toWeakSpace_setOf_norm_eq_zero hV hJ hr.le
  have hnorm : (0 : V) ∈ {u : V | ‖J u‖ = r} := (toWeakSpace 𝕜 V).injective.mem_set_image.1 h0
  simp only [mem_ofPred_eq, map_zero, norm_zero] at hnorm
  exact hr.ne hnorm

end WeakClosureSphere

end ContinuousLinearMap

namespace TauCeti

section NormSphere

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Weak closure of the sphere.** In an infinite-dimensional normed space over `ℝ` or `ℂ`, the
weak closure of `Metric.sphere x r` (`0 ≤ r`) is `Metric.closedBall x r`. -/
theorem closure_toWeakSpace_sphere (hV : ¬ FiniteDimensional 𝕜 V) (x : V) {r : ℝ} (hr : 0 ≤ r) :
    closure (toWeakSpace 𝕜 V '' sphere x r) = toWeakSpace 𝕜 V '' closedBall x r := by
  simpa using (ContinuousLinearMap.id 𝕜 V).closure_toWeakSpace_preimage_sphere
    hV Function.injective_id x hr

/-- In an infinite-dimensional normed space over `ℝ` or `ℂ`, a sphere of positive radius is not
closed in the weak topology. -/
theorem not_isClosed_toWeakSpace_sphere (hV : ¬ FiniteDimensional 𝕜 V) (x : V) {r : ℝ}
    (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' sphere x r) := by
  intro hclosed
  have hmem : toWeakSpace 𝕜 V x ∈ toWeakSpace 𝕜 V '' sphere x r := by
    rw [← hclosed.closure_eq, closure_toWeakSpace_sphere hV x hr.le]
    exact mem_image_of_mem _ (mem_closedBall_self hr.le)
  have hx : x ∈ sphere x r := (toWeakSpace 𝕜 V).injective.mem_set_image.1 hmem
  exact hr.ne (by simpa using hx)

end NormSphere

end TauCeti
