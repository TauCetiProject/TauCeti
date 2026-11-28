/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Bounded linear maps characterised by limits

Let `e : X → Y` be an injective linear map from a seminormed space into a Hausdorff topological
module, and let `S i : V →ₗ[𝕜] Y` be linear maps on a seminormed space `V`. Suppose that for every
`v` the values `S i v` converge along a filter `l` to `e x` for some `x` with `‖x‖ ≤ C ‖v‖`. Then
`v ↦ x` is a continuous linear map `V →L[𝕜] X`
(`ContinuousLinearMap.ofTendstoOfInjective`): it is linear because limits are unique and `e` is
injective, and continuous by the bound.

This is how a map defined by a series, such as a sum of Littlewood–Paley blocks converging in
the tempered distributions, becomes a bounded operator into a normed space embedded in them.

## Main declarations

* `ContinuousLinearMap.ofTendstoOfInjective`: the continuous linear map `v ↦ x`.
* `ContinuousLinearMap.ofTendstoOfInjective_apply_eq_iff`: its value at `v` is the unique `x`
  with `S i v → e x`.
* `ContinuousLinearMap.norm_ofTendstoOfInjective_apply_le`: it satisfies `‖x‖ ≤ C ‖v‖`.
-/

public section

noncomputable section

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 V X Y G α : Type*} [Ring 𝕜] [SeminormedAddCommGroup V] [Module 𝕜 V]
  [SeminormedAddCommGroup X] [Module 𝕜 X] [AddCommMonoid Y] [Module 𝕜 Y] [TopologicalSpace Y]
  [T2Space Y] [ContinuousAdd Y] [ContinuousConstSMul 𝕜 Y] [FunLike G X Y]
  [LinearMapClass G 𝕜 X Y] (e : G) (he : Function.Injective e) {l : Filter α} [l.NeBot]
  (S : α → V →ₗ[𝕜] Y) {C : ℝ}
  (h : ∀ v, ∃ x : X, Tendsto (fun i ↦ S i v) l (𝓝 (e x)) ∧ ‖x‖ ≤ C * ‖v‖)

/-- A map from a seminormed space `V` to a seminormed space `X`, embedded injectively and linearly
in a Hausdorff topological module by `e`, characterised by `S i v → e x` along `l` for linear maps
`S i` and bounded by `‖x‖ ≤ C ‖v‖`, is a continuous linear map. -/
def ofTendstoOfInjective : V →L[𝕜] X :=
  have key (v : V) : Tendsto (fun i ↦ S i v) l (𝓝 (e (h v).choose)) := (h v).choose_spec.1
  LinearMap.mkContinuous
    { toFun v := (h v).choose
      map_add' u v := he <| tendsto_nhds_unique (key (u + v)) <| by
        simpa only [map_add] using (key u).add (key v)
      map_smul' c v := he <| tendsto_nhds_unique (key (c • v)) <| by
        simpa only [map_smul, RingHom.id_apply] using (key v).const_smul c }
    C fun v ↦ (h v).choose_spec.2

/-- The values `S i v` converge to `e` of `ofTendstoOfInjective e he S h v`. -/
theorem tendsto_ofTendstoOfInjective (v : V) :
    Tendsto (fun i ↦ S i v) l (𝓝 (e (ofTendstoOfInjective e he S h v))) :=
  (h v).choose_spec.1

/-- The value of `ofTendstoOfInjective e he S h` at `v` is the unique `x` with `S i v → e x`. -/
theorem ofTendstoOfInjective_apply_eq_iff {v : V} {x : X} :
    ofTendstoOfInjective e he S h v = x ↔ Tendsto (fun i ↦ S i v) l (𝓝 (e x)) :=
  ⟨fun hx ↦ hx ▸ tendsto_ofTendstoOfInjective e he S h v,
    fun hx ↦ he <| tendsto_nhds_unique (tendsto_ofTendstoOfInjective e he S h v) hx⟩

/-- `ofTendstoOfInjective e he S h` satisfies the bound `‖x‖ ≤ C ‖v‖` it was built from. -/
theorem norm_ofTendstoOfInjective_apply_le (v : V) :
    ‖ofTendstoOfInjective e he S h v‖ ≤ C * ‖v‖ :=
  (h v).choose_spec.2

end ContinuousLinearMap
