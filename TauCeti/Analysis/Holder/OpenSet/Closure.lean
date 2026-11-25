/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Basic
public import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Topology.MetricSpace.Holder

/-!
# Values on the closure of an element of `C^{k+1,α}(Ω)`

Let `Ω` be a convex open set of a real normed space `E` and `F` a Banach space. An element `f` of
`C^{k+1,α}(Ω, F)` has derivative bounded by its norm, so on the convex set `Ω` it is Lipschitz with
constant `‖f‖`. It is therefore uniformly continuous, and extends continuously to the closure of
`Ω`: its value at a point `x` of the closure is the limit of `f` along `Ω` at `x`, Mathlib's
`extendFrom Ω f`. These are the boundary values in boundary value problems on `Ω`.

This file defines that extension (`TauCeti.CkHolderSpaceOn.closureExtend`), shows that it agrees
with `f` on `Ω`, is the limit of `f` at the points of the closure, and is Lipschitz on the closure
with constant `‖f‖`, and records the value at a point of the closure as a continuous linear map of
norm at most one (`TauCeti.CkHolderSpaceOn.closureExtendL`). Some condition on `Ω` is needed: on a
slit annulus in the plane the angle function is in `C^{1,α}` but jumps across the slit, so it has
no limit at the points of the slit.

## Main declarations

* `TauCeti.CkHolderSpaceOn.closureExtend`: the extension of an element to the closure of `Ω`.
* `TauCeti.CkHolderSpaceOn.closureExtend_apply`: it agrees with the element on `Ω`.
* `TauCeti.CkHolderSpaceOn.tendsto_closureExtend`: at a point of the closure it is the limit of
  the element along `Ω`; `TauCeti.CkHolderSpaceOn.closureExtend_eq_of_continuousWithinAt`
  identifies it with any continuous representative.
* `TauCeti.CkHolderSpaceOn.lipschitzOnWith_closureExtend`: it is Lipschitz on the closure, with
  constant the norm of the element.
* `TauCeti.CkHolderSpaceOn.closureExtendL`: the value at a point of the closure, as a continuous
  linear map of norm at most one (`TauCeti.CkHolderSpaceOn.norm_closureExtendL_le_one`).
-/

public noncomputable section

open Filter Set TopologicalSpace Topology
open scoped NNReal

namespace TauCeti.CkHolderSpaceOn

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The extension of an element of `C^{k+1,α}(Ω)` to the closure of `Ω`: its value at a point is
the limit of the element along `Ω` there (`TauCeti.CkHolderSpaceOn.tendsto_closureExtend`). It
agrees with the element on `Ω`; outside the closure of `Ω` its values carry no meaning. -/
def closureExtend (f : CkHolderSpaceOn (k + 1) α Ω F) : E → F :=
  extendFrom (Ω : Set E) f.extend

theorem closureExtend_def (f : CkHolderSpaceOn (k + 1) α Ω F) :
    f.closureExtend = extendFrom (Ω : Set E) f.extend :=
  (rfl)

/-- The extension of `f` to the closure of `Ω` agrees with `f` on `Ω`. -/
@[simp]
theorem closureExtend_apply (f : CkHolderSpaceOn (k + 1) α Ω F) (x : Ω) :
    f.closureExtend x = f x := by
  rw [closureExtend_def, extendFrom_extends f.contDiffOn_extend.continuousOn x.val x.property,
    extend_apply]

/-- Near a point of `Ω`, the extension to the closure agrees with the extension by zero; so the
two have the same derivatives at the points of `Ω`. -/
theorem closureExtend_eventuallyEq_extend (f : CkHolderSpaceOn (k + 1) α Ω F) (x : Ω) :
    f.closureExtend =ᶠ[𝓝 (x : E)] f.extend := by
  filter_upwards [Ω.isOpen.mem_nhds x.property] with y hy
  rw [f.closureExtend_apply ⟨y, hy⟩, f.extend_apply ⟨y, hy⟩]

/-- At a point `x` of the closure of `Ω`, the extension to the closure takes the value at `x` of any
function that agrees with the element on `Ω` and is continuous within `Ω` at `x`. -/
theorem closureExtend_eq_of_continuousWithinAt (f : CkHolderSpaceOn (k + 1) α Ω F) {g : E → F}
    (hg : ∀ y : Ω, g y = f y) {x : E} (hx : x ∈ closure (Ω : Set E))
    (hgx : ContinuousWithinAt g Ω x) : f.closureExtend x = g x := by
  refine extendFrom_eq hx (hgx.tendsto.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [hg ⟨y, hy⟩, f.extend_apply ⟨y, hy⟩]

/-- On a convex set `Ω`, the extension by zero of an element of `C^{k+1,α}(Ω)` is Lipschitz on
`Ω`, with constant the norm of the element, which bounds its derivative. -/
theorem lipschitzOnWith_extend (f : CkHolderSpaceOn (k + 1) α Ω F) (hΩ : Convex ℝ (Ω : Set E)) :
    LipschitzOnWith ‖f‖₊ f.extend Ω := by
  refine hΩ.lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ) (fun x hx ↦ ?_) fun x hx ↦ ?_
  · exact (f.contDiffOn_extend.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt
      (by simp)
  · rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, ← norm_iteratedFDeriv_one]
    exact f.norm_iteratedFDeriv_extend_le (by omega) ⟨x, hx⟩

variable [CompleteSpace F]

/-- On a convex set `Ω`, the extension of an element of `C^{k+1,α}(Ω)` to the closure is the limit
of the element along `Ω` at every point of the closure. -/
theorem tendsto_closureExtend (f : CkHolderSpaceOn (k + 1) α Ω F) (hΩ : Convex ℝ (Ω : Set E))
    {x : E} (hx : x ∈ closure (Ω : Set E)) :
    Tendsto f.extend (𝓝[Ω] x) (𝓝 (f.closureExtend x)) := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  refine tendsto_extendFrom (CompleteSpace.complete ?_)
  exact (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le
    (f.lipschitzOnWith_extend hΩ).uniformContinuousOn inf_le_right

/-- On a convex set `Ω`, the extension of an element of `C^{k+1,α}(Ω)` to the closure is Lipschitz
on the closure, with constant the norm of the element. -/
theorem lipschitzOnWith_closureExtend (f : CkHolderSpaceOn (k + 1) α Ω F)
    (hΩ : Convex ℝ (Ω : Set E)) :
    LipschitzOnWith ‖f‖₊ f.closureExtend (closure (Ω : Set E)) := by
  have heq : EqOn f.closureExtend f.extend Ω := fun x hx ↦ by
    rw [f.closureExtend_apply ⟨x, hx⟩, f.extend_apply ⟨x, hx⟩]
  rw [← holderOnWith_one]
  exact (HolderOnWith.congr (holderOnWith_one.2 (f.lipschitzOnWith_extend hΩ))
    heq.symm).of_subset_closure
    subset_rfl fun x hx ↦ ((f.tendsto_closureExtend hΩ hx).congr' <|
      eventually_nhdsWithin_of_forall fun y hy ↦ (heq hy).symm)

/-- The extension of an element of `C^{k+1,α}(Ω)` to the closure of a convex `Ω` is continuous on
the closure. -/
theorem continuousOn_closureExtend (f : CkHolderSpaceOn (k + 1) α Ω F)
    (hΩ : Convex ℝ (Ω : Set E)) : ContinuousOn f.closureExtend (closure (Ω : Set E)) :=
  (f.lipschitzOnWith_closureExtend hΩ).continuousOn

/-- At a point of the closure of a convex `Ω`, the value of the extension is bounded by the
`C^{k+1,α}(Ω)` norm. -/
theorem norm_closureExtend_le (f : CkHolderSpaceOn (k + 1) α Ω F) (hΩ : Convex ℝ (Ω : Set E))
    {x : E} (hx : x ∈ closure (Ω : Set E)) : ‖f.closureExtend x‖ ≤ ‖f‖ := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  refine le_of_tendsto (f.tendsto_closureExtend hΩ hx).norm ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [f.extend_apply ⟨y, hy⟩]
  exact f.norm_apply_le _

/-- The extension to the closure of a convex `Ω` is additive at the points of the closure. -/
theorem closureExtend_add (f g : CkHolderSpaceOn (k + 1) α Ω F) (hΩ : Convex ℝ (Ω : Set E))
    {x : E} (hx : x ∈ closure (Ω : Set E)) :
    (f + g).closureExtend x = f.closureExtend x + g.closureExtend x := by
  refine extendFrom_eq hx (((f.tendsto_closureExtend hΩ hx).add
    (g.tendsto_closureExtend hΩ hx)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [f.extend_apply ⟨y, hy⟩, g.extend_apply ⟨y, hy⟩, (f + g).extend_apply ⟨y, hy⟩, coe_add,
    Pi.add_apply]

/-- The extension to the closure of a convex `Ω` commutes with scalar multiplication at the points
of the closure. -/
theorem closureExtend_smul (c : ℝ) (f : CkHolderSpaceOn (k + 1) α Ω F)
    (hΩ : Convex ℝ (Ω : Set E)) {x : E} (hx : x ∈ closure (Ω : Set E)) :
    (c • f).closureExtend x = c • f.closureExtend x := by
  refine extendFrom_eq hx (((f.tendsto_closureExtend hΩ hx).const_smul c).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [f.extend_apply ⟨y, hy⟩, (c • f).extend_apply ⟨y, hy⟩, coe_smul, Pi.smul_apply]

/-- The value at a point `x` of the closure of a convex `Ω` of the extension of an element of
`C^{k+1,α}(Ω)` to the closure, as a continuous linear map. -/
def closureExtendL (hΩ : Convex ℝ (Ω : Set E)) {x : E} (hx : x ∈ closure (Ω : Set E)) :
    CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun f := f.closureExtend x
      map_add' f g := closureExtend_add f g hΩ hx
      map_smul' c f := closureExtend_smul c f hΩ hx }
    1 fun f ↦ by simpa using f.norm_closureExtend_le hΩ hx

@[simp]
theorem closureExtendL_apply (hΩ : Convex ℝ (Ω : Set E)) {x : E} (hx : x ∈ closure (Ω : Set E))
    (f : CkHolderSpaceOn (k + 1) α Ω F) : closureExtendL hΩ hx f = f.closureExtend x :=
  (rfl)

/-- The value at a point of the closure has operator norm at most one. -/
theorem norm_closureExtendL_le_one (hΩ : Convex ℝ (Ω : Set E)) {x : E}
    (hx : x ∈ closure (Ω : Set E)) :
    ‖closureExtendL (k := k) (α := α) (F := F) hΩ hx‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end TauCeti.CkHolderSpaceOn
