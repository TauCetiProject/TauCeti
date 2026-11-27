/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Basic
public import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.IntervalCases
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# Values on the closure of elements of `C^{k+1,α}(Ω)`

An element of `C^{k,α}(Ω)` is a function on the open set `Ω` only. On a convex open set and from
order one on, its derivative is bounded by its norm, so by the mean value theorem it is Lipschitz
on `Ω` with constant its norm, and with values in a Banach space it converges at each point of
the closure of `Ω`. This file names the resulting extension to the closure, the limit of the
element along `Ω` (Mathlib's `extendFrom`), and packages the value at a point of the closure as a
continuous linear functional of norm at most one. These boundary values are how boundary
conditions are imposed on elements of `C^{k+1,α}(Ω)`, for instance totally real boundary
conditions for the Cauchy–Riemann operator on the disc.

Conversely, a function that is differentiable on an open `Ω` with compact closure, whose value and
derivative extend continuously to the closure and whose derivative is `α`-Hölder on `Ω`, defines
an element of `C^{1,α}(Ω)`, for every exponent `α`
(`TauCeti.exists_ckHolderSpaceOn_one_of_isCompact_closure`).

## Main declarations

* `TauCeti.CkHolderSpaceOn.closureExtend`: the extension `extendFrom Ω f` of an element to `E`; it
  agrees with the element on `Ω` (`TauCeti.CkHolderSpaceOn.closureExtend_apply`), and the zero
  element extends by zero (`TauCeti.CkHolderSpaceOn.closureExtend_zero`).
* `TauCeti.CkHolderSpaceOn.closureExtend_eq_of_continuousWithinAt`: it is the value at the point
  of any function agreeing with the element on `Ω` and continuous within `Ω` there.
* `TauCeti.CkHolderSpaceOn.differentiableOn_closureExtend`: from order one on, the extension to the
  closure is differentiable on `Ω`.
* `TauCeti.CkHolderSpaceOn.lipschitzOnWith_extend`: on a convex open set an element of
  `C^{k+1,α}(Ω)` is Lipschitz on `Ω` with constant its norm.
* `TauCeti.CkHolderSpaceOn.tendsto_closureExtend`,
  `TauCeti.CkHolderSpaceOn.lipschitzOnWith_closureExtend`: the element converges at each point of
  the closure to its extension, which is Lipschitz on the closure with the same constant.
* `TauCeti.CkHolderSpaceOn.closureEvalL`: the value of the extension at a point of the closure,
  as a continuous linear functional on `C^{k+1,α}(Ω)` of norm at most one.
* `TauCeti.exists_ckHolderSpaceOn_one_of_isCompact_closure`: an element of `C^{1,α}(Ω)` from a
  function differentiable on `Ω` whose value and derivative are continuous on the compact closure,
  with derivative `α`-Hölder on `Ω`. Unlike
  `TauCeti.CkHolderSpaceOn.exists_apply_eq_of_differentiableOn_of_holderOnWith`, it also covers
  the exponent `α = 0`.
-/

public section

noncomputable section

namespace TauCeti.CkHolderSpaceOn

open Filter TopologicalSpace Topology
open scoped NNReal

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The extension of an element of `C^{k,α}(Ω)` to `E` by its limits along `Ω`
(Mathlib's `extendFrom`). It agrees with the element on `Ω`; on a convex open set, from order one
on and for complete values, it is the continuous extension of the element to the closure of `Ω`
(`TauCeti.CkHolderSpaceOn.lipschitzOnWith_closureExtend`). -/
def closureExtend (f : CkHolderSpaceOn k α Ω F) : E → F :=
  extendFrom Ω f.extend

/-- The defining formula for `closureExtend`. -/
theorem closureExtend_def (f : CkHolderSpaceOn k α Ω F) :
    f.closureExtend = extendFrom Ω f.extend :=
  (rfl)

/-- The extension to the closure agrees with the element on `Ω`. -/
@[simp]
theorem closureExtend_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    f.closureExtend x = f x := by
  rw [closureExtend, extendFrom_extends f.contDiffOn_extend.continuousOn x x.property,
    extend_apply]

/-- The extension to the closure agrees with the extension by zero near each point of `Ω`. -/
theorem closureExtend_eventuallyEq_extend (f : CkHolderSpaceOn k α Ω F) {x : E} (hx : x ∈ Ω) :
    f.closureExtend =ᶠ[𝓝 x] f.extend := by
  filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
  exact (f.closureExtend_apply ⟨y, hy⟩).trans (f.extend_apply_of_mem hy).symm

/-- **Elements of `C^{k+1,α}(Ω)` are Lipschitz.** On a convex open set, an element of
`C^{k+1,α}(Ω)` is Lipschitz on `Ω` with constant its norm, which bounds its derivative. -/
theorem lipschitzOnWith_extend (hΩ : Convex ℝ (Ω : Set E)) (f : CkHolderSpaceOn (k + 1) α Ω F) :
    LipschitzOnWith ‖f‖₊ f.extend Ω := by
  refine hΩ.lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ) (fun x hx ↦ ?_) fun x hx ↦ ?_
  · exact f.differentiableAt_extend hx
  · rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact f.norm_iteratedFDeriv_extend_le (i := 1) (by omega) ⟨x, hx⟩

/-- From order one on, the extension to the closure is differentiable on `Ω`. -/
theorem differentiableOn_closureExtend (f : CkHolderSpaceOn (k + 1) α Ω F) :
    DifferentiableOn ℝ f.closureExtend Ω := fun _ hx ↦
  ((f.differentiableAt_extend hx).congr_of_eventuallyEq
    (f.closureExtend_eventuallyEq_extend hx)).differentiableWithinAt

/-- **Uniqueness of the extension to the closure.** At a point of the closure of `Ω`, the
extension to the closure takes the value of any function that agrees with the element on `Ω` and
is continuous within `Ω` at that point. -/
theorem closureExtend_eq_of_continuousWithinAt (f : CkHolderSpaceOn k α Ω F) {g : E → F}
    (hfg : ∀ x : Ω, f x = g x) {x : E} (hx : x ∈ closure (Ω : Set E))
    (hg : ContinuousWithinAt g Ω x) : f.closureExtend x = g x := by
  refine extendFrom_eq hx (hg.tendsto.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [f.extend_apply_of_mem hy, hfg]

/-- The extension of the zero element of `C^{k,α}(Ω)` vanishes on the closure of `Ω`. -/
@[simp]
theorem closureExtend_zero {x : E} (hx : x ∈ closure (Ω : Set E)) :
    (0 : CkHolderSpaceOn k α Ω F).closureExtend x = 0 := by
  refine extendFrom_eq hx (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [extend_apply _ ⟨y, hy⟩, coe_zero, Pi.zero_apply]

variable [CompleteSpace F]

/-- On a convex open set, an element of `C^{k+1,α}(Ω)` with complete values converges along `Ω`
at each point of the closure of `Ω`, to the value of its extension to the closure. -/
theorem tendsto_closureExtend (hΩ : Convex ℝ (Ω : Set E)) (f : CkHolderSpaceOn (k + 1) α Ω F)
    {x : E} (hx : x ∈ closure (Ω : Set E)) :
    Tendsto f.extend (𝓝[Ω] x) (𝓝 (f.closureExtend x)) :=
  HolderOnWith.tendsto_extendFrom (C := ‖f‖₊) (r := 1)
    (f.lipschitzOnWith_extend hΩ).holderOnWith one_pos hx

/-- On a convex open set, the extension to the closure of an element of `C^{k+1,α}(Ω)` with
complete values is Lipschitz on the closure of `Ω`, with constant the norm of the element. -/
theorem lipschitzOnWith_closureExtend (hΩ : Convex ℝ (Ω : Set E))
    (f : CkHolderSpaceOn (k + 1) α Ω F) :
    LipschitzOnWith ‖f‖₊ f.closureExtend (closure Ω) :=
  holderOnWith_one.1 (HolderOnWith.extendFrom_closure (C := ‖f‖₊) (r := 1)
    (f.lipschitzOnWith_extend hΩ).holderOnWith one_pos).2

/-- On a convex open set, the extension to the closure of an element of `C^{k+1,α}(Ω)` with
complete values is continuous on the closure of `Ω`. -/
theorem continuousOn_closureExtend (hΩ : Convex ℝ (Ω : Set E))
    (f : CkHolderSpaceOn (k + 1) α Ω F) :
    ContinuousOn f.closureExtend (closure Ω) :=
  (f.lipschitzOnWith_closureExtend hΩ).continuousOn

/-- The values of the extension to the closure are bounded by the norm of the element. -/
theorem norm_closureExtend_le (hΩ : Convex ℝ (Ω : Set E)) (f : CkHolderSpaceOn (k + 1) α Ω F)
    {x : E} (hx : x ∈ closure (Ω : Set E)) : ‖f.closureExtend x‖ ≤ ‖f‖ := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  refine le_of_tendsto (f.tendsto_closureExtend hΩ hx).norm
    (eventually_nhdsWithin_of_forall fun y hy ↦ ?_)
  rw [f.extend_apply_of_mem hy]
  exact f.norm_apply_le _

/-- The extension to the closure is additive. -/
theorem closureExtend_add (hΩ : Convex ℝ (Ω : Set E)) (f g : CkHolderSpaceOn (k + 1) α Ω F)
    {x : E} (hx : x ∈ closure (Ω : Set E)) :
    (f + g).closureExtend x = f.closureExtend x + g.closureExtend x := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  refine tendsto_nhds_unique ((f + g).tendsto_closureExtend hΩ hx) ?_
  refine ((f.tendsto_closureExtend hΩ hx).add (g.tendsto_closureExtend hΩ hx)).congr'
    (eventually_nhdsWithin_of_forall fun y hy ↦ ?_)
  rw [(f + g).extend_apply_of_mem hy, f.extend_apply_of_mem hy, g.extend_apply_of_mem hy,
    coe_add, Pi.add_apply]

/-- The extension to the closure commutes with real scalar multiplication. -/
theorem closureExtend_smul (hΩ : Convex ℝ (Ω : Set E)) (c : ℝ) (f : CkHolderSpaceOn (k + 1) α Ω F)
    {x : E} (hx : x ∈ closure (Ω : Set E)) :
    (c • f).closureExtend x = c • f.closureExtend x := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  refine tendsto_nhds_unique ((c • f).tendsto_closureExtend hΩ hx) ?_
  refine ((f.tendsto_closureExtend hΩ hx).const_smul c).congr'
    (eventually_nhdsWithin_of_forall fun y hy ↦ ?_)
  rw [(c • f).extend_apply_of_mem hy, f.extend_apply_of_mem hy, coe_smul, Pi.smul_apply]

/-- The value at a point `x` of the closure of a convex open set `Ω`, as a continuous linear
functional of norm at most one on `C^{k+1,α}(Ω)`: the limit of the element along `Ω` at `x`. -/
def closureEvalL (hΩ : Convex ℝ (Ω : Set E)) {x : E} (hx : x ∈ closure (Ω : Set E)) :
    CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun f := f.closureExtend x
      map_add' f g := closureExtend_add hΩ f g hx
      map_smul' c f := closureExtend_smul hΩ c f hx } 1 fun f ↦ by
    rw [one_mul]
    exact norm_closureExtend_le hΩ f hx

@[simp]
theorem closureEvalL_apply (hΩ : Convex ℝ (Ω : Set E)) {x : E} (hx : x ∈ closure (Ω : Set E))
    (f : CkHolderSpaceOn (k + 1) α Ω F) : closureEvalL hΩ hx f = f.closureExtend x :=
  (rfl)

/-- The value at a point of the closure has operator norm at most one. -/
theorem norm_closureEvalL_le (hΩ : Convex ℝ (Ω : Set E)) {x : E}
    (hx : x ∈ closure (Ω : Set E)) : ‖closureEvalL (k := k) (α := α) (F := F) hΩ hx‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end TauCeti.CkHolderSpaceOn

namespace TauCeti

open TopologicalSpace
open scoped NNReal

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function `u` that is differentiable on an open set `Ω` with compact closure, with `u` and a
field `u'` continuous on the closure, where `u'` is the derivative of `u` on `Ω` and is `α`-Hölder
on `Ω`, agrees on `Ω` with an element of `C^{1,α}(Ω)`. -/
theorem exists_ckHolderSpaceOn_one_of_isCompact_closure (hΩ : IsCompact (closure (Ω : Set E)))
    {u : E → F} (hu : ContinuousOn u (closure (Ω : Set E))) (hud : DifferentiableOn ℝ u Ω)
    {u' : E → E →L[ℝ] F} {K : ℝ≥0} (hu'c : ContinuousOn u' (closure (Ω : Set E)))
    (hu'H : HolderOnWith K α u' Ω) (hu' : ∀ z ∈ (Ω : Set E), fderiv ℝ u z = u' z) :
    ∃ U : CkHolderSpaceOn 1 α Ω F, ∀ x, U x = u x := by
  have hcd : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) u Ω := by
    rw [show ((1 : ℕ) : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen]
    exact ⟨hud, by simp, contDiffOn_zero.2 ((hu'c.mono subset_closure).congr hu')⟩
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hu
  obtain ⟨C', hC'⟩ := hΩ.exists_bound_of_continuousOn hu'c
  refine ⟨CkHolderSpaceOn.ofContDiffOn u hcd (fun i hi ↦ ?_) ⟨K, ?_⟩,
    CkHolderSpaceOn.ofContDiffOn_apply _ _ _ _⟩
  · interval_cases i
    · exact ⟨C, fun x ↦ by
        rw [norm_iteratedFDeriv_zero]
        exact hC x (subset_closure x.property)⟩
    · exact ⟨C', fun x ↦ by
        rw [norm_iteratedFDeriv_one, hu' x x.property]
        exact hC' x (subset_closure x.property)⟩
  · have h : HolderOnWith K α (iteratedFDeriv ℝ 1 u) Ω := by
      rw [holderOnWith_iteratedFDeriv_succ_iff, holderOnWith_iteratedFDeriv_zero_iff]
      exact hu'H.congr fun z hz ↦ (hu' z hz).symm
    exact h.holderWith

end TauCeti
