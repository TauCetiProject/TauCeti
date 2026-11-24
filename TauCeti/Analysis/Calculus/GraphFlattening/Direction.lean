/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Flattening a graph along a direction

For a real function `γ` on a real normed space `E` and a vector `ν`, the shear
`TauCeti.shearAlong γ ν z = z + γ z • ν` moves each point along `ν` by the height `γ z`. When `γ`
is invariant under translation along `ν`, the shear by `-γ` inverts it
(`TauCeti.shearAlong_neg_shearAlong`, `TauCeti.shearAlong_shearAlong_neg`), and for a unit vector
`ν` in an inner product space it raises the height `⟪y, ν⟫` by `γ y`
(`TauCeti.real_inner_shearAlong`), so it carries the height `⟪y, ν⟫` to the height
`⟪x, ν⟫ - γ x` above the graph of `γ` (`TauCeti.real_inner_shearAlong_sub`). So it flattens
the region above the graph of `γ` over the hyperplane `ν^⊥` to a half-space, without the
splitting `E = ℝ × ν^⊥` used by `TauCeti.graphFlattening`. For continuous `γ`, the closure of the
region above the graph is the region on or above it (`TauCeti.closure_setOf_lt_real_inner`).
So if a set `Ω` agrees on an open set `W` with the region above the graph, then on `W` the closure
of `Ω` is the region on or above the graph (`TauCeti.closure_inter_eq_setOf_le_real_inner_inter`)
and the frontier of `Ω` is the graph (`TauCeti.frontier_inter_eq_setOf_eq_real_inner_inter`).

This file records the calculus of this shear. It is `C^m` when `γ` is
(`TauCeti.contDiff_shearAlong`), its derivative is `id + Dγ(y) ν`
(`TauCeti.hasFDerivAt_shearAlong`), of norm at most `1 + ‖Dγ(y)‖` when `‖ν‖ ≤ 1`, and its second
derivative is `D²γ(h, k) ν`. The second-order chain rule through it
(`TauCeti.fderiv_fderiv_comp_shearAlong_apply`) reads

`D²(w ∘ φ)(y)(h, k) = D²w(φ y)(h + Dγ(y) h ν, k + Dγ(y) k ν) + D²γ(y)(h, k) Dw(φ y) ν`,

which, for `w` with values in any real normed space, gives Hölder and sup bounds for
`D²(w ∘ φ)` from those of `Dw`, `D²w`, `Dγ` and `D²γ`
(`TauCeti.holderOnWith_fderiv_fderiv_comp_shearAlong`,
`TauCeti.norm_fderiv_fderiv_comp_shearAlong_le`). A shear by a `G`-Lipschitz function is
`(1 + G)`-Lipschitz (`TauCeti.lipschitzWith_shearAlong`), so composing with it preserves Hölder
continuity (`TauCeti.holderOnWith_comp_shearAlong`).
-/

public section

open Set
open scoped NNReal InnerProductSpace

namespace TauCeti

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The **shear** `z ↦ z + γ z • ν` of `E` along the vector `ν` by the height function `γ`. -/
def shearAlong (γ : E → ℝ) (ν : E) (z : E) : E :=
  z + γ z • ν

theorem shearAlong_def (γ : E → ℝ) (ν z : E) : shearAlong γ ν z = z + γ z • ν :=
  (rfl)

variable {γ : E → ℝ} {ν : E}

/-- The shear by `-γ` inverts the shear by `γ` when `γ` is invariant along `ν`. -/
theorem shearAlong_neg_shearAlong (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (y : E) :
    shearAlong (-γ) ν (shearAlong γ ν y) = y := by
  rw [shearAlong_def (-γ), shearAlong_def, Pi.neg_apply, hγν, neg_smul, add_neg_cancel_right]

/-- The shear by `γ` inverts the shear by `-γ` when `γ` is invariant along `ν`. -/
theorem shearAlong_shearAlong_neg (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (x : E) :
    shearAlong γ ν (shearAlong (-γ) ν x) = x := by
  rw [shearAlong_def γ, shearAlong_def, Pi.neg_apply, hγν, neg_smul, neg_add_cancel_right]

end Module

section InnerProduct

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : E → ℝ} {ν : E}

/-- For a unit vector `ν`, the shear `shearAlong γ ν` raises the height `⟪y, ν⟫` by `γ y`. -/
theorem real_inner_shearAlong (hν : ‖ν‖ = 1) (y : E) :
    ⟪shearAlong γ ν y, ν⟫_ℝ = ⟪y, ν⟫_ℝ + γ y := by
  rw [shearAlong_def, real_inner_add_smul_self_of_norm_eq_one hν]

/-- For a unit vector `ν` and `γ` invariant along `ν`, the shear `shearAlong γ ν` carries the
height `⟪y, ν⟫` to the height `⟪x, ν⟫ - γ x` above the graph of `γ`. -/
theorem real_inner_shearAlong_sub (hν : ‖ν‖ = 1) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (y : E) : ⟪shearAlong γ ν y, ν⟫_ℝ - γ (shearAlong γ ν y) = ⟪y, ν⟫_ℝ := by
  rw [real_inner_shearAlong hν, shearAlong_def, hγν, add_sub_cancel_right]

/-- For a unit vector `ν` and a continuous `γ` invariant along `ν`, the closure of the region
`{x | γ x < ⟪x, ν⟫}` above the graph of `γ` is the region `{x | γ x ≤ ⟪x, ν⟫}` on or above it:
a point of the graph is the limit of the points `x + t ν`, `t > 0`, above it. -/
theorem closure_setOf_lt_real_inner (hν : ‖ν‖ = 1) (hγ : Continuous γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    closure {x | γ x < ⟪x, ν⟫_ℝ} = {x | γ x ≤ ⟪x, ν⟫_ℝ} := by
  refine (closure_lt_subset_le hγ (continuous_id.inner continuous_const)).antisymm
    fun x (hx : γ x ≤ ⟪x, ν⟫_ℝ) => mem_closure_of_tendsto (f := fun t : ℝ => x + t • ν)
      (b := nhdsWithin 0 (Ioi 0)) ?_ (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
  · have hc : Continuous fun t : ℝ => x + t • ν := by fun_prop
    exact (hc.tendsto' 0 x (by simp)).mono_left nhdsWithin_le_nhds
  · simp only [mem_ofPred_eq, id_eq, hγν, real_inner_add_smul_self_of_norm_eq_one hν]
    linarith

/-- If `Ω` agrees on an open set `W` with the region `{y | γ y < ⟪y, ν⟫}` above the graph of a
continuous function `γ` invariant along a unit vector `ν`, then on `W` the closure of `Ω` is the
region `{y | γ y ≤ ⟪y, ν⟫}` on or above the graph. -/
theorem closure_inter_eq_setOf_le_real_inner_inter {Ω W : Set E} (hW : IsOpen W) (hν : ‖ν‖ = 1)
    (hγ : Continuous γ) (hγν : ∀ y (t : ℝ), γ (y + t • ν) = γ y)
    (hΩW : Ω ∩ W = {y | γ y < ⟪y, ν⟫_ℝ} ∩ W) :
    closure Ω ∩ W = {y | γ y ≤ ⟪y, ν⟫_ℝ} ∩ W := by
  rw [← closure_setOf_lt_real_inner hν hγ hγν]
  refine Subset.antisymm (fun y hy => ⟨?_, hy.2⟩) fun y hy => ⟨?_, hy.2⟩
  · -- `closure Ω ∩ W ⊆ closure (Ω ∩ W)`, the closure of a part of the region above the graph.
    have hy' := hW.closure_inter hy
    rw [hΩW] at hy'
    exact closure_mono inter_subset_left hy'
  · -- `closure {γ < ⟪·, ν⟫} ∩ W ⊆ closure ({γ < ⟪·, ν⟫} ∩ W) = closure (Ω ∩ W)`.
    have hy' := hW.inter_closure ⟨hy.2, hy.1⟩
    rw [inter_comm, ← hΩW] at hy'
    exact closure_mono inter_subset_left hy'

/-- If `Ω` agrees on an open set `W` with the region `{y | γ y < ⟪y, ν⟫}` above the graph of a
continuous function `γ` invariant along a unit vector `ν`, then on `W` the frontier of `Ω` is the
graph `{y | γ y = ⟪y, ν⟫}`. -/
theorem frontier_inter_eq_setOf_eq_real_inner_inter {Ω W : Set E} (hW : IsOpen W)
    (hν : ‖ν‖ = 1) (hγ : Continuous γ) (hγν : ∀ y (t : ℝ), γ (y + t • ν) = γ y)
    (hΩW : Ω ∩ W = {y | γ y < ⟪y, ν⟫_ℝ} ∩ W) :
    frontier Ω ∩ W = {y | γ y = ⟪y, ν⟫_ℝ} ∩ W := by
  have ho : IsOpen {y | γ y < ⟪y, ν⟫_ℝ} := isOpen_lt hγ (continuous_id.inner continuous_const)
  -- On the open set `W`, the frontier of `Ω` is that of the open region above the graph.
  rw [← frontier_inter_open_inter hW, hΩW, frontier_inter_open_inter hW, ho.frontier_eq,
    closure_setOf_lt_real_inner hν hγ hγν]
  ext y
  simp only [mem_inter_iff, mem_sdiff, mem_ofPred_eq, not_lt, ← le_antisymm_iff]

end InnerProduct

section Lipschitz

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {γ : E → ℝ} {ν : E}

/-- The shear `shearAlong γ ν` by a `G`-Lipschitz function with `‖ν‖ ≤ 1` is
`(1 + G)`-Lipschitz. -/
theorem lipschitzWith_shearAlong (hν : ‖ν‖ ≤ 1) {G : ℝ≥0} (hγ : LipschitzWith G γ) :
    LipschitzWith (1 + G) (shearAlong γ ν) := by
  refine (LipschitzWith.id.add
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ν).lipschitzWith.comp hγ)).weaken ?_
  gcongr
  refine mul_le_of_le_one_left zero_le ?_
  rw [← NNReal.coe_le_one, coe_nnNorm, ContinuousLinearMap.norm_smulRight_apply]
  exact (mul_le_mul ContinuousLinearMap.norm_id_le hν (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- The shear `shearAlong γ ν` by a `G`-Lipschitz function with `‖ν‖ ≤ 1` maps the closed ball of
radius `r` about `y₀` into the closed ball of radius `(1 + G) r` about its image. -/
theorem dist_shearAlong_le (hν : ‖ν‖ ≤ 1) {G : ℝ≥0} (hγ : LipschitzWith G γ) {y y₀ : E}
    {r : ℝ} (hy : dist y y₀ ≤ r) : dist (shearAlong γ ν y) (shearAlong γ ν y₀) ≤ (1 + G) * r :=
  ((lipschitzWith_shearAlong hν hγ).dist_le_mul y y₀).trans (by gcongr; push_cast; rfl)

/-- A function Hölder on `t`, composed with a shear by a `G`-Lipschitz function that maps `s` into
`t`, is Hölder on `s`, the constant multiplied by `(1 + G)^α`. -/
theorem holderOnWith_comp_shearAlong {F : Type*} [PseudoMetricSpace F] (hν : ‖ν‖ ≤ 1)
    {G K α : ℝ≥0} (hγ : LipschitzWith G γ) {f : E → F} {s t : Set E} (hf : HolderOnWith K α f t)
    (hst : MapsTo (shearAlong γ ν) s t) :
    HolderOnWith (K * (1 + G) ^ (α : ℝ)) α (fun y => f (shearAlong γ ν y)) s := by
  have h := hf.comp ((lipschitzWith_shearAlong hν hγ).holderWith.holderOnWith s) hst
  rwa [mul_one] at h

end Lipschitz

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ν : E}

/-- The map `id + f ν`, for a linear functional `f` with `‖f‖ ≤ G` and `‖ν‖ ≤ 1`, has norm at
most `1 + G`. -/
theorem norm_id_add_smulRight_le (hν : ‖ν‖ ≤ 1) {f : E →L[ℝ] ℝ} {G : ℝ≥0} (hf : ‖f‖ ≤ G) :
    ‖ContinuousLinearMap.id ℝ E + f.smulRight ν‖ ≤ ((1 + G : ℝ≥0) : ℝ) :=
  calc _ ≤ ‖ContinuousLinearMap.id ℝ E‖ + ‖f.smulRight ν‖ := norm_add_le _ _
    _ ≤ 1 + G * 1 := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = _ := by push_cast; ring

/-- For `‖ν‖ ≤ 1`, the family of maps `id + f(·) ν` is Hölder with the Hölder constant of the
family of linear functionals `f`. -/
theorem holderOnWith_id_add_smulRight {X : Type*} [PseudoMetricSpace X] (hν : ‖ν‖ ≤ 1)
    {f : X → E →L[ℝ] ℝ} {s : Set X} {α K : ℝ≥0} (hf : HolderOnWith K α f s) :
    HolderOnWith K α (fun y => ContinuousLinearMap.id ℝ E + (f y).smulRight ν) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hsub : (ContinuousLinearMap.id ℝ E + (f x).smulRight ν) -
      (ContinuousLinearMap.id ℝ E + (f y).smulRight ν) = (f x - f y).smulRight ν := by
    ext h
    simp [sub_smul]
  rw [dist_eq_norm (ContinuousLinearMap.id ℝ E + (f x).smulRight ν), hsub,
    ContinuousLinearMap.norm_smulRight_apply]
  have hd := hf.dist_le hx hy
  rw [dist_eq_norm (f x)] at hd
  calc _ ≤ ‖f x - f y‖ * 1 := by gcongr
    _ ≤ _ := by rw [mul_one]; exact hd

variable {γ : E → ℝ}

/-- The shear `shearAlong γ ν` is `C^m` at `y` when `γ` is. -/
theorem contDiffAt_shearAlong {m : WithTop ℕ∞} {y : E} (hγ : ContDiffAt ℝ m γ y) :
    ContDiffAt ℝ m (shearAlong γ ν) y :=
  contDiffAt_fun_id.add (hγ.smul contDiffAt_const)

/-- The shear `shearAlong γ ν` is `C^m` when `γ` is. -/
theorem contDiff_shearAlong {m : WithTop ℕ∞} (hγ : ContDiff ℝ m γ) :
    ContDiff ℝ m (shearAlong γ ν) :=
  contDiff_iff_contDiffAt.2 fun _ => contDiffAt_shearAlong hγ.contDiffAt

/-- The derivative of the shear `shearAlong γ ν`. -/
theorem hasFDerivAt_shearAlong {y : E} (hγ : DifferentiableAt ℝ γ y) :
    HasFDerivAt (shearAlong γ ν) (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν) y :=
  (hasFDerivAt_id y).add (hγ.hasFDerivAt.smul_const ν)

/-- The second derivative of the shear `shearAlong γ ν` is `D²γ (h, k) ν`. -/
theorem fderiv_fderiv_shearAlong_apply {y : E} (hγ : ContDiffAt ℝ 2 γ y) (h k : E) :
    fderiv ℝ (fderiv ℝ (shearAlong γ ν)) y h k = fderiv ℝ (fderiv ℝ γ) y h k • ν := by
  have h1 : shearAlong γ ν = (fun z => z) + fun z => γ z • ν := rfl
  rw [h1, fderiv_fderiv_add (u := fun z : E => z) (w := fun z => γ z • ν) contDiffAt_fun_id
    (hγ.smul contDiffAt_const),
    add_apply, add_apply,
    fderiv_fderiv_smul_const_apply hγ]
  have h0 : fderiv ℝ (fun z : E => z) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun _ => fderiv_fun_id
  simp [h0]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The second-order chain rule through a shear.** For `φ = shearAlong γ ν`, the second
derivative of `w ∘ φ` is `D²w(φ y)(h + Dγ(y) h ν, k + Dγ(y) k ν) + D²γ(y)(h, k) Dw(φ y) ν`. -/
theorem fderiv_fderiv_comp_shearAlong_apply {w : E → F} {y : E}
    (hw : ContDiffAt ℝ 2 w (shearAlong γ ν y)) (hγ : ContDiffAt ℝ 2 γ y) (h k : E) :
    fderiv ℝ (fderiv ℝ (w ∘ shearAlong γ ν)) y h k =
      fderiv ℝ (fderiv ℝ w) (shearAlong γ ν y) (h + fderiv ℝ γ y h • ν)
          (k + fderiv ℝ γ y k • ν) +
        fderiv ℝ (fderiv ℝ γ) y h k • fderiv ℝ w (shearAlong γ ν y) ν := by
  rw [fderiv_fderiv_comp_apply (φ := shearAlong γ ν) (b := y) hw (contDiffAt_shearAlong hγ),
    (hasFDerivAt_shearAlong (hγ.differentiableAt two_ne_zero)).fderiv,
    fderiv_fderiv_shearAlong_apply hγ]
  simp [map_smul]

/-- The second derivative through a shear, as a bilinear map. The second term is
`(h, k) ↦ D²γ(y)(h, k) Dw(φ y) ν`. -/
theorem fderiv_fderiv_comp_shearAlong {w : E → F} {y : E}
    (hw : ContDiffAt ℝ 2 w (shearAlong γ ν y)) (hγ : ContDiffAt ℝ 2 γ y) :
    fderiv ℝ (fderiv ℝ (w ∘ shearAlong γ ν)) y =
      (fderiv ℝ (fderiv ℝ w) (shearAlong γ ν y)).bilinearComp
          (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν)
          (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν) +
        ((StrongDual.smulRightL ℝ E F).flip (fderiv ℝ w (shearAlong γ ν y) ν)).comp
          (fderiv ℝ (fderiv ℝ γ) y) := by
  ext h k
  simp [fderiv_fderiv_comp_shearAlong_apply hw hγ]

/-- **Hölder continuity of second derivatives through a shear.** For `φ = shearAlong γ ν` with
`‖ν‖ ≤ 1`, if on `s` the derivatives `Dγ` and `D²γ` are bounded by `G₁` and `G₂` and Hölder with
constants `K₁` and `K₂`, and `Dw ∘ φ`, `D²w ∘ φ` are bounded by `N₁` and `N₂` and Hölder with
constants `H` and `V`, then `D²(w ∘ φ)` is Hölder on `s`. -/
theorem holderOnWith_fderiv_fderiv_comp_shearAlong (hν : ‖ν‖ ≤ 1) {w : E → F} {s : Set E}
    {α G₁ G₂ K₁ K₂ N₁ N₂ V H : ℝ≥0} (hγ : ∀ y ∈ s, ContDiffAt ℝ 2 γ y)
    (hw : ∀ y ∈ s, ContDiffAt ℝ 2 w (shearAlong γ ν y))
    (hG1 : ∀ y ∈ s, ‖fderiv ℝ γ y‖ ≤ G₁) (hG2 : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G₂)
    (hK1 : HolderOnWith K₁ α (fderiv ℝ γ) s) (hK2 : HolderOnWith K₂ α (fderiv ℝ (fderiv ℝ γ)) s)
    (hN1 : ∀ y ∈ s, ‖fderiv ℝ w (shearAlong γ ν y)‖ ≤ N₁)
    (hN2 : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ w) (shearAlong γ ν y)‖ ≤ N₂)
    (hV : HolderOnWith V α (fun y => fderiv ℝ (fderiv ℝ w) (shearAlong γ ν y)) s)
    (hH : HolderOnWith H α (fun y => fderiv ℝ w (shearAlong γ ν y)) s) :
    HolderOnWith
      (V * (1 + G₁) * (1 + G₁) + N₂ * K₁ * (1 + G₁) + N₂ * (1 + G₁) * K₁ + (N₁ * K₂ + G₂ * H))
      α (fderiv ℝ (fderiv ℝ (w ∘ shearAlong γ ν))) s := by
  have hS := holderOnWith_id_add_smulRight hν hK1
  have hSb (y : E) (hy : y ∈ s) := norm_id_add_smulRight_le hν (hG1 y hy)
  have h1 := ContinuousLinearMap.holderOnWith_bilinearComp hV hS hS hN2 hSb hSb
  have hc : HolderOnWith H α (fun y => fderiv ℝ w (shearAlong γ ν y) ν) s :=
    hH.clm_apply_of_norm_le_one hν
  have hcb (y : E) (hy : y ∈ s) : ‖fderiv ℝ w (shearAlong γ ν y) ν‖ ≤ N₁ :=
    ((fderiv ℝ w _).unit_le_opNorm ν hν).trans (hN1 y hy)
  have h2 := ContinuousLinearMap.holderOnWith_smulRightL_flip_comp hc hK2 hcb hG2
  exact (h1.add h2).congr fun y hy => (fderiv_fderiv_comp_shearAlong (hw y hy) (hγ y hy)).symm

/-- The bound `‖D²(w ∘ φ)‖ ≤ N₂ (1 + G₁)² + N₁ G₂` for the shear `φ = shearAlong γ ν`. -/
theorem norm_fderiv_fderiv_comp_shearAlong_le (hν : ‖ν‖ ≤ 1) {w : E → F} {y : E}
    {G₁ G₂ N₁ N₂ : ℝ≥0} (hγ : ContDiffAt ℝ 2 γ y) (hw : ContDiffAt ℝ 2 w (shearAlong γ ν y))
    (hG1 : ‖fderiv ℝ γ y‖ ≤ G₁) (hG2 : ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G₂)
    (hN1 : ‖fderiv ℝ w (shearAlong γ ν y)‖ ≤ N₁)
    (hN2 : ‖fderiv ℝ (fderiv ℝ w) (shearAlong γ ν y)‖ ≤ N₂) :
    ‖fderiv ℝ (fderiv ℝ (w ∘ shearAlong γ ν)) y‖ ≤ N₂ * (1 + G₁) * (1 + G₁) + N₁ * G₂ := by
  have hSb := norm_id_add_smulRight_le hν hG1
  have hc : ‖fderiv ℝ w (shearAlong γ ν y) ν‖ ≤ N₁ :=
    ((fderiv ℝ w _).unit_le_opNorm ν hν).trans hN1
  rw [fderiv_fderiv_comp_shearAlong hw hγ]
  refine (norm_add_le (_ : E →L[ℝ] E →L[ℝ] F) _).trans (add_le_add ?_ ?_)
  · refine (ContinuousLinearMap.norm_bilinearComp_le _ _ _).trans ?_
    push_cast at hSb ⊢
    gcongr
  · refine (ContinuousLinearMap.norm_smulRightL_flip_comp_le _ _).trans ?_
    gcongr

end Derivative

end TauCeti
