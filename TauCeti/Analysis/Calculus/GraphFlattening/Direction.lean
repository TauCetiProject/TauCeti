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
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Flattening a graph along a direction

For a real function `γ` on a real normed space `E` and a vector `ν`, the shear
`φ z = z + γ z • ν` moves each point along `ν` by the height `γ z`. When `γ` is invariant under
translation along `ν`, the shear by `-γ` inverts it (`TauCeti.shear_neg_shear`,
`TauCeti.shear_shear_neg`), and for a unit vector `ν` in an inner product space it carries the
height `⟪y, ν⟫` to the height `⟪x, ν⟫ - γ x` above the graph of `γ`
(`TauCeti.real_inner_shear_sub`). So it flattens the region above the graph of `γ` over the
hyperplane `ν^⊥` to a half-space, without the splitting `E = ℝ × ν^⊥` used by
`TauCeti.graphFlattening`.

This file records the calculus of this shear. Its derivative is `id + Dγ(y) ν`
(`TauCeti.hasFDerivAt_shear`), of norm at most `1 + ‖Dγ(y)‖` when `‖ν‖ ≤ 1`, and its second
derivative is `D²γ(h, k) ν`. The second-order chain rule through it
(`TauCeti.fderiv_fderiv_comp_shear_apply`) reads

`D²(w ∘ φ)(y)(h, k) = D²w(φ y)(h + Dγ(y) h ν, k + Dγ(y) k ν) + D²γ(y)(h, k) Dw(φ y) ν`,

which, for `w` with values in any real normed space, gives Hölder and sup bounds for
`D²(w ∘ φ)` from those of `Dw`, `D²w`, `Dγ` and `D²γ`
(`TauCeti.holderOnWith_fderiv_fderiv_comp_shear`, `TauCeti.norm_fderiv_fderiv_comp_shear_le`).
A shear by a `G`-Lipschitz function is `(1 + G)`-Lipschitz (`TauCeti.lipschitzWith_shear`), so
composing with it preserves Hölder continuity (`TauCeti.holderOnWith_comp_shear`).
-/

public section

open Set
open scoped NNReal InnerProductSpace

namespace TauCeti

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {γ : E → ℝ} {ν : E}

/-- The shear `x ↦ x - γ x ν` inverts the shear `y ↦ y + γ y ν` when `γ` is invariant along `ν`. -/
theorem shear_neg_shear (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (y : E) :
    y + γ y • ν + (-γ (y + γ y • ν)) • ν = y := by
  rw [hγν, neg_smul, add_neg_cancel_right]

/-- The shear `y ↦ y + γ y ν` inverts the shear `x ↦ x - γ x ν` when `γ` is invariant along `ν`. -/
theorem shear_shear_neg (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (x : E) :
    x + (-γ x) • ν + γ (x + (-γ x) • ν) • ν = x := by
  rw [hγν, neg_smul, neg_add_cancel_right]

end Module

section InnerProduct

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : E → ℝ} {ν : E}

/-- For a unit vector `ν` and `γ` invariant along `ν`, the shear `y ↦ y + γ y ν` carries the
height `⟪y, ν⟫` to the height `⟪x, ν⟫ - γ x` above the graph of `γ`. -/
theorem real_inner_shear_sub (hν : ‖ν‖ = 1) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (y : E) :
    ⟪y + γ y • ν, ν⟫_ℝ - γ (y + γ y • ν) = ⟪y, ν⟫_ℝ := by
  rw [hγν, real_inner_add_smul_self_of_norm_eq_one hν]
  ring

end InnerProduct

section Lipschitz

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {γ : E → ℝ} {ν : E}

/-- A shear `y ↦ y + γ y ν` by a `G`-Lipschitz function with `‖ν‖ ≤ 1` is `(1 + G)`-Lipschitz. -/
theorem lipschitzWith_shear (hν : ‖ν‖ ≤ 1) {G : ℝ≥0} (hγ : LipschitzWith G γ) :
    LipschitzWith (1 + G) fun z : E => z + γ z • ν := by
  refine (LipschitzWith.id.add
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ν).lipschitzWith.comp hγ)).weaken ?_
  gcongr
  refine mul_le_of_le_one_left zero_le ?_
  rw [← NNReal.coe_le_one, coe_nnNorm, ContinuousLinearMap.norm_smulRight_apply]
  exact (mul_le_mul ContinuousLinearMap.norm_id_le hν (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- The shear `y ↦ y + γ y ν` by a `G`-Lipschitz function with `‖ν‖ ≤ 1` maps the closed ball of
radius `r` about `y₀` into the closed ball of radius `(1 + G) r` about its image. -/
theorem dist_shear_le (hν : ‖ν‖ ≤ 1) {G : ℝ≥0} (hγ : LipschitzWith G γ) {y y₀ : E}
    {r : ℝ} (hy : dist y y₀ ≤ r) : dist (y + γ y • ν) (y₀ + γ y₀ • ν) ≤ (1 + G) * r :=
  ((lipschitzWith_shear hν hγ).dist_le_mul y y₀).trans (by gcongr; push_cast; rfl)

/-- A function Hölder on `t`, composed with a shear by a `G`-Lipschitz function that maps `s` into
`t`, is Hölder on `s`, the constant multiplied by `(1 + G)^α`. -/
theorem holderOnWith_comp_shear {F : Type*} [PseudoMetricSpace F] (hν : ‖ν‖ ≤ 1)
    {G K α : ℝ≥0} (hγ : LipschitzWith G γ) {f : E → F} {s t : Set E} (hf : HolderOnWith K α f t)
    (hst : MapsTo (fun z => z + γ z • ν) s t) :
    HolderOnWith (K * (1 + G) ^ (α : ℝ)) α (fun y => f (y + γ y • ν)) s := by
  have h := hf.comp ((lipschitzWith_shear hν hγ).holderWith.holderOnWith s) hst
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

/-- The derivative of the shear `z ↦ z + γ z • ν`. -/
theorem hasFDerivAt_shear {y : E} (hγ : DifferentiableAt ℝ γ y) :
    HasFDerivAt (fun z => z + γ z • ν)
      (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν) y :=
  (hasFDerivAt_id y).add (hγ.hasFDerivAt.smul_const ν)

/-- The second derivative of the shear `z ↦ z + γ z • ν` is `D²γ (h, k) ν`. -/
theorem fderiv_fderiv_shear_apply {y : E} (hγ : ContDiffAt ℝ 2 γ y) (h k : E) :
    fderiv ℝ (fderiv ℝ fun z => z + γ z • ν) y h k = fderiv ℝ (fderiv ℝ γ) y h k • ν := by
  have h1 : (fun z : E => z + γ z • ν) = (fun z => z) + fun z => γ z • ν := rfl
  rw [h1, fderiv_fderiv_add (u := fun z : E => z) (w := fun z => γ z • ν) contDiffAt_fun_id
    (hγ.smul contDiffAt_const),
    add_apply, add_apply,
    fderiv_fderiv_smul_const_apply hγ]
  have h0 : fderiv ℝ (fun z : E => z) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun _ => fderiv_fun_id
  simp [h0]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The second-order chain rule through a shear.** For `φ z = z + γ z • ν`, the second
derivative of `w ∘ φ` is `D²w(φ y)(h + Dγ(y) h ν, k + Dγ(y) k ν) + D²γ(y)(h, k) Dw(φ y) ν`. -/
theorem fderiv_fderiv_comp_shear_apply {w : E → F} {y : E}
    (hw : ContDiffAt ℝ 2 w (y + γ y • ν)) (hγ : ContDiffAt ℝ 2 γ y) (h k : E) :
    fderiv ℝ (fderiv ℝ (w ∘ fun z => z + γ z • ν)) y h k =
      fderiv ℝ (fderiv ℝ w) (y + γ y • ν) (h + fderiv ℝ γ y h • ν) (k + fderiv ℝ γ y k • ν) +
        fderiv ℝ (fderiv ℝ γ) y h k • fderiv ℝ w (y + γ y • ν) ν := by
  have hφ : ContDiffAt ℝ 2 (fun z => z + γ z • ν) y := contDiffAt_fun_id.add
    (hγ.smul contDiffAt_const)
  rw [fderiv_fderiv_comp_apply (φ := fun z => z + γ z • ν) (b := y) hw hφ,
    (hasFDerivAt_shear (hγ.differentiableAt two_ne_zero)).fderiv, fderiv_fderiv_shear_apply hγ]
  simp [map_smul]

/-- The second derivative through a shear, as a bilinear map. The second term is
`(h, k) ↦ D²γ(y)(h, k) Dw(φ y) ν`. -/
theorem fderiv_fderiv_comp_shear {w : E → F} {y : E}
    (hw : ContDiffAt ℝ 2 w (y + γ y • ν)) (hγ : ContDiffAt ℝ 2 γ y) :
    fderiv ℝ (fderiv ℝ (w ∘ fun z => z + γ z • ν)) y =
      (fderiv ℝ (fderiv ℝ w) (y + γ y • ν)).bilinearComp
          (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν)
          (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν) +
        ((StrongDual.smulRightL ℝ E F).flip (fderiv ℝ w (y + γ y • ν) ν)).comp
          (fderiv ℝ (fderiv ℝ γ) y) := by
  ext h k
  simp [fderiv_fderiv_comp_shear_apply hw hγ]

/-- **Hölder continuity of second derivatives through a shear.** For `φ z = z + γ z • ν` with
`‖ν‖ ≤ 1`, if on `s` the derivatives `Dγ` and `D²γ` are bounded by `G₁` and `G₂` and Hölder with
constants `K₁` and `K₂`, and `Dw ∘ φ`, `D²w ∘ φ` are bounded by `N₁` and `N₂` and Hölder with
constants `H` and `V`, then `D²(w ∘ φ)` is Hölder on `s`. -/
theorem holderOnWith_fderiv_fderiv_comp_shear (hν : ‖ν‖ ≤ 1) {w : E → F} {s : Set E}
    {α G₁ G₂ K₁ K₂ N₁ N₂ V H : ℝ≥0} (hγ : ∀ y ∈ s, ContDiffAt ℝ 2 γ y)
    (hw : ∀ y ∈ s, ContDiffAt ℝ 2 w (y + γ y • ν))
    (hG1 : ∀ y ∈ s, ‖fderiv ℝ γ y‖ ≤ G₁) (hG2 : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G₂)
    (hK1 : HolderOnWith K₁ α (fderiv ℝ γ) s) (hK2 : HolderOnWith K₂ α (fderiv ℝ (fderiv ℝ γ)) s)
    (hN1 : ∀ y ∈ s, ‖fderiv ℝ w (y + γ y • ν)‖ ≤ N₁)
    (hN2 : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ w) (y + γ y • ν)‖ ≤ N₂)
    (hV : HolderOnWith V α (fun y => fderiv ℝ (fderiv ℝ w) (y + γ y • ν)) s)
    (hH : HolderOnWith H α (fun y => fderiv ℝ w (y + γ y • ν)) s) :
    HolderOnWith
      (V * (1 + G₁) * (1 + G₁) + N₂ * K₁ * (1 + G₁) + N₂ * (1 + G₁) * K₁ + (N₁ * K₂ + G₂ * H))
      α (fderiv ℝ (fderiv ℝ (w ∘ fun z => z + γ z • ν))) s := by
  have hS := holderOnWith_id_add_smulRight hν hK1
  have hSb (y : E) (hy : y ∈ s) := norm_id_add_smulRight_le hν (hG1 y hy)
  have h1 := ContinuousLinearMap.holderOnWith_bilinearComp hV hS hS hN2 hSb hSb
  have hc : HolderOnWith H α (fun y => fderiv ℝ w (y + γ y • ν) ν) s :=
    hH.clm_apply_of_norm_le_one hν
  have hcb (y : E) (hy : y ∈ s) : ‖fderiv ℝ w (y + γ y • ν) ν‖ ≤ N₁ :=
    ((fderiv ℝ w _).unit_le_opNorm ν hν).trans (hN1 y hy)
  have h2 := ContinuousLinearMap.holderOnWith_smulRightL_flip_comp hc hK2 hcb hG2
  exact (h1.add h2).congr fun y hy => (fderiv_fderiv_comp_shear (hw y hy) (hγ y hy)).symm

/-- The bound `‖D²(w ∘ φ)‖ ≤ N₂ (1 + G₁)² + N₁ G₂` for the shear `φ z = z + γ z • ν`. -/
theorem norm_fderiv_fderiv_comp_shear_le (hν : ‖ν‖ ≤ 1) {w : E → F} {y : E} {G₁ G₂ N₁ N₂ : ℝ≥0}
    (hγ : ContDiffAt ℝ 2 γ y) (hw : ContDiffAt ℝ 2 w (y + γ y • ν))
    (hG1 : ‖fderiv ℝ γ y‖ ≤ G₁) (hG2 : ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G₂)
    (hN1 : ‖fderiv ℝ w (y + γ y • ν)‖ ≤ N₁) (hN2 : ‖fderiv ℝ (fderiv ℝ w) (y + γ y • ν)‖ ≤ N₂) :
    ‖fderiv ℝ (fderiv ℝ (w ∘ fun z => z + γ z • ν)) y‖ ≤
      N₂ * (1 + G₁) * (1 + G₁) + N₁ * G₂ := by
  have hSb := norm_id_add_smulRight_le hν hG1
  have hc : ‖fderiv ℝ w (y + γ y • ν) ν‖ ≤ N₁ :=
    ((fderiv ℝ w _).unit_le_opNorm ν hν).trans hN1
  rw [fderiv_fderiv_comp_shear hw hγ]
  refine (norm_add_le (_ : E →L[ℝ] E →L[ℝ] F) _).trans (add_le_add ?_ ?_)
  · refine (ContinuousLinearMap.norm_bilinearComp_le _ _ _).trans ?_
    push_cast at hSb ⊢
    gcongr
  · refine (ContinuousLinearMap.norm_smulRightL_flip_comp_le _ _).trans ?_
    gcongr

end Derivative

end TauCeti
