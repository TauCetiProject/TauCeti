/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.SecondDerivative
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.PeriodicDeriv
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
the region above the graph of `γ` over the hyperplane `ν^⊥` to the half-space
`{0 < ⟪y, ν⟫}` (`TauCeti.preimage_shearAlong_setOf_lt_inner`), without the
splitting `E = ℝ × ν^⊥` used by `TauCeti.graphFlattening`.

This file records the calculus of this shear. It is `C^m` when `γ` is
(`TauCeti.contDiff_shearAlong`), its derivative is `id + Dγ(y) ν`
(`TauCeti.hasFDerivAt_shearAlong`), of norm at most `1 + ‖Dγ(y)‖` when `‖ν‖ ≤ 1`
(`TauCeti.norm_fderiv_shearAlong_le`). When `Dγ(y) ν = 0`, for instance when `γ` is invariant
along `ν`, this derivative is a transvection, of Jacobian determinant one
(`TauCeti.det_fderiv_shearAlong`, and `TauCeti.abs_det_fderiv_shearAlong` for `γ` differentiable
and invariant along `ν`). For `γ` invariant along `ν` the derivative of the inverse shear at
`shearAlong γ ν y` inverts it (`TauCeti.fderiv_shearAlong_neg_comp_fderiv`,
`TauCeti.fderiv_comp_fderiv_shearAlong_neg`). Its second
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

/-- If `γ` is invariant along `ν`, so is `-γ`. -/
theorem neg_apply_add_smul_eq (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (x : E) (t : ℝ) :
    (-γ) (x + t • ν) = (-γ) x := by
  rw [Pi.neg_apply, Pi.neg_apply, hγν]

/-- The shear `shearAlong γ ν` is injective when `γ` is invariant along `ν`. -/
theorem injective_shearAlong (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    Function.Injective (shearAlong γ ν) :=
  Function.LeftInverse.injective (g := shearAlong (-γ) ν) (shearAlong_neg_shearAlong hγν)

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

/-- For a unit vector `ν` and `γ` invariant along `ν`, the preimage under the shear
`shearAlong γ ν` of the region `{γ x < ⟪x, ν⟫}` above the graph of `γ` is the half-space
`{0 < ⟪y, ν⟫}`. -/
theorem preimage_shearAlong_setOf_lt_inner (hν : ‖ν‖ = 1)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    shearAlong γ ν ⁻¹' {x | γ x < ⟪x, ν⟫_ℝ} = {y | 0 < ⟪y, ν⟫_ℝ} := by
  ext y
  rw [mem_preimage, mem_ofPred_eq, mem_ofPred_eq, ← sub_pos, real_inner_shearAlong_sub hν hγν]

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

/-- The shear `shearAlong γ ν` is differentiable when `γ` is. -/
theorem differentiable_shearAlong (hγ : Differentiable ℝ γ) : Differentiable ℝ (shearAlong γ ν) :=
  fun y => (hasFDerivAt_shearAlong (hγ y)).differentiableAt

/-- The derivative of the shear `shearAlong γ ν` is `id + Dγ(y) ν`. -/
theorem fderiv_shearAlong {y : E} (hγ : DifferentiableAt ℝ γ y) :
    fderiv ℝ (shearAlong γ ν) y = ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν :=
  (hasFDerivAt_shearAlong hγ).fderiv

/-- The shear by a function with derivative of norm at most `K` at `y` has derivative of norm at
most `1 + K` at `y`, for `‖ν‖ ≤ 1`. -/
theorem norm_fderiv_shearAlong_le (hν : ‖ν‖ ≤ 1) {K : ℝ≥0} {y : E} (hγ : DifferentiableAt ℝ γ y)
    (hK : ‖fderiv ℝ γ y‖ ≤ K) : ‖fderiv ℝ (shearAlong γ ν) y‖ ≤ 1 + K := by
  rw [fderiv_shearAlong hγ]
  exact_mod_cast norm_id_add_smulRight_le hν hK

/-- The inverse shear `shearAlong (-γ) ν` has derivative of norm at most `1 + K` at `y` when
`‖Dγ(y)‖ ≤ K` and `‖ν‖ ≤ 1`. -/
theorem norm_fderiv_shearAlong_neg_le (hν : ‖ν‖ ≤ 1) {K : ℝ≥0} {y : E}
    (hγ : DifferentiableAt ℝ γ y) (hK : ‖fderiv ℝ γ y‖ ≤ K) :
    ‖fderiv ℝ (shearAlong (-γ) ν) y‖ ≤ 1 + K :=
  norm_fderiv_shearAlong_le hν hγ.neg (by rwa [fderiv_neg, norm_neg])

/-- For `γ` invariant along `ν`, the derivative of the inverse shear `shearAlong (-γ) ν` at
`shearAlong γ ν y` is a left inverse of the derivative of the shear `shearAlong γ ν` at `y`. -/
theorem fderiv_shearAlong_neg_comp_fderiv (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {y : E}
    (hy : DifferentiableAt ℝ γ y) (hΦy : DifferentiableAt ℝ γ (shearAlong γ ν y)) :
    fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y) ∘L fderiv ℝ (shearAlong γ ν) y =
      ContinuousLinearMap.id ℝ E :=
  fderiv_comp_fderiv_eq_id_of_eqOn_comp_id uniqueDiffWithinAt_univ
    (hasFDerivAt_shearAlong hy).differentiableAt (hasFDerivAt_shearAlong hΦy.neg).differentiableAt
    (fun z _ => shearAlong_neg_shearAlong hγν z) (mem_univ y)

/-- For `γ` invariant along `ν`, the derivative of the shear `shearAlong γ ν` at `y` is a left
inverse of the derivative of the inverse shear `shearAlong (-γ) ν` at `shearAlong γ ν y`. -/
theorem fderiv_comp_fderiv_shearAlong_neg (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {y : E}
    (hy : DifferentiableAt ℝ γ y) (hΦy : DifferentiableAt ℝ γ (shearAlong γ ν y)) :
    fderiv ℝ (shearAlong γ ν) y ∘L fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y) =
      ContinuousLinearMap.id ℝ E := by
  have h := fderiv_comp_fderiv_eq_id_of_eqOn_comp_id uniqueDiffWithinAt_univ
    (hasFDerivAt_shearAlong hΦy.neg).differentiableAt
    (hasFDerivAt_shearAlong (y := shearAlong (-γ) ν (shearAlong γ ν y))
      (by rwa [shearAlong_neg_shearAlong hγν])).differentiableAt
    (fun z _ => shearAlong_shearAlong_neg hγν z) (mem_univ _)
  rwa [shearAlong_neg_shearAlong hγν] at h

/-- If `Dγ(y) ν = 0`, for instance when `γ` is invariant along `ν`, the shear `shearAlong γ ν`
has Jacobian determinant one at `y`: its derivative `id + Dγ(y) ν` is a transvection. -/
theorem det_fderiv_shearAlong [FiniteDimensional ℝ E] {y : E} (hγ : DifferentiableAt ℝ γ y)
    (hγν : fderiv ℝ γ y ν = 0) : (fderiv ℝ (shearAlong γ ν) y).det = 1 := by
  have h : ((fderiv ℝ (shearAlong γ ν) y : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      LinearMap.transvection (fderiv ℝ γ y : E →ₗ[ℝ] ℝ) ν := by
    ext h
    simp [fderiv_shearAlong hγ, LinearMap.transvection.apply]
  rw [ContinuousLinearMap.det, h, LinearMap.transvection.det, ContinuousLinearMap.coe_coe, hγν,
    add_zero]

/-- For `γ` differentiable and invariant along `ν`, the shear `shearAlong γ ν` has Jacobian
determinant of absolute value one everywhere, by `TauCeti.det_fderiv_shearAlong`. -/
theorem abs_det_fderiv_shearAlong [FiniteDimensional ℝ E] (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (y : E) :
    |(fderiv ℝ (shearAlong γ ν) y).det| = 1 := by
  rw [det_fderiv_shearAlong (hγ y)
    (fderiv_apply_eq_zero_of_forall_periodic_smul (fun t x => hγν x t) y), abs_one]

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
