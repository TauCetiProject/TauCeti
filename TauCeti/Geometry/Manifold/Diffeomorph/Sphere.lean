/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.Sphere.Boost
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Level-preserving rotations and boosts of `Sⁿ × ℝ`

Let `u` be a unit vector of a real inner product space `E` of dimension `n + 1`, let `α : ℝ → ℝ`
be smooth, and let `Q : ℝ → E ≃ₗᵢ[ℝ] E` be a family of linear isometries depending smoothly on the
parameter. Applying at level `s` the isometry `Q s` and then the boost of rapidity `α s` toward
`u` (`TauCeti.sphereBoost`) defines a smooth map `TauCeti.boostRotate u α Q` of `ℝ × E`, which
maps the unit sphere at each level to itself. Its inverse at level `s` is the boost of rapidity
`-α s` followed by `(Q s)⁻¹`, so it defines a diffeomorphism of `Sⁿ × ℝ` preserving the levels
(`TauCeti.boostRotateDiffeomorph`).

At a point `-u` fixed by every `Q s`, the boost stretches tangent vectors by `exp (α s)`, so the
derivative of `boostRotate` there in a direction `(0, ξ)` is `exp (α s) • Q s ξ`
(`TauCeti.fderiv_boostRotate_apply_zero`). A level-preserving family can thus prescribe both the
direction and the speed of a family of tangent vectors at `-u`, one level at a time.

## Main definitions

* `TauCeti.boostRotate u α Q`: at level `s`, the linear isometry `Q s` followed by the boost of
  rapidity `α s` toward `u`.
* `TauCeti.boostRotateDiffeomorph`: the level-preserving diffeomorphism of `Sⁿ × ℝ` which
  `boostRotate` defines.

## Main results

* `TauCeti.norm_boostRotate`, `TauCeti.contDiffAt_boostRotate`: `boostRotate` maps the unit
  sphere to itself and is smooth along `ℝ × Sⁿ`.
* `TauCeti.coe_boostRotateDiffeomorph_apply_fst`, `TauCeti.boostRotateDiffeomorph_apply_snd`: the
  two components of `boostRotateDiffeomorph`.
* `TauCeti.coe_boostRotateDiffeomorph_symm_apply_fst`,
  `TauCeti.boostRotateDiffeomorph_symm_apply_snd`: the two components of its inverse.
* `TauCeti.fderiv_boostRotate_apply_zero`: the derivative of `boostRotate` at its fixed point.
-/

public section

noncomputable section

open Set Function Manifold Metric Module Real
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {u : E} {α : ℝ → ℝ} {Q : ℝ → E ≃ₗᵢ[ℝ] E}

/-- The linear isometry `Q s` followed by the boost of rapidity `α s` toward `u`, applied at level
`s` to the vector `x`. -/
def boostRotate (u : E) (α : ℝ → ℝ) (Q : ℝ → E ≃ₗᵢ[ℝ] E) (p : ℝ × E) : E :=
  sphereBoost u (α p.1) (Q p.1 p.2)

/-- At level `s`, `boostRotate` applies `Q s` and then the boost of rapidity `α s`. -/
@[simp]
theorem boostRotate_apply (s : ℝ) (x : E) :
    boostRotate u α Q (s, x) = sphereBoost u (α s) (Q s x) :=
  (rfl)

/-- `boostRotate` maps the unit sphere to itself. -/
theorem norm_boostRotate (hu : ‖u‖ = 1) (s : ℝ) {x : E} (hx : ‖x‖ = 1) :
    ‖boostRotate u α Q (s, x)‖ = 1 :=
  norm_sphereBoost hu (by rwa [LinearIsometryEquiv.norm_map]) _

/-- The map `boostRotate` is smooth at every point of `ℝ × Sⁿ`. -/
theorem contDiffAt_boostRotate (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (s : ℝ) {x : E} (hx : ‖x‖ = 1) :
    ContDiffAt ℝ ∞ (boostRotate u α Q) (s, x) := by
  have hx' : ‖Q s x‖ = 1 := by rwa [LinearIsometryEquiv.norm_map]
  exact (contDiffAt_sphereBoost (cosh_add_sinh_mul_inner_pos hu hx' _).ne').comp (s, x)
    ((hα.comp contDiff_fst).prodMk hQ).contDiffAt

/-- Level by level, the rotation `Q s` followed by the boost of rapidity `α s` toward the unit
vector `u` is a diffeomorphism of `Sⁿ × ℝ` preserving the level `s`: its inverse at level `s` is
the boost of rapidity `-α s` followed by `(Q s)⁻¹`. -/
def boostRotateDiffeomorph (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) :
    (sphere (0 : E) 1 × ℝ) ≃ₘ^∞⟮(𝓡 n).prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ)⟯ (sphere (0 : E) 1 × ℝ) where
  toFun p := (⟨boostRotate u α Q (p.2, p.1), mem_sphere_zero_iff_norm.2
    (norm_boostRotate hu _ (norm_eq_of_mem_sphere p.1))⟩, p.2)
  invFun p := (⟨(Q p.2).symm (sphereBoost u (-α p.2) p.1), mem_sphere_zero_iff_norm.2 (by
    rw [LinearIsometryEquiv.norm_map]; exact norm_sphereBoost hu (norm_eq_of_mem_sphere p.1) _)⟩,
    p.2)
  left_inv p := by
    have hx : ‖Q p.2 p.1‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact norm_eq_of_mem_sphere _
    refine Prod.ext (Subtype.ext ?_) rfl
    simp only [boostRotate_apply]
    rw [sphereBoost_sphereBoost hu hx, neg_add_cancel, sphereBoost_zero, id,
      LinearIsometryEquiv.symm_apply_apply]
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) rfl
    simp only [boostRotate_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [sphereBoost_sphereBoost hu (norm_eq_of_mem_sphere p.1), add_neg_cancel, sphereBoost_zero,
      id]
  contMDiff_toFun := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine ContMDiff.codRestrict_sphere (fun p => ?_) _
    have hin : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × E) ∞
        fun p : sphere (0 : E) 1 × ℝ => (p.2, (p.1 : E)) :=
      contMDiff_snd.prodMk_space (contMDiff_coe_sphere.comp contMDiff_fst)
    exact (contDiffAt_boostRotate hu hα hQ p.2 (norm_eq_of_mem_sphere p.1)).contMDiffAt.comp p
      (hin p)
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine ContMDiff.codRestrict_sphere (fun p => ?_) _
    have hb : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
        (fun p : sphere (0 : E) 1 × ℝ => sphereBoost u (-α p.2) p.1) p := by
      have hin : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × E) ∞
          fun p : sphere (0 : E) 1 × ℝ => (-α p.2, (p.1 : E)) :=
        ((hα.contMDiff.comp contMDiff_snd).neg).prodMk_space
          (contMDiff_coe_sphere.comp contMDiff_fst)
      exact (contDiffAt_sphereBoost (cosh_add_sinh_mul_inner_pos hu
        (norm_eq_of_mem_sphere p.1) _).ne').contMDiffAt.comp p (hin p)
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    exact (ContDiff.linearIsometryEquiv_symm_apply hQ).contMDiff.contMDiffAt.comp p
      ((contMDiff_snd p).prodMk_space hb)

/-- The sphere component of `boostRotateDiffeomorph` is `boostRotate` at the level of the
point. -/
@[simp]
theorem coe_boostRotateDiffeomorph_apply_fst (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (p : sphere (0 : E) 1 × ℝ) :
    ((boostRotateDiffeomorph (n := n) hu hα hQ p).1 : E) = boostRotate u α Q (p.2, p.1) :=
  (rfl)

/-- `boostRotateDiffeomorph` preserves the levels. -/
@[simp]
theorem boostRotateDiffeomorph_apply_snd (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (p : sphere (0 : E) 1 × ℝ) :
    (boostRotateDiffeomorph (n := n) hu hα hQ p).2 = p.2 :=
  (rfl)

/-- The sphere component of the inverse of `boostRotateDiffeomorph` is the boost of rapidity
`-α s` followed by `(Q s)⁻¹`, at the level `s` of the point. -/
@[simp]
theorem coe_boostRotateDiffeomorph_symm_apply_fst (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (p : sphere (0 : E) 1 × ℝ) :
    (((boostRotateDiffeomorph (n := n) hu hα hQ).symm p).1 : E) =
      (Q p.2).symm (sphereBoost u (-α p.2) p.1) :=
  (rfl)

/-- The inverse of `boostRotateDiffeomorph` preserves the levels. -/
@[simp]
theorem boostRotateDiffeomorph_symm_apply_snd (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (p : sphere (0 : E) 1 × ℝ) :
    ((boostRotateDiffeomorph (n := n) hu hα hQ).symm p).2 = p.2 :=
  (rfl)

/-- At a point `-u` fixed by every `Q s`, the derivative of `boostRotate` in a direction `(0, ξ)`
with `Q s ξ` tangent to the sphere at `-u` is `Q s ξ` stretched by `exp (α s)`. -/
theorem fderiv_boostRotate_apply_zero (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (s : ℝ) (hQu : Q s (-u) = -u) {ξ : E}
    (hξ : ⟪Q s ξ, u⟫ = 0) :
    fderiv ℝ (boostRotate u α Q) (s, -u) (0, ξ) = exp (α s) • Q s ξ := by
  have hD := ((contDiffAt_boostRotate hu hα hQ s (by rw [norm_neg, hu])).differentiableAt
    (by simp)).hasFDerivAt
  -- The slice `x ↦ boostRotate u α Q (s, x)` is the boost after the linear isometry `Q s`.
  have h₁ := hD.comp (-u) (hasFDerivAt_prodMk_right s (-u))
  have hB : HasFDerivAt (sphereBoost u (α s)) (fderiv ℝ (sphereBoost u (α s)) (-u)) (Q s (-u)) := by
    rw [hQu]
    exact (differentiableAt_sphereBoost (cosh_add_sinh_mul_inner_pos hu
      (by rw [norm_neg, hu]) _).ne').hasFDerivAt
  have h₂ := hB.comp (-u) (Q s).toContinuousLinearEquiv.hasFDerivAt
  have h := congrArg (fun L : E →L[ℝ] E => L ξ) (h₁.unique h₂)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inr_apply] at h
  rw [h]
  exact fderiv_sphereBoost_neg_self_apply hu _ hξ

end TauCeti
