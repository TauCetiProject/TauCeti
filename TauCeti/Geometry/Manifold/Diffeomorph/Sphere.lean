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
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
* `TauCeti.hasDerivAt_boostRotate_comp`: the derivative of the rotation and boost along a curve
  through the fixed point.
* `TauCeti.exists_diffeomorph_apply_eq`: a level-preserving diffeomorphism of `Sⁿ × ℝ` turning a
  smooth family of velocities at a fixed point into a single one.
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

/-- The derivative at `(t, v)` of the rotation by `Q t` followed by the boost toward `-v` of
rapidity `α t = log (‖W‖ / ‖A‖)`, in the direction `(0, A)` for `A` orthogonal to `v`, is `W`
when `Q t` turns the direction of `A` into that of `W`. Read along a curve through `v` with
velocity `A` at a fixed time, this gives the velocity of the image curve. -/
theorem hasDerivAt_boostRotate_comp {v A W : E} {α : ℝ → ℝ}
    {Q : ℝ → E ≃ₗᵢ[ℝ] E} (hv' : ‖-v‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) {t : ℝ} (hQv : Q t v = v) (hAv : ⟪A, v⟫ = 0)
    (hA0 : A ≠ 0) (hW : W ≠ 0) (hdir : ‖A‖⁻¹ • Q t A = ‖W‖⁻¹ • W)
    (hαt : α t = Real.log (‖W‖ / ‖A‖)) {c : ℝ → E} {s : ℝ → ℝ} {θ₀ : ℝ}
    (hc : HasDerivAt c A θ₀) (hs : HasDerivAt s 0 θ₀) (hc₀ : c θ₀ = v) (hs₀ : s θ₀ = t) :
    HasDerivAt (fun θ => boostRotate (-v) α Q (s θ, c θ)) W θ₀ := by
  have hBR := ((contDiffAt_boostRotate hv' hα hQ t (by rwa [norm_neg] at hv')).differentiableAt
    (by simp)).hasFDerivAt
  have hD := hBR.comp_hasDerivAt_of_eq θ₀ (hs.prodMk hc) (by rw [hs₀, hc₀])
  have hval := fderiv_boostRotate_apply_zero hv' hα hQ t (by rw [neg_neg, hQv]) (ξ := A)
    (by rw [inner_neg_right, ← hQv, LinearIsometryEquiv.inner_map_map, hAv, neg_zero])
  rw [neg_neg, hαt, Real.exp_log (div_pos (norm_pos_iff.2 hW) (norm_pos_iff.2 hA0))] at hval
  rwa [hval, norm_div_norm_smul_eq_of_inv_norm_smul_eq_normalize hdir] at hD

/-- **The rotation and boost.** For a smooth family `A t` of nonzero vectors orthogonal to the unit
vector `v` (in dimension at least `3`), there is a diffeomorphism `Ψ` of `Sⁿ × ℝ` preserving the
levels, which fixes the points over `v` and the levels where `A t = A 0`, and whose derivative
turns the velocity `A t` of a curve through `v` at level `t` into `A 0`. -/
theorem exists_diffeomorph_apply_eq {v W : E} (hn : 3 ≤ n) (hv : ‖v‖ = 1) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) (hA0 : ∀ t, A t ≠ 0) (hAv : ∀ t, ⟪A t, v⟫ = 0) (hAW : A 0 = W) :
    ∃ Ψ : (sphere (0 : E) 1 × ℝ) ≃ₘ^∞⟮(𝓡 n).prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ)⟯
        (sphere (0 : E) 1 × ℝ),
      (∀ p, (Ψ p).2 = p.2) ∧ (∀ t, A t = W → ∀ y, Ψ (y, t) = (y, t)) ∧
      (∀ (y : sphere (0 : E) 1) t, (y : E) = v → Ψ (y, t) = (y, t)) ∧
      ∀ (t : ℝ) (c : ℝ → sphere (0 : E) 1) (s : ℝ → ℝ) (θ₀ : ℝ), (c θ₀ : E) = v → s θ₀ = t →
        HasDerivAt (fun θ => (c θ : E)) (A t) θ₀ → HasDerivAt s 0 θ₀ →
          HasDerivAt (fun θ => ((Ψ (c θ, s θ)).1 : E)) W θ₀ := by
  have hW : W ≠ 0 := hAW ▸ hA0 0
  set u : ℝ → E := fun t => ‖A t‖⁻¹ • A t with hu_def
  have hu : ContDiff ℝ ∞ u :=
    ((hA.norm ℝ hA0).inv fun t => norm_ne_zero_iff.2 (hA0 t)).smul hA
  have hut' (t : ℝ) : ‖A t‖⁻¹ • A t = u t := (congrFun hu_def t).symm
  have hu0 : u 0 = ‖W‖⁻¹ • W := by simp only [hu_def, hAW]
  have hfin : 2 < finrank ℝ (ℝ ∙ v)ᗮ := by
    rw [Submodule.finrank_orthogonal_span_singleton (n := n)
      (norm_ne_zero_iff.1 (hv.symm ▸ one_ne_zero))]
    omega
  obtain ⟨Q, hQ, hQv, hQu, hQ1⟩ := exists_contDiff_linearIsometryEquiv_apply_eq (k := ∞)
    (by simp) hfin hu (fun t => norm_smul_inv_norm (hA0 t)) 
    (fun t => by rw [hu_def, real_inner_smul_left, hAv, mul_zero]) 0
  set α : ℝ → ℝ := fun t => Real.log (‖W‖ / ‖A t‖) with hα_def
  have hα : ContDiff ℝ ∞ α :=
    (contDiff_const.div (hA.norm ℝ hA0) fun t => norm_ne_zero_iff.2 (hA0 t)).log fun t =>
      (div_pos (norm_pos_iff.2 hW) (norm_pos_iff.2 (hA0 t))).ne'
  have hv' : ‖-v‖ = 1 := by rw [norm_neg, hv]
  have hΨ₁ (p : sphere (0 : E) 1 × ℝ) :
      ((boostRotateDiffeomorph (n := n) hv' hα hQ p).1 : E) = boostRotate (-v) α Q (p.2, p.1) :=
    coe_boostRotateDiffeomorph_apply_fst hv' hα hQ p
  have hΨ₂ (p : sphere (0 : E) 1 × ℝ) : (boostRotateDiffeomorph (n := n) hv' hα hQ p).2 = p.2 :=
    boostRotateDiffeomorph_apply_snd hv' hα hQ p
  refine ⟨boostRotateDiffeomorph (n := n) hv' hα hQ, hΨ₂, fun t hAt y => ?_, fun y t hy => ?_,
    fun t c s θ₀ hc₀ hs₀ hc hs => ?_⟩
  · have hut : u t = u 0 := by simp only [hu_def, hAt, hAW]
    refine Prod.ext (Subtype.ext ?_) (hΨ₂ _)
    simp only [hΨ₁, boostRotate_apply, hQ1 t hut, hα_def, hAt, div_self (norm_ne_zero_iff.2 hW),
      Real.log_one, sphereBoost_zero, _root_.id]
  · refine Prod.ext (Subtype.ext ?_) (hΨ₂ _)
    have h := sphereBoost_neg_self hv' (α t)
    rw [neg_neg] at h
    simp only [hΨ₁, boostRotate_apply]
    rw [hy, hQv, h]
  · have hdir : ‖A t‖⁻¹ • Q t (A t) = ‖W‖⁻¹ • W := by
      rw [← map_smul, hut' t, hQu, hu0]
    simp only [hΨ₁]
    exact hasDerivAt_boostRotate_comp hv' hα hQ (hQv t) (hAv t) (hA0 t) hW hdir rfl hc hs hc₀ hs₀

end TauCeti
