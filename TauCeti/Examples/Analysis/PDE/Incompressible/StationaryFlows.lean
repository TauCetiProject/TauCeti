/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.PlaneWave
import TauCeti.LinearAlgebra.Determinant.RankOne

/-!
# Checks: shear, strain and Beltrami flows

Three families of explicit velocity fields solve the incompressible Euler equations
`∂ₜu + (u·∇)u + ∇p = 0`, `div u = 0` pointwise. None of them has finite energy unless it
vanishes, so they test the pointwise (classical) form of the equations, the sign conventions for
vorticity, and the interplay between the convective term `(u·∇)u = ∇u (u)`, the pressure and the
Laplacian.

**Shear flows.** For orthogonal vectors `v` and `w` and a profile `g : ℝ → ℝ`, the field
`u x = g ⟪v, x⟫ • w` moves each hyperplane orthogonal to `v` rigidly in the direction `w`; on
`ℝ²` with `v = e₂` and `w = e₁` it is `u = (g(x₂), 0)`.

* The convective term vanishes identically (`TauCeti.fderiv_comp_inner_smul_apply_self`), with
  no regularity of `g`, so `u` with zero pressure is a stationary Euler solution. It is
  divergence-free (`TauCeti.trace_fderiv_comp_inner_smul`).
* For unit vectors `w` and `v`, its vorticity `∂₁u₂ − ∂₂u₁ = ⟪∇u w, v⟫ − ⟪∇u v, w⟫` in the frame
  `(w, v)` is `−g'(⟪v, x⟫)` (`TauCeti.inner_fderiv_comp_inner_smul_sub`); on `ℝ²`, `ω = −g'(x₂)`.
* Its flow map is `X(α, t) = α + t g(⟪v, α⟫) w`, on `ℝ²` the map `(α₁ + t g(α₂), α₂)`
  (`TauCeti.hasDerivAt_add_mul_smul`). Its Jacobian determinant is `1` for every `t`
  (`TauCeti.det_fderiv_add_mul_smul`), while the Jacobian itself is unbounded in `t` wherever
  `g' ≠ 0` (`TauCeti.tendsto_norm_fderiv_add_mul_smul`). For a single time the flow map is the
  shear `TauCeti.planeShear` of `ℝ × ℝ`, up to the order of the coordinates.

**Bernoulli pressure.** If the antisymmetric part of `∇u` annihilates `u`, then
`(u·∇)u = (∇u)† u = ∇(‖u‖² / 2)`, so `u` with the pressure `p = −‖u‖² / 2` is a stationary Euler
solution (`TauCeti.fderiv_apply_self_add_gradient_neg_norm_sq_div_two_eq_zero`). This covers the
two remaining families.

**Strain flows.** A self-adjoint linear field `u = L` is irrotational and solves the stationary
Euler equations with `p = −‖L x‖² / 2`
(`ContinuousLinearMap.fderiv_apply_self_add_gradient_neg_norm_sq_div_two_eq_zero`). On `ℝ³` the
strain `u = (−γ₁x₁, −γ₂x₂, (γ₁ + γ₂)x₃)` is trace-free and self-adjoint
(`TauCeti.trace_fderiv_strain`, `TauCeti.isSelfAdjoint_fderiv_strain`), and since `Δu = 0` it
solves the Navier–Stokes equations `(u·∇)u + ∇p = νΔu` for every viscosity `ν`, with
`p = −½(γ₁²x₁² + γ₂²x₂² + (γ₁ + γ₂)²x₃²)`
(`TauCeti.fderiv_strain_apply_add_gradient_eq_smul_laplacian`).

**Beltrami flows.** The Arnold–Beltrami–Childress field `TauCeti.abcField A B C`,
`u = (A sin x₃ + C cos x₂, B sin x₁ + A cos x₃, C sin x₂ + B cos x₁)`, is its own curl: the
antisymmetric part of its derivative is `∇u h − (∇u)† h = u × h`
(`TauCeti.fderiv_abcField_sub_adjoint_apply`). It is divergence-free
(`TauCeti.trace_fderiv_abcField`), and with `p = −‖u‖² / 2` it is a stationary Euler solution
(`TauCeti.fderiv_abcField_apply_self_add_gradient_eq_zero`). It also satisfies `Δu = −u`
(`TauCeti.laplacian_abcField`), and a stationary Euler solution with `Δu = −μ u` decays into a
Navier–Stokes solution `(e^{−νμt} u, e^{−2νμt} p)`
(`TauCeti.deriv_add_fderiv_add_gradient_eq_smul_laplacian_of_laplacian_eq_neg_smul`); for the ABC
field this is `TauCeti.deriv_add_fderiv_abcField_add_gradient_eq_smul_laplacian`.

## References

* A. J. Majda, A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University Press,
  2002, Chapters 1 and 2.
* T. Dombre, U. Frisch, J. M. Greene, M. Hénon, A. Mehr, A. M. Soward, *Chaotic streamlines in
  the ABC flows*, J. Fluid Mech. 167 (1986), 353–391.
-/

public section

open Filter Real WithLp
open scoped Gradient InnerProductSpace Laplacian Matrix

namespace TauCeti

section Shear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : ℝ → ℝ} {v w : E}

/-- The derivative of the shear flow `y ↦ g ⟪v, y⟫ • w` for differentiable `g`. -/
private theorem hasFDerivAt_comp_inner_smul {x : E} (hg : DifferentiableAt ℝ g ⟪v, x⟫_ℝ) :
    HasFDerivAt (fun y ↦ g ⟪v, y⟫_ℝ • w)
      ((deriv g ⟪v, x⟫_ℝ • innerSL ℝ v).smulRight w) x :=
  (hg.hasDerivAt.comp_hasFDerivAt x (innerSL ℝ v).hasFDerivAt).smul_const w

/-- **The convective term of a shear flow vanishes.** If `⟪v, w⟫ = 0`, the shear flow
`u y = g ⟪v, y⟫ • w` satisfies `(u·∇)u = 0` everywhere, for every function `g`; with zero
pressure it is a stationary solution of the Euler equations. -/
theorem fderiv_comp_inner_smul_apply_self (hvw : ⟪v, w⟫_ℝ = 0) (x : E) :
    fderiv ℝ (fun y ↦ g ⟪v, y⟫_ℝ • w) x (g ⟪v, x⟫_ℝ • w) = 0 := by
  have h := fderiv_comp_inner (fun s ↦ g s • w) v x
  simp [h, hvw]

/-- **A shear flow is divergence-free.** If `⟪v, w⟫ = 0` and `g` is differentiable at `⟪v, x⟫`,
the shear flow `y ↦ g ⟪v, y⟫ • w` has trace-free derivative at `x`. -/
theorem trace_fderiv_comp_inner_smul [FiniteDimensional ℝ E] (hvw : ⟪v, w⟫_ℝ = 0) {x : E}
    (hg : DifferentiableAt ℝ g ⟪v, x⟫_ℝ) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ g ⟪v, y⟫_ℝ • w) x) = 0 := by
  rw [trace_fderiv_smul_const (χ := fun y ↦ g ⟪v, y⟫_ℝ)
    (hg.comp x (innerSL ℝ v).differentiableAt) w, fderiv_comp_inner]
  simp [hvw]

/-- **The vorticity of a shear flow.** If `⟪v, w⟫ = 0` and `g` is differentiable at `⟪v, x⟫`,
the antisymmetric part of the derivative of `u y = g ⟪v, y⟫ • w` satisfies
`⟪∇u w, v⟫ − ⟪∇u v, w⟫ = −‖v‖² ‖w‖² g'(⟪v, x⟫)`. For unit vectors this is the vorticity
`∂₁u₂ − ∂₂u₁ = −g'` in the frame `(w, v)`. -/
theorem inner_fderiv_comp_inner_smul_sub (hvw : ⟪v, w⟫_ℝ = 0) {x : E}
    (hg : DifferentiableAt ℝ g ⟪v, x⟫_ℝ) :
    ⟪fderiv ℝ (fun y ↦ g ⟪v, y⟫_ℝ • w) x w, v⟫_ℝ - ⟪fderiv ℝ (fun y ↦ g ⟪v, y⟫_ℝ • w) x v, w⟫_ℝ =
      -(‖v‖ ^ 2 * ‖w‖ ^ 2 * deriv g ⟪v, x⟫_ℝ) := by
  rw [(hasFDerivAt_comp_inner_smul hg).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply,
    innerSL_apply_apply, smul_eq_mul, inner_smul_left, hvw,
    real_inner_self_eq_norm_sq, RCLike.conj_to_real]
  ring

/-- **The flow map of a shear flow.** If `⟪v, w⟫ = 0`, the curve `t ↦ α + (t g ⟪v, α⟫) • w`
starting at `α` is an integral curve of the shear flow `u y = g ⟪v, y⟫ • w`: its velocity at
time `t` is `u` evaluated at its position. No regularity of `g` is needed. -/
theorem hasDerivAt_add_mul_smul (hvw : ⟪v, w⟫_ℝ = 0) (α : E) (t : ℝ) :
    HasDerivAt (fun s ↦ α + (s * g ⟪v, α⟫_ℝ) • w)
      (g ⟪v, α + (t * g ⟪v, α⟫_ℝ) • w⟫_ℝ • w) t := by
  have h : ⟪v, α + (t * g ⟪v, α⟫_ℝ) • w⟫_ℝ = ⟪v, α⟫_ℝ := by
    simp [inner_add_right, inner_smul_right, hvw]
  rw [h]
  simpa using ((hasDerivAt_id t).mul_const (g ⟪v, α⟫_ℝ)).smul_const w |>.const_add α

/-- The derivative of the time-`t` flow map `y ↦ y + (t g ⟪v, y⟫) • w` of a shear flow is the
identity plus a rank-one map. -/
private theorem hasFDerivAt_add_mul_smul {α : E} (hg : DifferentiableAt ℝ g ⟪v, α⟫_ℝ) (t : ℝ) :
    HasFDerivAt (fun y ↦ y + (t * g ⟪v, y⟫_ℝ) • w)
      (1 + (innerSL ℝ v).smulRight ((t * deriv g ⟪v, α⟫_ℝ) • w)) α := by
  have h := ((hg.hasDerivAt.comp_hasFDerivAt α (innerSL ℝ v).hasFDerivAt).const_mul t).smul_const w
  refine (hasFDerivAt_id α).add (h.congr_fderiv ?_)
  ext y
  simp [smul_smul, mul_comm]

/-- **The flow of a shear flow preserves volume.** If `⟪v, w⟫ = 0` and `g` is differentiable at
`⟪v, α⟫`, the time-`t` flow map `y ↦ y + (t g ⟪v, y⟫) • w` has Jacobian determinant `1` at `α`. -/
theorem det_fderiv_add_mul_smul (hvw : ⟪v, w⟫_ℝ = 0) {α : E}
    (hg : DifferentiableAt ℝ g ⟪v, α⟫_ℝ) (t : ℝ) :
    LinearMap.det (fderiv ℝ (fun y ↦ y + (t * g ⟪v, y⟫_ℝ) • w) α : E →ₗ[ℝ] E) = 1 := by
  rw [(hasFDerivAt_add_mul_smul hg t).fderiv]
  by_cases hfin : FiniteDimensional ℝ E
  swap
  · exact LinearMap.det_eq_one_of_not_module_finite hfin _
  rcases eq_or_ne (Module.finrank ℝ E) 0 with h | h
  · exact LinearMap.det_eq_one_of_finrank_eq_zero h _
  have hdet := LinearMap.det_smul_one_add_smulRight (Nat.pos_of_ne_zero h) (1 : ℝ)
    (innerSL ℝ v : E →ₗ[ℝ] ℝ) ((t * deriv g ⟪v, α⟫_ℝ) • w)
  simp only [one_smul, one_pow, one_mul, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
    inner_smul_right, hvw, mul_zero, add_zero] at hdet
  rw [← hdet]
  congr 1

/-- **The deformation of a shear flow grows without bound.** If `v` and `w` are nonzero and
`g` has nonzero derivative at `⟪v, α⟫`, the Jacobian of the time-`t` flow map
`y ↦ y + (t g ⟪v, y⟫) • w` at `α` tends to infinity in norm as `t → ∞`. -/
theorem tendsto_norm_fderiv_add_mul_smul (hv : v ≠ 0) (hw : w ≠ 0) {α : E}
    (hg : DifferentiableAt ℝ g ⟪v, α⟫_ℝ) (hg' : deriv g ⟪v, α⟫_ℝ ≠ 0) :
    Tendsto (fun t : ℝ ↦ ‖fderiv ℝ (fun y ↦ y + (t * g ⟪v, y⟫_ℝ) • w) α‖) atTop atTop := by
  set c := |deriv g ⟪v, α⟫_ℝ| * ‖v‖ * ‖w‖
  have hc : 0 < c := by positivity
  refine tendsto_atTop_mono (fun t ↦ ?_)
    (tendsto_atTop_add_const_right _ (-1) (tendsto_id.const_mul_atTop hc))
  rw [(hasFDerivAt_add_mul_smul hg t).fderiv]
  set D : E →L[ℝ] E := 1 + (innerSL ℝ v).smulRight ((t * deriv g ⟪v, α⟫_ℝ) • w)
  -- `D v = v + a` for the vector `a = ‖v‖² t g' w`, of norm `‖v‖ c |t|`.
  set a : E := (‖v‖ ^ 2 * (t * deriv g ⟪v, α⟫_ℝ)) • w
  have hDv : D v = v + a := by
    simp [D, a, smul_smul]
  have ha : ‖a‖ = ‖v‖ * (c * |t|) := by
    simp only [a, c, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
    ring
  have hle : ‖a‖ ≤ ‖D‖ * ‖v‖ + ‖v‖ :=
    calc ‖a‖ = ‖D v - v‖ := by rw [hDv, add_sub_cancel_left]
      _ ≤ ‖D v‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ ‖D‖ * ‖v‖ + ‖v‖ := by gcongr; exact D.le_opNorm v
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hct : c * |t| ≤ ‖D‖ + 1 := le_of_mul_le_mul_left (by rw [← ha]; linarith) hv'
  have : c * t ≤ c * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) hc.le
  simp only [id]
  linarith

end Shear

section Bernoulli

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Bernoulli pressure for a vanishing Lamb vector.** If the antisymmetric part of the
derivative of `u` annihilates `u x`, that is `∇u (u x) = (∇u)† (u x)`, then the velocity `u`
with the pressure `p y = −‖u y‖² / 2` satisfies the stationary Euler equation
`(u·∇)u + ∇p = 0` at `x`: in general `∇(‖u‖² / 2) = (∇u)† u`. -/
theorem fderiv_apply_self_add_gradient_neg_norm_sq_div_two_eq_zero {u : E → E} {x : E}
    (hu : DifferentiableAt ℝ u x)
    (h : fderiv ℝ u x (u x) = ContinuousLinearMap.adjoint (fderiv ℝ u x) (u x)) :
    fderiv ℝ u x (u x) + ∇ (fun y ↦ -(‖u y‖ ^ 2 / 2)) x = 0 := by
  have hp : HasGradientAt (fun y ↦ -(‖u y‖ ^ 2 / 2))
      (-ContinuousLinearMap.adjoint (fderiv ℝ u x) (u x)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine ((hu.hasFDerivAt.norm_sq.const_mul (-(1 / 2) : ℝ)).congr_of_eventuallyEq
      (.of_forall fun y ↦ by ring)).congr_fderiv ?_
    ext k
    simp [ContinuousLinearMap.adjoint_inner_left]
  rw [hp.gradient, h, add_neg_cancel]

/-- **Irrotational linear flows solve the Euler equations.** A self-adjoint linear velocity
field `u = L`, with pressure `p y = −‖L y‖² / 2`, satisfies the stationary Euler equation
`(u·∇)u + ∇p = 0` everywhere: `(u·∇)u = L (L x) = L† (L x) = −∇p`. -/
theorem _root_.ContinuousLinearMap.fderiv_apply_self_add_gradient_neg_norm_sq_div_two_eq_zero
    (L : E →L[ℝ] E) (hL : IsSelfAdjoint L) (x : E) :
    fderiv ℝ L x (L x) + ∇ (fun y ↦ -(‖L y‖ ^ 2 / 2)) x = 0 :=
  TauCeti.fderiv_apply_self_add_gradient_neg_norm_sq_div_two_eq_zero L.differentiableAt
    (by rw [L.fderiv, hL.adjoint_eq])

end Bernoulli

section Strain

/-- The strain field `(−γ₁x₁, −γ₂x₂, (γ₁ + γ₂)x₃)` is the diagonal matrix
`diag(−γ₁, −γ₂, γ₁ + γ₂)` acting on `ℝ³`. -/
private theorem strain_eq_toEuclideanCLM (γ₁ γ₂ : ℝ) :
    (fun x : EuclideanSpace ℝ (Fin 3) ↦ !₂[-γ₁ * x 0, -γ₂ * x 1, (γ₁ + γ₂) * x 2]) =
      ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal ![-γ₁, -γ₂, γ₁ + γ₂])) := by
  funext x
  ext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]

/-- **The strain flow is irrotational**: its derivative is self-adjoint. -/
theorem isSelfAdjoint_fderiv_strain (γ₁ γ₂ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    IsSelfAdjoint (fderiv ℝ
      (fun y : EuclideanSpace ℝ (Fin 3) ↦ !₂[-γ₁ * y 0, -γ₂ * y 1, (γ₁ + γ₂) * y 2]) x) := by
  rw [strain_eq_toEuclideanCLM, ContinuousLinearMap.fderiv]
  exact (Matrix.isHermitian_diagonal _).isSelfAdjoint.map _

/-- **The strain flow is divergence-free**: its derivative has trace
`−γ₁ − γ₂ + (γ₁ + γ₂) = 0`. -/
theorem trace_fderiv_strain (γ₁ γ₂ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (fderiv ℝ
      (fun y : EuclideanSpace ℝ (Fin 3) ↦ !₂[-γ₁ * y 0, -γ₂ * y 1, (γ₁ + γ₂) * y 2]) x) = 0 := by
  rw [strain_eq_toEuclideanCLM, ContinuousLinearMap.fderiv,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [ContinuousLinearMap.coe_coe, ← strain_eq_toEuclideanCLM]
  simp [Fin.sum_univ_three, EuclideanSpace.inner_single_left]
  ring

/-- **The strain flow solves the Navier–Stokes equations.** On `ℝ³`, the stationary velocity
`u = (−γ₁x₁, −γ₂x₂, (γ₁ + γ₂)x₃)` with pressure `p = −½(γ₁²x₁² + γ₂²x₂² + (γ₁ + γ₂)²x₃²)`
satisfies `(u·∇)u + ∇p = νΔu` for every viscosity `ν`; both sides vanish, since `Δu = 0`. -/
theorem fderiv_strain_apply_add_gradient_eq_smul_laplacian (γ₁ γ₂ ν : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) ↦ !₂[-γ₁ * y 0, -γ₂ * y 1, (γ₁ + γ₂) * y 2]) x
        !₂[-γ₁ * x 0, -γ₂ * x 1, (γ₁ + γ₂) * x 2] +
      ∇ (fun y : EuclideanSpace ℝ (Fin 3) ↦
        -((γ₁ ^ 2 * y 0 ^ 2 + γ₂ ^ 2 * y 1 ^ 2 + (γ₁ + γ₂) ^ 2 * y 2 ^ 2) / 2)) x =
      ν • Δ (fun y : EuclideanSpace ℝ (Fin 3) ↦ !₂[-γ₁ * y 0, -γ₂ * y 1, (γ₁ + γ₂) * y 2]) x := by
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal ![-γ₁, -γ₂, γ₁ + γ₂])
  have hp : (fun y : EuclideanSpace ℝ (Fin 3) ↦
      -((γ₁ ^ 2 * y 0 ^ 2 + γ₂ ^ 2 * y 1 ^ 2 + (γ₁ + γ₂) ^ 2 * y 2 ^ 2) / 2)) =
      fun y ↦ -(‖L y‖ ^ 2 / 2) := by
    funext y
    rw [← congrFun (strain_eq_toEuclideanCLM γ₁ γ₂) y, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_three]
    ring
  have hL : IsSelfAdjoint L := (Matrix.isHermitian_diagonal _).isSelfAdjoint.map _
  have hx := congrFun (strain_eq_toEuclideanCLM γ₁ γ₂) x
  simp only at hx
  rw [hx, hp, strain_eq_toEuclideanCLM, L.laplacian, Pi.zero_apply, smul_zero]
  exact L.fderiv_apply_self_add_gradient_neg_norm_sq_div_two_eq_zero hL x

end Strain

section Decay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Decaying eigenfields of stationary Euler flows solve Navier–Stokes.** Suppose that `(u, p)`
satisfies the stationary Euler equation `(u·∇)u + ∇p = 0` at `x` and that `Δu = −μ u` at `x`.
Then for every viscosity `ν` the velocity `U t = e^{−νμt} u` with pressure `P t = e^{−2νμt} p`
satisfies the Navier–Stokes momentum equation `∂ₜU + (U·∇)U + ∇P = νΔU` at `(t, x)`. -/
theorem deriv_add_fderiv_add_gradient_eq_smul_laplacian_of_laplacian_eq_neg_smul
    {u : E → E} {p : E → ℝ} {x : E} {μ : ℝ} (hu : ContDiffAt ℝ 2 u x)
    (hE : fderiv ℝ u x (u x) + ∇ p x = 0) (hΔ : Δ u x = -μ • u x) (ν t : ℝ) :
    deriv (fun s ↦ exp (-(ν * μ * s)) • u x) t +
        fderiv ℝ (fun y ↦ exp (-(ν * μ * t)) • u y) x (exp (-(ν * μ * t)) • u x) +
        ∇ (fun y ↦ exp (-(2 * ν * μ * t)) * p y) x =
      ν • Δ (fun y ↦ exp (-(ν * μ * t)) • u y) x := by
  set c := exp (-(ν * μ * t))
  have hd : deriv (fun s ↦ exp (-(ν * μ * s)) • u x) t = (-(ν * μ) * c) • u x := by
    have h : HasDerivAt (fun s : ℝ ↦ -(ν * μ * s)) (-(ν * μ)) t :=
      ((hasDerivAt_id t).const_mul (ν * μ)).neg.congr_deriv (by simp)
    rw [(h.exp.smul_const (u x)).deriv, mul_comm]
  have hc : exp (-(2 * ν * μ * t)) = c * c := by
    rw [← exp_add]
    ring_nf
  have hF : fderiv ℝ (fun y ↦ c • u y) x = c • fderiv ℝ u x :=
    congrFun (fderiv_const_smul_field (f := u) c) x
  have hG : ∇ (fun y ↦ c * c * p y) x = (c * c) • ∇ p x := gradient_const_smul (f := p) (c * c)
  have hL : Δ (fun y ↦ c • u y) x = c • Δ u x := InnerProductSpace.laplacian_smul c hu
  rw [hd, hF, hc, hG, hL, hΔ, smul_apply, map_smul,
    eq_neg_of_add_eq_zero_left hE]
  module

end Decay

section Beltrami

/-- The **Arnold–Beltrami–Childress (ABC) field** on `ℝ³` with amplitudes `A`, `B`, `C`. In the
usual numbering `x₁, x₂, x₃` of the coordinates (here `x 0`, `x 1`, `x 2`) it is
`u = (A sin x₃ + C cos x₂, B sin x₁ + A cos x₃, C sin x₂ + B cos x₁)`. It is a Beltrami field:
it equals its own curl. -/
noncomputable def abcField (A B C : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[A * sin (x 2) + C * cos (x 1), B * sin (x 0) + A * cos (x 2), C * sin (x 1) + B * cos (x 0)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The circular plane wave `x ↦ sin ⟪v, x⟫ • a + cos ⟪v, x⟫ • b`. -/
private noncomputable def wave (a b v : E) : E → E :=
  fun x ↦ sin ⟪v, x⟫_ℝ • a + cos ⟪v, x⟫_ℝ • b

/-- The profile `s ↦ sin s • a + cos s • b` of a circular wave differentiates to the profile with
coefficients `(-b, a)`. -/
private theorem hasDerivAt_sin_smul_add_cos_smul (a b : E) (s : ℝ) :
    HasDerivAt (fun s ↦ sin s • a + cos s • b) (sin s • -b + cos s • a) s := by
  convert ((hasDerivAt_sin s).smul_const a).add ((hasDerivAt_cos s).smul_const b) using 1
  simp only [smul_neg, neg_smul]
  abel

private theorem hasFDerivAt_wave (a b v x : E) :
    HasFDerivAt (wave a b v) ((innerSL ℝ v).smulRight (wave (-b) a v x)) x := by
  refine ((hasDerivAt_sin_smul_add_cos_smul a b _).hasFDerivAt.comp x
    (innerSL ℝ v).hasFDerivAt).congr_fderiv ?_
  ext h
  simp [wave]

private theorem contDiff_wave (a b v : E) {n : WithTop ℕ∞} : ContDiff ℝ n (wave a b v) :=
  ((contDiff_sin.smul contDiff_const).add (contDiff_cos.smul contDiff_const)).comp
    (innerSL ℝ v).contDiff

private theorem laplacian_wave [FiniteDimensional ℝ E] (a b v x : E) :
    Δ (wave a b v) x = -(‖v‖ ^ 2 • wave a b v x) := by
  have hd (a b : E) : deriv (fun s ↦ sin s • a + cos s • b) = fun s ↦ sin s • -b + cos s • a :=
    funext fun s ↦ (hasDerivAt_sin_smul_add_cos_smul a b s).deriv
  have h : Δ (wave a b v) x = ‖v‖ ^ 2 • deriv (deriv fun s ↦ sin s • a + cos s • b) ⟪v, x⟫_ℝ :=
    laplacian_comp_inner (fun s ↦ sin s • a + cos s • b) v x
  rw [h, hd, hd, wave]
  module

/-- The ABC field is a sum of three circular plane waves along the coordinate axes. -/
private theorem abcField_eq (A B C : ℝ) :
    abcField A B C =
      wave (A • EuclideanSpace.single 0 1) (A • EuclideanSpace.single 1 1)
          (EuclideanSpace.single 2 1) +
        wave (B • EuclideanSpace.single 1 1) (B • EuclideanSpace.single 2 1)
          (EuclideanSpace.single 0 1) +
        wave (C • EuclideanSpace.single 2 1) (C • EuclideanSpace.single 0 1)
          (EuclideanSpace.single 1 1) := by
  funext x
  ext i
  fin_cases i <;> simp [abcField, wave, EuclideanSpace.inner_single_left] <;> ring

/-- The ABC field is smooth. -/
theorem contDiff_abcField (A B C : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (abcField A B C) := by
  rw [abcField_eq]
  exact ((contDiff_wave _ _ _).add (contDiff_wave _ _ _)).add (contDiff_wave _ _ _)

/-- **The derivative of the ABC field**, in coordinates indexed from `0`. -/
theorem fderiv_abcField_apply (A B C : ℝ) (x h : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (abcField A B C) x h =
      !₂[-C * sin (x 1) * h 1 + A * cos (x 2) * h 2, B * cos (x 0) * h 0 - A * sin (x 2) * h 2,
        -B * sin (x 0) * h 0 + C * cos (x 1) * h 1] := by
  rw [abcField_eq, (((hasFDerivAt_wave _ _ _ x).add (hasFDerivAt_wave _ _ _ x)).add
    (hasFDerivAt_wave _ _ _ x)).fderiv]
  ext i
  fin_cases i <;> simp [wave, EuclideanSpace.inner_single_left] <;> ring

/-- **The ABC field is divergence-free.** -/
theorem trace_fderiv_abcField (A B C : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (fderiv ℝ (abcField A B C) x) = 0 := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [Fin.sum_univ_three, fderiv_abcField_apply, EuclideanSpace.inner_single_left]

/-- **The ABC field is its own curl.** The antisymmetric part of its derivative acts by the
cross product with the field itself: `∇u h − (∇u)† h = u × h`, so the vorticity vector of `u`
is `u`. -/
theorem fderiv_abcField_sub_adjoint_apply (A B C : ℝ) (x h : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (abcField A B C) x h - ContinuousLinearMap.adjoint (fderiv ℝ (abcField A B C) x) h =
      toLp 2 (ofLp (abcField A B C x) ⨯₃ ofLp h) := by
  refine ext_inner_right ℝ fun k ↦ ?_
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
  simp [fderiv_abcField_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, cross_apply, abcField]
  ring

/-- **The ABC field is an eigenfield of the Laplacian**: `Δu = −u`. -/
theorem laplacian_abcField (A B C : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    Δ (abcField A B C) x = -abcField A B C x := by
  have hw (a b v : EuclideanSpace ℝ (Fin 3)) : ContDiffAt ℝ 2 (wave a b v) x :=
    (contDiff_wave a b v).contDiffAt
  rw [abcField_eq, ContDiffAt.laplacian_add (show ContDiffAt ℝ 2 (_ + _) x from
    (hw _ _ _).add (hw _ _ _)) (hw _ _ _), (hw _ _ _).laplacian_add (hw _ _ _), laplacian_wave,
    laplacian_wave, laplacian_wave]
  simp only [(EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)).1, one_pow, one_smul,
    Pi.add_apply]
  abel

/-- **The ABC field is a stationary Euler flow.** With the Bernoulli pressure
`p = −‖u‖² / 2` it satisfies `(u·∇)u + ∇p = 0`, since its curl is parallel to it. -/
theorem fderiv_abcField_apply_self_add_gradient_eq_zero (A B C : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (abcField A B C) x (abcField A B C x) +
        ∇ (fun y ↦ -(‖abcField A B C y‖ ^ 2 / 2)) x = 0 := by
  refine fderiv_apply_self_add_gradient_neg_norm_sq_div_two_eq_zero
    ((contDiff_abcField A B C (n := 1)).differentiable one_ne_zero x) ?_
  rw [← sub_eq_zero, fderiv_abcField_sub_adjoint_apply, cross_self, toLp_zero]

/-- **The decaying ABC flow solves the Navier–Stokes equations.** For every viscosity `ν`, the
velocity `U t = e^{−νt} u` with pressure `P t = −e^{−2νt} ‖u‖² / 2`, where `u` is the ABC field,
satisfies `∂ₜU + (U·∇)U + ∇P = νΔU`; it is divergence-free by `TauCeti.trace_fderiv_abcField`. -/
theorem deriv_add_fderiv_abcField_add_gradient_eq_smul_laplacian (A B C ν t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    deriv (fun s ↦ exp (-(ν * s)) • abcField A B C x) t +
        fderiv ℝ (fun y ↦ exp (-(ν * t)) • abcField A B C y) x
          (exp (-(ν * t)) • abcField A B C x) +
        ∇ (fun y ↦ exp (-(2 * ν * t)) * -(‖abcField A B C y‖ ^ 2 / 2)) x =
      ν • Δ (fun y ↦ exp (-(ν * t)) • abcField A B C y) x := by
  simpa using deriv_add_fderiv_add_gradient_eq_smul_laplacian_of_laplacian_eq_neg_smul
    (μ := 1) (contDiff_abcField A B C).contDiffAt
    (fderiv_abcField_apply_self_add_gradient_eq_zero A B C x)
    (by rw [laplacian_abcField, neg_smul, one_smul]) ν t

end Beltrami

end TauCeti
