/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace

/-!
# Vorticity and the classical vorticity equation

The *vorticity* of a velocity field `u : E → E` on a real inner product space is the
antisymmetric part of its gradient, the skew-adjoint operator `Ω = ∇u − (∇u)†`, where
`∇u = fderiv ℝ u x` and `†` is the adjoint. In an orthonormal basis its entries are
`Ωⱼₖ = ∂ₖuⱼ − ∂ⱼuₖ`.

For a velocity `u` and pressure `p` satisfying the momentum equation of the incompressible Euler
equations, `∂ₜu + (u·∇)u + ∇p = 0`, pointwise near `x` at time `t`, with `u` jointly `C²` in
`(t, x)` and `p t` spatially `C²`, the vorticity satisfies the **vorticity equation**

`∂ₜΩ + (u·∇)Ω + Ω ∇u + (∇u)† Ω = 0`

at `(t, x)`. Here the convective term is the spatial derivative of `Ω` in the direction `u`. The
pressure drops out because its Hessian is self-adjoint. The equation needs no incompressibility.
Taking the trace of the differentiated momentum equation instead gives, for a velocity that is
divergence-free near `(t, x)`, the Poisson equation `−Δp = trace ((∇u)²)` for the pressure.

On an oriented two-dimensional space with rotation `J` by `π/2`, the vorticity is a multiple of
`J`: `Ω = ω J`, where the *scalar vorticity* `ω = −trace (J ∇u)` is `∂₁u₂ − ∂₂u₁` in every
positively oriented orthonormal frame. The vorticity equation then becomes the scalar equation
`∂ₜω + u·∇ω + ω div u = 0`, which for divergence-free `u` is the transport equation
`∂ₜω + u·∇ω = 0`. The rigid rotation `u x = J x` has scalar vorticity `2`.

## Main definitions

* `TauCeti.vorticity`: the vorticity tensor `∇u − (∇u)†`.
* `Orientation.scalarVorticity`: the scalar vorticity `ω` of a planar velocity field.

## Main results

* `TauCeti.deriv_vorticity_add_fderiv_vorticity_add_eq_zero`: the vorticity equation in every
  dimension.
* `TauCeti.neg_laplacian_eq_trace_fderiv_mul_fderiv`: the pressure Poisson equation
  `−Δp = trace ((∇u)²)` for divergence-free velocities.
* `Orientation.vorticity_eq_scalarVorticity_smul`: `Ω = ω J` in the plane.
* `Orientation.scalarVorticity_eq_inner_sub_inner`: `ω = ∂₁u₂ − ∂₂u₁` in an oriented frame.
* `Orientation.deriv_scalarVorticity_add_fderiv_scalarVorticity_add_mul_trace_eq_zero`:
  `∂ₜω + u·∇ω + ω div u = 0` in the plane.
* `Orientation.deriv_scalarVorticity_add_fderiv_scalarVorticity_eq_zero`: `∂ₜω + u·∇ω = 0` for
  divergence-free planar velocities.

## References

* A. J. Majda, A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University Press,
  2002, Chapter 1 (the vorticity equation, its two-dimensional form and the pressure Poisson
  equation).
* T. Tao, *254A: Incompressible fluid equations*, Notes 3, 2018 (the vorticity tensor as the
  antisymmetric part of the gradient in every dimension).
-/

public section

open Filter Topology ContinuousLinearMap Module
open scoped Gradient InnerProductSpace Laplacian

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section CompleteSpace

variable [CompleteSpace E]

/-- The **vorticity** of a velocity field `u` at `x`: the antisymmetric part `∇u − (∇u)†` of its
gradient, a skew-adjoint operator. In an orthonormal basis its entries are `∂ₖuⱼ − ∂ⱼuₖ`. -/
noncomputable def vorticity (u : E → E) (x : E) : E →L[ℝ] E :=
  fderiv ℝ u x - adjoint (fderiv ℝ u x)

theorem vorticity_def (u : E → E) (x : E) :
    vorticity u x = fderiv ℝ u x - adjoint (fderiv ℝ u x) :=
  (rfl)

/-- The vorticity paired with two vectors: `⟪Ω v, w⟫ = ⟪∇u v, w⟫ − ⟪v, ∇u w⟫`. -/
theorem inner_vorticity_apply (u : E → E) (x v w : E) :
    ⟪vorticity u x v, w⟫_ℝ = ⟪fderiv ℝ u x v, w⟫_ℝ - ⟪v, fderiv ℝ u x w⟫_ℝ := by
  rw [vorticity_def, sub_apply, inner_sub_left, adjoint_inner_left]

/-- The vorticity is skew-adjoint. -/
@[simp]
theorem adjoint_vorticity (u : E → E) (x : E) : adjoint (vorticity u x) = -vorticity u x := by
  rw [vorticity_def, map_sub, adjoint_adjoint, neg_sub]

/-- The vorticity vanishes exactly where the gradient is self-adjoint. -/
theorem vorticity_eq_zero_iff (u : E → E) (x : E) :
    vorticity u x = 0 ↔ IsSelfAdjoint (fderiv ℝ u x) := by
  rw [vorticity_def, sub_eq_zero, IsSelfAdjoint, star_eq_adjoint, eq_comm]

/-- **The velocity-gradient equation.** Differentiating the momentum equation
`∂ₜu + (u·∇)u + ∇p = 0` in space gives `∂ₜ∇u + (u·∇)∇u + (∇u)² + ∇²p = 0`, with a self-adjoint
Hessian `∇²p`. The time derivative of `∇u` is identified with the spatial derivative of `∂ₜu`
through the symmetry of mixed partial derivatives. -/
private theorem exists_hasDerivAt_fderiv {u : ℝ → E → E} {p : ℝ → E → ℝ} {t : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 (Function.uncurry u) (t, x)) (hp : ContDiffAt ℝ 2 (p t) x)
    (heq : ∀ᶠ y in 𝓝 x, deriv (fun s ↦ u s y) t + fderiv ℝ (u t) y (u t y) + ∇ (p t) y = 0) :
    ∃ Adot : E →L[ℝ] E, ∃ D : E →L[ℝ] E →L[ℝ] E,
      HasDerivAt (fun s ↦ fderiv ℝ (u s) x) Adot t ∧ HasFDerivAt (fderiv ℝ (u t)) D x ∧
      Adot + D (u t x) + fderiv ℝ (u t) x * fderiv ℝ (u t) x + fderiv ℝ (∇ (p t)) x = 0 := by
  have hu2 : ContDiffAt ℝ (minSmoothness ℝ 2) (Function.uncurry u) (t, x) := by simpa using hu
  have hnear : ∀ᶠ z in 𝓝 (t, x), DifferentiableAt ℝ (Function.uncurry u) z :=
    (hu.eventually (by simp)).mono fun z hz ↦ hz.differentiableAt (by simp)
  -- the time derivative of `∇u` and the spatial derivative of `∂ₜu` are the same operator
  have hAdot : HasDerivAt (fun s ↦ fderiv ℝ (u s) x)
      (fderiv ℝ (timeFDeriv (Function.uncurry u) t) x) t := by
    refine (hasDerivAt_spatialFDeriv hu2).congr_of_eventuallyEq ?_
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hnear] with s hs
    simpa using fderiv_timeSlice hs
  have hdt : HasFDerivAt (fun y ↦ deriv (fun s ↦ u s y) t)
      (fderiv ℝ (timeFDeriv (Function.uncurry u) t) x) x :=
    hu.differentiableAt_timeFDeriv.hasFDerivAt.congr_of_eventuallyEq
      (hu.of_le (by norm_num)).deriv_parameterCurve_eventuallyEq_timeFDeriv
  -- the spatial second derivatives of `u t` and `p t`
  have hut : ContDiffAt ℝ 2 (u t) x := hu.comp x (contDiff_prodMk_right t).contDiffAt
  have hA : HasFDerivAt (fderiv ℝ (u t)) (fderiv ℝ (fderiv ℝ (u t)) x) x :=
    ((hut.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD : ∀ v w, fderiv ℝ (fderiv ℝ (u t)) x v w = fderiv ℝ (fderiv ℝ (u t)) x w v :=
    hut.isSymmSndFDerivAt (by simp)
  have hH : HasFDerivAt (∇ (p t)) (fderiv ℝ (∇ (p t)) x) x :=
    ((hp.gradient_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨_, _, hAdot, hA, ?_⟩
  -- the momentum equation holds near `x`, so its spatial derivative at `x` vanishes
  have hF := (hdt.add (hA.clm_apply (hut.differentiableAt (by simp)).hasFDerivAt)).add hH
  have h0 : HasFDerivAt (fun y ↦ deriv (fun s ↦ u s y) t + fderiv ℝ (u t) y (u t y) + ∇ (p t) y)
      (0 : E →L[ℝ] E) x := (hasFDerivAt_const (0 : E) x).congr_of_eventuallyEq heq
  ext v
  have hv := congrArg (fun T : E →L[ℝ] E ↦ T v) (hF.unique h0)
  simp only [add_apply, comp_apply, flip_apply, zero_apply, mul_def] at hv ⊢
  rw [hD] at hv
  rw [← hv]
  abel

/-- The vorticity version of `exists_hasDerivAt_fderiv`: the vorticity is differentiable in time
and space at `(t, x)`, and its derivatives satisfy the vorticity equation. -/
private theorem exists_hasDerivAt_vorticity {u : ℝ → E → E} {p : ℝ → E → ℝ} {t : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 (Function.uncurry u) (t, x)) (hp : ContDiffAt ℝ 2 (p t) x)
    (heq : ∀ᶠ y in 𝓝 x, deriv (fun s ↦ u s y) t + fderiv ℝ (u t) y (u t y) + ∇ (p t) y = 0) :
    ∃ Ωdot : E →L[ℝ] E, ∃ Ω' : E →L[ℝ] E →L[ℝ] E,
      HasDerivAt (fun s ↦ vorticity (u s) x) Ωdot t ∧ HasFDerivAt (vorticity (u t)) Ω' x ∧
      Ωdot + Ω' (u t x) + vorticity (u t) x ∘L fderiv ℝ (u t) x +
        adjoint (fderiv ℝ (u t) x) ∘L vorticity (u t) x = 0 := by
  obtain ⟨Adot, D, hAdot, hD, hsum⟩ := exists_hasDerivAt_fderiv hu hp heq
  set H := fderiv ℝ (∇ (p t)) x
  -- the Hessian of the pressure is self-adjoint, so the pressure drops out of the vorticity
  have hH : IsSelfAdjoint H := isSelfAdjoint_iff_isSymmetric.mpr <|
    isSymmetric_of_hasFDerivAt_gradient
      ((hp.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp))
      ((hp.gradient_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hvort : ∀ (v : E → E) (y : E), vorticity v y = fderiv ℝ v y - star (fderiv ℝ v y) :=
    fun v y ↦ by rw [vorticity_def, star_eq_adjoint]
  refine ⟨Adot - star Adot, D - ((starL' ℝ : (E →L[ℝ] E) ≃L[ℝ] (E →L[ℝ] E)) :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)).comp D, ?_, ?_, ?_⟩
  · exact (hAdot.sub hAdot.star).congr_of_eventuallyEq (.of_forall fun s ↦ hvort _ _)
  · exact (hD.sub hD.star).congr_of_eventuallyEq (.of_forall fun y ↦ hvort _ _)
  -- the algebra: `∂ₜΩ + Ω'u = (∂ₜA + Du) − (∂ₜA + Du)†` and `∂ₜA + Du = −(∇u)² − ∇²p`
  set A := fderiv ℝ (u t) x
  have hkey : Adot + D (u t x) = -(A * A) - H := by
    rw [← sub_eq_zero, ← hsum]
    abel
  have hstar : star Adot + star (D (u t x)) = -(star A * star A) - H := by
    rw [← star_add, hkey, star_sub, star_neg, star_mul, hH.star_eq]
  simp only [sub_apply, coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    starL'_apply, vorticity_def, ← star_eq_adjoint, ← mul_def]
  calc Adot - star Adot + (D (u t x) - star (D (u t x))) + (A - star A) * A +
        star A * (A - star A)
      = (Adot + D (u t x)) - (star Adot + star (D (u t x))) + (A - star A) * A +
        star A * (A - star A) := by abel
    _ = 0 := by rw [hkey, hstar]; noncomm_ring

/-- **The vorticity equation.** Let `u` be jointly `C²` in `(t, x)` and `p t` be `C²` at `x`,
and suppose that the momentum equation of the Euler equations,
`∂ₜu + (u·∇)u + ∇p = 0`, holds at time `t` near `x`. Then the vorticity `Ω = ∇u − (∇u)†`
satisfies `∂ₜΩ + (u·∇)Ω + Ω ∇u + (∇u)† Ω = 0` at `(t, x)`. No incompressibility is needed. -/
theorem deriv_vorticity_add_fderiv_vorticity_add_eq_zero
    {u : ℝ → E → E} {p : ℝ → E → ℝ} {t : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 (Function.uncurry u) (t, x)) (hp : ContDiffAt ℝ 2 (p t) x)
    (heq : ∀ᶠ y in 𝓝 x, deriv (fun s ↦ u s y) t + fderiv ℝ (u t) y (u t y) + ∇ (p t) y = 0) :
    deriv (fun s ↦ vorticity (u s) x) t + fderiv ℝ (vorticity (u t)) x (u t x) +
        vorticity (u t) x ∘L fderiv ℝ (u t) x + adjoint (fderiv ℝ (u t) x) ∘L vorticity (u t) x =
      0 := by
  obtain ⟨Ωdot, Ω', hΩdot, hΩ', h⟩ := exists_hasDerivAt_vorticity hu hp heq
  rwa [hΩdot.deriv, hΩ'.fderiv]

end CompleteSpace

/-- **The pressure Poisson equation.** Let `u` be jointly `C²` in `(t, x)`, divergence-free near
`(t, x)`, and `p t` be `C²` at `x`, and suppose that `∂ₜu + (u·∇)u + ∇p = 0` holds at time `t`
near `x`. Then `−Δp = trace ((∇u)²)` at `(t, x)`. -/
theorem neg_laplacian_eq_trace_fderiv_mul_fderiv [FiniteDimensional ℝ E] {u : ℝ → E → E}
    {p : ℝ → E → ℝ} {t : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 (Function.uncurry u) (t, x)) (hp : ContDiffAt ℝ 2 (p t) x)
    (heq : ∀ᶠ y in 𝓝 x, deriv (fun s ↦ u s y) t + fderiv ℝ (u t) y (u t y) + ∇ (p t) y = 0)
    (hdiv : ∀ᶠ z in 𝓝 (t, x), LinearMap.trace ℝ E (fderiv ℝ (u z.1) z.2 : E →ₗ[ℝ] E) = 0) :
    -Δ (p t) x =
      LinearMap.trace ℝ E (fderiv ℝ (u t) x * fderiv ℝ (u t) x : E →L[ℝ] E) := by
  obtain ⟨Adot, D, hAdot, hD, hsum⟩ := exists_hasDerivAt_fderiv hu hp heq
  -- the trace, as a continuous linear functional on operators
  set τ : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.trace ℝ E ∘ₗ ContinuousLinearMap.coeLM ℝ)
  have hτ : ∀ T : E →L[ℝ] E, τ T = LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) := fun _ ↦ by simp [τ]
  -- the divergence vanishes near `(t, x)`, so its time and space derivatives vanish there
  have ht : τ Adot = 0 := by
    have h₀ : HasDerivAt (fun s ↦ τ (fderiv ℝ (u s) x)) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq <|
        ((continuous_id.prodMk continuous_const).tendsto t).eventually hdiv
    exact (τ.hasFDerivAt.comp_hasDerivAt t hAdot).unique h₀
  have hx : τ (D (u t x)) = 0 := by
    have h₀ : HasFDerivAt (fun y ↦ τ (fderiv ℝ (u t) y)) (0 : E →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq <|
        ((continuous_const.prodMk continuous_id).tendsto x).eventually hdiv
    simpa using congrArg (fun T : E →L[ℝ] ℝ ↦ T (u t x)) ((τ.hasFDerivAt.comp x hD).unique h₀)
  have hΔ : Δ (p t) x = τ (fderiv ℝ (∇ (p t)) x) := by
    simp [laplacian_eq_trace_iteratedGradientChain_one, hτ]
  have := congrArg τ hsum
  rw [map_add, map_add, map_add, ht, hx, map_zero, ← hΔ] at this
  rw [← hτ]
  linarith

end TauCeti

namespace Orientation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2))

local notation "J" => o.rightAngleRotation

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

/-- The trace in the positively oriented orthonormal frame `(e, J e)`. -/
private theorem trace_eq_inner_add_inner {e : E} (he : ‖e‖ = 1) (T : E →L[ℝ] E) :
    LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) = ⟪e, T e⟫_ℝ + ⟪J e, T (J e)⟫_ℝ := by
  have hon : Orthonormal ℝ ![e, J e] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he]
  let b : OrthonormalBasis (Fin 2) ℝ E :=
    (o.basisRightAngleRotation e (by rintro rfl; simp at he)).toOrthonormalBasis
      (by simpa using hon)
  rw [LinearMap.trace_eq_sum_inner _ b, Fin.sum_univ_two]
  simp [b]

/-- Two operators on the plane agree once their matrix entries in the frame `(e, J e)` agree. -/
private theorem ext_inner_frame {e : E} (he : e ≠ 0) {X Y : E →L[ℝ] E}
    (h : ∀ v ∈ ({e, J e} : Set E), ∀ w ∈ ({e, J e} : Set E), ⟪X v, w⟫_ℝ = ⟪Y v, w⟫_ℝ) :
    X = Y := by
  set b := o.basisRightAngleRotation e he
  refine ContinuousLinearMap.coe_injective (b.ext fun i ↦ ?_)
  refine InnerProductSpace.ext_inner_right_basis b fun j ↦ ?_
  have hb : ∀ k, b k ∈ ({e, J e} : Set E) := fun k ↦ by fin_cases k <;> simp [b]
  exact h _ (hb i) _ (hb j)

private theorem exists_norm_eq_one : ∃ e : E, ‖e‖ = 1 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = 2)
  exact exists_norm_eq E zero_le_one

/-- The **scalar vorticity** of a planar velocity field: `ω = −trace (J ∇u)`, which is
`∂₁u₂ − ∂₂u₁` in every positively oriented orthonormal frame
(`Orientation.scalarVorticity_eq_inner_sub_inner`) and satisfies `Ω = ω J`
(`Orientation.vorticity_eq_scalarVorticity_smul`). -/
noncomputable def scalarVorticity (u : E → E) (x : E) : ℝ :=
  -LinearMap.trace ℝ E ((J : E →L[ℝ] E) ∘L fderiv ℝ u x : E →L[ℝ] E)

theorem scalarVorticity_def (u : E → E) (x : E) :
    o.scalarVorticity u x = -LinearMap.trace ℝ E ((J : E →L[ℝ] E) ∘L fderiv ℝ u x : E →L[ℝ] E) :=
  (rfl)

/-- The scalar vorticity in the positively oriented orthonormal frame `(e, J e)`:
`ω = ⟪J e, ∇u e⟫ − ⟪e, ∇u (J e)⟫`, that is, `∂₁u₂ − ∂₂u₁`. -/
theorem scalarVorticity_eq_inner_sub_inner (u : E → E) (x : E) {e : E} (he : ‖e‖ = 1) :
    o.scalarVorticity u x = ⟪J e, fderiv ℝ u x e⟫_ℝ - ⟪e, fderiv ℝ u x (J e)⟫_ℝ := by
  rw [scalarVorticity_def, o.trace_eq_inner_add_inner he]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, o.inner_rightAngleRotation_swap,
    o.rightAngleRotation_rightAngleRotation, inner_neg_left]
  ring

/-- Every vector of the plane is expanded in the positively oriented orthonormal frame
`(e, J e)`. -/
private theorem eq_inner_smul_add_inner_smul {e : E} (he : ‖e‖ = 1) (v : E) :
    v = ⟪e, v⟫_ℝ • e + ⟪J e, v⟫_ℝ • J e := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  refine InnerProductSpace.ext_inner_left_basis (o.basisRightAngleRotation e he0) fun i ↦ ?_
  fin_cases i <;>
    simp [inner_add_right, inner_smul_right, he, real_inner_comm e]

/-- **The planar vorticity is a multiple of the rotation.** In an oriented plane, the vorticity
tensor is `Ω = ω J`, with `ω` the scalar vorticity. -/
theorem vorticity_eq_scalarVorticity_smul (u : E → E) (x : E) :
    vorticity u x = o.scalarVorticity u x • (J : E →L[ℝ] E) := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := E)
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  rw [o.scalarVorticity_eq_inner_sub_inner u x he]
  obtain ⟨a, c, h₁⟩ : ∃ a c : ℝ, fderiv ℝ u x e = a • e + c • J e :=
    ⟨_, _, o.eq_inner_smul_add_inner_smul he _⟩
  obtain ⟨b, d, h₂⟩ : ∃ b d : ℝ, fderiv ℝ u x (J e) = b • e + d • J e :=
    ⟨_, _, o.eq_inner_smul_add_inner_smul he _⟩
  refine o.ext_inner_frame he0 ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  simp only [inner_vorticity_apply]
  simp [h₁, h₂, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, he,
    real_inner_comm e (J e)]

/-- In the plane, `J A + A† J = (trace A) J` for every operator `A`. -/
private theorem rightAngleRotation_comp_add_adjoint_comp (A : E →L[ℝ] E) :
    (J : E →L[ℝ] E) ∘L A + adjoint A ∘L (J : E →L[ℝ] E) =
      LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • (J : E →L[ℝ] E) := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := E)
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  rw [o.trace_eq_inner_add_inner he]
  obtain ⟨a, c, h₁⟩ : ∃ a c : ℝ, A e = a • e + c • J e :=
    ⟨_, _, o.eq_inner_smul_add_inner_smul he _⟩
  obtain ⟨b, d, h₂⟩ : ∃ b d : ℝ, A (J e) = b • e + d • J e :=
    ⟨_, _, o.eq_inner_smul_add_inner_smul he _⟩
  refine o.ext_inner_frame he0 ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  simp [adjoint_inner_left, h₁, h₂, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, he, real_inner_comm e (J e)]

/-- **The scalar vorticity equation.** Let `u` be jointly `C²` in `(t, x)` on an oriented plane
and `p t` be `C²` at `x`, and suppose that `∂ₜu + (u·∇)u + ∇p = 0` holds at time `t` near `x`.
Then the scalar vorticity satisfies `∂ₜω + u·∇ω + ω div u = 0` at `(t, x)`, where
`div u = trace ∇u`. -/
theorem deriv_scalarVorticity_add_fderiv_scalarVorticity_add_mul_trace_eq_zero
    {u : ℝ → E → E} {p : ℝ → E → ℝ} {t : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 (Function.uncurry u) (t, x)) (hp : ContDiffAt ℝ 2 (p t) x)
    (heq : ∀ᶠ y in 𝓝 x, deriv (fun s ↦ u s y) t + fderiv ℝ (u t) y (u t y) + ∇ (p t) y = 0) :
    deriv (fun s ↦ o.scalarVorticity (u s) x) t +
        fderiv ℝ (o.scalarVorticity (u t)) x (u t x) +
        o.scalarVorticity (u t) x * LinearMap.trace ℝ E (fderiv ℝ (u t) x : E →ₗ[ℝ] E) = 0 := by
  obtain ⟨Ωdot, Ω', hΩdot, hΩ', h⟩ := exists_hasDerivAt_vorticity hu hp heq
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := E)
  -- the scalar vorticity is the entry `⟪J e, Ω e⟫` of the vorticity tensor
  set ℓ : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ (J e)).comp (apply ℝ E e)
  have hℓ : ∀ v : E → E, o.scalarVorticity v = fun y ↦ ℓ (vorticity v y) := by
    intro v
    ext1 y
    simp [ℓ, o.vorticity_eq_scalarVorticity_smul, he]
  have h₁ : HasDerivAt (fun s ↦ ℓ (vorticity (u s) x)) (ℓ Ωdot) t :=
    ℓ.hasFDerivAt.comp_hasDerivAt t hΩdot
  have h₂ : HasFDerivAt (fun y ↦ ℓ (vorticity (u t) y)) (ℓ ∘L Ω') x := ℓ.hasFDerivAt.comp x hΩ'
  simp only [hℓ]
  rw [h₁.deriv, h₂.fderiv]
  rw [o.vorticity_eq_scalarVorticity_smul, smul_comp, comp_smul, add_assoc _ (_ • _), ← smul_add,
    o.rightAngleRotation_comp_add_adjoint_comp, smul_smul] at h
  simpa [ℓ, o.vorticity_eq_scalarVorticity_smul, he] using congrArg ℓ h

/-- **Transport of the scalar vorticity.** For a velocity field that is divergence-free at
`(t, x)` and satisfies the momentum equation `∂ₜu + (u·∇)u + ∇p = 0` at time `t` near `x`, the
scalar vorticity is transported by the flow: `∂ₜω + u·∇ω = 0` at `(t, x)`. -/
theorem deriv_scalarVorticity_add_fderiv_scalarVorticity_eq_zero
    {u : ℝ → E → E} {p : ℝ → E → ℝ} {t : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 (Function.uncurry u) (t, x)) (hp : ContDiffAt ℝ 2 (p t) x)
    (heq : ∀ᶠ y in 𝓝 x, deriv (fun s ↦ u s y) t + fderiv ℝ (u t) y (u t y) + ∇ (p t) y = 0)
    (hdiv : LinearMap.trace ℝ E (fderiv ℝ (u t) x : E →ₗ[ℝ] E) = 0) :
    deriv (fun s ↦ o.scalarVorticity (u s) x) t +
      fderiv ℝ (o.scalarVorticity (u t)) x (u t x) = 0 := by
  simpa [hdiv] using
    o.deriv_scalarVorticity_add_fderiv_scalarVorticity_add_mul_trace_eq_zero hu hp heq

/-- **Rigid rotation.** The rotation `u x = J x` by `π/2` has scalar vorticity `2`. -/
@[simp]
theorem scalarVorticity_rightAngleRotation (x : E) : o.scalarVorticity J x = 2 := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := E)
  rw [o.scalarVorticity_eq_inner_sub_inner _ x he, LinearIsometryEquiv.fderiv]
  simp [he]
  norm_num

end Orientation
