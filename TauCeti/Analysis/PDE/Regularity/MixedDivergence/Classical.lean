/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MixedDivergence.Basic
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.Calculus.FDeriv.ExpSmul

/-!
# The classical equation after lifting a mixed divergence term

The lifted divergence is the original mixed divergence minus the matching drift term,
plus the solution itself, all multiplied by the exponential weight. The horizontal line
derivatives are transported through the projection. The vertical derivative differentiates
only the exponential, so the formula puts no differentiability hypothesis on the coefficients.
-/

public noncomputable section

open Filter Set
open scoped ContDiff Gradient InnerProductSpace Topology Real

namespace TauCeti.PDE.MixedDivergence

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "E'" => EuclideanSpace ℝ (ι ⊕ Unit)
local notation "e" => EuclideanSpace.basisFun ι ℝ
local notation "e'" => EuclideanSpace.basisFun (ι ⊕ Unit) ℝ

/-- The derivative of the exponential extension in any lifted direction. -/
theorem fderiv_lift_apply {u : E → ℝ} {x : E'}
    (hu : DifferentiableAt ℝ u (horizontal x)) (d : E') :
    fderiv ℝ (lift u) x d =
      rexp (vertical x) * (fderiv ℝ u (horizontal x) (horizontal d) +
        u (horizontal x) * vertical d) := by
  have h := hu.hasFDerivAt.comp x horizontal.hasFDerivAt
  have hl : lift u = fun w ↦ rexp (vertical w) • (u ∘ horizontal) w := by
    funext w
    simp [lift_apply, smul_eq_mul]
  rw [hl]
  simpa only [Function.comp_apply, smul_eq_mul, h.fderiv, ContinuousLinearMap.comp_apply,
    mul_comm (vertical d)] using
    fderiv_exp_smul_apply vertical.hasFDerivAt h.differentiableAt d

/-- The horizontal component of the gradient of a lifted function. -/
theorem horizontal_gradient_lift {u : E → ℝ} {x : E'}
    (hu : DifferentiableAt ℝ u (horizontal x)) :
    horizontal (∇ (lift u) x) = rexp (vertical x) • ∇ u (horizontal x) := by
  classical
  ext i
  rw [horizontal_apply, gradient_apply_eq_fderiv_apply_single, ← EuclideanSpace.basisFun_apply,
    fderiv_lift_apply hu, horizontal_basis_inl, vertical_basis_inl]
  simp [gradient_apply_eq_fderiv_apply_single, EuclideanSpace.basisFun_apply]

/-- The vertical derivative of the lifted function is the function itself. -/
theorem vertical_gradient_lift {u : E → ℝ} {x : E'}
    (hu : DifferentiableAt ℝ u (horizontal x)) :
    vertical (∇ (lift u) x) = lift u x := by
  classical
  rw [vertical_apply, gradient_apply_eq_fderiv_apply_single, ← EuclideanSpace.basisFun_apply,
    fderiv_lift_apply hu, horizontal_basis_inr, vertical_basis_inr]
  simp [lift_apply]

/-- The divergence of the flux `a ∇u + b u` in the original coordinates. -/
def divMixedGradient (a : E → Matrix ι ι ℝ) (b : E → E) (u : E → ℝ) (x : E) : ℝ :=
  ∑ i, lineDeriv ℝ (fun y ↦ matrixBilinearForm (a y) (e i) (∇ u y) + b y i * u y) x (e i)

/-- The mixed divergence is the sum of the coordinate derivatives of the flux `a ∇u + b u`. -/
theorem divMixedGradient_def (a : E → Matrix ι ι ℝ) (b : E → E) (u : E → ℝ) (x : E) :
    divMixedGradient a b u x =
      ∑ i, lineDeriv ℝ (fun y ↦ matrixBilinearForm (a y) (e i) (∇ u y) + b y i * u y) x
        (e i) := (rfl)

/-- Along a horizontal direction the exponential weight is constant. This formula holds
also when the base function has no line derivative, using the total derivative convention. -/
theorem lineDeriv_lift_horizontal (g : E → ℝ) (x : E') (v : E) :
    lineDeriv ℝ (lift g) x (liftPoint v 0) =
      rexp (vertical x) * lineDeriv ℝ g (horizontal x) v := by
  -- Restriction to this line keeps its height fixed; constant multiplication also preserves
  -- the zero value of the total derivative at nondifferentiable points.
  simp [lineDeriv, lift_apply, map_add, map_smul, deriv_const_mul_field]

/-- Along the vertical direction the exponential extension differentiates to itself,
without a regularity assumption on the base function. -/
theorem lineDeriv_lift_vertical (g : E → ℝ) (x : E') :
    lineDeriv ℝ (lift g) x (liftPoint 0 1) = lift g x := by
  have h : HasLineDerivAt ℝ (lift g) (lift g x) x (liftPoint 0 1) := by
    simpa [HasLineDerivAt, lift_apply, map_add, map_smul] using
      (((hasDerivAt_id (0 : ℝ)).const_add (vertical x)).exp.mul_const (g (horizontal x)))
  exact h.lineDeriv

private theorem liftFlux_horizontal (a : E → Matrix ι ι ℝ) (b : E → E) {u : E → ℝ}
    {x : E'} (hu : DifferentiableAt ℝ u (horizontal x)) (i : ι) :
    matrixBilinearForm (skewBlock (a (horizontal x)) (b (horizontal x))) (e' (Sum.inl i))
      (∇ (lift u) x) = rexp (vertical x) *
        (matrixBilinearForm (a (horizontal x)) (e i) (∇ u (horizontal x)) +
          b (horizontal x) i * u (horizontal x)) := by
  classical
  rw [matrixBilinearForm_skewBlock, horizontal_basis_inl, vertical_basis_inl,
    horizontal_gradient_lift hu, vertical_gradient_lift hu]
  simp [lift_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  ring

private theorem liftFlux_vertical (a : E → Matrix ι ι ℝ) (b : E → E) {u : E → ℝ}
    {x : E'} (hu : DifferentiableAt ℝ u (horizontal x)) :
    matrixBilinearForm (skewBlock (a (horizontal x)) (b (horizontal x))) (e' (Sum.inr ()))
      (∇ (lift u) x) = rexp (vertical x) *
        (u (horizontal x) - ⟪b (horizontal x), ∇ u (horizontal x)⟫_ℝ) := by
  rw [matrixBilinearForm_skewBlock, horizontal_basis_inr, vertical_basis_inr,
    horizontal_gradient_lift hu, vertical_gradient_lift hu]
  simp [lift_apply, real_inner_smul_right]
  ring

private theorem lineDeriv_liftFlux_horizontal (a : E → Matrix ι ι ℝ) (b : E → E)
    {u : E → ℝ} {x : E'} (hu : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u (horizontal y)) (i : ι) :
    lineDeriv ℝ (fun y ↦ matrixBilinearForm
      (skewBlock (a (horizontal y)) (b (horizontal y))) (e' (Sum.inl i)) (∇ (lift u) y)) x
      (e' (Sum.inl i)) = rexp (vertical x) * lineDeriv ℝ
      (fun y ↦ matrixBilinearForm (a y) (e i) (∇ u y) + b y i * u y) (horizontal x) (e i) := by
  have h : (fun y ↦ matrixBilinearForm (skewBlock (a (horizontal y)) (b (horizontal y)))
      (e' (Sum.inl i)) (∇ (lift u) y)) =ᶠ[𝓝 x]
      lift (fun y ↦ matrixBilinearForm (a y) (e i) (∇ u y) + b y i * u y) :=
    hu.mono fun _ hy ↦ by simpa only [lift_apply] using liftFlux_horizontal a b hy i
  rw [h.lineDeriv_eq, ← liftPoint_horizontal_vertical (e' (Sum.inl i)),
    horizontal_basis_inl, vertical_basis_inl]
  exact lineDeriv_lift_horizontal
    (fun y ↦ matrixBilinearForm (a y) (e i) (∇ u y) + b y i * u y) x (e i)

private theorem lineDeriv_liftFlux_vertical (a : E → Matrix ι ι ℝ) (b : E → E)
    {u : E → ℝ} {x : E'} (hu : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u (horizontal y)) :
    lineDeriv ℝ (fun y ↦ matrixBilinearForm
      (skewBlock (a (horizontal y)) (b (horizontal y))) (e' (Sum.inr ())) (∇ (lift u) y)) x
      (e' (Sum.inr ())) = rexp (vertical x) *
      (u (horizontal x) - ⟪b (horizontal x), ∇ u (horizontal x)⟫_ℝ) := by
  have h : (fun y ↦ matrixBilinearForm (skewBlock (a (horizontal y)) (b (horizontal y)))
      (e' (Sum.inr ())) (∇ (lift u) y)) =ᶠ[𝓝 x]
      lift (fun y ↦ u y - ⟪b y, ∇ u y⟫_ℝ) :=
    hu.mono fun _ hy ↦ by simpa only [lift_apply] using liftFlux_vertical a b hy
  rw [h.lineDeriv_eq, ← liftPoint_horizontal_vertical (e' (Sum.inr ())),
    horizontal_basis_inr, vertical_basis_inr]
  simpa only [lift_apply] using lineDeriv_lift_vertical (fun y ↦ u y - ⟪b y, ∇ u y⟫_ℝ) x

/-- The lifted divergence includes the original mixed flux, drift and a single extra
zeroth-order term. -/
theorem divMatrixGradient_lift (a : E → Matrix ι ι ℝ) (b : E → E)
    {u : E → ℝ} {x : E'} (hu : ∀ᶠ y in 𝓝 (horizontal x), DifferentiableAt ℝ u y) :
    divMatrixGradient (fun y ↦ skewBlock (a (horizontal y)) (b (horizontal y))) (lift u) x =
      rexp (vertical x) * (divMixedGradient a b u (horizontal x) -
        ⟪b (horizontal x), ∇ u (horizontal x)⟫_ℝ + u (horizontal x)) := by
  have h : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u (horizontal y) :=
    (horizontal.continuous.continuousAt (x := x)).tendsto.eventually hu
  rw [divMatrixGradient_def, Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
  simp only [Subsingleton.elim (default : Unit) (), lineDeriv_liftFlux_horizontal a b h,
    lineDeriv_liftFlux_vertical a b h]
  rw [← Finset.mul_sum, divMixedGradient_def]
  ring

/-- The lifted principal divergence equation is equivalent to the original mixed
divergence equation at the projected point. The vertical derivative shifts the potential
by one. -/
theorem divMatrixGradient_lift_eq_iff (a : E → Matrix ι ι ℝ) (b : E → E)
    {u c f : E → ℝ} {x : E'} (hu : ∀ᶠ y in 𝓝 (horizontal x), DifferentiableAt ℝ u y) :
    divMatrixGradient (fun y ↦ skewBlock (a (horizontal y)) (b (horizontal y))) (lift u) x =
        (c (horizontal x) + 1) * lift u x - lift f x ↔
      divMixedGradient a b u (horizontal x) =
        ⟪b (horizontal x), ∇ u (horizontal x)⟫_ℝ + c (horizontal x) * u (horizontal x) -
          f (horizontal x) := by
  rw [divMatrixGradient_lift a b hu]
  simp only [lift_apply]
  constructor
  · intro h
    have h' := h.trans (show _ = rexp (vertical x) *
      ((c (horizontal x) + 1) * u (horizontal x) - f (horizontal x)) by ring)
    linarith only [mul_left_cancel₀ (Real.exp_ne_zero _) h']
  · intro h
    rw [h]
    ring

end TauCeti.PDE.MixedDivergence
