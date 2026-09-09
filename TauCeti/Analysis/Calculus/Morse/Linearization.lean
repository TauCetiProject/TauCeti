/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Calculus.Morse.Basic
-- Private: the norm comparison between the gradient and Fréchet derivative and the mean value
-- inequality are used only to prove the local estimates below.
import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Linearization of the negative-gradient field at a Morse critical point

The stable-manifold theorem starts with the derivative of the vector field at an equilibrium. For
a gradient field on a real Hilbert space, the second derivative of the function naturally takes
values in the continuous dual. The Riesz equivalence turns it into an endomorphism of the original
space: `TauCeti.hessianOperator`.

At a twice continuously differentiable point this operator is self-adjoint, by symmetry of the
second derivative. At a nondegenerate critical point it is invertible, and the negative-gradient
field has derivative `-hessianOperator f x`. Consequently the field is its invertible linear part
up to a remainder of order `o(‖y - x‖)`. The characterization
`TauCeti.isNondegenerateCriticalPoint_iff_neg_gradient_linearization` packages exactly the
equilibrium and invertible-linearization hypotheses needed for the stable-manifold theorem in the
gradient setting.

The definition uses Mathlib's totalized Fréchet derivative, just as
`TauCeti.IsNondegenerateCriticalPoint` and `TauCeti.hessianQuadraticForm` do. Regularity enters the
results that identify the operator as the derivative of the gradient and prove self-adjointness.

## Main declarations

* `TauCeti.hessianOperator`: the Riesz-represented Hessian as an endomorphism of the Hilbert space.
* `TauCeti.hessianOperator_congr_of_eventuallyEq`: the operator depends only on the germ of the
  function at the point.
* `ContDiffAt.isSelfAdjoint_hessianOperator`: symmetry of the second derivative becomes
  self-adjointness of the Hessian operator.
* `ContDiffAt.hasFDerivAt_neg_gradient`: the derivative of `-∇ f` is the negative Hessian
  operator.
* `ContDiffAt.neg_gradient_sub_linearization_isLittleO`: at a `C²` critical point the nonlinear
  remainder after subtracting the linearization is little-o of the displacement.
* `ContDiffAt.exists_norm_gradient_le_mul_norm_sub` and
  `ContDiffAt.exists_abs_sub_le_mul_norm_sub_sq`: local upper estimates near a critical point.
* `TauCeti.IsNondegenerateCriticalPoint.exists_mul_norm_sub_le_norm_gradient` and
  `TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_gradient_sq`: local lower and
  Łojasiewicz estimates near a nondegenerate critical point.
* `TauCeti.isNondegenerateCriticalPoint_iff_neg_gradient_linearization`: nondegenerate critical
  points are exactly the equilibria with invertible negative-gradient linearization, under `C²`
  regularity.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Filter InnerProductSpace Metric Set Topology
open scoped Gradient

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f g : E → ℝ} {x : E}

/-- The Hessian of `f` at `x`, represented as an endomorphism of the Hilbert space using the Riesz
equivalence. Its inner product with `w` is the second derivative of `f` evaluated on `v, w`.

The definition is meaningful without regularity because Mathlib's Fréchet derivative is
totalized by zero. Twice continuous differentiability is assumed when this operator is used as
the derivative of the gradient. -/
noncomputable def hessianOperator (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    fderiv ℝ (fderiv ℝ f) x

/-- Applying the Riesz map to the Hessian operator recovers the dual-valued second derivative. -/
@[simp]
theorem toDual_hessianOperator (f : E → ℝ) (x : E) :
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      hessianOperator f x = fderiv ℝ (fderiv ℝ f) x := by
  ext v
  simp [hessianOperator]

/-- The inner-product characterization of the Hessian operator. -/
@[simp]
theorem inner_hessianOperator_left (f : E → ℝ) (x v w : E) :
    ⟪hessianOperator f x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ f) x v w := by
  simp only [hessianOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact InnerProductSpace.toDual_symm_apply

/-- The Hessian operator depends only on the germ of the function at the point. -/
theorem hessianOperator_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    hessianOperator f x = hessianOperator g x := by
  rw [hessianOperator, hessianOperator, hfg.fderiv.fderiv_eq]

end TauCeti

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E}

open TauCeti

/-- Twice continuous differentiability makes the Hessian operator self-adjoint. This is the
operator form of symmetry of the second Fréchet derivative. -/
theorem isSelfAdjoint_hessianOperator (hf : ContDiffAt ℝ 2 f x) :
    IsSelfAdjoint (hessianOperator f x) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro v w
  calc
    ⟪(hessianOperator f x : E → E) v, w⟫_ℝ =
        fderiv ℝ (fderiv ℝ f) x v w := inner_hessianOperator_left f x v w
    _ = fderiv ℝ (fderiv ℝ f) x w v := hf.isSymmSndFDerivAt (by norm_num) v w
    _ = ⟪(hessianOperator f x : E → E) w, v⟫_ℝ :=
      (inner_hessianOperator_left f x w v).symm
    _ = ⟪v, (hessianOperator f x : E → E) w⟫_ℝ := real_inner_comm _ _

/-- The gradient is differentiable at a twice continuously differentiable point, with derivative
the Hessian operator. -/
theorem hasFDerivAt_gradient (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (∇ f) (hessianOperator f x) x := by
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ContDiffAt.hasFDerivAt_fderiv hf le_rfl
  have h := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt.comp x hfd
  -- The composed function is the gradient, by the defining property `toDual_gradient` of `∇ f`.
  have hfun : ⇑(InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv ∘ fderiv ℝ f = ∇ f := by
    funext y
    simp only [Function.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    exact ((InnerProductSpace.toDual ℝ E).eq_symm_apply.2 toDual_gradient).symm
  rw [hfun] at h
  -- The composed derivative is the Hessian operator, by its definition.
  rw [hessianOperator]
  exact h

/-- The negative-gradient vector field is differentiable at a twice continuously differentiable
point, with derivative minus the Hessian operator. -/
theorem hasFDerivAt_neg_gradient (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (-∇ f) (-hessianOperator f x) x :=
  (hasFDerivAt_gradient hf).neg

/-- At a critical point of a twice continuously differentiable function, the negative-gradient
field differs from its linearization by a term of order `o(‖y - x‖)`. This is the nonlinear
remainder controlled in the local stable-manifold argument. -/
theorem neg_gradient_sub_linearization_isLittleO (hf : ContDiffAt ℝ 2 f x) (hgrad : ∇ f x = 0) :
    (fun y ↦ (-∇ f) y + hessianOperator f x (y - x)) =o[nhds x]
      (fun y ↦ y - x) := by
  have hrem := (hasFDerivAt_neg_gradient hf).isLittleO
  simpa only [Pi.neg_apply, hgrad, neg_zero, sub_zero, neg_apply, sub_neg_eq_add] using hrem

/-- Near a critical point of a twice continuously differentiable function the gradient is bounded
above by a multiple of the distance to that point: it vanishes at the point and is differentiable
there. -/
theorem exists_norm_gradient_le_mul_norm_sub (hf : ContDiffAt ℝ 2 f x) (hgrad : ∇ f x = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖∇ f y‖ ≤ C * ‖y - x‖ := by
  refine ⟨‖hessianOperator f x‖ + 1, by positivity, ?_⟩
  filter_upwards [(hf.neg_gradient_sub_linearization_isLittleO hgrad).def one_pos] with y hy
  rw [one_mul] at hy
  have h2 : ‖hessianOperator f x (y - x)‖ ≤ ‖hessianOperator f x‖ * ‖y - x‖ :=
    (hessianOperator f x).le_opNorm _
  have h1 : ‖∇ f y‖ ≤ ‖(-∇ f) y + hessianOperator f x (y - x)‖
      + ‖hessianOperator f x (y - x)‖ := by
    calc ‖∇ f y‖ = ‖(-∇ f) y‖ := by simp
      _ = ‖((-∇ f) y + hessianOperator f x (y - x)) - hessianOperator f x (y - x)‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  nlinarith

/-- Near a critical point of a twice continuously differentiable function the absolute energy
difference `|f y - f x|` is bounded by a multiple of the squared distance to that point. This is
the mean value inequality applied along the segment from `x` to `y`, on which the gradient is
bounded by a multiple of `‖y - x‖`. -/
theorem exists_abs_sub_le_mul_norm_sub_sq (hf : ContDiffAt ℝ 2 f x) (hgrad : ∇ f x = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, |f y - f x| ≤ C * ‖y - x‖ ^ 2 := by
  obtain ⟨C, hC, hbd⟩ := hf.exists_norm_gradient_le_mul_norm_sub hgrad
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hbd.and hdiff)
  refine ⟨C, hC, Metric.eventually_nhds_iff.2 ⟨r, hr, fun {y} hy ↦ ?_⟩⟩
  have hyr : ‖y - x‖ < r := by rwa [← dist_eq_norm]
  have hsub : Metric.closedBall x ‖y - x‖ ⊆ Metric.ball x r := fun z hz ↦
    lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hyr
  have hkey : ‖f y - f x‖ ≤ C * ‖y - x‖ * ‖y - x‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := Metric.closedBall x ‖y - x‖) (f' := fun z ↦ fderiv ℝ f z)
      (fun z hz ↦ ?_) (fun z hz ↦ ?_) (convex_closedBall x ‖y - x‖) ?_ ?_
    · exact ((hball (hsub hz)).2).hasFDerivAt.hasFDerivWithinAt
    · rw [← norm_gradient_eq_norm_fderiv]
      refine ((hball (hsub hz)).1).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      have hz' := Metric.mem_closedBall.1 hz
      rwa [dist_eq_norm] at hz'
    · exact Metric.mem_closedBall_self (norm_nonneg _)
    · simp [Metric.mem_closedBall, dist_eq_norm]
  calc |f y - f x| = ‖f y - f x‖ := by rw [Real.norm_eq_abs]
    _ ≤ C * ‖y - x‖ * ‖y - x‖ := hkey
    _ = C * ‖y - x‖ ^ 2 := by ring

end ContDiffAt

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E}

/-- The Hessian operator is invertible exactly when the dual-valued second derivative is. Thus
the Hilbert-space operator formulation is equivalent to the Banach-space formulation used in
`TauCeti.IsNondegenerateCriticalPoint`. -/
theorem isInvertible_hessianOperator_iff :
    (hessianOperator f x).IsInvertible ↔ (fderiv ℝ (fderiv ℝ f) x).IsInvertible := by
  rw [← ContinuousLinearMap.isInvertible_equiv_comp
    (e := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv)]
  rw [toDual_hessianOperator]

/-- The Hessian operator at a nondegenerate critical point is invertible. -/
theorem IsNondegenerateCriticalPoint.isInvertible_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) : (hessianOperator f x).IsInvertible :=
  isInvertible_hessianOperator_iff.2 h.isInvertible

/-- The gradient vanishes at a nondegenerate critical point. This translates the dual-valued
criticality condition in `TauCeti.IsNondegenerateCriticalPoint` through the Riesz equivalence. -/
theorem IsNondegenerateCriticalPoint.gradient_eq_zero
    (h : IsNondegenerateCriticalPoint f x) : ∇ f x = 0 := by
  apply (InnerProductSpace.toDual ℝ E).injective
  simp [h.fderiv_eq_zero]

/-- Negating a Hessian operator preserves and reflects invertibility. -/
theorem isInvertible_neg_hessianOperator_iff :
    (-hessianOperator f x).IsInvertible ↔ (hessianOperator f x).IsInvertible := by
  have hneg : -hessianOperator f x =
      (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) ∘L hessianOperator f x := by
    ext v
    simp
  rw [hneg, ContinuousLinearMap.isInvertible_equiv_comp]

/-- The derivative of the negative-gradient field at a nondegenerate critical point is
invertible. -/
theorem IsNondegenerateCriticalPoint.isInvertible_neg_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) : (-hessianOperator f x).IsInvertible :=
  isInvertible_neg_hessianOperator_iff.2 h.isInvertible_hessianOperator

/-- The nonlinear-remainder estimate at a nondegenerate critical point. -/
theorem IsNondegenerateCriticalPoint.neg_gradient_sub_linearization_isLittleO
    (h : IsNondegenerateCriticalPoint f x) :
    (fun y ↦ (-∇ f) y + hessianOperator f x (y - x)) =o[nhds x]
      (fun y ↦ y - x) :=
  h.contDiffAt.neg_gradient_sub_linearization_isLittleO h.gradient_eq_zero

/-- Near a nondegenerate critical point the gradient is bounded below by a multiple of the
distance to that point: the Hessian operator is invertible, hence bounded below, and the gradient
differs from it by a term of smaller order. -/
theorem IsNondegenerateCriticalPoint.exists_mul_norm_sub_le_norm_gradient
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ c > 0, ∀ᶠ y in 𝓝 x, c * ‖y - x‖ ≤ ‖∇ f y‖ := by
  obtain ⟨A, hA⟩ := h.isInvertible_hessianOperator
  set M : ℝ := ‖(A.symm : E →L[ℝ] E)‖ + 1 with hMdef
  have hMpos : 0 < M := by positivity
  have hlow : ∀ v : E, ‖v‖ ≤ M * ‖hessianOperator f x v‖ := by
    intro v
    have h1 : ‖v‖ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖(A : E →L[ℝ] E) v‖ := by
      conv_lhs => rw [← A.symm_apply_apply v]
      exact (A.symm : E →L[ℝ] E).le_opNorm _
    rw [← hA]
    nlinarith [norm_nonneg ((A : E →L[ℝ] E) v)]
  have h2M : (0 : ℝ) < 2 * M := by positivity
  have hinv : (0 : ℝ) < (2 * M)⁻¹ := by positivity
  refine ⟨(2 * M)⁻¹, hinv, ?_⟩
  filter_upwards [h.neg_gradient_sub_linearization_isLittleO.def hinv] with y hy
  set R : ℝ := ‖(-∇ f) y + hessianOperator f x (y - x)‖ with hRdef
  have hR : 2 * M * R ≤ ‖y - x‖ := by
    calc 2 * M * R ≤ 2 * M * ((2 * M)⁻¹ * ‖y - x‖) :=
          mul_le_mul_of_nonneg_left hy h2M.le
      _ = ‖y - x‖ := by field_simp
  have h1 : ‖y - x‖ ≤ M * ‖hessianOperator f x (y - x)‖ := hlow _
  have h2 : ‖hessianOperator f x (y - x)‖ ≤ R + ‖∇ f y‖ := by
    calc ‖hessianOperator f x (y - x)‖
        = ‖((-∇ f) y + hessianOperator f x (y - x)) - (-∇ f) y‖ := by
            rw [add_sub_cancel_left]
      _ ≤ ‖(-∇ f) y + hessianOperator f x (y - x)‖ + ‖(-∇ f) y‖ := norm_sub_le _ _
      _ = R + ‖∇ f y‖ := by simp [hRdef]
  have h3 : M * ‖hessianOperator f x (y - x)‖ ≤ M * (R + ‖∇ f y‖) :=
    mul_le_mul_of_nonneg_left h2 hMpos.le
  rw [inv_mul_le_iff₀ h2M]
  nlinarith

/-- **The Morse form of Łojasiewicz's gradient inequality.** Near a nondegenerate critical point
the absolute energy difference is bounded by a multiple of the squared norm of the gradient;
equivalently the Łojasiewicz inequality holds there with the optimal exponent `1 / 2`. For a
merely smooth function no such inequality is available, and a gradient trajectory can spiral
forever without converging. -/
theorem IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_gradient_sq
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 x, lam * |f y - f x| ≤ ‖∇ f y‖ ^ 2 := by
  obtain ⟨c, hc, h1⟩ := h.exists_mul_norm_sub_le_norm_gradient
  obtain ⟨C, hC, h2⟩ := h.contDiffAt.exists_abs_sub_le_mul_norm_sub_sq h.gradient_eq_zero
  refine ⟨c ^ 2 / C, by positivity, ?_⟩
  filter_upwards [h1, h2] with y hy1 hy2
  have h3 : (c * ‖y - x‖) ^ 2 ≤ ‖∇ f y‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hy1 2
  calc c ^ 2 / C * |f y - f x| ≤ c ^ 2 / C * (C * ‖y - x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hy2 (by positivity)
    _ = (c * ‖y - x‖) ^ 2 := by field_simp
    _ ≤ ‖∇ f y‖ ^ 2 := h3

/-- On a real Hilbert space, nondegeneracy can be read entirely from the gradient and its Hessian
operator. -/
theorem isNondegenerateCriticalPoint_iff_gradient :
    IsNondegenerateCriticalPoint f x ↔
      ContDiffAt ℝ 2 f x ∧ ∇ f x = 0 ∧ (hessianOperator f x).IsInvertible := by
  constructor
  · intro h
    exact ⟨h.contDiffAt, h.gradient_eq_zero, h.isInvertible_hessianOperator⟩
  · rintro ⟨hf, hgrad, hinv⟩
    refine ⟨hf, ?_, isInvertible_hessianOperator_iff.1 hinv⟩
    rw [← toDual_gradient]
    simp [hgrad]

/-- A nondegenerate critical point is precisely an equilibrium of the negative-gradient field
whose derivative is invertible, under the stated `C²` regularity. This is the hyperbolicity input
to the stable-manifold theorem in the self-adjoint gradient setting. -/
theorem isNondegenerateCriticalPoint_iff_neg_gradient_linearization :
    IsNondegenerateCriticalPoint f x ↔
      ContDiffAt ℝ 2 f x ∧ (-∇ f) x = 0 ∧
        (fderiv ℝ (-∇ f) x).IsInvertible := by
  constructor
  · intro h
    refine ⟨h.contDiffAt, by simp [h.gradient_eq_zero], ?_⟩
    rw [(ContDiffAt.hasFDerivAt_neg_gradient h.contDiffAt).fderiv]
    exact h.isInvertible_neg_hessianOperator
  · rintro ⟨hf, hzero, hinv⟩
    rw [(ContDiffAt.hasFDerivAt_neg_gradient hf).fderiv,
      isInvertible_neg_hessianOperator_iff] at hinv
    rw [isNondegenerateCriticalPoint_iff_gradient]
    refine ⟨hf, ?_, hinv⟩
    simpa only [Pi.neg_apply, neg_eq_zero] using hzero

end TauCeti
