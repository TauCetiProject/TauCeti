/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
-- Private: the derivative sum and scalar rules and the symmetry of second derivatives are used
-- only inside the proofs below.
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The gradient is an isometric conjugate-linear image of the Fréchet derivative

Mathlib defines `gradient f x`, written `∇ f x`, as the Riesz representative
`(InnerProductSpace.toDual 𝕜 F).symm (fderiv 𝕜 f x)` of the Fréchet derivative of a scalar
function on an inner product space, and develops its differential calculus. This file records the
three consequences of the defining formula that come from `toDual` being a *conjugate-linear
isometric equivalence*: the gradient has the same norm as the derivative, it is additive, and it
is conjugate-homogeneous. Since `toDual` is moreover continuous, the gradient of an arbitrary
function is Borel measurable, as the Fréchet derivative is.

These are exactly what is needed to see a family of gradients as a conjugate-linear,
norm-preserving image of the corresponding family of derivatives. Over `ℝ` it is linear; for
instance, `φ ↦ ∇ φ` is linear on real-valued test functions, and `‖∇ φ‖` may be estimated by any
theorem about `‖Dφ‖`.

## Main declarations

* `TauCeti.norm_gradient_eq_norm_fderiv`: `‖∇ f x‖ = ‖fderiv 𝕜 f x‖`.
* `TauCeti.gradient_add`: additivity of the gradient at a point of differentiability.
* `TauCeti.gradient_const_smul`: `∇ (c • f) x = conj c • ∇ f x`.
* `TauCeti.gradient_of_notMem_tsupport`: the gradient vanishes off the topological support.
* `HasCompactSupport.gradient`: the gradient of a compactly supported function is compactly
  supported.
* `TauCeti.measurable_gradient`: the gradient of any function is measurable.
* `ContDiff.gradient_right`: over `ℝ`, where `toDual` is linear, the gradient of a `C^{m+1}`
  function is `Cᵐ`; `HasCompactSupport.memLp_gradient`: the gradient of a compactly supported
  `C¹` function is in `Lᵖ(μ)` for every measure `μ` finite on compact sets;
  `ContDiffAt.continuousAt_fderiv_gradient` and
  `ContDiffAt.eventually_differentiableAt_gradient`: the Hessian of a function `C²` at `x` is
  continuous at `x`, and its gradient is differentiable near `x`.
* `TauCeti.hasGradientAt_mul_norm_sq_add` and `TauCeti.gradient_mul_norm_sq_add`: over `ℝ`, the
  quadratic `y ↦ (a / 2) ‖y‖² + c` has gradient `a • y` at `y`.
* `TauCeti.gradient_norm_sq` and `TauCeti.differentiable_gradient_norm_sq`: the gradient of
  the squared norm is the radial vector field and is differentiable.
* `TauCeti.isSymmetric_of_hasFDerivAt_gradient`: over `ℝ`, the derivative of the gradient (the
  Hessian as an endomorphism of `E`) is a symmetric operator wherever it exists, provided the
  function is differentiable nearby.
* `TauCeti.norm_gradient_fderiv_apply_le`: `‖∇ (∂ᵥ f) x‖ ≤ ‖v‖ ‖D²f x‖`.
* `TauCeti.norm_iteratedFDeriv_two_sub_le_sum`: the operator norm of `D²f x - D²f y` is at most
  the sum, over an orthonormal basis `(bᵢ)`, of `‖∇ (∂_{bᵢ} f) x - ∇ (∂_{bᵢ} f) y‖`.
-/

public section

namespace TauCeti

open InnerProductSpace

open Filter
open scoped ComplexConjugate Gradient Topology

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F] {f g : F → 𝕜} {x : F}

/-- The gradient has the same norm as the Fréchet derivative it represents: `toDual` is an
isometry. -/
theorem norm_gradient_eq_norm_fderiv (f : F → 𝕜) (x : F) : ‖∇ f x‖ = ‖fderiv 𝕜 f x‖ :=
  (toDual 𝕜 F).symm.norm_map _

/-- The gradient is additive wherever both summands are differentiable. -/
theorem gradient_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ∇ (f + g) x = ∇ f x + ∇ g x := by
  apply (toDual 𝕜 F).injective
  simp only [toDual_gradient, map_add, fderiv_add hf hg]

/-- The gradient is conjugate-homogeneous: `toDual` is conjugate-linear, so scaling the function
by `c` scales the gradient by `conj c`. Over `ℝ` the conjugation is the identity. -/
theorem gradient_const_smul (c : 𝕜) :
    ∇ (c • f) x = conj c • ∇ f x := by
  apply (toDual 𝕜 F).injective
  simp only [toDual_gradient, map_smulₛₗ, RingHomCompTriple.comp_apply, RingHom.id_apply,
    fderiv_const_smul_field, Pi.smul_apply]

/-- The gradient vanishes off the topological support of the function, as the Fréchet derivative
does. -/
@[simp]
theorem gradient_of_notMem_tsupport (h : x ∉ tsupport f) : ∇ f x = 0 := by
  rw [gradient, fderiv_of_notMem_tsupport 𝕜 h, map_zero]

/-- The gradient of a compactly supported function is compactly supported, as is its Fréchet
derivative (`HasCompactSupport.fderiv`). -/
theorem _root_.HasCompactSupport.gradient (hf : HasCompactSupport f) : HasCompactSupport (∇ f) :=
  hf.mono' fun _ hx ↦ by_contra fun h ↦ hx (gradient_of_notMem_tsupport h)

/-- The gradient of an arbitrary function is Borel measurable, as is its Fréchet derivative
(`measurable_fderiv`); no differentiability is assumed, the gradient being `0` where `f` is not
differentiable. -/
@[fun_prop]
theorem measurable_gradient [MeasurableSpace F] [BorelSpace F] (f : F → 𝕜) : Measurable (∇ f) := by
  have h : ∇ f = (toDual 𝕜 F).symm ∘ fderiv 𝕜 f := by
    ext1 x
    rw [Function.comp_apply, ← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  rw [h]
  exact (toDual 𝕜 F).symm.continuous.measurable.comp (measurable_fderiv 𝕜 f)

/-- Over `ℝ` the Riesz isomorphism is a linear isometry, so the gradient of a `C^{m+1}` function
is `Cᵐ`, just as its Fréchet derivative is. -/
theorem _root_.ContDiff.gradient_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {m n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (∇ f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)

/-- Over `ℝ`, the gradient of a compactly supported `C¹` function is in `Lᵖ(μ)` for every
measure `μ` finite on compact sets, being continuous with compact support. -/
theorem _root_.HasCompactSupport.memLp_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {p : ENNReal} {μ : MeasureTheory.Measure E} [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    {f : E → ℝ} (hfc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) :
    MeasureTheory.MemLp (∇ f) p μ :=
  (hf.gradient_right (m := 0) (by simp)).continuous.memLp_of_hasCompactSupport hfc.gradient

/-- The pointwise form of `ContDiff.gradient_right`: over `ℝ`, the gradient of a function that is
`C^{m+1}` at `x` is `Cᵐ` at `x`. -/
theorem _root_.ContDiffAt.gradient_right {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {m n : WithTop ℕ∞} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ n f x) (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (∇ f) x :=
  (toDual ℝ E).symm.contDiff.contDiffAt.comp x (hf.fderiv_right hmn)

/-- Over `ℝ`, a function that is `C²` at `x` has a Hessian `fderiv ℝ (∇ f)` continuous at `x`. -/
theorem _root_.ContDiffAt.continuousAt_fderiv_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {n : WithTop ℕ∞} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ n f x) (hn : 2 ≤ n) : ContinuousAt (fderiv ℝ (∇ f)) x :=
  (hf.gradient_right (m := 1) hn).continuousAt_fderiv one_ne_zero

/-- Over `ℝ`, the gradient of a function that is `C²` at `x` is differentiable near `x`. -/
theorem _root_.ContDiffAt.eventually_differentiableAt_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {n : WithTop ℕ∞} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ n f x) (hn : 2 ≤ n) : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (∇ f) y :=
  ((hf.gradient_right (m := 1) hn).eventually (by simp)).mono fun _ hy =>
    hy.differentiableAt one_ne_zero

/-- Over `ℝ`, the quadratic `y ↦ (a / 2) ‖y‖² + c` has gradient `a • y` at `y`. -/
theorem hasGradientAt_mul_norm_sq_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (a c : ℝ) (y : E) :
    HasGradientAt (fun y : E => a / 2 * ‖y‖ ^ 2 + c) (a • y) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (((HasFDerivAt.norm_sq (hasFDerivAt_id y)).const_mul (a / 2)).add_const
    c).congr_fderiv ?_
  ext z
  simp only [toDual_apply_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, id_eq,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, real_inner_smul_left]
  ring

/-- Over `ℝ`, the gradient of the quadratic `y ↦ (a / 2) ‖y‖² + c` at `y` is `a • y`. -/
theorem gradient_mul_norm_sq_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (a c : ℝ) (y : E) : ∇ (fun y : E => a / 2 * ‖y‖ ^ 2 + c) y = a • y :=
  (hasGradientAt_mul_norm_sq_add a c y).gradient

/-- Over `ℝ`, the gradient of the squared norm is the radial vector field. -/
@[simp]
theorem gradient_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (y : E) : ∇ (fun y : E => ‖y‖ ^ 2) y = (2 : ℝ) • y := by
  simpa using gradient_mul_norm_sq_add (E := E) 2 0 y

/-- Over `ℝ`, the gradient of the squared norm is differentiable. -/
theorem differentiable_gradient_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
  Differentiable ℝ (∇ fun y : E => ‖y‖ ^ 2) := by
  -- `fun_prop` needs the gradient rewritten as a function; the pointwise simp theorem
  -- cannot rewrite under this function-valued goal without first exposing that equality.
  rw [show (∇ fun y : E => ‖y‖ ^ 2) = fun y => (2 : ℝ) • y by
    funext y
    exact gradient_norm_sq y]
  fun_prop

/-- **The Hessian is symmetric.** If a real function `f` is differentiable near `x` and its
gradient has derivative `H` at `x`, then `H` is a symmetric operator:
`⟪H v, w⟫ = ⟪v, H w⟫`. This is Schwarz's theorem for the second derivative, read through the
Riesz isomorphism. -/
theorem isSymmetric_of_hasFDerivAt_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x : E} {H : E →L[ℝ] E}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hH : HasFDerivAt (∇ f) H x) :
    (H : E →ₗ[ℝ] E).IsSymmetric := by
  set L : E →L[ℝ] StrongDual ℝ E := (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ : ∀ᶠ y in 𝓝 x, HasFDerivAt f (L (∇ f y)) y := hf.mono fun y hy => by
    simpa [L, toDual_gradient] using hy.hasFDerivAt
  intro v w
  simpa [L, real_inner_comm] using
    second_derivative_symmetric_of_eventually h₁ (L.hasFDerivAt.comp x hH) v w

/-- The gradient of a directional derivative is controlled by the second derivative:
`‖∇ (∂ᵥ f) x‖ ≤ ‖v‖ ‖D²f x‖`, wherever `fderiv ℝ f` is differentiable. -/
theorem norm_gradient_fderiv_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (fderiv ℝ f) x) (v : E) :
    ‖∇ (fun y => fderiv ℝ f y v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [norm_gradient_eq_norm_fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [fderiv_clm_apply_const_apply hx v w]
  have h := (iteratedFDeriv ℝ 2 f x).le_opNorm ![w, v]
  rw [iteratedFDeriv_two_apply] at h
  simpa [Fin.prod_univ_two, mul_comm, mul_left_comm, mul_assoc] using h

/-- **The second derivative through the gradients of directional derivatives.** For an
orthonormal basis `(bᵢ)`, the operator norm of `D²f x - D²f y` is at most
`∑ᵢ ‖∇ (∂_{bᵢ} f) x - ∇ (∂_{bᵢ} f) y‖`, wherever `fderiv ℝ f` is differentiable at `x` and `y`.
So a Hölder or Lipschitz bound on the gradients of the directional derivatives of `f` along a basis
is one on `D²f`. -/
theorem norm_iteratedFDeriv_two_sub_le_sum {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {f : E → ℝ} {x y : E} (hx : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hy : DifferentiableAt ℝ (fderiv ℝ f) y) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤
      ∑ i, ‖∇ (fun z => fderiv ℝ f z (b i)) x - ∇ (fun z => fderiv ℝ f z (b i)) y‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  -- Expand the second slot in the basis `b`.
  have hB : ∀ z, DifferentiableAt ℝ (fderiv ℝ f) z → iteratedFDeriv ℝ 2 f z m =
      ∑ i, b.repr (m 1) i * ⟪∇ (fun w => fderiv ℝ f w (b i)) z, m 0⟫_ℝ := by
    intro z hz
    rw [iteratedFDeriv_two_apply]
    conv_lhs => rw [← b.sum_repr (m 1)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, inner_gradient_left, fderiv_clm_apply_const_apply hz]
  rw [sub_apply, hB x hx, hB y hy, ← Finset.sum_sub_distrib, Fin.prod_univ_two, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, ← inner_sub_left, norm_mul]
  calc ‖b.repr (m 1) i‖ * ‖⟪_, m 0⟫_ℝ‖ ≤ ‖m 1‖ * (‖_‖ * ‖m 0‖) := by
        gcongr
        · exact (PiLp.norm_apply_le (b.repr (m 1)) i).trans_eq (b.repr.norm_map (m 1))
        · exact norm_inner_le_norm _ _
    _ = _ := by ring

end TauCeti
