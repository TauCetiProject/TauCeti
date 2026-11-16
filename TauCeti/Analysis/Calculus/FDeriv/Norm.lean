/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# Derivatives and norms

A map whose norm is locally constant has derivative orthogonal to its value. In particular, the
derivative of a map into a sphere is tangent to the sphere. Away from the origin, a vanishing
derivative of a norm-composition forces the one-dimensional profile derivative to vanish.
Reflections in hyperplanes show that any radially invariant map on a real inner product space has
constant operator norm of the Fréchet derivative along each sphere
(`TauCeti.norm_fderiv_eq_of_norm_eq`), and on a real normed space, every level set of a radially
nonincreasing map on which `fderiv` never vanishes lies on a single sphere
(`TauCeti.norm_eq_of_eq_of_forall_fderiv_ne_zero`).

The squared norm of the derivative of a map from `ℂ` to a Euclidean space is at most twice the
sum of the squared partial derivatives of its components along `1` and `I`
(`TauCeti.norm_fderiv_sq_le_two_mul_sum_sq`).

The function `y ↦ √(a - ‖y‖²)`, whose graph over the ball of radius `√a` is a hemisphere, has
derivative `-(√(a - ‖x‖²))⁻¹ ⟪x, ·⟫` wherever `a - ‖x‖² ≠ 0`; in particular it is flat at the
origin.
-/

public section

open Filter
open scoped Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Away from the origin, a vanishing totalized derivative of a radial function forces its
one-dimensional profile derivative to vanish. The profile need not be differentiable. -/
theorem deriv_eq_zero_of_fderiv_comp_norm_eq_zero {v : ℝ → E} {x : F} (hx : x ≠ 0)
    (hcrit : fderiv ℝ (fun y : F ↦ v ‖y‖) x = 0) : deriv v ‖x‖ = 0 := by
  by_contra hv
  have hn : DifferentiableAt ℝ (‖·‖) x := differentiableAt_id.norm ℝ hx
  -- The chain rule, evaluated at `x`: `‖x‖ • deriv v ‖x‖ = 0` since `fderiv ℝ (‖·‖) x x = ‖x‖`.
  have h := congr($(((differentiableAt_of_deriv_ne_zero hv).hasDerivAt.hasFDerivAt.comp x
    hn.hasFDerivAt).fderiv.symm.trans hcrit) x)
  exact hv (by simpa [hn.fderiv_norm_self, hx] using h)

/-- A map whose norm is constant near `w` has Fréchet derivative at `w` orthogonal to its
value. In particular, the derivative of a map into a sphere is tangent to the sphere.
At nondifferentiable points, the Fréchet derivative is zero by definition. -/
theorem inner_fderiv_eq_zero_of_eventually_norm_eq {ψ : E → F} {w : E}
    (hψ : ∀ᶠ y in 𝓝 w, ‖ψ y‖ = ‖ψ w‖) (u : E) :
    ⟪ψ w, fderiv ℝ ψ w u⟫ = 0 := by
  by_cases hd : DifferentiableAt ℝ ψ w
  · have h₁ := HasFDerivAt.norm_sq hd.hasFDerivAt
    have h₂ : HasFDerivAt (fun y => ‖ψ y‖ ^ 2) (0 : E →L[ℝ] ℝ) w :=
      (hasFDerivAt_const (‖ψ w‖ ^ 2) w).congr_of_eventuallyEq
        (hψ.mono fun y hy => by simp [hy])
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L u) (h₁.unique h₂)
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- The squared operator norm of the derivative of a map from `ℂ` to a Euclidean space is at most
twice the sum, over the components, of the squared partial derivatives along `1` and `I`. -/
theorem norm_fderiv_sq_le_two_mul_sum_sq {ι : Type*} [Fintype ι] (u : ℂ → EuclideanSpace ℝ ι)
    (z : ℂ) :
    ‖fderiv ℝ u z‖ ^ 2 ≤
      2 * ∑ i, (fderiv ℝ (fun w ↦ u w i) z 1 ^ 2 + fderiv ℝ (fun w ↦ u w i) z Complex.I ^ 2) := by
  by_cases hu : DifferentiableAt ℝ u z
  swap
  · rw [fderiv_zero_of_not_differentiableAt hu, norm_zero, zero_pow two_ne_zero]
    positivity
  have hD := (fderiv ℝ u z).opNorm_sq_le_card_mul_sum_norm_apply_sq_orthonormalBasis
    Complex.orthonormalBasisOneI
  simp only [Fintype.card_fin, Nat.cast_ofNat, Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hD
  -- The squared norm of a directional derivative is the sum over the components.
  have hcomp (v : ℂ) : ‖fderiv ℝ u z v‖ ^ 2 = ∑ i, fderiv ℝ (fun w ↦ u w i) z v ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h : HasFDerivAt (fun w ↦ u w i) ((EuclideanSpace.proj i).comp (fderiv ℝ u z)) z :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hu.hasFDerivAt
    rw [h.fderiv]
    rfl
  rwa [hcomp, hcomp, ← Finset.sum_add_distrib] at hD

/-- The hemisphere function `y ↦ √(a - ‖y‖²)` has derivative `-(√(a - ‖x‖²))⁻¹ ⟪x, ·⟫` at every
point `x` with `a - ‖x‖² ≠ 0`. -/
theorem hasFDerivAt_sqrt_sub_norm_sq {a : ℝ} {x : F} (hx : a - ‖x‖ ^ 2 ≠ 0) :
    HasFDerivAt (fun y : F ↦ √(a - ‖y‖ ^ 2)) (-(√(a - ‖x‖ ^ 2))⁻¹ • innerSL ℝ x) x := by
  refine ((((hasFDerivAt_id x).norm_sq).const_sub a).sqrt hx).congr_fderiv ?_
  ext y
  simp only [id_eq, one_div, mul_inv_rev, ContinuousLinearMap.comp_id, smul_neg, neg_apply,
    smul_apply, coe_innerSL_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, neg_smul, neg_inj]
  ring

/-- The Fréchet derivative of `y ↦ ‖y - x₀‖ ^ 2` at `x` is `2 • innerSL ℝ (x - x₀)`. -/
theorem hasFDerivAt_norm_sq_sub (x₀ x : F) :
    HasFDerivAt (fun y => ‖y - x₀‖ ^ 2) (2 • innerSL ℝ (x - x₀)) x := by
  simpa using ((hasFDerivAt_id x).sub_const x₀).norm_sq

/-- A map on a real inner product space that depends only on the norm has equal Fréchet derivative
operator norms at any two points of equal norm. At nondifferentiable points, the totalized `fderiv`
is zero by definition. -/
theorem norm_fderiv_eq_of_norm_eq {f : F → E} {x y : F}
    (hrad : ∀ z w : F, ‖z‖ = ‖w‖ → f z = f w) (hxy : ‖x‖ = ‖y‖) :
    ‖fderiv ℝ f x‖ = ‖fderiv ℝ f y‖ := by
  let R : F ≃ₗᵢ[ℝ] F := Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hcomp : f ∘ R.toContinuousLinearEquiv = f :=
    funext fun z ↦ hrad (R z) z (R.norm_map z)
  have hfderiv := R.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := x)
  rw [hcomp] at hfderiv
  rw [hfderiv]
  simp [R, Submodule.reflection_sub hxy]

/-- On a real normed space, every level set of a radially nonincreasing map along which `fderiv ℝ f`
never vanishes lies on a single sphere. At nondifferentiable points, the totalized `fderiv` is zero
by definition. -/
theorem norm_eq_of_eq_of_forall_fderiv_ne_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [PartialOrder G] {f : E → G} {x y : E}
    (hrad : ∀ z w : E, ‖z‖ ≤ ‖w‖ → f w ≤ f z)
    (hreg : ∀ z : E, f z = f x → fderiv ℝ f z ≠ 0) (hxy : f x = f y) :
    ‖x‖ = ‖y‖ := by
  have key {a b : E} (ha : f a = f x) (hb : f b = f x) (hlt : ‖a‖ < ‖b‖) : False := by
    have hb_pos : 0 < ‖b‖ := (norm_nonneg a).trans_lt hlt
    let w₀ : E := ((‖a‖ + ‖b‖) / (2 * ‖b‖)) • b
    have hw₀ : ‖w₀‖ = (‖a‖ + ‖b‖) / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hmem : w₀ ∈ {w : E | ‖a‖ < ‖w‖ ∧ ‖w‖ < ‖b‖} := ⟨by linarith, by linarith⟩
    have hopen : IsOpen {w : E | ‖a‖ < ‖w‖ ∧ ‖w‖ < ‖b‖} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hconst : ∀ w ∈ {w : E | ‖a‖ < ‖w‖ ∧ ‖w‖ < ‖b‖}, f w = f x := fun w hw ↦
      le_antisymm (ha ▸ hrad a w hw.1.le) (hb ▸ hrad w b hw.2.le)
    have hfd : HasFDerivAt f (0 : E →L[ℝ] G) w₀ :=
      (hasFDerivAt_const (f x) w₀).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hopen.mem_nhds hmem) hconst)
    exact hreg w₀ (hconst w₀ hmem) hfd.fderiv
  rcases lt_trichotomy ‖x‖ ‖y‖ with h | h | h
  · exact (key rfl hxy.symm h).elim
  · exact h
  · exact (key hxy.symm rfl h).elim

end TauCeti
