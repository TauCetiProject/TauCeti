/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic

import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The reaction tensor on algebraic curvature four-tensors

In Uhlenbeck's orthonormal-frame formulation of the Ricci flow, the Riemann curvature four-tensor
evolves by `D_t R = Δ R + Q(R)`, where the quadratic reaction `Q(r)` of a four-tensor `r` on a
finite-dimensional real inner product space `V` has components

`Q(r)ᵢⱼₖₗ = ∑ p, ∑ q, rᵢⱼₚₑ rₖₗₚₑ + 2 ∑ p, ∑ q, rᵢₚₖₑ rⱼₚₗₑ - 2 ∑ p, ∑ q, rᵢₚₗₑ rⱼₚₖₑ`

in any orthonormal basis `(bᵢ)` (with the subscript `e` standing for `q`). Expanding these
components against the rank-one four-tensors
`coordFourTensor b i j k l : (u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫` in the standard
orthonormal basis gives `TauCeti.FourTensor.reactionTensor`, together with its continuous symmetric
bilinear polarization `TauCeti.FourTensor.reactionBilinear : FourTensor V [×2]→L[ℝ] FourTensor V`
satisfying `reactionBilinear ![r, r] = reactionTensor r`.

Because each of the three double sums contracts two four-tensors across a full pair of inner-product
slots, the resulting four-tensor is independent of the chosen orthonormal basis
(`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`). More generally, pulling back along any
continuous linear map `P : W →L[ℝ] V` with `P ∘L P.adjoint = id` commutes with both
`reactionBilinear` and `reactionTensor`; this simultaneously yields orthogonal equivariance under
linear isometric equivalences and commutation with zero extension to an `L²` direct sum
`WithLp 2 (V × U)` along `WithLp.fstL`.

When `r` is an algebraic curvature tensor, `reactionTensor r` again satisfies both pair
antisymmetries, pair interchange, and the first Bianchi identity
(`TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor`,
`TauCeti.FourTensor.reactionTensor_mem_algebraicCurvatureSubmodule`), and by polarization so does
`reactionBilinear ![r, s]`. Consequently the autonomous ODE `r' = Q(r)` restricts to the closed
subspace `TauCeti.FourTensor.algebraicCurvatureSubmodule V`; its smoothness, Fréchet derivative
`h ↦ 2 • reactionBilinear ![r, h]`, explicit operator-norm bound `‖reactionBilinear‖ ≤ 5 * dim V`,
and Lipschitz bounds on closed balls supply the analytic inputs for ODE invariance of curvature
cones.

Contracting `Q(r)` for an algebraic curvature tensor `r` cancels the quadratic Weyl terms in the
trace, leaving `Ric(Q(r))(u, v) = 2 ∑ p, ∑ q, Ric(r)(b p, b q) r(u, b p, v, b q)` and
`Scal(Q(r)) = 2 ∑ p, ∑ q, Ric(r)(b p, b q)² ≥ 0` (vanishing exactly when `Ric(r) = 0`). Pairing `r`
against `constantCurvature V` gives
`reactionBilinear ![r, constantCurvature V] = kulkarniNomizu (ricci r) (innerₗ V)`, so the
constant-curvature tensor satisfies `Q(I) = 2 (n - 1) I`. On the rank-one two-plane curvature
tensor `TauCeti.FourTensor.planeCurvature u v`, `(a, b, c, d) ↦ (⟪u, a⟫ ⟪v, b⟫ - ⟪u, b⟫ ⟪v, a⟫)
(⟪u, c⟫ ⟪v, d⟫ - ⟪u, d⟫ ⟪v, c⟫)` (which represents the curvature of `S² × ℝⁿ⁻²` for an orthonormal
pair `u, v`), the last two sums in `Q` cancel term by term and
`Q(planeCurvature u v) = (2 * constantCurvature V ![u, v, u, v]) • planeCurvature u v`, reducing to
`2 • planeCurvature u v` when `u, v` are orthonormal.

## Main definitions

* `TauCeti.FourTensor.coordFourTensor`: the rank-one four-tensor
  `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫`.
* `TauCeti.FourTensor.planeCurvature`: the rank-one algebraic curvature four-tensor of a pair of
  vectors `u, v`.
* `TauCeti.FourTensor.reactionComponent`: the components `Q(r)ᵢⱼₖₗ` in an orthonormal basis.
* `TauCeti.FourTensor.reactionTensor`: the quadratic reaction four-tensor `Q(r)`.
* `TauCeti.FourTensor.reactionBilinear`: the continuous symmetric bilinear polarization of
  `reactionTensor`.

## Main statements

* `TauCeti.FourTensor.reactionBilinear_apply_orthonormalBasis` and
  `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`: basis-independent contraction formulas
  in every orthonormal basis.
* `TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor`,
  `TauCeti.FourTensor.reactionTensor_mem_algebraicCurvatureSubmodule`, and
  `TauCeti.FourTensor.IsAlgebraicCurvature.reactionBilinear`: preservation of the algebraic
  curvature symmetries.
* `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_of_comp_adjoint_eq_id`,
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv`, and
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_fstL`: coisometry pullback, orthogonal
  equivariance, and commutation with zero extension.
* `TauCeti.FourTensor.norm_reactionBilinear_le`, `TauCeti.FourTensor.contDiff_reactionTensor`,
  `TauCeti.FourTensor.hasStrictFDerivAt_reactionTensor`,
  `TauCeti.FourTensor.lipschitzOnWith_reactionTensor_closedBall`, and
  `TauCeti.FourTensor.locallyLipschitz_reactionTensor`: norm and regularity estimates.
* `TauCeti.FourTensor.ricci_reactionTensor`, `TauCeti.FourTensor.scalar_reactionTensor`,
  `TauCeti.FourTensor.reactionBilinear_constantCurvature_right`,
  `TauCeti.FourTensor.reactionTensor_constantCurvature`, and
  `TauCeti.FourTensor.reactionTensor_planeCurvature`: contractions and model eigenspaces of `Q`.

## References

* S. Brendle and R. Schoen, *Manifolds with 1/4-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307, Section 2.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, Section 2.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University Press
  (2006), Chapter 2.
-/

public section

open LinearMap (BilinForm)
open scoped ContDiff InnerProductSpace NNReal

noncomputable section

namespace TauCeti

namespace FourTensor

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The rank-one four-tensor `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫` attached to four
vectors of a family `b`. -/
def coordFourTensor {ι : Type*} (b : ι → V) (i j k l : ι) : FourTensor V :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).compContinuousLinearMap
    ![innerSL ℝ (b i), innerSL ℝ (b j), innerSL ℝ (b k), innerSL ℝ (b l)]

/-- Evaluation of `coordFourTensor` on a four-tuple of vectors. -/
@[simp]
theorem coordFourTensor_apply {ι : Type*} (b : ι → V) (i j k l : ι) (u v z w : V) :
    coordFourTensor b i j k l ![u, v, z, w] =
      ⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ := by
  simp only [coordFourTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ, innerSL_apply_apply]
  ring

/-- The operator norm of `coordFourTensor b i j k l` is at most `‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖`. -/
theorem norm_coordFourTensor_le {ι : Type*} (b : ι → V) (i j k l : ι) :
    ‖coordFourTensor b i j k l‖ ≤ ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext a; fin_cases a <;> rfl
  conv_lhs => rw [hm, coordFourTensor_apply]
  rw [Fin.prod_univ_four]
  simp only [Real.norm_eq_abs, abs_mul]
  calc |⟪b i, m 0⟫_ℝ| * |⟪b j, m 1⟫_ℝ| * |⟪b k, m 2⟫_ℝ| * |⟪b l, m 3⟫_ℝ|
      ≤ (‖b i‖ * ‖m 0‖) * (‖b j‖ * ‖m 1‖) * (‖b k‖ * ‖m 2‖) * (‖b l‖ * ‖m 3‖) := by
        gcongr <;> exact abs_real_inner_le_norm _ _
    _ = ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖) := by ring

/-- Every four-tensor expands in an orthonormal basis `b` as the linear combination of
`coordFourTensor b i j k l` weighted by its entries `r ![b i, b j, b k, b l]`. -/
theorem sum_coordFourTensor_smul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) :
    ∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] • coordFourTensor b i j k l = r := by
  refine ext_vec fun u v z w ↦ ?_
  simp only [sum_apply, smul_apply, coordFourTensor_apply, smul_eq_mul]
  conv_rhs => rw [← b.sum_repr' u, apply_sum_first]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [apply_smul_first, ← b.sum_repr' v, apply_sum_second, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  conv_rhs => rw [apply_smul_second, ← b.sum_repr' z, apply_sum_third]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  conv_rhs => rw [apply_smul_third, ← b.sum_repr' w, apply_sum_fourth]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [apply_smul_fourth]
  ring

/-- The rank-one algebraic curvature four-tensor attached to two vectors `u, v : V`, sending
`(a, b, c, d)` to `(⟪u, a⟫ ⟪v, b⟫ - ⟪u, b⟫ ⟪v, a⟫) (⟪u, c⟫ ⟪v, d⟫ - ⟪u, d⟫ ⟪v, c⟫)`. For an
orthonormal pair `u, v` this is the curvature four-tensor of `S² × ℝⁿ⁻²` along the two-plane
spanned by `u` and `v`. -/
def planeCurvature (u v : V) : FourTensor V :=
  coordFourTensor ![u, v] 0 1 0 1 - coordFourTensor ![u, v] 0 1 1 0 -
    coordFourTensor ![u, v] 1 0 0 1 + coordFourTensor ![u, v] 1 0 1 0

/-- Evaluation of the rank-one plane curvature tensor `planeCurvature u v`. -/
@[simp]
theorem planeCurvature_apply (u v a b c d : V) :
    planeCurvature u v ![a, b, c, d] =
      (⟪u, a⟫_ℝ * ⟪v, b⟫_ℝ - ⟪u, b⟫_ℝ * ⟪v, a⟫_ℝ) *
        (⟪u, c⟫_ℝ * ⟪v, d⟫_ℝ - ⟪u, d⟫_ℝ * ⟪v, c⟫_ℝ) := by
  simp only [planeCurvature, add_apply, sub_apply, coordFourTensor_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `planeCurvature u v` is symmetric in `u` and `v`. -/
theorem planeCurvature_comm (u v : V) : planeCurvature u v = planeCurvature v u := by
  refine ext_vec fun a b c d ↦ ?_
  rw [planeCurvature_apply, planeCurvature_apply]
  ring

/-- A degenerate pair `(u, u)` gives the zero plane curvature tensor. -/
@[simp]
theorem planeCurvature_self (u : V) : planeCurvature u u = 0 := by
  refine ext_vec fun a b c d ↦ ?_
  rw [planeCurvature_apply, zero_apply]
  ring

/-- Scaling the first vector scales `planeCurvature` quadratically. -/
theorem planeCurvature_smul_left (t : ℝ) (u v : V) :
    planeCurvature (t • u) v = (t ^ 2) • planeCurvature u v := by
  refine ext_vec fun a b c d ↦ ?_
  simp only [smul_apply, planeCurvature_apply, real_inner_smul_left, smul_eq_mul]
  ring

/-- Scaling the second vector scales `planeCurvature` quadratically. -/
theorem planeCurvature_smul_right (u : V) (t : ℝ) (v : V) :
    planeCurvature u (t • v) = (t ^ 2) • planeCurvature u v := by
  rw [planeCurvature_comm, planeCurvature_smul_left, planeCurvature_comm]

/-- For every pair `u, v`, `planeCurvature u v` is an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_planeCurvature (u v : V) :
    IsAlgebraicCurvature (planeCurvature u v) := by
  refine ⟨fun a b c d ↦ ?_, fun a b c d ↦ ?_, fun a b c d ↦ ?_, fun a b c d ↦ ?_⟩ <;>
    simp only [planeCurvature_apply] <;> ring

/-- On repeated arguments `(a, b, a, b)`, `planeCurvature u v` is a square. -/
theorem planeCurvature_apply_self (u v a b : V) :
    planeCurvature u v ![a, b, a, b] = (⟪u, a⟫_ℝ * ⟪v, b⟫_ℝ - ⟪u, b⟫_ℝ * ⟪v, a⟫_ℝ) ^ 2 := by
  rw [planeCurvature_apply, sq]

/-- `planeCurvature u v` has nonnegative sectional values on every pair of vectors. -/
theorem planeCurvature_apply_self_nonneg (u v a b : V) :
    0 ≤ planeCurvature u v ![a, b, a, b] := by
  rw [planeCurvature_apply_self]
  exact sq_nonneg _

/-- Pulling `planeCurvature (f u) (f v)` back along a linear isometry `f` gives
`planeCurvature u v`. -/
theorem planeCurvature_compContinuousLinearMap_linearIsometry {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : W →ₗᵢ[ℝ] V) (u v : W) :
    (planeCurvature (f u) (f v)).compContinuousLinearMap (fun _ ↦ f.toContinuousLinearMap) =
      planeCurvature u v := by
  refine ext_vec fun a b c d ↦ ?_
  rw [compContinuousLinearMap_apply_vec]
  simp

/-- Zero-extending `planeCurvature u v` from `V` to `WithLp 2 (V × U)` along `WithLp.fstL` produces
`planeCurvature` of the included vectors `(u, 0)` and `(v, 0)`. -/
theorem planeCurvature_compContinuousLinearMap_fstL {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] (u v : V) :
    (planeCurvature u v).compContinuousLinearMap (fun _ ↦ WithLp.fstL 2 ℝ V U) =
      planeCurvature (WithLp.toLp 2 (u, 0)) (WithLp.toLp 2 (v, 0)) := by
  refine ext_vec fun a b c d ↦ ?_
  rw [compContinuousLinearMap_apply_vec]
  simp

/-- The components of the reaction tensor `Q(r)` in an orthonormal basis `b`, with
`rᵢⱼₚₑ = r(b i, b j, b p, b q)`:
`Q(r)ᵢⱼₖₗ = ∑ p, ∑ q, rᵢⱼₚₑ rₖₗₚₑ + 2 ∑ p, ∑ q, rᵢₚₖₑ rⱼₚₗₑ - 2 ∑ p, ∑ q, rᵢₚₗₑ rⱼₚₖₑ`
(Brendle–Schoen, *Manifolds with 1/4-pinched curvature are space forms*, Section 2). -/
def reactionComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) : ℝ :=
  (∑ p, ∑ q, r ![b i, b j, b p, b q] * r ![b k, b l, b p, b q]) +
    2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * r ![b j, b p, b l, b q]) -
    2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * r ![b j, b p, b k, b q])

/-- Explicit formula for `reactionComponent`. -/
theorem reactionComponent_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) :
    reactionComponent b r i j k l =
      (∑ p, ∑ q, r ![b i, b j, b p, b q] * r ![b k, b l, b p, b q]) +
        2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * r ![b j, b p, b l, b q]) -
        2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * r ![b j, b p, b k, b q]) :=
  (rfl)

/-- Bianchi contraction identity for an algebraic curvature tensor `r` and a finite family
`f : ι → V`:
`2 ∑ p, ∑ q, r(u, v, f p, f q) r(z, f p, w, f q) =
  ∑ p, ∑ q, r(u, v, f p, f q) r(z, w, f p, f q)`. -/
theorem IsAlgebraicCurvature.two_mul_sum_mul_eq {ι : Type*} [Fintype ι]
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (f : ι → V) (u v z w : V) :
    2 * (∑ p, ∑ q, r ![u, v, f p, f q] * r ![z, f p, w, f q]) =
      ∑ p, ∑ q, r ![u, v, f p, f q] * r ![z, w, f p, f q] := by
  have hswap : (∑ p, ∑ q, r ![u, v, f p, f q] * r ![z, f p, w, f q]) =
      -∑ p, ∑ q, r ![u, v, f p, f q] * r ![z, f q, w, f p] := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hr.antisymm_last u v (f q) (f p), neg_mul]
  have hbianchi (p q : ι) :
      r ![z, f p, w, f q] - r ![z, f q, w, f p] = r ![z, w, f p, f q] := by
    have hcyc := hr.cyclic_eq_zero (f p) w (f q) z
    have h1 : r ![f p, w, f q, z] = r ![z, f q, w, f p] := by
      rw [hr.antisymm_first, hr.antisymm_last, neg_neg, hr.swap_pairs]
    have h2 : r ![w, f q, f p, z] = -r ![z, f p, w, f q] := by
      rw [hr.antisymm_last, hr.swap_pairs]
    have h3 : r ![f q, f p, w, z] = r ![z, w, f p, f q] := by
      rw [hr.antisymm_first, hr.antisymm_last, neg_neg, hr.swap_pairs]
    linear_combination -hcyc + h1 + h2 + h3
  have hsum : 2 * (∑ p, ∑ q, r ![u, v, f p, f q] * r ![z, f p, w, f q]) =
      (∑ p, ∑ q, r ![u, v, f p, f q] * r ![z, f p, w, f q]) -
        ∑ p, ∑ q, r ![u, v, f p, f q] * r ![z, f q, w, f p] := by
    linear_combination hswap
  rw [hsum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← mul_sub, hbianchi]

/-- Continuous linear evaluation of a four-tensor at four vectors. -/
private def evalCLM (u v z w : V) : FourTensor V →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 ↦ V) ℝ ![u, v, z, w]

/-- Continuous bilinear product `(r, s) ↦ r(u₁, v₁, z₁, w₁) * s(u₂, v₂, z₂, w₂)`. -/
private def mulEvalBilin (u₁ v₁ z₁ w₁ u₂ v₂ z₂ w₂ : V) :
    FourTensor V [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 2 ℝ).compContinuousLinearMap
    ![evalCLM u₁ v₁ z₁ w₁, evalCLM u₂ v₂ z₂ w₂]

@[simp]
private theorem mulEvalBilin_apply (u₁ v₁ z₁ w₁ u₂ v₂ z₂ w₂ : V) (r s : FourTensor V) :
    mulEvalBilin u₁ v₁ z₁ w₁ u₂ v₂ z₂ w₂ ![r, s] =
      r ![u₁, v₁, z₁, w₁] * s ![u₂, v₂, z₂, w₂] := by
  simp [mulEvalBilin, evalCLM, List.ofFn_succ]

/-- The `(i, j, k, l)`-component functional of the symmetric bilinear polarization of the reaction
tensor in an orthonormal basis `b`. -/
private def reactionBilinearComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (i j k l : ι) : FourTensor V [×2]→L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (∑ p, ∑ q,
      (mulEvalBilin (b i) (b j) (b p) (b q) (b k) (b l) (b p) (b q) +
        mulEvalBilin (b k) (b l) (b p) (b q) (b i) (b j) (b p) (b q))) +
    (∑ p, ∑ q,
      (mulEvalBilin (b i) (b p) (b k) (b q) (b j) (b p) (b l) (b q) +
        mulEvalBilin (b j) (b p) (b l) (b q) (b i) (b p) (b k) (b q))) -
    (∑ p, ∑ q,
      (mulEvalBilin (b i) (b p) (b l) (b q) (b j) (b p) (b k) (b q) +
        mulEvalBilin (b j) (b p) (b k) (b q) (b i) (b p) (b l) (b q)))

/-- The bilinear form `(x, y) ↦ r(u, v, x, y)` slicing the last two slots of a four-tensor. -/
private def lastSlice (r : FourTensor V) (u v : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, v, x, y])
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

/-- The bilinear form `(x, y) ↦ r(u, x, z, y)` slicing the second and fourth slots of a
four-tensor. -/
private def evenSlice (r : FourTensor V) (u z : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, x, z, y])
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

end InnerProductSpace

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The four-tensor `(u, v, z, w) ↦ r(u, v, x, y) * s(z, w, x, y)` for fixed `x, y : V`. -/
private def pairFirstFourTensor (r s : FourTensor V) (x y : V) : FourTensor V :=
  let f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
    MultilinearMap.mk' (fun m ↦ r ![m 0, m 1, x, y] * s ![m 2, m 3, x, y])
      (fun m i a b ↦ by
        fin_cases i
        · simp [Function.update, r.apply_add_first, add_mul]
        · simp [Function.update, r.apply_add_second, add_mul]
        · simp [Function.update, s.apply_add_first, mul_add]
        · simp [Function.update, s.apply_add_second, mul_add])
      (fun m i c a ↦ by
        fin_cases i
        · simp [Function.update, r.apply_smul_first, mul_assoc]
        · simp [Function.update, r.apply_smul_second, mul_assoc]
        · simp [Function.update, s.apply_smul_first, mul_left_comm]
        · simp [Function.update, s.apply_smul_second, mul_left_comm])
  { f with cont := f.continuous_of_finiteDimensional }

@[simp]
private theorem pairFirstFourTensor_apply (r s : FourTensor V) (x y u v z w : V) :
    pairFirstFourTensor r s x y ![u, v, z, w] = r ![u, v, x, y] * s ![z, w, x, y] := rfl

/-- The four-tensor `(u, v, z, w) ↦ r(u, x, z, y) * s(v, x, w, y)` for fixed `x, y : V`. -/
private def pairMixedFourTensor (r s : FourTensor V) (x y : V) : FourTensor V :=
  let f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
    MultilinearMap.mk' (fun m ↦ r ![m 0, x, m 2, y] * s ![m 1, x, m 3, y])
      (fun m i a b ↦ by
        fin_cases i
        · simp [Function.update, r.apply_add_first, add_mul]
        · simp [Function.update, s.apply_add_first, mul_add]
        · simp [Function.update, r.apply_add_third, add_mul]
        · simp [Function.update, s.apply_add_third, mul_add])
      (fun m i c a ↦ by
        fin_cases i
        · simp [Function.update, r.apply_smul_first, mul_assoc]
        · simp [Function.update, s.apply_smul_first, mul_left_comm]
        · simp [Function.update, r.apply_smul_third, mul_assoc]
        · simp [Function.update, s.apply_smul_third, mul_left_comm])
  { f with cont := f.continuous_of_finiteDimensional }

@[simp]
private theorem pairMixedFourTensor_apply (r s : FourTensor V) (x y u v z w : V) :
    pairMixedFourTensor r s x y ![u, v, z, w] = r ![u, x, z, y] * s ![v, x, w, y] := rfl

/-- The four-tensor `(u, v, z, w) ↦ r(u, x, w, y) * s(v, x, z, y)` for fixed `x, y : V`. -/
private def pairCrossFourTensor (r s : FourTensor V) (x y : V) : FourTensor V :=
  let f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
    MultilinearMap.mk' (fun m ↦ r ![m 0, x, m 3, y] * s ![m 1, x, m 2, y])
      (fun m i a b ↦ by
        fin_cases i
        · simp [Function.update, r.apply_add_first, add_mul]
        · simp [Function.update, s.apply_add_first, mul_add]
        · simp [Function.update, s.apply_add_third, mul_add]
        · simp [Function.update, r.apply_add_third, add_mul])
      (fun m i c a ↦ by
        fin_cases i
        · simp [Function.update, r.apply_smul_first, mul_assoc]
        · simp [Function.update, s.apply_smul_first, mul_left_comm]
        · simp [Function.update, s.apply_smul_third, mul_left_comm]
        · simp [Function.update, r.apply_smul_third, mul_assoc])
  { f with cont := f.continuous_of_finiteDimensional }

@[simp]
private theorem pairCrossFourTensor_apply (r s : FourTensor V) (x y u v z w : V) :
    pairCrossFourTensor r s x y ![u, v, z, w] = r ![u, x, w, y] * s ![v, x, z, y] := rfl

/-- The reaction tensor `Q(r)` of the curvature evolution `D_t R = Δ R + Q(R)`, expanded in the
standard orthonormal basis of `V`:
`Q(r) = ∑ i, ∑ j, ∑ k, ∑ l, Q(r)ᵢⱼₖₗ • coordFourTensor b i j k l`. Its independence of the
orthonormal basis is `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionComponent (stdOrthonormalBasis ℝ V) r i j k l •
      coordFourTensor (stdOrthonormalBasis ℝ V) i j k l

/-- The continuous symmetric bilinear polarization of `reactionTensor`, normalized so that
`reactionBilinear ![r, r] = reactionTensor r`. -/
def reactionBilinear : FourTensor V [×2]→L[ℝ] FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (reactionBilinearComponent (stdOrthonormalBasis ℝ V) i j k l).smulRight
      (coordFourTensor (stdOrthonormalBasis ℝ V) i j k l)

/-- Basis independence of `reactionBilinear`: in every orthonormal basis `b` of `V`,
`reactionBilinear ![r, s]` is given by the symmetrized double contraction over `b`. -/
theorem reactionBilinear_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinear ![r, s] ![u, v, z, w] =
      2⁻¹ * (∑ p, ∑ q, (r ![u, v, b p, b q] * s ![z, w, b p, b q] +
          s ![u, v, b p, b q] * r ![z, w, b p, b q])) +
        (∑ p, ∑ q, (r ![u, b p, z, b q] * s ![v, b p, w, b q] +
          s ![u, b p, z, b q] * r ![v, b p, w, b q])) -
        (∑ p, ∑ q, (r ![u, b p, w, b q] * s ![v, b p, z, b q] +
          s ![u, b p, w, b q] * r ![v, b p, z, b q])) := by
  set e := stdOrthonormalBasis ℝ V with he
  -- Bundle the contraction in `e` as a four-tensor `T`; its basis expansion in `e` is
  -- literally `reactionBilinear ![r, s]`.
  let T : FourTensor V :=
    (2⁻¹ : ℝ) • (∑ p, ∑ q,
        (pairFirstFourTensor r s (e p) (e q) + pairFirstFourTensor s r (e p) (e q))) +
      (∑ p, ∑ q,
        (pairMixedFourTensor r s (e p) (e q) + pairMixedFourTensor s r (e p) (e q))) -
      (∑ p, ∑ q,
        (pairCrossFourTensor r s (e p) (e q) + pairCrossFourTensor s r (e p) (e q)))
  have hT : reactionBilinear ![r, s] = T := by
    rw [← sum_coordFourTensor_smul e T, reactionBilinear, ← he]
    simp only [sum_apply, ContinuousMultilinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ congrArg (· • _) ?_
    simp only [T, reactionBilinearComponent, sub_apply, add_apply, smul_apply, sum_apply,
      mulEvalBilin_apply, pairFirstFourTensor_apply, pairMixedFourTensor_apply,
      pairCrossFourTensor_apply, smul_eq_mul]
    congr 1
    · congr 1
      · exact congrArg (2⁻¹ * ·)
          (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
      · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  -- Any double contraction of two bilinear forms over `e` equals the contraction over `b`.
  have h1 {φ ψ : V →ₗ[ℝ] ℝ} : (∑ p, φ (e p) * ψ (e p)) = ∑ p, φ (b p) * ψ (b p) := by
    simpa only [LinearMap.coe_smulRight, LinearMap.smul_apply, smul_eq_mul] using
      (bilinFormTrace_eq_sum (φ.smulRight ψ) e).symm.trans
        (bilinFormTrace_eq_sum (φ.smulRight ψ) b)
  have hbasis (F G : BilinForm ℝ V) :
      (∑ p, ∑ q, F (e p) (e q) * G (e p) (e q)) = ∑ p, ∑ q, F (b p) (b q) * G (b p) (b q) := by
    calc (∑ p, ∑ q, F (e p) (e q) * G (e p) (e q))
        = ∑ p, ∑ q, F (e p) (b q) * G (e p) (b q) :=
          Finset.sum_congr rfl fun p _ ↦ h1 (φ := F (e p)) (ψ := G (e p))
      _ = ∑ q, ∑ p, F.flip (b q) (e p) * G.flip (b q) (e p) := Finset.sum_comm
      _ = ∑ q, ∑ p, F.flip (b q) (b p) * G.flip (b q) (b p) :=
          Finset.sum_congr rfl fun q _ ↦ h1 (φ := F.flip (b q)) (ψ := G.flip (b q))
      _ = ∑ p, ∑ q, F (b p) (b q) * G (b p) (b q) := Finset.sum_comm
  rw [hT]
  simp only [T, sub_apply, add_apply, smul_apply, sum_apply, smul_eq_mul,
    pairFirstFourTensor_apply, pairMixedFourTensor_apply, pairCrossFourTensor_apply,
    Finset.sum_add_distrib]
  have b1 := hbasis (lastSlice r u v) (lastSlice s z w)
  have b2 := hbasis (lastSlice s u v) (lastSlice r z w)
  have b3 := hbasis (evenSlice r u z) (evenSlice s v w)
  have b4 := hbasis (evenSlice s u z) (evenSlice r v w)
  have b5 := hbasis (evenSlice r u w) (evenSlice s v z)
  have b6 := hbasis (evenSlice s u w) (evenSlice r v z)
  simp only [lastSlice, evenSlice, LinearMap.mk₂_apply] at b1 b2 b3 b4 b5 b6
  rw [b1, b2, b3, b4, b5, b6]

/-- On the diagonal `(r, r)`, `reactionBilinear` recovers `reactionTensor`. -/
@[simp]
theorem reactionBilinear_self (r : FourTensor V) :
    reactionBilinear ![r, r] = reactionTensor r := by
  set e := stdOrthonormalBasis ℝ V with he
  let T : FourTensor V :=
    (∑ p, ∑ q, pairFirstFourTensor r r (e p) (e q)) +
      (2 : ℝ) • (∑ p, ∑ q, pairMixedFourTensor r r (e p) (e q)) -
      (2 : ℝ) • (∑ p, ∑ q, pairCrossFourTensor r r (e p) (e q))
  have hT : reactionTensor r = T := by
    rw [← sum_coordFourTensor_smul e T, reactionTensor, ← he]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    simp [T, reactionComponent]
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis e, hT]
  simp only [T, sub_apply, add_apply, smul_apply, sum_apply, smul_eq_mul,
    pairFirstFourTensor_apply, pairMixedFourTensor_apply, pairCrossFourTensor_apply,
    ← two_mul, ← Finset.mul_sum]
  ring

/-- `reactionBilinear` is symmetric in its two four-tensor arguments. -/
theorem reactionBilinear_comm (r s : FourTensor V) :
    reactionBilinear ![r, s] = reactionBilinear ![s, r] := by
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  simp only [Finset.sum_add_distrib]
  ring

/-- `reactionBilinear` is additive in its first argument. -/
theorem reactionBilinear_add_left (r₁ r₂ s : FourTensor V) :
    reactionBilinear ![r₁ + r₂, s] = reactionBilinear ![r₁, s] + reactionBilinear ![r₂, s] := by
  have hu (x : FourTensor V) : Function.update ![r₁, s] 0 x = ![x, s] := by
    funext i; fin_cases i <;> rfl
  simpa only [hu] using reactionBilinear.map_update_add ![r₁, s] 0 r₁ r₂

/-- `reactionBilinear` is additive in its second argument. -/
theorem reactionBilinear_add_right (r s₁ s₂ : FourTensor V) :
    reactionBilinear ![r, s₁ + s₂] = reactionBilinear ![r, s₁] + reactionBilinear ![r, s₂] := by
  rw [reactionBilinear_comm, reactionBilinear_add_left, reactionBilinear_comm s₁ r,
    reactionBilinear_comm s₂ r]

/-- `reactionBilinear` is homogeneous in its first argument. -/
theorem reactionBilinear_smul_left (c : ℝ) (r s : FourTensor V) :
    reactionBilinear ![c • r, s] = c • reactionBilinear ![r, s] := by
  have hu (x : FourTensor V) : Function.update ![r, s] 0 x = ![x, s] := by
    funext i; fin_cases i <;> rfl
  simpa only [hu] using reactionBilinear.map_update_smul ![r, s] 0 c r

/-- `reactionBilinear` is homogeneous in its second argument. -/
theorem reactionBilinear_smul_right (r : FourTensor V) (c : ℝ) (s : FourTensor V) :
    reactionBilinear ![r, c • s] = c • reactionBilinear ![r, s] := by
  rw [reactionBilinear_comm, reactionBilinear_smul_left, reactionBilinear_comm]

/-- `reactionBilinear` vanishes when its first argument is zero. -/
@[simp]
theorem reactionBilinear_zero_left (s : FourTensor V) : reactionBilinear ![0, s] = 0 :=
  reactionBilinear.map_coord_zero 0 rfl

/-- `reactionBilinear` vanishes when its second argument is zero. -/
@[simp]
theorem reactionBilinear_zero_right (r : FourTensor V) : reactionBilinear ![r, 0] = 0 :=
  reactionBilinear.map_coord_zero 1 rfl

/-- `reactionBilinear` negates when its first argument is negated. -/
@[simp]
theorem reactionBilinear_neg_left (r s : FourTensor V) :
    reactionBilinear ![-r, s] = -reactionBilinear ![r, s] := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← reactionBilinear_add_left, neg_add_cancel, reactionBilinear_zero_left]

/-- `reactionBilinear` negates when its second argument is negated. -/
@[simp]
theorem reactionBilinear_neg_right (r s : FourTensor V) :
    reactionBilinear ![r, -s] = -reactionBilinear ![r, s] := by
  rw [reactionBilinear_comm, reactionBilinear_neg_left, reactionBilinear_comm]

/-- `reactionBilinear` preserves subtraction in its first argument. -/
theorem reactionBilinear_sub_left (r₁ r₂ s : FourTensor V) :
    reactionBilinear ![r₁ - r₂, s] = reactionBilinear ![r₁, s] - reactionBilinear ![r₂, s] := by
  rw [sub_eq_add_neg, reactionBilinear_add_left, reactionBilinear_neg_left, ← sub_eq_add_neg]

/-- `reactionBilinear` preserves subtraction in its second argument. -/
theorem reactionBilinear_sub_right (r s₁ s₂ : FourTensor V) :
    reactionBilinear ![r, s₁ - s₂] = reactionBilinear ![r, s₁] - reactionBilinear ![r, s₂] := by
  rw [sub_eq_add_neg, reactionBilinear_add_right, reactionBilinear_neg_right, ← sub_eq_add_neg]

/-- Basis independence of the reaction tensor: in every orthonormal basis `b` of `V`, `Q(r)` is
the contraction
`Q(r)(u, v, z, w) = ∑ p, ∑ q, r(u, v, b p, b q) r(z, w, b p, b q) +
  2 ∑ p, ∑ q, r(u, b p, z, b q) r(v, b p, w, b q) -
  2 ∑ p, ∑ q, r(u, b p, w, b q) r(v, b p, z, b q)`. -/
theorem reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
        2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) := by
  rw [← reactionBilinear_self, reactionBilinear_apply_orthonormalBasis b]
  simp only [← two_mul, ← Finset.mul_sum]
  ring

/-- The reaction tensor of `0` is `0`. -/
@[simp]
theorem reactionTensor_zero : reactionTensor (0 : FourTensor V) = 0 := by
  rw [← reactionBilinear_self, reactionBilinear_zero_left]

/-- Negating a four-tensor leaves its reaction tensor unchanged. -/
@[simp]
theorem reactionTensor_neg (r : FourTensor V) : reactionTensor (-r) = reactionTensor r := by
  rw [← reactionBilinear_self, reactionBilinear_neg_left, reactionBilinear_neg_right, neg_neg,
    reactionBilinear_self]

/-- `reactionTensor` is homogeneous of degree two: `Q(c • r) = c² • Q(r)`. -/
theorem reactionTensor_smul (c : ℝ) (r : FourTensor V) :
    reactionTensor (c • r) = (c ^ 2) • reactionTensor r := by
  rw [← reactionBilinear_self, reactionBilinear_smul_left, reactionBilinear_smul_right, smul_smul,
    ← sq, reactionBilinear_self]

/-- Quadratic expansion of `reactionTensor` on a sum. -/
theorem reactionTensor_add (r s : FourTensor V) :
    reactionTensor (r + s) =
      reactionTensor r + (2 : ℝ) • reactionBilinear ![r, s] + reactionTensor s := by
  rw [← reactionBilinear_self, reactionBilinear_add_left, reactionBilinear_add_right,
    reactionBilinear_add_right, reactionBilinear_self, reactionBilinear_self,
    reactionBilinear_comm s r, two_smul]
  abel

/-- Quadratic expansion of `reactionTensor` on a difference. -/
theorem reactionTensor_sub (r s : FourTensor V) :
    reactionTensor (r - s) =
      reactionTensor r - (2 : ℝ) • reactionBilinear ![r, s] + reactionTensor s := by
  rw [sub_eq_add_neg, reactionTensor_add, reactionBilinear_neg_right, reactionTensor_neg,
    smul_neg, ← sub_eq_add_neg]

/-- Polarization: `reactionBilinear` is recovered from `reactionTensor` by
`B(r, s) = 2⁻¹ • (Q(r + s) - Q(r) - Q(s))`. -/
theorem reactionBilinear_eq_half_sub (r s : FourTensor V) :
    reactionBilinear ![r, s] =
      (2⁻¹ : ℝ) • (reactionTensor (r + s) - reactionTensor r - reactionTensor s) := by
  have h : reactionTensor (r + s) - reactionTensor r - reactionTensor s =
      (2 : ℝ) • reactionBilinear ![r, s] := by
    rw [reactionTensor_add]
    abel
  rw [h, smul_smul]
  norm_num

/-- Difference factorization `Q(r) - Q(s) = B(r + s, r - s)`. -/
theorem reactionTensor_sub_reactionTensor (r s : FourTensor V) :
    reactionTensor r - reactionTensor s = reactionBilinear ![r + s, r - s] := by
  rw [reactionBilinear_add_left, reactionBilinear_sub_right, reactionBilinear_sub_right,
    reactionBilinear_self, reactionBilinear_self, reactionBilinear_comm s r]
  abel

/-! ### Preservation of algebraic curvature symmetries -/

/-- The reaction tensor of an algebraic curvature tensor is an algebraic curvature tensor: `Q`
preserves both pair antisymmetries, pair interchange, and the first Bianchi identity. -/
theorem IsAlgebraicCurvature.reactionTensor {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.reactionTensor r) := by
  set b := stdOrthonormalBasis ℝ V
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [reactionTensor_apply_orthonormalBasis b]
  · have hA : (∑ p, ∑ q, r ![v, u, b p, b q] * r ![z, w, b p, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp_rw [hr.antisymm_first v u, neg_mul, Finset.sum_neg_distrib]
    have hBC (x y : V) : (∑ p, ∑ q, r ![v, b p, x, b q] * r ![u, b p, y, b q]) =
        ∑ p, ∑ q, r ![u, b p, y, b q] * r ![v, b p, x, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [hA, hBC z w, hBC w z]
    ring
  · have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, z, b p, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp_rw [hr.antisymm_first w z, mul_neg, Finset.sum_neg_distrib]
    rw [hA]
    ring
  · have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
        ∑ p, ∑ q, r ![z, w, b p, b q] * r ![u, v, b p, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    have hB (x y : V) : (∑ p, ∑ q, r ![z, b p, x, b q] * r ![w, b p, y, b q]) =
        ∑ p, ∑ q, r ![x, b p, z, b q] * r ![y, b p, w, b q] := by
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hr.swap_pairs z (b q) x (b p), hr.swap_pairs w (b q) y (b p)]
    have hC : (∑ p, ∑ q, r ![z, b p, v, b q] * r ![w, b p, u, b q]) =
        ∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q] := by
      rw [hB v u]
      exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [hA, hB u v, hC]
  · -- Group `2 * (B(x, y, t) - C(y, t, x)) = -A(t, x, y)` for each cyclic triple `(x, y, t)`.
    have hBC (x y t : V) :
        2 * ((∑ p, ∑ q, r ![x, b p, t, b q] * r ![y, b p, w, b q]) -
            ∑ p, ∑ q, r ![y, b p, w, b q] * r ![t, b p, x, b q]) =
          -∑ p, ∑ q, r ![t, x, b p, b q] * r ![y, w, b p, b q] := by
      have hdiff : (∑ p, ∑ q, r ![x, b p, t, b q] * r ![y, b p, w, b q]) -
          (∑ p, ∑ q, r ![y, b p, w, b q] * r ![t, b p, x, b q]) =
          -∑ p, ∑ q, r ![t, x, b p, b q] * r ![y, b p, w, b q] := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        have hcyc := hr.cyclic_eq_zero x (b p) t (b q)
        have hant := hr.antisymm_first (b p) t x (b q)
        have hxt : r ![x, b p, t, b q] - r ![t, b p, x, b q] = -r ![t, x, b p, b q] := by
          linear_combination hcyc - hant
        calc r ![x, b p, t, b q] * r ![y, b p, w, b q] -
              r ![y, b p, w, b q] * r ![t, b p, x, b q]
            = (r ![x, b p, t, b q] - r ![t, b p, x, b q]) * r ![y, b p, w, b q] := by ring
          _ = -(r ![t, x, b p, b q] * r ![y, b p, w, b q]) := by rw [hxt, neg_mul]
      rw [hdiff, mul_neg, hr.two_mul_sum_mul_eq b t x y w]
    linear_combination hBC u v z + hBC v z u + hBC z u v

/-- `reactionTensor` maps `algebraicCurvatureSubmodule V` into itself. -/
theorem reactionTensor_mem_algebraicCurvatureSubmodule {r : FourTensor V}
    (hr : r ∈ algebraicCurvatureSubmodule V) :
    reactionTensor r ∈ algebraicCurvatureSubmodule V := by
  rw [mem_algebraicCurvatureSubmodule] at hr ⊢
  exact hr.reactionTensor

/-- The symmetric bilinear polarization `reactionBilinear` preserves algebraic curvature tensors. -/
theorem IsAlgebraicCurvature.reactionBilinear {r s : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hs : IsAlgebraicCurvature s) :
    IsAlgebraicCurvature (FourTensor.reactionBilinear ![r, s]) := by
  rw [← mem_algebraicCurvatureSubmodule] at hr hs ⊢
  rw [reactionBilinear_eq_half_sub]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.sub_mem _
      (reactionTensor_mem_algebraicCurvatureSubmodule (Submodule.add_mem _ hr hs))
      (reactionTensor_mem_algebraicCurvatureSubmodule hr))
    (reactionTensor_mem_algebraicCurvatureSubmodule hs))

/-- `reactionBilinear` maps pairs in `algebraicCurvatureSubmodule V` into
`algebraicCurvatureSubmodule V`. -/
theorem reactionBilinear_mem_algebraicCurvatureSubmodule {r s : FourTensor V}
    (hr : r ∈ algebraicCurvatureSubmodule V) (hs : s ∈ algebraicCurvatureSubmodule V) :
    reactionBilinear ![r, s] ∈ algebraicCurvatureSubmodule V := by
  rw [mem_algebraicCurvatureSubmodule] at hr hs ⊢
  exact hr.reactionBilinear hs

/-! ### Coisometry pullback, orthogonal equivariance, and zero extension -/

/-- Pulling back four-tensors along any continuous linear map `P : W →L[ℝ] V` with
`P ∘L P.adjoint = id` commutes with `reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_of_comp_adjoint_eq_id {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (r s : FourTensor V) :
    reactionBilinear ![r.compContinuousLinearMap fun _ ↦ P,
        s.compContinuousLinearMap fun _ ↦ P] =
      (reactionBilinear ![r, s]).compContinuousLinearMap fun _ ↦ P := by
  set bW := stdOrthonormalBasis ℝ W
  set bV := stdOrthonormalBasis ℝ V
  have hP' (x : V) : P (P.adjoint x) = x := by
    simpa using DFunLike.congr_fun hP x
  have h1 {φ ψ : V →ₗ[ℝ] ℝ} :
      (∑ a, φ (P (bW a)) * ψ (P (bW a))) = ∑ p, φ (bV p) * ψ (bV p) := by
    have hexp (a : Fin (Module.finrank ℝ W)) :
        φ (P (bW a)) = ∑ p, ⟪bW a, P.adjoint (bV p)⟫_ℝ * φ (bV p) := by
      conv_lhs => rw [← bV.sum_repr' (P (bW a)), map_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [map_smul, smul_eq_mul, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    calc (∑ a, φ (P (bW a)) * ψ (P (bW a)))
        = ∑ a, ∑ p, ⟪bW a, P.adjoint (bV p)⟫_ℝ * φ (bV p) * ψ (P (bW a)) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [hexp a, Finset.sum_mul]
      _ = ∑ p, φ (bV p) * ∑ a, ⟪bW a, P.adjoint (bV p)⟫_ℝ * ψ (P (bW a)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ ↦ by ring
      _ = ∑ p, φ (bV p) * ψ (P (∑ a, ⟪bW a, P.adjoint (bV p)⟫_ℝ • bW a)) := by
          refine Finset.sum_congr rfl fun p _ ↦ congrArg (φ (bV p) * ·) ?_
          rw [map_sum, map_sum]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [map_smul, map_smul, smul_eq_mul]
      _ = ∑ p, φ (bV p) * ψ (bV p) := by
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [bW.sum_repr', hP']
  have h2 (F G : BilinForm ℝ V) :
      (∑ a, ∑ b, F (P (bW a)) (P (bW b)) * G (P (bW a)) (P (bW b))) =
        ∑ p, ∑ q, F (bV p) (bV q) * G (bV p) (bV q) := by
    calc (∑ a, ∑ b, F (P (bW a)) (P (bW b)) * G (P (bW a)) (P (bW b)))
        = ∑ a, ∑ q, F (P (bW a)) (bV q) * G (P (bW a)) (bV q) :=
          Finset.sum_congr rfl fun a _ ↦ h1 (φ := F (P (bW a))) (ψ := G (P (bW a)))
      _ = ∑ q, ∑ a, F.flip (bV q) (P (bW a)) * G.flip (bV q) (P (bW a)) := Finset.sum_comm
      _ = ∑ q, ∑ p, F.flip (bV q) (bV p) * G.flip (bV q) (bV p) :=
          Finset.sum_congr rfl fun q _ ↦ h1 (φ := F.flip (bV q)) (ψ := G.flip (bV q))
      _ = ∑ p, ∑ q, F (bV p) (bV q) * G (bV p) (bV q) := Finset.sum_comm
  refine ext_vec fun u v z w ↦ ?_
  rw [compContinuousLinearMap_apply_vec,
    reactionBilinear_apply_orthonormalBasis bW, reactionBilinear_apply_orthonormalBasis bV]
  simp only [compContinuousLinearMap_apply_vec, Finset.sum_add_distrib]
  have c1 := h2 (lastSlice r (P u) (P v)) (lastSlice s (P z) (P w))
  have c2 := h2 (lastSlice s (P u) (P v)) (lastSlice r (P z) (P w))
  have c3 := h2 (evenSlice r (P u) (P z)) (evenSlice s (P v) (P w))
  have c4 := h2 (evenSlice s (P u) (P z)) (evenSlice r (P v) (P w))
  have c5 := h2 (evenSlice r (P u) (P w)) (evenSlice s (P v) (P z))
  have c6 := h2 (evenSlice s (P u) (P w)) (evenSlice r (P v) (P z))
  simp only [lastSlice, evenSlice, LinearMap.mk₂_apply] at c1 c2 c3 c4 c5 c6
  rw [c1, c2, c3, c4, c5, c6]

/-- Pulling back a four-tensor along any continuous linear map `P : W →L[ℝ] V` with
`P ∘L P.adjoint = id` commutes with `reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_of_comp_adjoint_eq_id {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V) (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ P) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ P := by
  rw [← reactionBilinear_self, ← reactionBilinear_self,
    reactionBilinear_compContinuousLinearMap_of_comp_adjoint_eq_id hP]

/-- `reactionBilinear` is equivariant under linear isometric equivalences. -/
theorem reactionBilinear_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r s : FourTensor V) :
    reactionBilinear
        ![r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap,
          s.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap] =
      (reactionBilinear ![r, s]).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  refine reactionBilinear_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r s
  have hcoe : e.toLinearIsometry.toContinuousLinearMap = (e : W →L[ℝ] V) := rfl
  rw [hcoe, LinearIsometryEquiv.adjoint_eq_symm]
  ext x
  exact e.apply_symm_apply x

/-- `reactionTensor` is equivariant under linear isometric equivalences (`O(n)`-equivariance). -/
theorem reactionTensor_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    reactionTensor
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  rw [← reactionBilinear_self, ← reactionBilinear_self,
    reactionBilinear_compContinuousLinearMap_linearIsometryEquiv]

/-- Zero extension from `V` to `WithLp 2 (V × U)` along `WithLp.fstL` commutes with
`reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_fstL {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (r s : FourTensor V) :
    reactionBilinear ![r.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U,
        s.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U] =
      (reactionBilinear ![r, s]).compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U := by
  refine reactionBilinear_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r s
  have hadj (x : V) : (WithLp.fstL 2 ℝ V U).adjoint x = WithLp.toLp 2 (x, 0) := by
    refine ext_inner_left ℝ fun z ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_right, WithLp.prod_inner_apply]
    simp
  ext x
  simp [hadj x]

/-- Zero extension from `V` to `WithLp 2 (V × U)` along `WithLp.fstL` commutes with
`reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_fstL {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U := by
  rw [← reactionBilinear_self, ← reactionBilinear_self,
    reactionBilinear_compContinuousLinearMap_fstL]

/-! ### Norm bounds, smoothness, Fréchet derivative, and Lipschitz estimates -/

/-- For each pair of four-tensors `r, s`, `‖reactionBilinear ![r, s]‖ ≤ 5 * dim V * ‖r‖ * ‖s‖`. -/
theorem norm_reactionBilinear_apply_le (r s : FourTensor V) :
    ‖reactionBilinear ![r, s]‖ ≤ 5 * (Module.finrank ℝ V : ℝ) * ‖r‖ * ‖s‖ := by
  set b := stdOrthonormalBasis ℝ V
  have hnorm {θ : V →ₗ[ℝ] ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hθ : ∀ z, |θ z| ≤ C * ‖z‖) :
      ‖∑ q, θ (b q) • b q‖ ≤ C := by
    set z := ∑ q, θ (b q) • b q
    have hz : ‖z‖ ^ 2 = θ z := by
      have h1 : ⟪z, z⟫_ℝ = ∑ q, θ (b q) * θ (b q) := by
        simpa [z] using b.orthonormal.inner_sum (fun q ↦ θ (b q)) (fun q ↦ θ (b q)) Finset.univ
      rw [← real_inner_self_eq_norm_sq, h1, map_sum]
      simp [map_smul, smul_eq_mul]
    have hle : ‖z‖ ^ 2 ≤ C * ‖z‖ := by
      calc ‖z‖ ^ 2 = |θ z| := by rw [← hz, abs_of_nonneg (sq_nonneg _)]
        _ ≤ C * ‖z‖ := hθ z
    nlinarith [norm_nonneg z]
  have hsum {F G : BilinForm ℝ V} {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
      (hF : ∀ p x, |F (b p) x| ≤ A * ‖x‖) (hG : ∀ p x, |G (b p) x| ≤ B * ‖x‖) :
      |∑ p, ∑ q, F (b p) (b q) * G (b p) (b q)| ≤ (Module.finrank ℝ V : ℝ) * (A * B) := by
    have hp (p) : |∑ q, F (b p) (b q) * G (b p) (b q)| ≤ A * B := by
      have hxy : (∑ q, F (b p) (b q) * G (b p) (b q)) =
          ⟪∑ q, F (b p) (b q) • b q, ∑ q, G (b p) (b q) • b q⟫_ℝ := by
        simpa using
          (b.orthonormal.inner_sum (fun q ↦ F (b p) (b q)) (fun q ↦ G (b p) (b q)) Finset.univ).symm
      rw [hxy]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hnorm hA0 (hF p)) (hnorm hB0 (hG p)) (norm_nonneg _) hA0)
    calc |∑ p, ∑ q, F (b p) (b q) * G (b p) (b q)|
        ≤ ∑ p, |∑ q, F (b p) (b q) * G (b p) (b q)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin (Module.finrank ℝ V), A * B := Finset.sum_le_sum fun p _ ↦ hp p
      _ = (Module.finrank ℝ V : ℝ) * (A * B) := by simp
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hm]
  rw [Fin.prod_univ_four, reactionBilinear_apply_orthonormalBasis b, Real.norm_eq_abs]
  have hlast (t : FourTensor V) (u v : V) (p : Fin (Module.finrank ℝ V)) (x : V) :
      |lastSlice t u v (b p) x| ≤ (‖t‖ * ‖u‖ * ‖v‖) * ‖x‖ := by
    simpa only [lastSlice, LinearMap.mk₂_apply, Real.norm_eq_abs, Fin.prod_univ_four,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, b.norm_eq_one,
      mul_one, mul_assoc] using t.le_opNorm ![u, v, b p, x]
  have heven (t : FourTensor V) (u z : V) (p : Fin (Module.finrank ℝ V)) (x : V) :
      |evenSlice t u z (b p) x| ≤ (‖t‖ * ‖u‖ * ‖z‖) * ‖x‖ := by
    have h := t.le_opNorm ![u, b p, z, x]
    rw [Real.norm_eq_abs, Fin.prod_univ_four] at h
    simpa only [evenSlice, LinearMap.mk₂_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, b.norm_eq_one, one_mul, mul_one, mul_assoc] using h
  let P : ℝ := (Module.finrank ℝ V : ℝ) * ‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)
  have s1 := (hsum (by positivity) (by positivity) (hlast r (m 0) (m 1))
    (hlast s (m 2) (m 3))).trans_eq (by ring : _ = P)
  have s2 := (hsum (by positivity) (by positivity) (hlast s (m 0) (m 1))
    (hlast r (m 2) (m 3))).trans_eq (by ring : _ = P)
  have s3 := (hsum (by positivity) (by positivity) (heven r (m 0) (m 2))
    (heven s (m 1) (m 3))).trans_eq (by ring : _ = P)
  have s4 := (hsum (by positivity) (by positivity) (heven s (m 0) (m 2))
    (heven r (m 1) (m 3))).trans_eq (by ring : _ = P)
  have s5 := (hsum (by positivity) (by positivity) (heven r (m 0) (m 3))
    (heven s (m 1) (m 2))).trans_eq (by ring : _ = P)
  have s6 := (hsum (by positivity) (by positivity) (heven s (m 0) (m 3))
    (heven r (m 1) (m 2))).trans_eq (by ring : _ = P)
  simp only [lastSlice, evenSlice, LinearMap.mk₂_apply] at s1 s2 s3 s4 s5 s6
  simp only [Finset.sum_add_distrib]
  have tri1 (x y z : ℝ) : |x + y - z| ≤ |x| + |y| + |z| := by
    linarith [abs_sub (x + y) z, abs_add_le x y]
  refine (tri1 _ _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
  have tri2 := abs_add_le
    (∑ p, ∑ q, r ![m 0, m 1, b p, b q] * s ![m 2, m 3, b p, b q])
    (∑ p, ∑ q, s ![m 0, m 1, b p, b q] * r ![m 2, m 3, b p, b q])
  have tri3 := abs_add_le
    (∑ p, ∑ q, r ![m 0, b p, m 2, b q] * s ![m 1, b p, m 3, b q])
    (∑ p, ∑ q, s ![m 0, b p, m 2, b q] * r ![m 1, b p, m 3, b q])
  have tri4 := abs_add_le
    (∑ p, ∑ q, r ![m 0, b p, m 3, b q] * s ![m 1, b p, m 2, b q])
    (∑ p, ∑ q, s ![m 0, b p, m 3, b q] * r ![m 1, b p, m 2, b q])
  linarith

/-- The operator norm of `reactionBilinear` is at most `5 * dim V`. -/
theorem norm_reactionBilinear_le :
    ‖reactionBilinear (V := V)‖ ≤ 5 * (Module.finrank ℝ V : ℝ) := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun p ↦ ?_
  have hp : p = ![p 0, p 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hp]
  rw [Fin.prod_univ_two]
  exact (norm_reactionBilinear_apply_le (p 0) (p 1)).trans_eq (by ring)

/-- The operator norm of `reactionTensor r` is at most `5 * dim V * ‖r‖²`. -/
theorem norm_reactionTensor_le (r : FourTensor V) :
    ‖reactionTensor r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) * ‖r‖ ^ 2 := by
  rw [← reactionBilinear_self, sq]
  exact (norm_reactionBilinear_apply_le r r).trans_eq (by ring)

/-- Difference estimate `‖Q(r) - Q(s)‖ ≤ ‖reactionBilinear‖ * (‖r‖ + ‖s‖) * ‖r - s‖`. -/
theorem norm_reactionTensor_sub_le (r s : FourTensor V) :
    ‖reactionTensor r - reactionTensor s‖ ≤
      ‖reactionBilinear (V := V)‖ * (‖r‖ + ‖s‖) * ‖r - s‖ := by
  rw [reactionTensor_sub_reactionTensor]
  have hle : ‖reactionBilinear ![r + s, r - s]‖ ≤
      ‖reactionBilinear (V := V)‖ * ‖r + s‖ * ‖r - s‖ := by
    simpa only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_assoc] using reactionBilinear.le_opNorm ![r + s, r - s]
  calc ‖reactionBilinear ![r + s, r - s]‖
      ≤ ‖reactionBilinear (V := V)‖ * ‖r + s‖ * ‖r - s‖ := hle
    _ ≤ ‖reactionBilinear (V := V)‖ * (‖r‖ + ‖s‖) * ‖r - s‖ := by
        gcongr
        exact norm_add_le r s

/-- `reactionTensor` is smooth (`C^∞`). -/
theorem contDiff_reactionTensor : ContDiff ℝ ∞ (reactionTensor (V := V)) := by
  have heq : (reactionTensor (V := V)) = fun r ↦ reactionBilinear (fun _ ↦ r) :=
    funext fun r ↦ by
      have hp : (fun _ : Fin 2 ↦ r) = ![r, r] := by funext i; fin_cases i <;> rfl
      rw [hp, reactionBilinear_self]
  rw [heq]
  have hB : ContDiff ℝ ∞ (reactionBilinear (V := V)) :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ) (E := fun _ : Fin 2 ↦ FourTensor V)
      (F := FourTensor V) (reactionBilinear (V := V))
  have hdiag : ContDiff ℝ ∞ (fun (r : FourTensor V) (_ : Fin 2) ↦ r) :=
    contDiff_pi.2 fun _ ↦ contDiff_id
  exact hB.comp hdiag

/-- `reactionTensor` is continuous. -/
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  contDiff_reactionTensor.continuous

/-- Strict Fréchet derivative of `reactionTensor` at `r`:
`DQ(r)(h) = 2 • reactionBilinear ![r, h]`. -/
theorem hasStrictFDerivAt_reactionTensor (r : FourTensor V) :
    HasStrictFDerivAt (reactionTensor (V := V))
      ((2 : ℝ) • reactionBilinear.toContinuousLinearMap ![r, r] 1) r := by
  have heq : (reactionTensor (V := V)) = fun q ↦ reactionBilinear (fun _ ↦ q) :=
    funext fun q ↦ by
      have hp : (fun _ : Fin 2 ↦ q) = ![q, q] := by funext i; fin_cases i <;> rfl
      rw [hp, reactionBilinear_self]
  rw [heq]
  have hpi : HasStrictFDerivAt (fun (q : FourTensor V) (_ : Fin 2) ↦ q)
      (ContinuousLinearMap.pi fun _ : Fin 2 ↦ ContinuousLinearMap.id ℝ (FourTensor V)) r :=
    hasStrictFDerivAt_pi.2 fun _ ↦ hasStrictFDerivAt_id r
  convert (reactionBilinear.hasStrictFDerivAt (fun _ ↦ r)).comp
    (f := fun (q : FourTensor V) (_ : Fin 2) ↦ q) r hpi using 1
  ext h
  have hu0 : Function.update (fun _ : Fin 2 ↦ r) 0 h = ![h, r] := by
    funext i; fin_cases i <;> rfl
  have hu1 : Function.update (fun _ : Fin 2 ↦ r) 1 h = ![r, h] := by
    funext i; fin_cases i <;> rfl
  have hu1' : Function.update ![r, r] 1 h = ![r, h] := by
    funext i; fin_cases i <;> rfl
  simp only [smul_apply, ContinuousMultilinearMap.toContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply, Fin.sum_univ_two, hu0, hu1, hu1',
    reactionBilinear_comm h r, two_smul]

/-- Fréchet derivative of `reactionTensor` at `r`: `DQ(r)(h) = 2 • reactionBilinear ![r, h]`. -/
theorem hasFDerivAt_reactionTensor (r : FourTensor V) :
    HasFDerivAt (reactionTensor (V := V))
      ((2 : ℝ) • reactionBilinear.toContinuousLinearMap ![r, r] 1) r :=
  (hasStrictFDerivAt_reactionTensor r).hasFDerivAt

/-- Evaluation of the Fréchet derivative of `reactionTensor` at `r` on a perturbation `h`. -/
@[simp]
theorem fderiv_reactionTensor_apply (r h : FourTensor V) :
    fderiv ℝ (reactionTensor (V := V)) r h = (2 : ℝ) • reactionBilinear ![r, h] := by
  rw [(hasFDerivAt_reactionTensor r).fderiv]
  have hu : Function.update ![r, r] 1 h = ![r, h] := by
    funext i; fin_cases i <;> rfl
  simp [hu]

/-- On the closed ball of radius `R` around `0`, `reactionTensor` is Lipschitz with constant
`2 * R.toNNReal * ‖reactionBilinear‖₊`. -/
theorem lipschitzOnWith_reactionTensor_closedBall (R : ℝ) :
    LipschitzOnWith (2 * R.toNNReal * ‖reactionBilinear (V := V)‖₊)
      (reactionTensor (V := V)) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun r hr s hs ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hr hs
  have hR : 0 ≤ R := (norm_nonneg r).trans hr
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖reactionTensor r - reactionTensor s‖
      ≤ ‖reactionBilinear (V := V)‖ * (‖r‖ + ‖s‖) * ‖r - s‖ := norm_reactionTensor_sub_le r s
    _ ≤ ‖reactionBilinear (V := V)‖ * (R + R) * ‖r - s‖ := by gcongr
    _ = ↑(2 * R.toNNReal * ‖reactionBilinear (V := V)‖₊) * ‖r - s‖ := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal R hR, coe_nnNorm]
        ring

/-- `reactionTensor` is locally Lipschitz on `FourTensor V`. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) := fun r ↦
  ⟨2 * (‖r‖ + 1).toNNReal * ‖reactionBilinear (V := V)‖₊, Metric.closedBall 0 (‖r‖ + 1),
    Filter.mem_of_superset (Metric.ball_mem_nhds r zero_lt_one) fun s hs ↦ by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hdist : ‖s - r‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      linarith [norm_sub_norm_le s r],
    lipschitzOnWith_reactionTensor_closedBall (‖r‖ + 1)⟩

/-! ### Ricci and scalar contractions and model curvature eigenspaces -/

/-- In any orthonormal basis `b`, the Ricci contraction of `reactionTensor r` for an algebraic
curvature tensor `r` is `Ric(Q(r))(u, v) = 2 ∑ p, ∑ q, Ric(r)(b p, b q) r(u, b p, v, b q)`. -/
theorem ricci_reactionTensor {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (u v : V) :
    ricci (reactionTensor r) u v =
      2 * ∑ p, ∑ q, ricci r (b p) (b q) * r ![u, b p, v, b q] := by
  rw [ricci_apply_orthonormalBasis b]
  simp only [reactionTensor_apply_orthonormalBasis b, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcancel : (∑ i, ∑ p, ∑ q, r ![b i, u, b p, b q] * r ![b i, v, b p, b q]) =
      2 * ∑ i, ∑ p, ∑ q, r ![b i, b p, v, b q] * r ![u, b p, b i, b q] := by
    have hq (q : ι) :
        2 * (∑ i, ∑ p, r ![b i, b p, v, b q] * r ![u, b p, b i, b q]) =
          ∑ i, ∑ p, r ![b i, b p, v, b q] * r ![b i, b p, u, b q] := by
      have h := hr.two_mul_sum_mul_eq b v (b q) u (b q)
      have hlhs : (∑ p, ∑ i, r ![v, b q, b p, b i] * r ![u, b p, b q, b i]) =
          ∑ i, ∑ p, r ![b i, b p, v, b q] * r ![u, b p, b i, b q] := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
        rw [hr.swap_pairs v (b q), hr.antisymm_first (b p) (b i),
          hr.antisymm_last u (b p) (b q) (b i), neg_mul_neg]
      have hrhs : (∑ p, ∑ i, r ![v, b q, b p, b i] * r ![u, b q, b p, b i]) =
          ∑ i, ∑ p, r ![b i, b p, v, b q] * r ![b i, b p, u, b q] :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦ by
          rw [hr.swap_pairs v (b q), hr.swap_pairs u (b q)]
      rwa [hlhs, hrhs] at h
    calc (∑ i, ∑ p, ∑ q, r ![b i, u, b p, b q] * r ![b i, v, b p, b q])
        = ∑ i, ∑ q, ∑ p, r ![b i, u, b p, b q] * r ![b i, v, b p, b q] :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = ∑ q, ∑ i, ∑ p, r ![b i, u, b p, b q] * r ![b i, v, b p, b q] := Finset.sum_comm
      _ = ∑ i, ∑ q, ∑ p, r ![b q, u, b p, b i] * r ![b q, v, b p, b i] := rfl
      _ = ∑ q, ∑ i, ∑ p, r ![b q, u, b p, b i] * r ![b q, v, b p, b i] := Finset.sum_comm
      _ = ∑ q, ∑ i, ∑ p, r ![b i, b p, v, b q] * r ![b i, b p, u, b q] := by
          refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun p _ ↦ ?_
          rw [hr.antisymm_first (b q) u, hr.antisymm_last u (b q) (b p) (b i), neg_neg,
            hr.swap_pairs u (b q), hr.antisymm_first (b q) v,
            hr.antisymm_last v (b q) (b p) (b i), neg_neg, hr.swap_pairs v (b q), mul_comm]
      _ = ∑ q, 2 * ∑ i, ∑ p, r ![b i, b p, v, b q] * r ![u, b p, b i, b q] :=
          Finset.sum_congr rfl fun q _ ↦ (hq q).symm
      _ = 2 * ∑ i, ∑ p, ∑ q, r ![b i, b p, v, b q] * r ![u, b p, b i, b q] := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          exact congrArg (2 * ·) (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm)
  have hmid : (∑ i, ∑ p, ∑ q, r ![b i, b p, b i, b q] * r ![u, b p, v, b q]) =
      ∑ p, ∑ q, ricci r (b p) (b q) * r ![u, b p, v, b q] := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [← Finset.sum_mul, ricci_apply_orthonormalBasis b]
  rw [hcancel, hmid]
  ring

/-- For an algebraic curvature tensor `r`, the scalar contraction of `reactionTensor r` is twice
the squared Hilbert–Schmidt norm of its Ricci tensor:
`Scal(Q(r)) = 2 ∑ p, ∑ q, Ric(r)(b p, b q)²`. -/
theorem scalar_reactionTensor {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (reactionTensor r) = 2 * ∑ p, ∑ q, (ricci r (b p) (b q)) ^ 2 := by
  rw [scalar_apply, bilinFormTrace_eq_sum _ b]
  simp only [ricci_reactionTensor b hr, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← Finset.mul_sum, ← ricci_apply_orthonormalBasis b, sq]

/-- The scalar contraction of `reactionTensor r` is nonnegative for every algebraic curvature
tensor `r`. -/
theorem scalar_reactionTensor_nonneg {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    0 ≤ scalar (reactionTensor r) := by
  rw [scalar_reactionTensor (stdOrthonormalBasis ℝ V) hr]
  exact mul_nonneg zero_le_two
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- For an algebraic curvature tensor `r`, `scalar (reactionTensor r) = 0` if and only if `r` is
Ricci-flat (`ricci r = 0`). -/
theorem scalar_reactionTensor_eq_zero_iff {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (reactionTensor r) = 0 ↔ ricci r = 0 := by
  set b := stdOrthonormalBasis ℝ V
  rw [scalar_reactionTensor b hr]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hsum : (∑ p, ∑ q, (ricci r (b p) (b q)) ^ 2) = 0 := by linarith
  have hp : ∀ p, (∑ q, (ricci r (b p) (b q)) ^ 2) = 0 := fun p ↦
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _).1
      hsum p (Finset.mem_univ p)
  have hpq : ∀ p q, ricci r (b p) (b q) = 0 := fun p q ↦
    sq_eq_zero_iff.1 <|
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _).1 (hp p) q (Finset.mem_univ q)
  ext u v
  rw [← b.sum_repr' u, ← b.sum_repr' v, map_sum]
  simp [LinearMap.sum_apply, hpq]

/-- Contracting the last two slots of an algebraic curvature tensor `r` against
`constantCurvature V` in an orthonormal basis `b` evaluates `2 * r ![a, c, x, y]`. -/
theorem sum_mul_constantCurvature_last {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (a c x y : V) :
    (∑ p, ∑ q, r ![a, c, b p, b q] * constantCurvature V ![x, y, b p, b q]) =
      2 * r ![a, c, x, y] := by
  have heval (u v : V) :
      (∑ p, ∑ q, r ![a, c, b p, b q] * (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ)) = r ![a, c, u, v] := by
    conv_rhs => rw [← b.sum_repr' u, apply_sum_third]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    conv_rhs => rw [apply_smul_third, ← b.sum_repr' v, apply_sum_fourth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [apply_smul_fourth, real_inner_comm u (b p), real_inner_comm v (b q)]
    ring
  have hsub : (∑ p, ∑ q, r ![a, c, b p, b q] * constantCurvature V ![x, y, b p, b q]) =
      (∑ p, ∑ q, r ![a, c, b p, b q] * (⟪x, b p⟫_ℝ * ⟪y, b q⟫_ℝ)) -
        ∑ p, ∑ q, r ![a, c, b p, b q] * (⟪x, b q⟫_ℝ * ⟪y, b p⟫_ℝ) := by
    simp_rw [constantCurvature_apply, mul_sub, Finset.sum_sub_distrib]
  have h2 : (∑ p, ∑ q, r ![a, c, b p, b q] * (⟪x, b q⟫_ℝ * ⟪y, b p⟫_ℝ)) = r ![a, c, y, x] := by
    convert heval y x using 2 with p
    exact Finset.sum_congr rfl fun q _ ↦ by ring
  rw [hsub, heval, h2, hr.antisymm_last a c y x]
  ring

/-- Contracting the second and fourth slots of an algebraic curvature tensor `r` against
`constantCurvature V` in an orthonormal basis `b` yields
`ricci r a c * ⟪x, y⟫ - r ![a, y, c, x]`. -/
theorem sum_mul_constantCurvature_even {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (a c x y : V) :
    (∑ p, ∑ q, r ![a, b p, c, b q] * constantCurvature V ![x, b p, y, b q]) =
      ricci r a c * ⟪x, y⟫_ℝ - r ![a, y, c, x] := by
  have heval (u v : V) :
      (∑ p, ∑ q, r ![a, b p, c, b q] * (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ)) = r ![a, u, c, v] := by
    conv_rhs => rw [← b.sum_repr' u, apply_sum_second]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    conv_rhs => rw [apply_smul_second, ← b.sum_repr' v, apply_sum_fourth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [apply_smul_fourth, real_inner_comm u (b p), real_inner_comm v (b q)]
    ring
  have hsub : (∑ p, ∑ q, r ![a, b p, c, b q] * constantCurvature V ![x, b p, y, b q]) =
      (∑ p, ∑ q, r ![a, b p, c, b q] * (⟪x, y⟫_ℝ * ⟪b p, b q⟫_ℝ)) -
        ∑ p, ∑ q, r ![a, b p, c, b q] * (⟪x, b q⟫_ℝ * ⟪b p, y⟫_ℝ) := by
    simp_rw [constantCurvature_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 : (∑ p, ∑ q, r ![a, b p, c, b q] * (⟪x, y⟫_ℝ * ⟪b p, b q⟫_ℝ)) =
      ricci r a c * ⟪x, y⟫_ℝ := by
    have hdiag (p : ι) :
        (∑ q, r ![a, b p, c, b q] * (⟪x, y⟫_ℝ * ⟪b p, b q⟫_ℝ)) =
          r ![b p, a, b p, c] * ⟪x, y⟫_ℝ := by
      rw [Finset.sum_eq_single p]
      · rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow, mul_one,
          hr.antisymm_first a (b p), hr.antisymm_last (b p) a c (b p), neg_neg]
      · intro q _ hqp
        rw [b.orthonormal.2 hqp.symm, mul_zero, mul_zero]
      · intro hp
        exact absurd (Finset.mem_univ p) hp
    simp_rw [hdiag, ← Finset.sum_mul, ricci_apply_orthonormalBasis b]
  have h2 : (∑ p, ∑ q, r ![a, b p, c, b q] * (⟪x, b q⟫_ℝ * ⟪b p, y⟫_ℝ)) = r ![a, y, c, x] := by
    convert heval y x using 2 with p
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [real_inner_comm y (b p)]
    ring
  rw [hsub, h1, h2]

/-- Pairing an algebraic curvature tensor `r` with `constantCurvature V` under `reactionBilinear`
produces the Kulkarni–Nomizu product `kulkarniNomizu (ricci r) (innerₗ V)`. -/
theorem reactionBilinear_constantCurvature_right {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    reactionBilinear ![r, constantCurvature V] = kulkarniNomizu (ricci r) (innerₗ V) := by
  set b := stdOrthonormalBasis ℝ V
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis b, kulkarniNomizu_apply]
  simp only [Finset.sum_add_distrib, innerₗ_apply_apply]
  have s1a := sum_mul_constantCurvature_last b hr u v z w
  have s1b : (∑ p, ∑ q, constantCurvature V ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      2 * r ![u, v, z, w] := by
    simpa only [mul_comm (constantCurvature V _), hr.swap_pairs z w u v] using
      sum_mul_constantCurvature_last b hr z w u v
  have s2a := sum_mul_constantCurvature_even b hr u z v w
  have s2b : (∑ p, ∑ q, constantCurvature V ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      ricci r v w * ⟪u, z⟫_ℝ - r ![v, z, w, u] := by
    simpa only [mul_comm (constantCurvature V _)] using sum_mul_constantCurvature_even b hr v w u z
  have s3a := sum_mul_constantCurvature_even b hr u w v z
  have s3b : (∑ p, ∑ q, constantCurvature V ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      ricci r v z * ⟪u, w⟫_ℝ - r ![v, w, z, u] := by
    simpa only [mul_comm (constantCurvature V _)] using sum_mul_constantCurvature_even b hr v z u w
  rw [s1a, s1b, s2a, s2b, s3a, s3b]
  have t1 : r ![u, w, z, v] = -r ![v, z, u, w] := by
    rw [hr.swap_pairs, hr.antisymm_first z v]
  have t2 : r ![v, z, w, u] = -r ![v, z, u, w] :=
    hr.antisymm_last v z w u
  have t3 : r ![u, z, w, v] = r ![z, u, v, w] := by
    rw [hr.antisymm_first u z, hr.antisymm_last z u w v, neg_neg]
  have t4 : r ![v, w, z, u] = r ![z, u, v, w] :=
    hr.swap_pairs v w z u
  have hcyc := hr.cyclic_eq_zero u v z w
  linear_combination 2 * hcyc - t1 - t2 + t3 + t4

/-- Symmetric counterpart of `reactionBilinear_constantCurvature_right`. -/
theorem reactionBilinear_constantCurvature_left {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    reactionBilinear ![constantCurvature V, r] = kulkarniNomizu (ricci r) (innerₗ V) := by
  rw [reactionBilinear_comm, reactionBilinear_constantCurvature_right hr]

/-- The reaction tensor of `constantCurvature V` is `2 (n - 1) • constantCurvature V`. -/
@[simp]
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  rw [← reactionBilinear_self,
    reactionBilinear_constantCurvature_right isAlgebraicCurvature_constantCurvature,
    ricci_constantCurvature, map_smul, LinearMap.smul_apply]
  refine ext_vec fun u v z w ↦ ?_
  simp only [smul_apply, smul_eq_mul, kulkarniNomizu_apply, constantCurvature_apply,
    innerₗ_apply_apply]
  ring

/-- The Ricci contraction of `planeCurvature u v`. -/
theorem ricci_planeCurvature (u v x y : V) :
    ricci (planeCurvature u v) x y =
      ‖u‖ ^ 2 * ⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ - ⟪u, v⟫_ℝ * (⟪u, x⟫_ℝ * ⟪v, y⟫_ℝ + ⟪v, x⟫_ℝ * ⟪u, y⟫_ℝ) +
        ‖v‖ ^ 2 * ⟪u, x⟫_ℝ * ⟪u, y⟫_ℝ := by
  set b := stdOrthonormalBasis ℝ V
  rw [ricci_apply_orthonormalBasis b]
  have expand (i : Fin (Module.finrank ℝ V)) :
      planeCurvature u v ![b i, x, b i, y] =
        (⟪u, b i⟫_ℝ ^ 2) * (⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ) -
          (⟪u, b i⟫_ℝ * ⟪b i, v⟫_ℝ) * (⟪u, x⟫_ℝ * ⟪v, y⟫_ℝ + ⟪v, x⟫_ℝ * ⟪u, y⟫_ℝ) +
          (⟪v, b i⟫_ℝ ^ 2) * (⟪u, x⟫_ℝ * ⟪u, y⟫_ℝ) := by
    rw [planeCurvature_apply, real_inner_comm (b i) v]
    ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    b.sum_sq_inner_left, b.sum_inner_mul_inner]
  ring

/-- For an orthonormal pair `u, v`, `ricci (planeCurvature u v)` is the orthogonal projection form
onto `span {u, v}`: `(x, y) ↦ ⟪u, x⟫ ⟪u, y⟫ + ⟪v, x⟫ ⟪v, y⟫`. -/
theorem ricci_planeCurvature_of_orthonormal {u v : V} (huv : Orthonormal ℝ ![u, v]) (x y : V) :
    ricci (planeCurvature u v) x y = ⟪u, x⟫_ℝ * ⟪u, y⟫_ℝ + ⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ := by
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have horth : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [ricci_planeCurvature, hu, hv, horth]
  ring

/-- The scalar contraction of `planeCurvature u v` is `2 (‖u‖² ‖v‖² - ⟪u, v⟫²)`. -/
theorem scalar_planeCurvature (u v : V) :
    scalar (planeCurvature u v) = 2 * constantCurvature V ![u, v, u, v] := by
  set b := stdOrthonormalBasis ℝ V
  rw [scalar_apply, bilinFormTrace_eq_sum _ b]
  have expand (i : Fin (Module.finrank ℝ V)) :
      ricci (planeCurvature u v) (b i) (b i) =
        ‖u‖ ^ 2 * ⟪v, b i⟫_ℝ ^ 2 - 2 * ⟪u, v⟫_ℝ * (⟪u, b i⟫_ℝ * ⟪b i, v⟫_ℝ) +
          ‖v‖ ^ 2 * ⟪u, b i⟫_ℝ ^ 2 := by
    rw [ricci_planeCurvature, real_inner_comm (b i) v]
    ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    b.sum_sq_inner_left, b.sum_inner_mul_inner, constantCurvature_apply_self]
  ring

/-- For an orthonormal pair `u, v`, `scalar (planeCurvature u v) = 2`. -/
theorem scalar_planeCurvature_of_orthonormal {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    scalar (planeCurvature u v) = 2 := by
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have horth : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [scalar_planeCurvature, constantCurvature_apply_self, hu, hv, horth]
  ring

/-- On the rank-one curvature tensor `planeCurvature u v`, the reaction tensor acts by scalar
multiplication by `2 (‖u‖² ‖v‖² - ⟪u, v⟫²) = 2 * constantCurvature V ![u, v, u, v]`. -/
theorem reactionTensor_planeCurvature (u v : V) :
    reactionTensor (planeCurvature u v) =
      (2 * constantCurvature V ![u, v, u, v]) • planeCurvature u v := by
  set b := stdOrthonormalBasis ℝ V
  -- The double norm of the two-form `(x, y) ↦ ⟪u, x⟫ ⟪v, y⟫ - ⟪u, y⟫ ⟪v, x⟫` in `b` is twice
  -- the Gram determinant of `(u, v)`.
  have hnorm :
      (∑ p, ∑ q, (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) ^ 2) =
        2 * constantCurvature V ![u, v, u, v] := by
    have inner_q (p : Fin (Module.finrank ℝ V)) :
        (∑ q, (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) ^ 2) =
          ⟪u, b p⟫_ℝ ^ 2 * ‖v‖ ^ 2 - 2 * ⟪u, v⟫_ℝ * (⟪u, b p⟫_ℝ * ⟪b p, v⟫_ℝ) +
            ‖u‖ ^ 2 * ⟪v, b p⟫_ℝ ^ 2 := by
      have hq (q : Fin (Module.finrank ℝ V)) :
          (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) ^ 2 =
            ⟪u, b p⟫_ℝ ^ 2 * ⟪v, b q⟫_ℝ ^ 2 -
              2 * (⟪u, b p⟫_ℝ * ⟪b p, v⟫_ℝ) * (⟪u, b q⟫_ℝ * ⟪b q, v⟫_ℝ) +
              ⟪v, b p⟫_ℝ ^ 2 * ⟪u, b q⟫_ℝ ^ 2 := by
        rw [real_inner_comm (b p) v, real_inner_comm (b q) v]
        ring
      simp_rw [hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        b.sum_sq_inner_left, b.sum_inner_mul_inner]
      ring
    simp_rw [inner_q, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, b.sum_sq_inner_left, b.sum_inner_mul_inner, constantCurvature_apply_self]
    ring
  refine ext_vec fun x y z w ↦ ?_
  rw [reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul]
  -- The second and third double sums agree term-by-term for a factored rank-one four-tensor.
  have hcancel :
      (∑ p, ∑ q, planeCurvature u v ![x, b p, z, b q] *
          planeCurvature u v ![y, b p, w, b q]) =
        ∑ p, ∑ q, planeCurvature u v ![x, b p, w, b q] *
          planeCurvature u v ![y, b p, z, b q] :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      simp only [planeCurvature_apply]
      ring
  have hfirst :
      (∑ p, ∑ q, planeCurvature u v ![x, y, b p, b q] *
          planeCurvature u v ![z, w, b p, b q]) =
        (2 * constantCurvature V ![u, v, u, v]) * planeCurvature u v ![x, y, z, w] := by
    have hterm (p q : Fin (Module.finrank ℝ V)) :
        planeCurvature u v ![x, y, b p, b q] * planeCurvature u v ![z, w, b p, b q] =
          planeCurvature u v ![x, y, z, w] *
            (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) ^ 2 := by
      simp only [planeCurvature_apply]
      ring
    simp_rw [hterm, ← Finset.mul_sum, hnorm, mul_comm]
  rw [hcancel, hfirst]
  ring

/-- For an orthonormal pair `u, v` (representing the unit `S² × ℝⁿ⁻²` curvature),
`Q(planeCurvature u v) = 2 • planeCurvature u v`. -/
theorem reactionTensor_planeCurvature_of_orthonormal {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    reactionTensor (planeCurvature u v) = (2 : ℝ) • planeCurvature u v := by
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have horth : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [reactionTensor_planeCurvature, constantCurvature_apply_self, hu, hv, horth]
  norm_num

end FiniteDimensional

end FourTensor

end TauCeti
