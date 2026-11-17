/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Adjoint
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The reaction tensor on algebraic curvature four-tensors

In Uhlenbeck's orthonormal-frame formulation of the Ricci flow, the Riemann curvature four-tensor
evolves by `D_t R = Δ R + Q(R)`, where the quadratic reaction `Q(r)` of a four-tensor `r` on a
finite-dimensional real inner product space `V` has components

`Q(r)ᵢⱼₖₗ = ∑ p, ∑ q, rᵢⱼₚₑ rₖₗₚₑ + 2 ∑ p, ∑ q, rᵢₚₖₑ rⱼₚₗₑ - 2 ∑ p, ∑ q, rᵢₚₗₑ rⱼₚₖₑ`

in any orthonormal basis `(bᵢ)` (with the subscript `e` standing for `q`). Packaging the
symmetrized double contraction in the standard orthonormal basis as a bounded bilinear map gives
the continuous symmetric polarization `TauCeti.FourTensor.reactionBilinear V :
FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V`, and restricting to the diagonal defines the
quadratic reaction tensor `TauCeti.FourTensor.reactionTensor r = reactionBilinear V r r`.

Because each of the three double sums contracts two four-tensors across a full pair of inner-product
slots, the resulting four-tensor is independent of the chosen orthonormal basis
(`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`), and in every orthonormal basis `b`
its entries and coordinate expansion agree with `reactionComponent b r`
(`TauCeti.FourTensor.reactionComponent_eq_reactionTensor_apply`,
`TauCeti.FourTensor.sum_reactionComponent_smul_coordFourTensor`). More generally, pulling back along
any continuous linear map `P : W →L[ℝ] V` with `P ∘L P.adjoint = id` commutes with both
`reactionBilinear` and `reactionTensor`; this simultaneously yields orthogonal equivariance under
linear isometric equivalences and commutation with zero extension to an `L²` direct sum
`WithLp 2 (V × U)` along `WithLp.fstL`.

When `r` is an algebraic curvature tensor, `reactionTensor r` again satisfies both pair
antisymmetries, pair interchange, and the first Bianchi identity
(`TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor`,
`TauCeti.FourTensor.reactionTensor_mem_algebraicCurvatureSubmodule`), and by polarization so does
`reactionBilinear V r s`. Consequently the autonomous ODE `r' = Q(r)` restricts to the closed
subspace `TauCeti.FourTensor.algebraicCurvatureSubmodule V`; its `C^n` regularity (including real
analyticity), Fréchet derivative `(2 : ℝ) • reactionBilinear V r`, explicit operator-norm bound
`‖reactionBilinear V‖ ≤ 5 * dim V`, and Lipschitz bounds on closed balls supply the analytic inputs
for ODE invariance of curvature cones.

Contracting `Q(r)` for an algebraic curvature tensor `r` cancels the quadratic Weyl terms in the
trace, leaving `Ric(Q(r))(u, v) = 2 ∑ p, ∑ q, Ric(r)(b p, b q) r(u, b p, v, b q)` and
`Scal(Q(r)) = 2 ∑ p, ∑ q, Ric(r)(b p, b q)² ≥ 0` (vanishing exactly when `Ric(r) = 0`). Pairing `r`
against `constantCurvature V` gives
`reactionBilinear V r (constantCurvature V) = kulkarniNomizu (ricci r) (innerₗ V)`, so the
constant-curvature tensor satisfies `Q(I) = 2 (n - 1) I`. On the rank-one two-plane curvature
tensor `TauCeti.FourTensor.planeCurvature u v` (representing the curvature of `S² × ℝⁿ⁻²` for an
orthonormal pair `u, v`), the last two sums in `Q` cancel term by term and
`Q(planeCurvature u v) = (2 * constantCurvature V ![u, v, u, v]) • planeCurvature u v`, reducing to
`2 • planeCurvature u v` when `u, v` are orthonormal.

## Main definitions

* `TauCeti.FourTensor.reactionComponent`: the components `Q(r)ᵢⱼₖₗ` in an orthonormal basis.
* `TauCeti.FourTensor.reactionBilinear`: the continuous symmetric bilinear polarization of
  `reactionTensor`.
* `TauCeti.FourTensor.reactionTensor`: the quadratic reaction four-tensor `Q(r)`.

## Main statements

* `TauCeti.FourTensor.reactionBilinear_apply_orthonormalBasis`,
  `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`,
  `TauCeti.FourTensor.reactionComponent_eq_reactionTensor_apply`, and
  `TauCeti.FourTensor.sum_reactionComponent_smul_coordFourTensor`: basis-independent contraction
  and coordinate-expansion formulas in every orthonormal basis.
* `TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor`,
  `TauCeti.FourTensor.reactionTensor_mem_algebraicCurvatureSubmodule`, and
  `TauCeti.FourTensor.IsAlgebraicCurvature.reactionBilinear`: preservation of the algebraic
  curvature symmetries.
* `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_of_comp_adjoint_eq_id`,
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv`, and
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_fstL`: coisometry pullback, orthogonal
  equivariance, and commutation with zero extension.
* `TauCeti.FourTensor.norm_reactionBilinear_le`, `TauCeti.FourTensor.norm_reactionTensor_sub_le`,
  `TauCeti.FourTensor.contDiff_reactionTensor`,
  `TauCeti.FourTensor.hasStrictFDerivAt_reactionTensor`,
  `TauCeti.FourTensor.fderiv_reactionTensor`,
  `TauCeti.FourTensor.lipschitzOnWith_reactionTensor_closedBall`, and
  `TauCeti.FourTensor.locallyLipschitz_reactionTensor`: norm and regularity estimates.
* `TauCeti.FourTensor.ricci_reactionTensor`, `TauCeti.FourTensor.ricci_reactionBilinear`,
  `TauCeti.FourTensor.scalar_reactionTensor`, `TauCeti.FourTensor.scalar_reactionBilinear`,
  `TauCeti.FourTensor.reactionBilinear_constantCurvature_right`,
  `TauCeti.FourTensor.reactionTensor_constantCurvature`, and
  `TauCeti.FourTensor.reactionTensor_planeCurvature`: contractions and evaluations on model
  curvature tensors.

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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Public signatures cannot use private cached instances. Insert the canonical instances
-- directly into each signature involving nested operator spaces, avoiding instance-search
-- depth limits without exporting duplicate instances.
local macro "withEndOperatorNorms " V:term " in " t:term : term =>
  `(letI : NormedAddCommGroup (FourTensor $V →L[ℝ] FourTensor $V) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (FourTensor $V →L[ℝ] FourTensor $V) :=
      ContinuousLinearMap.toNormedSpace
    $t)

private local instance : NormedAddCommGroup (FourTensor V →L[ℝ] FourTensor V) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace ℝ (FourTensor V →L[ℝ] FourTensor V) :=
  ContinuousLinearMap.toNormedSpace

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

private theorem domDomCongr_swap_one_two_apply (r : FourTensor V) (a b c d : V) :
    r.domDomCongr (Equiv.swap 1 2) ![a, b, c, d] = r ![a, c, b, d] := by
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i; fin_cases i <;> rfl

/-- The bilinear form `(x, y) ↦ r ![u, x, z, y]` slicing the second and fourth slots of a
four-tensor. -/
private def secondFourthSlice (r : FourTensor V) (u z : V) : BilinForm ℝ V :=
  lastSlice (r.domDomCongr (Equiv.swap 1 2)) u z

@[simp]
private theorem secondFourthSlice_apply (r : FourTensor V) (u z x y : V) :
    secondFourthSlice r u z x y = r ![u, x, z, y] := by
  rw [secondFourthSlice, lastSlice_apply, domDomCongr_swap_one_two_apply]

private theorem abs_sum_mul_last_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    |∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]| ≤
      (Fintype.card ι : ℝ) * ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
  have hslice (t : FourTensor V) (a c x y : V) :
      ‖lastSlice t a c x y‖ ≤ (‖t‖ * ‖a‖ * ‖c‖) * ‖x‖ * ‖y‖ := by
    simpa only [lastSlice_apply, Fin.prod_univ_four, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, mul_assoc] using t.le_opNorm ![a, c, x, y]
  have h := b.orthonormal.norm_sum_sum_apply_mul_apply_le b.orthonormal Finset.univ Finset.univ
    (hslice r u v) (hslice s z w)
  simp only [lastSlice_apply, Real.norm_eq_abs, Finset.card_univ, min_self] at h
  exact h.trans_eq (by ring)

private theorem abs_sum_mul_second_fourth_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    |∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]| ≤
      (Fintype.card ι : ℝ) * ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
  have h := abs_sum_mul_last_le b
    (r.domDomCongr (Equiv.swap 1 2)) (s.domDomCongr (Equiv.swap 1 2)) u z v w
  simp only [domDomCongr_swap_one_two_apply, ContinuousMultilinearMap.norm_domDomCongr] at h
  exact h.trans_eq (by ring)

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- The bilinear form `(u, v) ↦ r(u, v, x, y)` slicing the first two slots of a four-tensor. -/
private def firstSlice (r : FourTensor V) (x y : V) : BilinForm ℝ V :=
  lastSlice (r.domDomCongr (Equiv.swap 0 2 * Equiv.swap 1 3)) x y

/-- The four-tensor `(u, v, z, w) ↦ r(u, v, x, y) * s(z, w, x, y)` for fixed `x, y : V`. -/
private def pairFirstFourTensor (r s : FourTensor V) (x y : V) : FourTensor V :=
  ofLinearMap₄ ((LinearMap.smulRightₗ.flip (firstSlice s x y)).comp (firstSlice r x y))

@[simp]
private theorem pairFirstFourTensor_apply (r s : FourTensor V) (x y u v z w : V) :
    pairFirstFourTensor r s x y ![u, v, z, w] = r ![u, v, x, y] * s ![z, w, x, y] := by
  simp only [pairFirstFourTensor, firstSlice, ofLinearMap₄_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, LinearMap.smulRightₗ_apply, LinearMap.coe_smulRight,
    LinearMap.smul_apply, lastSlice_apply, ContinuousMultilinearMap.domDomCongr_apply,
    smul_eq_mul, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  congr 1 <;> (congr 1; funext i; fin_cases i <;> rfl)

/-- The four-tensor `(u, v, z, w) ↦ r(u, x, z, y) * s(v, x, w, y)` for fixed `x, y : V`. -/
private def pairMixedFourTensor (r s : FourTensor V) (x y : V) : FourTensor V :=
  (pairFirstFourTensor (r.domDomCongr (Equiv.swap 1 2))
    (s.domDomCongr (Equiv.swap 1 2)) x y).domDomCongr (Equiv.swap 1 2)

@[simp]
private theorem pairMixedFourTensor_apply (r s : FourTensor V) (x y u v z w : V) :
    pairMixedFourTensor r s x y ![u, v, z, w] = r ![u, x, z, y] * s ![v, x, w, y] := by
  simp only [pairMixedFourTensor, domDomCongr_swap_one_two_apply, pairFirstFourTensor_apply]

/-- The four-tensor `(u, v, z, w) ↦ r(u, x, w, y) * s(v, x, z, y)` for fixed `x, y : V`. -/
private def pairCrossFourTensor (r s : FourTensor V) (x y : V) : FourTensor V :=
  (pairMixedFourTensor r s x y).domDomCongr (Equiv.swap 2 3)

@[simp]
private theorem pairCrossFourTensor_apply (r s : FourTensor V) (x y u v z w : V) :
    pairCrossFourTensor r s x y ![u, v, z, w] = r ![u, x, w, y] * s ![v, x, z, y] := by
  have h23 : (fun i ↦ ![u, v, z, w] (Equiv.swap 2 3 i)) = ![u, v, w, z] := by
    funext i; fin_cases i <;> rfl
  simp only [pairCrossFourTensor, ContinuousMultilinearMap.domDomCongr_apply, h23,
    pairMixedFourTensor_apply]

/-- The symmetrized double contraction of two four-tensors in the standard orthonormal basis. -/
private def reactionBilinearRaw (r s : FourTensor V) : FourTensor V :=
  let e := stdOrthonormalBasis ℝ V
  (2⁻¹ : ℝ) • (∑ p, ∑ q,
      (pairFirstFourTensor r s (e p) (e q) + pairFirstFourTensor s r (e p) (e q))) +
    (∑ p, ∑ q,
      (pairMixedFourTensor r s (e p) (e q) + pairMixedFourTensor s r (e p) (e q))) -
    (∑ p, ∑ q,
      (pairCrossFourTensor r s (e p) (e q) + pairCrossFourTensor s r (e p) (e q)))

private theorem reactionBilinearRaw_apply (r s : FourTensor V) (u v z w : V) :
    let e := stdOrthonormalBasis ℝ V
    reactionBilinearRaw r s ![u, v, z, w] =
      2⁻¹ * (∑ p, ∑ q, (r ![u, v, e p, e q] * s ![z, w, e p, e q] +
          s ![u, v, e p, e q] * r ![z, w, e p, e q])) +
        (∑ p, ∑ q, (r ![u, e p, z, e q] * s ![v, e p, w, e q] +
          s ![u, e p, z, e q] * r ![v, e p, w, e q])) -
        (∑ p, ∑ q, (r ![u, e p, w, e q] * s ![v, e p, z, e q] +
          s ![u, e p, w, e q] * r ![v, e p, z, e q])) := by
  simp only [reactionBilinearRaw, sub_apply, add_apply, smul_apply, sum_apply,
    pairFirstFourTensor_apply, pairMixedFourTensor_apply, pairCrossFourTensor_apply, smul_eq_mul]

private theorem reactionBilinearRaw_comm (r s : FourTensor V) :
    reactionBilinearRaw r s = reactionBilinearRaw s r := by
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinearRaw_apply, reactionBilinearRaw_apply]
  simp only [Finset.sum_add_distrib]
  ring

private theorem reactionBilinearRaw_add_left (r₁ r₂ s : FourTensor V) :
    reactionBilinearRaw (r₁ + r₂) s = reactionBilinearRaw r₁ s + reactionBilinearRaw r₂ s := by
  refine ext_vec fun u v z w ↦ ?_
  simp only [add_apply, reactionBilinearRaw_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem reactionBilinearRaw_smul_left (c : ℝ) (r s : FourTensor V) :
    reactionBilinearRaw (c • r) s = c • reactionBilinearRaw r s := by
  refine ext_vec fun u v z w ↦ ?_
  simp only [smul_apply, reactionBilinearRaw_apply, smul_eq_mul, Finset.sum_add_distrib,
    mul_assoc, mul_left_comm _ c, ← Finset.mul_sum]
  ring

variable (V) in
/-- The bilinear map underlying `reactionBilinear V`. -/
private def reactionBilinearLM : FourTensor V →ₗ[ℝ] FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.mk₂ ℝ reactionBilinearRaw reactionBilinearRaw_add_left reactionBilinearRaw_smul_left
    (fun r s₁ s₂ ↦ by
      rw [reactionBilinearRaw_comm, reactionBilinearRaw_add_left, reactionBilinearRaw_comm,
        reactionBilinearRaw_comm s₂])
    (fun c r s ↦ by
      rw [reactionBilinearRaw_comm, reactionBilinearRaw_smul_left, reactionBilinearRaw_comm])

private theorem norm_reactionBilinearLM_le (r s : FourTensor V) :
    ‖reactionBilinearLM V r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) * ‖r‖ * ‖s‖ := by
  set b := stdOrthonormalBasis ℝ V
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  conv_lhs => rw [show m = ![m 0, m 1, m 2, m 3] from (FinVec.etaExpand_eq m).symm]
  rw [Fin.prod_univ_four, reactionBilinearLM, LinearMap.mk₂_apply, reactionBilinearRaw_apply,
    Real.norm_eq_abs]
  -- Bound each of the six double contractions by `dim V * ‖r‖ * ‖s‖ * ∏ i, ‖m i‖`.
  let P : ℝ := (Module.finrank ℝ V : ℝ) * ‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)
  have hcard : (Fintype.card (Fin (Module.finrank ℝ V)) : ℝ) = Module.finrank ℝ V := by simp
  have s1 : |∑ p, ∑ q, r ![m 0, m 1, b p, b q] * s ![m 2, m 3, b p, b q]| ≤ P :=
    (abs_sum_mul_last_le b r s (m 0) (m 1) (m 2) (m 3)).trans_eq (by rw [hcard])
  have s2 : |∑ p, ∑ q, s ![m 0, m 1, b p, b q] * r ![m 2, m 3, b p, b q]| ≤ P :=
    (abs_sum_mul_last_le b s r (m 0) (m 1) (m 2) (m 3)).trans_eq
      (by rw [hcard]; dsimp only [P]; ring)
  have s3 : |∑ p, ∑ q, r ![m 0, b p, m 2, b q] * s ![m 1, b p, m 3, b q]| ≤ P :=
    (abs_sum_mul_second_fourth_le b r s (m 0) (m 1) (m 2) (m 3)).trans_eq (by rw [hcard])
  have s4 : |∑ p, ∑ q, s ![m 0, b p, m 2, b q] * r ![m 1, b p, m 3, b q]| ≤ P :=
    (abs_sum_mul_second_fourth_le b s r (m 0) (m 1) (m 2) (m 3)).trans_eq
      (by rw [hcard]; dsimp only [P]; ring)
  have s5 : |∑ p, ∑ q, r ![m 0, b p, m 3, b q] * s ![m 1, b p, m 2, b q]| ≤ P :=
    (abs_sum_mul_second_fourth_le b r s (m 0) (m 1) (m 3) (m 2)).trans_eq
      (by rw [hcard]; dsimp only [P]; ring)
  have s6 : |∑ p, ∑ q, s ![m 0, b p, m 3, b q] * r ![m 1, b p, m 2, b q]| ≤ P :=
    (abs_sum_mul_second_fourth_le b s r (m 0) (m 1) (m 3) (m 2)).trans_eq
      (by rw [hcard]; dsimp only [P]; ring)
  simp only [Finset.sum_add_distrib]
  -- Combine the six bounds with the weights `2⁻¹ * (P + P) + (P + P) + (P + P) = 5 * P`.
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
  linarith [show 5 * P =
      5 * (Module.finrank ℝ V : ℝ) * ‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖) by
    dsimp only [P]; ring]

variable (V) in
/-- The continuous symmetric bilinear polarization of `reactionTensor`, normalized so that
`reactionBilinear V r r = reactionTensor r`. -/
def reactionBilinear : withEndOperatorNorms V in
    FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V :=
  LinearMap.mkContinuous₂ (reactionBilinearLM V) (5 * (Module.finrank ℝ V : ℝ))
    norm_reactionBilinearLM_le

/-- The reaction tensor `Q(r)` of the curvature evolution `D_t R = Δ R + Q(R)`, defined as the
diagonal evaluation `reactionBilinear V r r`. Its contraction formula in any orthonormal basis is
`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`, and its coordinate expansion is
`TauCeti.FourTensor.sum_reactionComponent_smul_coordFourTensor`. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  reactionBilinear V r r

private theorem sum_mul_last_comp_of_comp_adjoint_eq_id {W ι κ : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι] [Fintype κ]
    (bW : OrthonormalBasis ι ℝ W) (bV : OrthonormalBasis κ ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    (∑ p, ∑ q, r ![u, v, P (bW p), P (bW q)] * s ![z, w, P (bW p), P (bW q)]) =
      ∑ p, ∑ q, r ![u, v, bV p, bV q] * s ![z, w, bV p, bV q] := by
  simpa only [lastSlice_apply] using
    bW.sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bV hP (lastSlice r u v) (lastSlice s z w)

private theorem sum_mul_secondFourth_comp_of_comp_adjoint_eq_id {W ι κ : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι] [Fintype κ]
    (bW : OrthonormalBasis ι ℝ W) (bV : OrthonormalBasis κ ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    (∑ p, ∑ q, r ![u, P (bW p), z, P (bW q)] * s ![v, P (bW p), w, P (bW q)]) =
      ∑ p, ∑ q, r ![u, bV p, z, bV q] * s ![v, bV p, w, bV q] := by
  simpa only [secondFourthSlice_apply] using
    bW.sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bV hP
      (secondFourthSlice r u z) (secondFourthSlice s v w)

private theorem reactionBilinearSum_comp_of_comp_adjoint_eq_id {W ι κ : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι] [Fintype κ]
    (bW : OrthonormalBasis ι ℝ W) (bV : OrthonormalBasis κ ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    2⁻¹ * (∑ p, ∑ q, (r ![u, v, P (bW p), P (bW q)] * s ![z, w, P (bW p), P (bW q)] +
        s ![u, v, P (bW p), P (bW q)] * r ![z, w, P (bW p), P (bW q)])) +
      (∑ p, ∑ q, (r ![u, P (bW p), z, P (bW q)] * s ![v, P (bW p), w, P (bW q)] +
        s ![u, P (bW p), z, P (bW q)] * r ![v, P (bW p), w, P (bW q)])) -
      (∑ p, ∑ q, (r ![u, P (bW p), w, P (bW q)] * s ![v, P (bW p), z, P (bW q)] +
        s ![u, P (bW p), w, P (bW q)] * r ![v, P (bW p), z, P (bW q)])) =
    2⁻¹ * (∑ p, ∑ q, (r ![u, v, bV p, bV q] * s ![z, w, bV p, bV q] +
        s ![u, v, bV p, bV q] * r ![z, w, bV p, bV q])) +
      (∑ p, ∑ q, (r ![u, bV p, z, bV q] * s ![v, bV p, w, bV q] +
        s ![u, bV p, z, bV q] * r ![v, bV p, w, bV q])) -
      (∑ p, ∑ q, (r ![u, bV p, w, bV q] * s ![v, bV p, z, bV q] +
        s ![u, bV p, w, bV q] * r ![v, bV p, z, bV q])) := by
  simp_rw [Finset.sum_add_distrib,
    sum_mul_last_comp_of_comp_adjoint_eq_id bW bV hP,
    sum_mul_secondFourth_comp_of_comp_adjoint_eq_id bW bV hP]

private theorem reactionBilinear_apply_eq (r s : FourTensor V) :
    reactionBilinear V r s = reactionBilinearRaw r s := by
  rw [reactionBilinear, LinearMap.mkContinuous₂_apply, reactionBilinearLM, LinearMap.mk₂_apply]

/-- Basis independence of `reactionBilinear`: in every orthonormal basis `b` of `V`,
`reactionBilinear V r s` is given by the symmetrized double contraction over `b`. -/
theorem reactionBilinear_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinear V r s ![u, v, z, w] =
      2⁻¹ * (∑ p, ∑ q, (r ![u, v, b p, b q] * s ![z, w, b p, b q] +
          s ![u, v, b p, b q] * r ![z, w, b p, b q])) +
        (∑ p, ∑ q, (r ![u, b p, z, b q] * s ![v, b p, w, b q] +
          s ![u, b p, z, b q] * r ![v, b p, w, b q])) -
        (∑ p, ∑ q, (r ![u, b p, w, b q] * s ![v, b p, z, b q] +
          s ![u, b p, w, b q] * r ![v, b p, z, b q])) := by
  rw [reactionBilinear_apply_eq, reactionBilinearRaw_apply]
  simpa only [ContinuousLinearMap.id_apply] using
    reactionBilinearSum_comp_of_comp_adjoint_eq_id (stdOrthonormalBasis ℝ V) b (P := .id ℝ V)
      (by simp [ContinuousLinearMap.adjoint_id]) r s u v z w

/-- On the diagonal `(r, r)`, `reactionBilinear V` recovers `reactionTensor`. -/
@[simp]
theorem reactionBilinear_self (r : FourTensor V) :
    reactionBilinear V r r = reactionTensor r :=
  (rfl)

/-- `reactionBilinear V` is symmetric in its two four-tensor arguments. -/
theorem reactionBilinear_comm (r s : FourTensor V) :
    reactionBilinear V r s = reactionBilinear V s r := by
  rw [reactionBilinear_apply_eq, reactionBilinear_apply_eq]
  exact reactionBilinearRaw_comm r s

/-- Operator-level symmetry of `reactionBilinear V`: flipping its two arguments leaves it
unchanged. -/
@[simp]
theorem reactionBilinear_flip :
    (reactionBilinear V).flip = reactionBilinear V := by
  ext r s : 2
  rw [ContinuousLinearMap.flip_apply]
  exact reactionBilinear_comm s r

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

/-- In any orthonormal basis `b`, `reactionComponent b r i j k l` is the `(i, j, k, l)` entry of
`reactionTensor r`. -/
theorem reactionComponent_eq_reactionTensor_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (i j k l : ι) :
    reactionComponent b r i j k l = reactionTensor r ![b i, b j, b k, b l] := by
  rw [reactionTensor_apply_orthonormalBasis b, reactionComponent_apply]

/-- In any orthonormal basis `b`, `reactionTensor r` expands as the linear combination of
`coordFourTensor b i j k l` weighted by `reactionComponent b r i j k l`. -/
theorem sum_reactionComponent_smul_coordFourTensor {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) :
    ∑ i, ∑ j, ∑ k, ∑ l, reactionComponent b r i j k l • coordFourTensor b i j k l =
      reactionTensor r := by
  simp_rw [reactionComponent_eq_reactionTensor_apply, sum_smul_coordFourTensor]

/-- The reaction tensor of `0` is `0`. -/
@[simp]
theorem reactionTensor_zero : reactionTensor (0 : FourTensor V) = 0 := by
  simp [← reactionBilinear_self]

/-- Negating a four-tensor leaves its reaction tensor unchanged. -/
@[simp]
theorem reactionTensor_neg (r : FourTensor V) : reactionTensor (-r) = reactionTensor r := by
  simp [← reactionBilinear_self]

/-- `reactionTensor` is homogeneous of degree two: `Q(c • r) = c² • Q(r)`. -/
theorem reactionTensor_smul (c : ℝ) (r : FourTensor V) :
    reactionTensor (c • r) = (c ^ 2) • reactionTensor r := by
  simp [← reactionBilinear_self, smul_smul, sq]

/-- Quadratic expansion of `reactionTensor` on a sum. -/
theorem reactionTensor_add (r s : FourTensor V) :
    reactionTensor (r + s) =
      reactionTensor r + (2 : ℝ) • reactionBilinear V r s + reactionTensor s := by
  simp only [← reactionBilinear_self, map_add, add_apply, reactionBilinear_comm s r, two_smul]
  abel

/-- Quadratic expansion of `reactionTensor` on a difference. -/
theorem reactionTensor_sub (r s : FourTensor V) :
    reactionTensor (r - s) =
      reactionTensor r - (2 : ℝ) • reactionBilinear V r s + reactionTensor s := by
  rw [sub_eq_add_neg, reactionTensor_add, map_neg, reactionTensor_neg, smul_neg, ← sub_eq_add_neg]

/-- Polarization: `reactionBilinear V` is recovered from `reactionTensor` by
`B(r, s) = 2⁻¹ • (Q(r + s) - Q(r) - Q(s))`. -/
theorem reactionBilinear_eq_half_sub (r s : FourTensor V) :
    reactionBilinear V r s =
      (2⁻¹ : ℝ) • (reactionTensor (r + s) - reactionTensor r - reactionTensor s) := by
  have h : reactionTensor (r + s) - reactionTensor r - reactionTensor s =
      (2 : ℝ) • reactionBilinear V r s := by
    rw [reactionTensor_add]
    abel
  rw [h, smul_smul]
  norm_num

/-- Difference factorization `Q(r) - Q(s) = B(r + s, r - s)`. -/
theorem reactionTensor_sub_reactionTensor (r s : FourTensor V) :
    reactionTensor r - reactionTensor s = reactionBilinear V (r + s) (r - s) := by
  simp only [← reactionBilinear_self, map_add, map_sub, add_apply, reactionBilinear_comm s r]
  abel

/-! ### Preservation of algebraic curvature symmetries -/

/-- First Bianchi identity for `reactionTensor r` when `r` is an algebraic curvature tensor. -/
private theorem reactionTensor_cyclic_eq_zero {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (u v z w : V) :
    reactionTensor r ![u, v, z, w] + reactionTensor r ![v, z, u, w] +
      reactionTensor r ![z, u, v, w] = 0 := by
  set b := stdOrthonormalBasis ℝ V
  simp only [reactionTensor_apply_orthonormalBasis b]
  -- Group `2 * (B(x, y, t) - C(y, t, x)) = -A(t, x, y)` for each cyclic triple `(x, y, t)`.
  have hBC (x y t : V) :
      2 * ((∑ p, ∑ q, r ![x, b p, t, b q] * r ![y, b p, w, b q]) -
          ∑ p, ∑ q, r ![y, b p, w, b q] * r ![t, b p, x, b q]) =
        -∑ p, ∑ q, r ![t, x, b p, b q] * r ![y, w, b p, b q] := by
    have hdiff : (∑ p, ∑ q, r ![x, b p, t, b q] * r ![y, b p, w, b q]) -
        (∑ p, ∑ q, r ![y, b p, w, b q] * r ![t, b p, x, b q]) =
        -∑ p, ∑ q, r ![t, x, b p, b q] * r ![y, b p, w, b q] := by
      simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      rw [mul_comm (r ![y, b p, w, b q]), ← sub_mul, hr.sub_swap_first_third,
        hr.antisymm_first x t, neg_mul]
    rw [hdiff, mul_neg, hr.two_mul_sum_mul_eq hr Finset.univ b t x y w]
  linear_combination hBC u v z + hBC v z u + hBC z u v

/-- The reaction tensor of an algebraic curvature tensor is an algebraic curvature tensor: `Q`
preserves both pair antisymmetries, pair interchange, and the first Bianchi identity. -/
theorem IsAlgebraicCurvature.reactionTensor {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.reactionTensor r) := by
  set b := stdOrthonormalBasis ℝ V
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, reactionTensor_cyclic_eq_zero hr⟩
  · -- Antisymmetry in the first pair: the first sum negates and the last two swap.
    simp only [reactionTensor_apply_orthonormalBasis b]
    have hA : (∑ p, ∑ q, r ![v, u, b p, b q] * r ![z, w, b p, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp_rw [hr.antisymm_first v u, neg_mul, Finset.sum_neg_distrib]
    have hBC (x y : V) : (∑ p, ∑ q, r ![v, b p, x, b q] * r ![u, b p, y, b q]) =
        ∑ p, ∑ q, r ![u, b p, y, b q] * r ![v, b p, x, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [hA, hBC z w, hBC w z]
    ring
  · -- Antisymmetry in the last pair: the first sum negates and the last two swap.
    simp only [reactionTensor_apply_orthonormalBasis b]
    have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, z, b p, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp_rw [hr.antisymm_first w z, mul_neg, Finset.sum_neg_distrib]
    rw [hA]
    ring
  · -- Pair interchange: commute the first sum and swap `(p, q)` via `swap_pairs` in the last two.
    simp only [reactionTensor_apply_orthonormalBasis b]
    have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
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

/-- `reactionTensor` maps `algebraicCurvatureSubmodule V` into itself. -/
theorem reactionTensor_mem_algebraicCurvatureSubmodule {r : FourTensor V}
    (hr : r ∈ algebraicCurvatureSubmodule V) :
    reactionTensor r ∈ algebraicCurvatureSubmodule V := by
  rw [mem_algebraicCurvatureSubmodule] at hr ⊢
  exact hr.reactionTensor

/-- The symmetric bilinear polarization `reactionBilinear` preserves algebraic curvature tensors. -/
theorem IsAlgebraicCurvature.reactionBilinear {r s : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hs : IsAlgebraicCurvature s) :
    IsAlgebraicCurvature (FourTensor.reactionBilinear V r s) := by
  rw [← mem_algebraicCurvatureSubmodule] at hr hs ⊢
  rw [reactionBilinear_eq_half_sub]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.sub_mem _
      (reactionTensor_mem_algebraicCurvatureSubmodule (Submodule.add_mem _ hr hs))
      (reactionTensor_mem_algebraicCurvatureSubmodule hr))
    (reactionTensor_mem_algebraicCurvatureSubmodule hs))

/-- `reactionBilinear V` maps pairs in `algebraicCurvatureSubmodule V` into
`algebraicCurvatureSubmodule V`. -/
theorem reactionBilinear_mem_algebraicCurvatureSubmodule {r s : FourTensor V}
    (hr : r ∈ algebraicCurvatureSubmodule V) (hs : s ∈ algebraicCurvatureSubmodule V) :
    reactionBilinear V r s ∈ algebraicCurvatureSubmodule V := by
  rw [mem_algebraicCurvatureSubmodule] at hr hs ⊢
  exact hr.reactionBilinear hs

/-! ### Coisometry pullback, orthogonal equivariance, and zero extension -/

/-- Pulling back four-tensors along any continuous linear map `P : W →L[ℝ] V` with
`P ∘L P.adjoint = id` commutes with `reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_of_comp_adjoint_eq_id {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (r s : FourTensor V) :
    reactionBilinear W (r.compContinuousLinearMap fun _ ↦ P)
        (s.compContinuousLinearMap fun _ ↦ P) =
      (reactionBilinear V r s).compContinuousLinearMap fun _ ↦ P := by
  refine ext_vec fun u v z w ↦ ?_
  rw [compContinuousLinearMap_apply_vec,
    reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ W),
    reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  simp only [compContinuousLinearMap_apply_vec]
  exact reactionBilinearSum_comp_of_comp_adjoint_eq_id
    (stdOrthonormalBasis ℝ W) (stdOrthonormalBasis ℝ V) hP r s (P u) (P v) (P z) (P w)

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
    reactionBilinear W
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionBilinear V r s).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  refine reactionBilinear_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r s
  rw [e.toContinuousLinearMap_toLinearIsometry, LinearIsometryEquiv.adjoint_eq_symm]
  ext x
  simp

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
    reactionBilinear (WithLp 2 (V × U))
        (r.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U)
        (s.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U) =
      (reactionBilinear V r s).compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U := by
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

/-- For each pair of four-tensors `r, s`, `‖reactionBilinear V r s‖ ≤ 5 * dim V * ‖r‖ * ‖s‖`. -/
theorem norm_reactionBilinear_apply_le (r s : FourTensor V) :
    ‖reactionBilinear V r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) * ‖r‖ * ‖s‖ := by
  rw [reactionBilinear, LinearMap.mkContinuous₂_apply]
  exact norm_reactionBilinearLM_le r s

/-- The operator norm of `reactionBilinear V` is at most `5 * dim V`. -/
theorem norm_reactionBilinear_le : withEndOperatorNorms V in
    ‖reactionBilinear V‖ ≤ 5 * (Module.finrank ℝ V : ℝ) :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) norm_reactionBilinearLM_le

/-- The operator norm of `reactionTensor r` is at most `5 * dim V * ‖r‖²`. -/
theorem norm_reactionTensor_le (r : FourTensor V) :
    ‖reactionTensor r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) * ‖r‖ ^ 2 := by
  rw [← reactionBilinear_self, sq]
  exact (norm_reactionBilinear_apply_le r r).trans_eq (by ring)

/-- Difference estimate `‖Q(r) - Q(s)‖ ≤ 5 * dim V * (‖r‖ + ‖s‖) * ‖r - s‖`. -/
theorem norm_reactionTensor_sub_le (r s : FourTensor V) :
    ‖reactionTensor r - reactionTensor s‖ ≤
      5 * (Module.finrank ℝ V : ℝ) * (‖r‖ + ‖s‖) * ‖r - s‖ :=
  ((reactionBilinear V).norm_apply_apply_sub_apply_apply_le r s).trans
    (by gcongr; exact norm_reactionBilinear_le)

/-- `reactionTensor` is `C^n` for every smoothness order `n` (including `∞` and `ω`). -/
@[fun_prop]
theorem contDiff_reactionTensor {n : ℕ∞ω} : ContDiff ℝ n (reactionTensor (V := V)) :=
  (reactionBilinear V).contDiff_apply_self

/-- `reactionTensor` is continuous. -/
@[fun_prop]
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 0)).continuous

/-- Strict Fréchet derivative of `reactionTensor` at `r`:
`DQ(r) = (2 : ℝ) • reactionBilinear V r`. -/
theorem hasStrictFDerivAt_reactionTensor (r : FourTensor V) :
    HasStrictFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r := by
  have h := (reactionBilinear V).hasStrictFDerivAt_apply_self r
  rw [reactionBilinear_flip, ← two_smul ℝ] at h
  exact h

/-- Fréchet derivative of `reactionTensor` at `r`: `DQ(r) = (2 : ℝ) • reactionBilinear V r`. -/
theorem hasFDerivAt_reactionTensor (r : FourTensor V) :
    HasFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r :=
  (hasStrictFDerivAt_reactionTensor r).hasFDerivAt

/-- The Fréchet derivative of `reactionTensor` at `r` is `(2 : ℝ) • reactionBilinear V r`. -/
@[simp]
theorem fderiv_reactionTensor (r : FourTensor V) :
    fderiv ℝ (reactionTensor (V := V)) r = (2 : ℝ) • reactionBilinear V r :=
  (hasFDerivAt_reactionTensor r).fderiv

/-- On the closed ball of radius `R` around `0`, `reactionTensor` is Lipschitz with constant
`10 * dim V * R.toNNReal`. -/
theorem lipschitzOnWith_reactionTensor_closedBall (R : ℝ) :
    LipschitzOnWith (10 * (Module.finrank ℝ V : ℝ≥0) * R.toNNReal)
      (reactionTensor (V := V)) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun r hr s hs ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hr hs
  have hR : 0 ≤ R := (norm_nonneg r).trans hr
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖reactionTensor r - reactionTensor s‖
      ≤ 5 * (Module.finrank ℝ V : ℝ) * (‖r‖ + ‖s‖) * ‖r - s‖ := norm_reactionTensor_sub_le r s
    _ ≤ 5 * (Module.finrank ℝ V : ℝ) * (R + R) * ‖r - s‖ := by gcongr
    _ = ↑(10 * (Module.finrank ℝ V : ℝ≥0) * R.toNNReal) * ‖r - s‖ := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, Real.coe_toNNReal R hR]
        ring

/-- `reactionTensor` is locally Lipschitz on `FourTensor V`. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 1)).locallyLipschitz

/-! ### Ricci and scalar contractions and model curvature evaluations -/

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
    calc (∑ i, ∑ p, ∑ q, r ![b i, u, b p, b q] * r ![b i, v, b p, b q])
        = ∑ i, ∑ p, ∑ q, r ![v, b i, b p, b q] * r ![u, b i, b p, b q] :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦
            Finset.sum_congr rfl fun q _ ↦ by
              rw [hr.antisymm_first (b i) u, hr.antisymm_first (b i) v, neg_mul_neg, mul_comm]
      _ = 2 * ∑ i, ∑ p, ∑ q, r ![v, b i, b p, b q] * r ![u, b p, b i, b q] := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦
            (hr.two_mul_sum_mul_eq hr Finset.univ b v (b i) u (b i)).symm
      _ = 2 * ∑ i, ∑ p, ∑ q, r ![b q, b p, v, b i] * r ![u, b p, b q, b i] := by
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦
            Finset.sum_congr rfl fun q _ ↦ ?_
          rw [hr.reverse v (b i), hr.antisymm_last (b q) (b p) (b i) v,
            hr.antisymm_last u (b p) (b i) (b q), neg_mul_neg]
      _ = 2 * ∑ q, ∑ p, ∑ i, r ![b q, b p, v, b i] * r ![u, b p, b q, b i] := by
          congr 1
          rw [Finset.sum_comm]
          exact (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans Finset.sum_comm
  have hmid : (∑ i, ∑ p, ∑ q, r ![b i, b p, b i, b q] * r ![u, b p, v, b q]) =
      ∑ p, ∑ q, ricci r (b p) (b q) * r ![u, b p, v, b q] := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [← Finset.sum_mul, ricci_apply_orthonormalBasis b]
  rw [hcancel, hmid]
  ring

/-- In any orthonormal basis `b`, the Ricci contraction of `reactionBilinear V r s` for algebraic
curvature tensors `r` and `s` is
`Ric(B(r, s))(u, v) = ∑ p, ∑ q, (Ric(r)(b p, b q) s(u, b p, v, b q) +
  Ric(s)(b p, b q) r(u, b p, v, b q))`. -/
theorem ricci_reactionBilinear {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r s : FourTensor V} (hr : IsAlgebraicCurvature r) (hs : IsAlgebraicCurvature s) (u v : V) :
    ricci (reactionBilinear V r s) u v =
      ∑ p, ∑ q, (ricci r (b p) (b q) * s ![u, b p, v, b q] +
        ricci s (b p) (b q) * r ![u, b p, v, b q]) := by
  have hrs : IsAlgebraicCurvature (r + s) := by
    rw [← mem_algebraicCurvatureSubmodule] at hr hs ⊢
    exact Submodule.add_mem _ hr hs
  rw [reactionBilinear_eq_half_sub, map_smul, map_sub, map_sub]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul,
    ricci_reactionTensor b hrs, ricci_reactionTensor b hr, ricci_reactionTensor b hs,
    map_add, LinearMap.add_apply, add_apply]
  have hsum :
      (∑ p, ∑ q, (ricci r (b p) (b q) + ricci s (b p) (b q)) *
          (r ![u, b p, v, b q] + s ![u, b p, v, b q])) -
        (∑ p, ∑ q, ricci r (b p) (b q) * r ![u, b p, v, b q]) -
        (∑ p, ∑ q, ricci s (b p) (b q) * s ![u, b p, v, b q]) =
      ∑ p, ∑ q, (ricci r (b p) (b q) * s ![u, b p, v, b q] +
        ricci s (b p) (b q) * r ![u, b p, v, b q]) := by
    simp_rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

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

/-- For algebraic curvature tensors `r` and `s`, the scalar contraction of
`reactionBilinear V r s` in any orthonormal basis `b` is twice the Hilbert–Schmidt inner product
of their Ricci tensors:
`Scal(B(r, s)) = 2 * ∑ p, ∑ q, Ric(r)(b p, b q) * Ric(s)(b p, b q)`. -/
theorem scalar_reactionBilinear {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r s : FourTensor V} (hr : IsAlgebraicCurvature r) (hs : IsAlgebraicCurvature s) :
    scalar (reactionBilinear V r s) =
      2 * ∑ p, ∑ q, ricci r (b p) (b q) * ricci s (b p) (b q) := by
  have hrs : IsAlgebraicCurvature (r + s) := by
    rw [← mem_algebraicCurvatureSubmodule] at hr hs ⊢
    exact Submodule.add_mem _ hr hs
  rw [reactionBilinear_eq_half_sub, map_smul, map_sub, map_sub, smul_eq_mul,
    scalar_reactionTensor b hrs, scalar_reactionTensor b hr, scalar_reactionTensor b hs]
  simp only [map_add, LinearMap.add_apply]
  have hsum :
      (∑ p, ∑ q, (ricci r (b p) (b q) + ricci s (b p) (b q)) ^ 2) -
        (∑ p, ∑ q, (ricci r (b p) (b q)) ^ 2) -
        (∑ p, ∑ q, (ricci s (b p) (b q)) ^ 2) =
      2 * ∑ p, ∑ q, ricci r (b p) (b q) * ricci s (b p) (b q) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

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
  rw [scalar_reactionTensor b hr, ← Fintype.sum_prod_type', mul_eq_zero,
    or_iff_right two_ne_zero, Finset.sum_sq_eq_zero_iff]
  refine ⟨fun h ↦ LinearMap.BilinForm.ext_basis b.toBasis fun p q ↦ ?_,
    fun h _ _ ↦ by simp [h]⟩
  simpa [OrthonormalBasis.coe_toBasis] using h (p, q) (Finset.mem_univ _)

/-- Pairing an algebraic curvature tensor `r` with `constantCurvature V` under `reactionBilinear V`
produces the Kulkarni–Nomizu product `kulkarniNomizu (ricci r) (innerₗ V)`. -/
theorem reactionBilinear_constantCurvature_right {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    reactionBilinear V r (constantCurvature V) = kulkarniNomizu (ricci r) (innerₗ V) := by
  set b := stdOrthonormalBasis ℝ V
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis b, kulkarniNomizu_apply]
  simp only [Finset.sum_add_distrib, innerₗ_apply_apply]
  have s1a := sum_mul_constantCurvature_last b hr u v z w
  have s1b : (∑ p, ∑ q, constantCurvature V ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      2 * r ![u, v, z, w] := by
    simpa only [mul_comm (constantCurvature V _), hr.swap_pairs z w u v] using
      sum_mul_constantCurvature_last b hr z w u v
  have s2a := sum_mul_constantCurvature_second_fourth b hr u z v w
  have s2b : (∑ p, ∑ q, constantCurvature V ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      ricci r v w * ⟪u, z⟫_ℝ - r ![v, z, w, u] := by
    simpa only [mul_comm (constantCurvature V _)] using
      sum_mul_constantCurvature_second_fourth b hr v w u z
  have s3a := sum_mul_constantCurvature_second_fourth b hr u w v z
  have s3b : (∑ p, ∑ q, constantCurvature V ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      ricci r v z * ⟪u, w⟫_ℝ - r ![v, w, z, u] := by
    simpa only [mul_comm (constantCurvature V _)] using
      sum_mul_constantCurvature_second_fourth b hr v z u w
  rw [s1a, s1b, s2a, s2b, s3a, s3b]
  have t1 : r ![u, w, z, v] = -r ![v, z, u, w] := by
    rw [hr.reverse, hr.antisymm_last]
  have t2 : r ![v, z, w, u] = -r ![v, z, u, w] :=
    hr.antisymm_last v z w u
  have t3 : r ![u, z, w, v] = r ![z, u, v, w] :=
    hr.swap_first_last u z w v
  have t4 : r ![v, w, z, u] = r ![z, u, v, w] :=
    hr.swap_pairs v w z u
  have hcyc := hr.cyclic_eq_zero u v z w
  linear_combination 2 * hcyc - t1 - t2 + t3 + t4

/-- Symmetric counterpart of `reactionBilinear_constantCurvature_right`. -/
theorem reactionBilinear_constantCurvature_left {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    reactionBilinear V (constantCurvature V) r = kulkarniNomizu (ricci r) (innerₗ V) := by
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

/-- On the rank-one curvature tensor `planeCurvature u v`, the reaction tensor acts by scalar
multiplication by `2 (‖u‖² ‖v‖² - ⟪u, v⟫²) = 2 * constantCurvature V ![u, v, u, v]`. -/
theorem reactionTensor_planeCurvature (u v : V) :
    reactionTensor (planeCurvature u v) =
      (2 * constantCurvature V ![u, v, u, v]) • planeCurvature u v := by
  set b := stdOrthonormalBasis ℝ V
  have hnorm :
      (∑ p, ∑ q, (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) ^ 2) =
        2 * constantCurvature V ![u, v, u, v] := by
    simp_rw [← planeCurvature_apply_self]
    rw [Finset.sum_comm, ← scalar_apply_orthonormalBasis b, scalar_planeCurvature]
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
  rw [reactionTensor_planeCurvature, ← scalar_planeCurvature,
    scalar_planeCurvature_of_orthonormal huv]

end FiniteDimensional

end FourTensor

end TauCeti
