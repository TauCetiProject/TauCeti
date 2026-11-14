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

/-!
# The reaction tensor on algebraic curvature four-tensors

In Uhlenbeck's orthonormal-frame formulation of the Ricci flow, the Riemann curvature four-tensor
evolves by `D_t R = Δ R + Q(R)`, where the quadratic reaction `Q(r)` of a four-tensor `r` on a
finite-dimensional real inner product space `V` has components

`Q(r)ᵢⱼₖₗ = ∑ p, ∑ q, rᵢⱼₚₑ rₖₗₚₑ + 2 ∑ p, ∑ q, rᵢₚₖₑ rⱼₚₗₑ - 2 ∑ p, ∑ q, rᵢₚₗₑ rⱼₚₖₑ`

in any orthonormal basis `(bᵢ)` (with the subscript `e` standing for `q`). Expanding these
components against the rank-one four-tensors `TauCeti.FourTensor.coordFourTensor` in the standard
orthonormal basis gives `TauCeti.FourTensor.reactionTensor`, together with its continuous symmetric
bilinear polarization `TauCeti.FourTensor.reactionBilinear V :
FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V` satisfying
`reactionBilinear V r r = reactionTensor r`.

Because each of the three double sums contracts two four-tensors across a full pair of inner-product
slots, the resulting four-tensor is independent of the chosen orthonormal basis
(`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`), and in every orthonormal basis `b`
its entries and coordinate expansion agree with `reactionComponent b r`
(`TauCeti.FourTensor.reactionComponent_eq_apply`,
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
* `TauCeti.FourTensor.reactionTensor`: the quadratic reaction four-tensor `Q(r)`.
* `TauCeti.FourTensor.reactionBilinear`: the continuous symmetric bilinear polarization of
  `reactionTensor`.

## Main statements

* `TauCeti.FourTensor.reactionBilinear_apply_orthonormalBasis`,
  `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`,
  `TauCeti.FourTensor.reactionComponent_eq_apply`, and
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
* `TauCeti.FourTensor.norm_reactionBilinear_le`, `TauCeti.FourTensor.contDiff_reactionTensor`,
  `TauCeti.FourTensor.hasStrictFDerivAt_reactionTensor`,
  `TauCeti.FourTensor.fderiv_reactionTensor`,
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

private local instance : NormedAddCommGroup (FourTensor V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace ℝ (FourTensor V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

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

/-- Continuous linear evaluation of a four-tensor at four vectors. -/
private def evalCLM (u v z w : V) : FourTensor V →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 ↦ V) ℝ ![u, v, z, w]

/-- Continuous bilinear product `(r, s) ↦ r(u₁, v₁, z₁, w₁) * s(u₂, v₂, z₂, w₂)`. -/
private def mulEvalBilin (u₁ v₁ z₁ w₁ u₂ v₂ z₂ w₂ : V) :
    FourTensor V →L[ℝ] FourTensor V →L[ℝ] ℝ :=
  (evalCLM u₁ v₁ z₁ w₁).smulRight (evalCLM u₂ v₂ z₂ w₂)

@[simp]
private theorem mulEvalBilin_apply (u₁ v₁ z₁ w₁ u₂ v₂ z₂ w₂ : V) (r s : FourTensor V) :
    mulEvalBilin u₁ v₁ z₁ w₁ u₂ v₂ z₂ w₂ r s =
      r ![u₁, v₁, z₁, w₁] * s ![u₂, v₂, z₂, w₂] := by
  simp [mulEvalBilin, evalCLM]

/-- The `(i, j, k, l)`-component functional of the symmetric bilinear polarization of the reaction
tensor in an orthonormal basis `b`. -/
private def reactionBilinearComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (i j k l : ι) : FourTensor V →L[ℝ] FourTensor V →L[ℝ] ℝ :=
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

@[simp]
private theorem lastSlice_apply (r : FourTensor V) (u v x y : V) :
    lastSlice r u v x y = r ![u, v, x, y] :=
  (rfl)

/-- The bilinear form `(x, y) ↦ r(u, x, z, y)` slicing the second and fourth slots of a
four-tensor. -/
private def evenSlice (r : FourTensor V) (u z : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, x, z, y])
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

@[simp]
private theorem evenSlice_apply (r : FourTensor V) (u z x y : V) :
    evenSlice r u z x y = r ![u, x, z, y] :=
  (rfl)

/-- Riesz-vector norm bound for a linear functional bounded by `C * ‖·‖`. -/
private theorem norm_sum_apply_smul_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {θ : V →ₗ[ℝ] ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hθ : ∀ z, |θ z| ≤ C * ‖z‖) :
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

/-- Cauchy–Schwarz bound on the double contraction of two bilinear forms over an orthonormal
basis `b`. -/
private theorem abs_sum_mul_bilinForm_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {F G : BilinForm ℝ V} {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hF : ∀ p x, |F (b p) x| ≤ A * ‖x‖) (hG : ∀ p x, |G (b p) x| ≤ B * ‖x‖) :
    |∑ p, ∑ q, F (b p) (b q) * G (b p) (b q)| ≤ (Fintype.card ι : ℝ) * (A * B) := by
  have hp (p : ι) : |∑ q, F (b p) (b q) * G (b p) (b q)| ≤ A * B := by
    have hxy : (∑ q, F (b p) (b q) * G (b p) (b q)) =
        ⟪∑ q, F (b p) (b q) • b q, ∑ q, G (b p) (b q) • b q⟫_ℝ := by
      simpa using
        (b.orthonormal.inner_sum (fun q ↦ F (b p) (b q)) (fun q ↦ G (b p) (b q))
          Finset.univ).symm
    rw [hxy]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (norm_sum_apply_smul_le b hA0 (hF p))
        (norm_sum_apply_smul_le b hB0 (hG p)) (norm_nonneg _) hA0)
  calc |∑ p, ∑ q, F (b p) (b q) * G (b p) (b q)|
      ≤ ∑ p, |∑ q, F (b p) (b q) * G (b p) (b q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : ι, A * B := Finset.sum_le_sum fun p _ ↦ hp p
    _ = (Fintype.card ι : ℝ) * (A * B) := by simp

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- Single-slot contraction of linear functionals pulled back along a coisometry `P : W →L[ℝ] V`
(`P ∘L P.adjoint = id`). -/
private theorem sum_mul_linearMap_comp_of_comp_adjoint_eq_id {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    {α β : Type*} [Fintype α] [Fintype β]
    (bW : OrthonormalBasis α ℝ W) (bV : OrthonormalBasis β ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (φ ψ : V →ₗ[ℝ] ℝ) :
    (∑ a, φ (P (bW a)) * ψ (P (bW a))) = ∑ p, φ (bV p) * ψ (bV p) := by
  have hP' (x : V) : P (P.adjoint x) = x := by
    simpa using DFunLike.congr_fun hP x
  have hexp (a : α) : φ (P (bW a)) = ∑ p, ⟪bW a, P.adjoint (bV p)⟫_ℝ * φ (bV p) := by
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

/-- Double contraction of two bilinear forms pulled back along a coisometry `P : W →L[ℝ] V`
(`P ∘L P.adjoint = id`). -/
private theorem sum_mul_bilinForm_comp_of_comp_adjoint_eq_id {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    {α β : Type*} [Fintype α] [Fintype β]
    (bW : OrthonormalBasis α ℝ W) (bV : OrthonormalBasis β ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (F G : BilinForm ℝ V) :
    (∑ a, ∑ b, F (P (bW a)) (P (bW b)) * G (P (bW a)) (P (bW b))) =
      ∑ p, ∑ q, F (bV p) (bV q) * G (bV p) (bV q) := by
  calc (∑ a, ∑ b, F (P (bW a)) (P (bW b)) * G (P (bW a)) (P (bW b)))
      = ∑ a, ∑ q, F (P (bW a)) (bV q) * G (P (bW a)) (bV q) :=
        Finset.sum_congr rfl fun a _ ↦
          sum_mul_linearMap_comp_of_comp_adjoint_eq_id bW bV hP (F (P (bW a))) (G (P (bW a)))
    _ = ∑ q, ∑ a, F.flip (bV q) (P (bW a)) * G.flip (bV q) (P (bW a)) := Finset.sum_comm
    _ = ∑ q, ∑ p, F.flip (bV q) (bV p) * G.flip (bV q) (bV p) :=
        Finset.sum_congr rfl fun q _ ↦
          sum_mul_linearMap_comp_of_comp_adjoint_eq_id bW bV hP (F.flip (bV q)) (G.flip (bV q))
    _ = ∑ p, ∑ q, F (bV p) (bV q) * G (bV p) (bV q) := Finset.sum_comm

/-- Orthonormal-basis invariance of the double contraction of two bilinear forms, obtained as the
`P = id` specialization of `sum_mul_bilinForm_comp_of_comp_adjoint_eq_id`. -/
private theorem sum_mul_bilinForm_orthonormalBasis {α β : Type*} [Fintype α] [Fintype β]
    (b₁ : OrthonormalBasis α ℝ V) (b₂ : OrthonormalBasis β ℝ V) (F G : BilinForm ℝ V) :
    (∑ a, ∑ b, F (b₁ a) (b₁ b) * G (b₁ a) (b₁ b)) =
      ∑ p, ∑ q, F (b₂ p) (b₂ q) * G (b₂ p) (b₂ q) := by
  simpa using sum_mul_bilinForm_comp_of_comp_adjoint_eq_id b₁ b₂
    (P := ContinuousLinearMap.id ℝ V)
    (by rw [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp]) F G

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
  have h12 (a b c d : V) : (fun i ↦ ![a, b, c, d] (Equiv.swap 1 2 i)) = ![a, c, b, d] := by
    funext i; fin_cases i <;> rfl
  simp only [pairMixedFourTensor, ContinuousMultilinearMap.domDomCongr_apply, h12,
    pairFirstFourTensor_apply]

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

/-- The reaction tensor `Q(r)` of the curvature evolution `D_t R = Δ R + Q(R)`, expanded in the
standard orthonormal basis of `V`:
`Q(r) = ∑ i, ∑ j, ∑ k, ∑ l, Q(r)ᵢⱼₖₗ • coordFourTensor b i j k l`. Its independence of the
orthonormal basis is `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionComponent (stdOrthonormalBasis ℝ V) r i j k l •
      coordFourTensor (stdOrthonormalBasis ℝ V) i j k l

variable (V) in
/-- The continuous symmetric bilinear polarization of `reactionTensor`, normalized so that
`reactionBilinear V r r = reactionTensor r`. -/
def reactionBilinear : withEndOperatorNorms V in
    FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    ((ContinuousLinearMap.smulRightL ℝ (FourTensor V) (FourTensor V)).flip
      (coordFourTensor (stdOrthonormalBasis ℝ V) i j k l)).comp
      (reactionBilinearComponent (stdOrthonormalBasis ℝ V) i j k l)

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
  set e := stdOrthonormalBasis ℝ V with he
  -- Bundle the contraction in `e` as a four-tensor `T`; its basis expansion in `e` is
  -- literally `reactionBilinear V r s`.
  let T : FourTensor V :=
    (2⁻¹ : ℝ) • (∑ p, ∑ q,
        (pairFirstFourTensor r s (e p) (e q) + pairFirstFourTensor s r (e p) (e q))) +
      (∑ p, ∑ q,
        (pairMixedFourTensor r s (e p) (e q) + pairMixedFourTensor s r (e p) (e q))) -
      (∑ p, ∑ q,
        (pairCrossFourTensor r s (e p) (e q) + pairCrossFourTensor s r (e p) (e q)))
  have hT : reactionBilinear V r s = T := by
    rw [← sum_smul_coordFourTensor e T, reactionBilinear, ← he]
    simp only [sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.smulRight_apply]
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
  rw [hT]
  simp only [T, sub_apply, add_apply, smul_apply, sum_apply, smul_eq_mul,
    pairFirstFourTensor_apply, pairMixedFourTensor_apply, pairCrossFourTensor_apply,
    Finset.sum_add_distrib]
  -- Transfer each of the six double contractions from `e` to `b`.
  have b1 := sum_mul_bilinForm_orthonormalBasis e b (lastSlice r u v) (lastSlice s z w)
  have b2 := sum_mul_bilinForm_orthonormalBasis e b (lastSlice s u v) (lastSlice r z w)
  have b3 := sum_mul_bilinForm_orthonormalBasis e b (evenSlice r u z) (evenSlice s v w)
  have b4 := sum_mul_bilinForm_orthonormalBasis e b (evenSlice s u z) (evenSlice r v w)
  have b5 := sum_mul_bilinForm_orthonormalBasis e b (evenSlice r u w) (evenSlice s v z)
  have b6 := sum_mul_bilinForm_orthonormalBasis e b (evenSlice s u w) (evenSlice r v z)
  simp only [lastSlice_apply, evenSlice_apply] at b1 b2 b3 b4 b5 b6
  rw [b1, b2, b3, b4, b5, b6]

/-- On the diagonal `(r, r)`, `reactionBilinear V` recovers `reactionTensor`. -/
@[simp]
theorem reactionBilinear_self (r : FourTensor V) :
    reactionBilinear V r r = reactionTensor r := by
  simp only [reactionBilinear, reactionTensor, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ congrArg (· • _) ?_
  simp only [reactionBilinearComponent, reactionComponent, sub_apply, add_apply, smul_apply,
    sum_apply, mulEvalBilin_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  · congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- `reactionBilinear V` is symmetric in its two four-tensor arguments. -/
theorem reactionBilinear_comm (r s : FourTensor V) :
    reactionBilinear V r s = reactionBilinear V s r := by
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  simp only [Finset.sum_add_distrib]
  ring

private theorem reactionBilinear_flip :
    (reactionBilinear V).flip = reactionBilinear V := by
  ext r s : 2
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
theorem reactionComponent_eq_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) :
    reactionComponent b r i j k l = reactionTensor r ![b i, b j, b k, b l] := by
  rw [reactionTensor_apply_orthonormalBasis b, reactionComponent_apply]

/-- In any orthonormal basis `b`, `reactionTensor r` expands as the linear combination of
`coordFourTensor b i j k l` weighted by `reactionComponent b r i j k l`. -/
theorem sum_reactionComponent_smul_coordFourTensor {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) :
    ∑ i, ∑ j, ∑ k, ∑ l, reactionComponent b r i j k l • coordFourTensor b i j k l =
      reactionTensor r := by
  simp_rw [reactionComponent_eq_apply, sum_smul_coordFourTensor]

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
      rw [hdiff, mul_neg, hr.two_mul_sum_mul_eq Finset.univ b t x y w]
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
  set bW := stdOrthonormalBasis ℝ W
  set bV := stdOrthonormalBasis ℝ V
  refine ext_vec fun u v z w ↦ ?_
  rw [compContinuousLinearMap_apply_vec,
    reactionBilinear_apply_orthonormalBasis bW, reactionBilinear_apply_orthonormalBasis bV]
  simp only [compContinuousLinearMap_apply_vec, Finset.sum_add_distrib]
  -- Transfer each of the six pulled-back double contractions from `bW` on `W` to `bV` on `V`.
  have c1 := sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bW bV hP
    (lastSlice r (P u) (P v)) (lastSlice s (P z) (P w))
  have c2 := sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bW bV hP
    (lastSlice s (P u) (P v)) (lastSlice r (P z) (P w))
  have c3 := sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bW bV hP
    (evenSlice r (P u) (P z)) (evenSlice s (P v) (P w))
  have c4 := sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bW bV hP
    (evenSlice s (P u) (P z)) (evenSlice r (P v) (P w))
  have c5 := sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bW bV hP
    (evenSlice r (P u) (P w)) (evenSlice s (P v) (P z))
  have c6 := sum_mul_bilinForm_comp_of_comp_adjoint_eq_id bW bV hP
    (evenSlice s (P u) (P w)) (evenSlice r (P v) (P z))
  simp only [lastSlice_apply, evenSlice_apply] at c1 c2 c3 c4 c5 c6
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
    reactionBilinear W
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionBilinear V r s).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  refine reactionBilinear_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r s
  rw [e.toContinuousLinearMap_toLinearIsometry, LinearIsometryEquiv.adjoint_eq_symm]
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
  set b := stdOrthonormalBasis ℝ V
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hm]
  rw [Fin.prod_univ_four, reactionBilinear_apply_orthonormalBasis b, Real.norm_eq_abs]
  -- Operator-norm bounds on each row of `lastSlice` and `evenSlice`.
  have hlast (t : FourTensor V) (u v : V) (p : Fin (Module.finrank ℝ V)) (x : V) :
      |lastSlice t u v (b p) x| ≤ (‖t‖ * ‖u‖ * ‖v‖) * ‖x‖ := by
    simpa only [lastSlice_apply, Real.norm_eq_abs, Fin.prod_univ_four,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, b.norm_eq_one,
      mul_one, mul_assoc] using t.le_opNorm ![u, v, b p, x]
  have heven (t : FourTensor V) (u z : V) (p : Fin (Module.finrank ℝ V)) (x : V) :
      |evenSlice t u z (b p) x| ≤ (‖t‖ * ‖u‖ * ‖z‖) * ‖x‖ := by
    have h := t.le_opNorm ![u, b p, z, x]
    rw [Real.norm_eq_abs, Fin.prod_univ_four] at h
    simpa only [evenSlice_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, b.norm_eq_one, one_mul, mul_one, mul_assoc] using h
  -- Bound each of the six double contractions by `dim V * ‖r‖ * ‖s‖ * ∏ i, ‖m i‖`.
  let P : ℝ := (Module.finrank ℝ V : ℝ) * ‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)
  have hcard : (Fintype.card (Fin (Module.finrank ℝ V)) : ℝ) = Module.finrank ℝ V := by simp
  have s1 : |∑ p, ∑ q, r ![m 0, m 1, b p, b q] * s ![m 2, m 3, b p, b q]| ≤ P :=
    (abs_sum_mul_bilinForm_le b (by positivity) (by positivity)
      (hlast r (m 0) (m 1)) (hlast s (m 2) (m 3))).trans_eq (by rw [hcard]; dsimp only [P]; ring)
  have s2 : |∑ p, ∑ q, s ![m 0, m 1, b p, b q] * r ![m 2, m 3, b p, b q]| ≤ P :=
    (abs_sum_mul_bilinForm_le b (by positivity) (by positivity)
      (hlast s (m 0) (m 1)) (hlast r (m 2) (m 3))).trans_eq (by rw [hcard]; dsimp only [P]; ring)
  have s3 : |∑ p, ∑ q, r ![m 0, b p, m 2, b q] * s ![m 1, b p, m 3, b q]| ≤ P :=
    (abs_sum_mul_bilinForm_le b (by positivity) (by positivity)
      (heven r (m 0) (m 2)) (heven s (m 1) (m 3))).trans_eq (by rw [hcard]; dsimp only [P]; ring)
  have s4 : |∑ p, ∑ q, s ![m 0, b p, m 2, b q] * r ![m 1, b p, m 3, b q]| ≤ P :=
    (abs_sum_mul_bilinForm_le b (by positivity) (by positivity)
      (heven s (m 0) (m 2)) (heven r (m 1) (m 3))).trans_eq (by rw [hcard]; dsimp only [P]; ring)
  have s5 : |∑ p, ∑ q, r ![m 0, b p, m 3, b q] * s ![m 1, b p, m 2, b q]| ≤ P :=
    (abs_sum_mul_bilinForm_le b (by positivity) (by positivity)
      (heven r (m 0) (m 3)) (heven s (m 1) (m 2))).trans_eq (by rw [hcard]; dsimp only [P]; ring)
  have s6 : |∑ p, ∑ q, s ![m 0, b p, m 3, b q] * r ![m 1, b p, m 2, b q]| ≤ P :=
    (abs_sum_mul_bilinForm_le b (by positivity) (by positivity)
      (heven s (m 0) (m 3)) (heven r (m 1) (m 2))).trans_eq (by rw [hcard]; dsimp only [P]; ring)
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

/-- The operator norm of `reactionBilinear V` is at most `5 * dim V`. -/
theorem norm_reactionBilinear_le : withEndOperatorNorms V in
    ‖reactionBilinear V‖ ≤ 5 * (Module.finrank ℝ V : ℝ) :=
  ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) norm_reactionBilinear_apply_le

/-- The operator norm of `reactionTensor r` is at most `5 * dim V * ‖r‖²`. -/
theorem norm_reactionTensor_le (r : FourTensor V) :
    ‖reactionTensor r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) * ‖r‖ ^ 2 := by
  rw [← reactionBilinear_self, sq]
  exact (norm_reactionBilinear_apply_le r r).trans_eq (by ring)

/-- Difference estimate `‖Q(r) - Q(s)‖ ≤ ‖reactionBilinear V‖ * (‖r‖ + ‖s‖) * ‖r - s‖`. -/
theorem norm_reactionTensor_sub_le (r s : FourTensor V) : withEndOperatorNorms V in
    ‖reactionTensor r - reactionTensor s‖ ≤
      ‖reactionBilinear V‖ * (‖r‖ + ‖s‖) * ‖r - s‖ := by
  rw [← reactionBilinear_self r, ← reactionBilinear_self s]
  exact (reactionBilinear V).norm_apply_apply_sub_apply_apply_le r s

/-- `reactionTensor` is `C^n` for every smoothness order `n` (including `∞` and `ω`). -/
@[fun_prop]
theorem contDiff_reactionTensor {n : ℕ∞ω} : ContDiff ℝ n (reactionTensor (V := V)) := by
  rw [show (reactionTensor (V := V)) = fun r ↦ reactionBilinear V r r from
    funext fun r ↦ (reactionBilinear_self r).symm]
  exact (reactionBilinear V).contDiff_apply_self

/-- `reactionTensor` is continuous. -/
@[fun_prop]
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 0)).continuous

/-- Strict Fréchet derivative of `reactionTensor` at `r`:
`DQ(r) = (2 : ℝ) • reactionBilinear V r`. -/
theorem hasStrictFDerivAt_reactionTensor (r : FourTensor V) :
    HasStrictFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r := by
  rw [show (reactionTensor (V := V)) = fun q ↦ reactionBilinear V q q from
    funext fun q ↦ (reactionBilinear_self q).symm]
  simpa only [reactionBilinear_flip, two_smul] using
    (reactionBilinear V).hasStrictFDerivAt_apply_self r

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
`2 * R.toNNReal * ‖reactionBilinear V‖₊`. -/
theorem lipschitzOnWith_reactionTensor_closedBall (R : ℝ) : withEndOperatorNorms V in
    LipschitzOnWith (2 * R.toNNReal * ‖reactionBilinear V‖₊)
      (reactionTensor (V := V)) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun r hr s hs ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hr hs
  have hR : 0 ≤ R := (norm_nonneg r).trans hr
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖reactionTensor r - reactionTensor s‖
      ≤ ‖reactionBilinear V‖ * (‖r‖ + ‖s‖) * ‖r - s‖ := norm_reactionTensor_sub_le r s
    _ ≤ ‖reactionBilinear V‖ * (R + R) * ‖r - s‖ := by gcongr
    _ = ↑(2 * R.toNNReal * ‖reactionBilinear V‖₊) * ‖r - s‖ := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal R hR, coe_nnNorm]
        ring

/-- `reactionTensor` is locally Lipschitz on `FourTensor V`. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 1)).locallyLipschitz

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
    have hi (i : ι) :
        2 * (∑ q, ∑ p, r ![b q, b p, v, b i] * r ![u, b p, b q, b i]) =
          ∑ q, ∑ p, r ![b q, b p, v, b i] * r ![b q, b p, u, b i] := by
      have h := hr.two_mul_sum_mul_eq Finset.univ b v (b i) u (b i)
      have hlhs : (∑ p, ∑ q, r ![v, b i, b p, b q] * r ![u, b p, b i, b q]) =
          ∑ q, ∑ p, r ![b q, b p, v, b i] * r ![u, b p, b q, b i] := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
        rw [hr.swap_pairs v (b i), hr.antisymm_first (b p) (b q),
          hr.antisymm_last u (b p) (b i) (b q), neg_mul_neg]
      have hrhs : (∑ p, ∑ q, r ![v, b i, b p, b q] * r ![u, b i, b p, b q]) =
          ∑ q, ∑ p, r ![b q, b p, v, b i] * r ![b q, b p, u, b i] :=
        Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ by
          rw [hr.swap_pairs v (b i), hr.swap_pairs u (b i)]
      rwa [hlhs, hrhs] at h
    calc (∑ i, ∑ p, ∑ q, r ![b i, u, b p, b q] * r ![b i, v, b p, b q])
        = ∑ i, ∑ q, ∑ p, r ![b i, u, b p, b q] * r ![b i, v, b p, b q] :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = ∑ i, ∑ q, ∑ p, r ![b q, b p, v, b i] * r ![b q, b p, u, b i] := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun q _ ↦
            Finset.sum_congr rfl fun p _ ↦ ?_
          rw [hr.antisymm_first (b i) u, hr.antisymm_last u (b i) (b p) (b q), neg_neg,
            hr.swap_pairs u (b i), hr.antisymm_first (b i) v,
            hr.antisymm_last v (b i) (b p) (b q), neg_neg, hr.swap_pairs v (b i), mul_comm]
      _ = ∑ i, 2 * ∑ q, ∑ p, r ![b q, b p, v, b i] * r ![u, b p, b q, b i] :=
          Finset.sum_congr rfl fun i _ ↦ (hi i).symm
      _ = 2 * ∑ q, ∑ p, ∑ i, r ![b q, b p, v, b i] * r ![u, b p, b q, b i] := by
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
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have horth : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [reactionTensor_planeCurvature, constantCurvature_apply_self, hu, hv, horth]
  norm_num

end FiniteDimensional

end FourTensor

end TauCeti
