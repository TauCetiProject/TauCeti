/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The algebraic curvature reaction tensor

Under Hamilton's Ricci flow, the Riemann curvature four-tensor evolves in a moving orthonormal
frame by a reaction-diffusion equation whose fibrewise quadratic reaction term `Q(r)` has
components

`Q(r)ᵢⱼₖₗ = ∑ p q, rᵢⱼₚₑ rₖₗₚₑ + 2 ∑ p q, rᵢₚₖₑ rⱼₚₗₑ - 2 ∑ p q, rᵢₚₗₑ rⱼₚₖₑ`

in any orthonormal basis `(bᵢ)`, with `rᵢⱼₖₗ = r(bᵢ, bⱼ, bₖ, bₗ)`. On the curvature-operator side
this quadratic map corresponds to Hamilton's `2 (R² + R#)`, where `R#` is the Lie-algebra square on
`⋀² V`.

This file defines the rank-one coordinate four-tensors `TauCeti.FourTensor.coordFourTensor`, the
component expression `TauCeti.FourTensor.reactionComponent`, the quadratic reaction map
`TauCeti.FourTensor.reactionTensor`, and its symmetric continuous bilinear polarization
`TauCeti.FourTensor.reactionBilinear`. Although `reactionTensor` is defined by expanding
`reactionComponent` in `stdOrthonormalBasis ℝ V`, each double sum over `(p, q)` is a full metric
contraction of two bilinear slices of `r`, so `reactionTensor r ![u, v, z, w]` is given by the same
contraction formula in *every* orthonormal basis
(`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`).

Consequently `reactionTensor` is equivariant under linear isometric equivalences, preserves the
closed submodule `TauCeti.FourTensor.algebraicCurvatureSubmodule V` of algebraic curvature tensors
(`TauCeti.FourTensor.reactionTensor_mem`), and restricts to a smooth, locally Lipschitz map
`TauCeti.FourTensor.algebraicCurvatureReaction` with explicit quadratic norm and closed-ball
Lipschitz bounds. On the unit-sphere constant-curvature tensor `constantCurvature V` it satisfies
`Q(I) = 2 (n - 1) I`, and on the rank-one plane curvature tensor `planeCurvature x y` of a pair of
vectors `(x, y)` it multiplies by twice the Gram determinant `‖x‖² ‖y‖² - ⟪x, y⟫²` (in particular
`Q(r) = 2 r` for an orthonormal pair, the curvature model of `S² × ℝⁿ⁻²`).

## Main definitions

* `TauCeti.FourTensor.coordFourTensor`: the rank-one four-tensor
  `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫`.
* `TauCeti.FourTensor.planeCurvature`: the rank-one algebraic curvature four-tensor
  `(u, v, z, w) ↦ (⟪x, u⟫ ⟪y, v⟫ - ⟪x, v⟫ ⟪y, u⟫) (⟪x, z⟫ ⟪y, w⟫ - ⟪x, w⟫ ⟪y, z⟫)`.
* `TauCeti.FourTensor.reactionComponent`: the components of `Q(r)` in an orthonormal basis.
* `TauCeti.FourTensor.reactionTensor`: Hamilton's quadratic curvature reaction `Q : FourTensor V →
  FourTensor V`.
* `TauCeti.FourTensor.reactionBilinear`: the symmetric continuous bilinear polarization of
  `reactionTensor`.
* `TauCeti.FourTensor.algebraicCurvatureReaction`: the restriction of `reactionTensor` to
  `algebraicCurvatureSubmodule V`.

## Main statements

* `TauCeti.FourTensor.sum_smul_coordFourTensor`: expansion of a four-tensor in the rank-one
  coordinate tensors of an orthonormal basis.
* `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`: basis independence of
  `reactionTensor`.
* `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv`: orthogonal
  equivariance of `reactionTensor`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor` and
  `TauCeti.FourTensor.reactionTensor_mem`: `reactionTensor` preserves the pair antisymmetries, pair
  interchange, and the first Bianchi identity.
* `TauCeti.FourTensor.contDiff_reactionTensor`,
  `TauCeti.FourTensor.lipschitzOnWith_reactionTensor_closedBall`, and
  `TauCeti.FourTensor.locallyLipschitz_reactionTensor`: smoothness and bounded-set Lipschitz
  regularity of `reactionTensor` (and its restriction `algebraicCurvatureReaction`).
* `TauCeti.FourTensor.reactionTensor_constantCurvature` and
  `TauCeti.FourTensor.reactionTensor_planeCurvature`: evaluation of `reactionTensor` on constant
  sectional curvature and on rank-one plane curvature tensors.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, Section 2.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307, Section 2.
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace NNReal ContDiff

noncomputable section

namespace TauCeti.FourTensor

section BilinSlices

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The bilinear form `(x, y) ↦ r(x, y, z, w)` obtained by fixing the last two arguments of `r`. -/
private def slice12 (r : FourTensor V) (z w : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![x, y, z, w])
    (fun _ _ _ ↦ apply_add_first ..) (fun _ _ _ ↦ apply_smul_first ..)
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)

/-- The bilinear form `(x, y) ↦ r(u, v, x, y)` obtained by fixing the first two arguments of `r`. -/
private def slice34 (r : FourTensor V) (u v : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, v, x, y])
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

/-- The bilinear form `(x, y) ↦ r(u, x, z, y)` obtained by fixing the first and third arguments of
`r`. -/
private def slice24 (r : FourTensor V) (u z : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, x, z, y])
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

/-- The bilinear form `(x, y) ↦ r(x, p, y, q)` obtained by fixing the second and fourth arguments
of `r`. -/
private def slice13 (r : FourTensor V) (p q : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![x, p, y, q])
    (fun _ _ _ ↦ apply_add_first ..) (fun _ _ _ ↦ apply_smul_first ..)
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)

@[simp]
private theorem slice12_apply (r : FourTensor V) (z w x y : V) :
    slice12 r z w x y = r ![x, y, z, w] :=
  rfl

@[simp]
private theorem slice34_apply (r : FourTensor V) (u v x y : V) :
    slice34 r u v x y = r ![u, v, x, y] :=
  rfl

@[simp]
private theorem slice24_apply (r : FourTensor V) (u z x y : V) :
    slice24 r u z x y = r ![u, x, z, y] :=
  rfl

@[simp]
private theorem slice13_apply (r : FourTensor V) (p q x y : V) :
    slice13 r p q x y = r ![x, p, y, q] :=
  rfl

end BilinSlices

section CoordFourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W]
  [InnerProductSpace ℝ W]

/-- The rank-one four-tensor `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫` attached to four
vectors of a family `b`. -/
def coordFourTensor {ι : Type*} (b : ι → V) (i j k l : ι) : FourTensor V :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).compContinuousLinearMap
    ![innerSL ℝ (b i), innerSL ℝ (b j), innerSL ℝ (b k), innerSL ℝ (b l)]

/-- Unfolding definition of `coordFourTensor` as the composition of four inner-product covectors
with four-fold real multiplication. -/
theorem coordFourTensor_def {ι : Type*} (b : ι → V) (i j k l : ι) :
    coordFourTensor b i j k l =
      (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).compContinuousLinearMap
        ![innerSL ℝ (b i), innerSL ℝ (b j), innerSL ℝ (b k), innerSL ℝ (b l)] :=
  (rfl)

/-- Evaluation of `coordFourTensor` on an arbitrary four-tuple `m : Fin 4 → V`. -/
theorem coordFourTensor_apply_tuple {ι : Type*} (b : ι → V) (i j k l : ι) (m : Fin 4 → V) :
    coordFourTensor b i j k l m =
      ⟪b i, m 0⟫_ℝ * ⟪b j, m 1⟫_ℝ * ⟪b k, m 2⟫_ℝ * ⟪b l, m 3⟫_ℝ := by
  rw [coordFourTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn, Fin.prod_univ_four]
  simp [mul_assoc]

/-- Evaluation of `coordFourTensor` on four vectors `![u, v, z, w]`. -/
@[simp]
theorem coordFourTensor_apply {ι : Type*} (b : ι → V) (i j k l : ι) (u v z w : V) :
    coordFourTensor b i j k l ![u, v, z, w] =
      ⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ :=
  coordFourTensor_apply_tuple b i j k l ![u, v, z, w]

/-- The operator norm of `coordFourTensor b i j k l` is the product of the norms of the four
vectors `b i`, `b j`, `b k`, `b l`. -/
@[simp]
theorem norm_coordFourTensor {ι : Type*} (b : ι → V) (i j k l : ι) :
    ‖coordFourTensor b i j k l‖ = ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ := by
  have hle : ‖coordFourTensor b i j k l‖ ≤ ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ := by
    refine (coordFourTensor b i j k l).opNorm_le_bound (by positivity) fun m ↦ ?_
    rw [coordFourTensor_apply_tuple, Fin.prod_univ_four]
    simp only [Real.norm_eq_abs, abs_mul]
    calc |⟪b i, m 0⟫_ℝ| * |⟪b j, m 1⟫_ℝ| * |⟪b k, m 2⟫_ℝ| * |⟪b l, m 3⟫_ℝ|
        ≤ (‖b i‖ * ‖m 0‖) * (‖b j‖ * ‖m 1‖) * (‖b k‖ * ‖m 2‖) * (‖b l‖ * ‖m 3‖) := by
          gcongr <;> exact abs_real_inner_le_norm _ _
      _ = ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖) := by ring
  refine hle.antisymm ?_
  by_cases h0 : ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ = 0
  · rw [h0]
    exact norm_nonneg _
  · have hpos : 0 < ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have heval := (coordFourTensor b i j k l).le_opNorm ![b i, b j, b k, b l]
    rw [coordFourTensor_apply, Fin.prod_univ_four] at heval
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs] at heval
    have hsq : |‖b i‖ ^ 2 * ‖b j‖ ^ 2 * ‖b k‖ ^ 2 * ‖b l‖ ^ 2| =
        (‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖) * (‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖) := by
      rw [abs_of_nonneg (by positivity)]
      ring
    rw [hsq] at heval
    exact le_of_mul_le_mul_right heval hpos

/-- For an orthonormal family `b`, each rank-one coordinate four-tensor `coordFourTensor b i j k l`
has unit operator norm. -/
theorem _root_.Orthonormal.norm_coordFourTensor {ι : Type*} {b : ι → V} (hb : Orthonormal ℝ b)
    (i j k l : ι) : ‖coordFourTensor b i j k l‖ = 1 := by
  simp [hb.1]

/-- Pulling back `coordFourTensor (f ∘ c) i j k l` along a linear isometry `f` recovers
`coordFourTensor c i j k l`. -/
@[simp]
theorem coordFourTensor_compContinuousLinearMap_linearIsometry {ι : Type*} (f : W →ₗᵢ[ℝ] V)
    (c : ι → W) (i j k l : ι) :
    (coordFourTensor (f ∘ c) i j k l).compContinuousLinearMap (fun _ ↦ f.toContinuousLinearMap) =
      coordFourTensor c i j k l :=
  ext_vec fun u v z w ↦ by
    rw [compContinuousLinearMap_apply_vec]
    simp

/-- Pulling back `coordFourTensor b i j k l` along a linear isometric equivalence `e : W ≃ₗᵢ[ℝ] V`
transports the family `b` by `e.symm`. -/
theorem coordFourTensor_compContinuousLinearMap_linearIsometryEquiv {ι : Type*} (e : W ≃ₗᵢ[ℝ] V)
    (b : ι → V) (i j k l : ι) :
    (coordFourTensor b i j k l).compContinuousLinearMap
        (fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      coordFourTensor (e.symm ∘ b) i j k l :=
  ext_vec fun u v z w ↦ by
    rw [compContinuousLinearMap_apply_vec]
    simp [LinearIsometryEquiv.inner_map_eq_flip]

/-- Evaluating a linear combination of `coordFourTensor b i' j' k' l'` on `(b i, b j, b k, b l)`
for an orthonormal family `b` extracts the `(i, j, k, l)` coefficient. -/
theorem apply_sum_smul_coordFourTensor {ι : Type*} [Fintype ι] {b : ι → V} (hb : Orthonormal ℝ b)
    (c : ι → ι → ι → ι → ℝ) (i j k l : ι) :
    (∑ i', ∑ j', ∑ k', ∑ l', c i' j' k' l' • coordFourTensor b i' j' k' l')
      ![b i, b j, b k, b l] = c i j k l := by
  classical
  simp [sum_apply, orthonormal_iff_ite.mp hb]

/-- Every four-tensor `r` is the sum of its components in a finite orthonormal basis `b` against
the coordinate rank-one four-tensors `coordFourTensor b i j k l`. -/
theorem sum_smul_coordFourTensor {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] • coordFourTensor b i j k l) = r := by
  refine ext_vec fun u v z w ↦ ?_
  simp only [sum_apply, smul_apply, coordFourTensor_apply, smul_eq_mul]
  have step4 (i j k : ι) :
      ∑ l, r ![b i, b j, b k, b l] * (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ) =
        r ![b i, b j, b k, w] * (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ) := by
    calc _ = (∑ l, slice34 r (b i) (b j) (b k) (b l) * ⟪b l, w⟫_ℝ) *
          (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ ↦ by simp only [slice34_apply]; ring
      _ = _ := by rw [b.sum_apply_mul_inner, slice34_apply]
  have step3 (i j : ι) :
      ∑ k, r ![b i, b j, b k, w] * (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ) =
        r ![b i, b j, z, w] * (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ) := by
    calc _ = (∑ k, (slice34 r (b i) (b j)).flip w (b k) * ⟪b k, z⟫_ℝ) *
          (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ ↦ by
            simp only [LinearMap.BilinForm.flip_apply, slice34_apply]; ring
      _ = _ := by rw [b.sum_apply_mul_inner, LinearMap.BilinForm.flip_apply, slice34_apply]
  have step2 (i : ι) :
      ∑ j, r ![b i, b j, z, w] * (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ) =
        r ![b i, v, z, w] * ⟪b i, u⟫_ℝ := by
    calc _ = (∑ j, slice12 r z w (b i) (b j) * ⟪b j, v⟫_ℝ) * ⟪b i, u⟫_ℝ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ ↦ by simp only [slice12_apply]; ring
      _ = _ := by rw [b.sum_apply_mul_inner, slice12_apply]
  simp_rw [step4, step3, step2]
  simpa only [LinearMap.BilinForm.flip_apply, slice12_apply] using
    b.sum_apply_mul_inner ((slice12 r z w).flip v) u

/-- The rank-one algebraic curvature four-tensor attached to two vectors `x, y : V`,
`planeCurvature x y ![u, v, z, w] = (⟪x, u⟫ ⟪y, v⟫ - ⟪x, v⟫ ⟪y, u⟫) *
(⟪x, z⟫ ⟪y, w⟫ - ⟪x, w⟫ ⟪y, z⟫)`. On `⋀² V` it represents the rank-one operator
`ω ↦ ⟪x ∧ y, ω⟫ (x ∧ y)`; for an orthonormal pair `(x, y)` it is the curvature four-tensor of
`S² × ℝⁿ⁻²` along the `S²` factor `span {x, y}`. -/
def planeCurvature (x y : V) : FourTensor V :=
  coordFourTensor ![x, y] 0 1 0 1 - coordFourTensor ![x, y] 0 1 1 0 -
    coordFourTensor ![x, y] 1 0 0 1 + coordFourTensor ![x, y] 1 0 1 0

/-- Evaluation of `planeCurvature x y` as the product of two `2 × 2` Gram minors against
`(x, y)`. -/
@[simp]
theorem planeCurvature_apply (x y u v z w : V) :
    planeCurvature x y ![u, v, z, w] =
      (⟪x, u⟫_ℝ * ⟪y, v⟫_ℝ - ⟪x, v⟫_ℝ * ⟪y, u⟫_ℝ) *
        (⟪x, z⟫_ℝ * ⟪y, w⟫_ℝ - ⟪x, w⟫_ℝ * ⟪y, z⟫_ℝ) := by
  simp only [planeCurvature, add_apply, sub_apply, coordFourTensor_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Interchanging `x` and `y` negates both `2 × 2` minors and therefore leaves `planeCurvature`
unchanged. -/
theorem planeCurvature_comm (x y : V) : planeCurvature y x = planeCurvature x y :=
  ext_vec fun u v z w ↦ by
    simp only [planeCurvature_apply]
    ring

/-- The plane curvature tensor of a repeated vector vanishes. -/
@[simp]
theorem planeCurvature_self (x : V) : planeCurvature x x = 0 :=
  ext_vec fun u v z w ↦ by
    simp only [planeCurvature_apply, zero_apply]
    ring

/-- Every rank-one plane tensor `planeCurvature x y` is an algebraic curvature tensor; the first
Bianchi identity is the three-term Plücker relation for `2 × 2` minors. -/
theorem isAlgebraicCurvature_planeCurvature (x y : V) :
    IsAlgebraicCurvature (planeCurvature x y) := by
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [planeCurvature_apply] <;> ring

/-- Every `planeCurvature x y` belongs to `algebraicCurvatureSubmodule V`. -/
theorem planeCurvature_mem_algebraicCurvatureSubmodule (x y : V) :
    planeCurvature x y ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_planeCurvature x y)

/-- Pulling back `planeCurvature (f x) (f y)` along a linear isometry `f` gives
`planeCurvature x y`. -/
@[simp]
theorem planeCurvature_compContinuousLinearMap_linearIsometry (f : W →ₗᵢ[ℝ] V) (x y : W) :
    (planeCurvature (f x) (f y)).compContinuousLinearMap (fun _ ↦ f.toContinuousLinearMap) =
      planeCurvature x y :=
  ext_vec fun u v z w ↦ by
    rw [compContinuousLinearMap_apply_vec]
    simp

end CoordFourTensor

section OrthonormalHelpers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The components of the reaction tensor `Q(r)` in an orthonormal basis `b`, with
`r_ijpq = r(b i, b j, b p, b q)`:
`Q(r)_ijkl = ∑_pq r_ijpq r_klpq + 2 ∑_pq r_ipkq r_jplq - 2 ∑_pq r_iplq r_jpkq`
(Brendle–Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, Section 2). -/
def reactionComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) : ℝ :=
  (∑ p, ∑ q, r ![b i, b j, b p, b q] * r ![b k, b l, b p, b q]) +
  2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * r ![b j, b p, b l, b q]) -
  2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * r ![b j, b p, b k, b q])

/-- Unfolding formula for `reactionComponent`. -/
theorem reactionComponent_def {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) :
    reactionComponent b r i j k l =
      (∑ p, ∑ q, r ![b i, b j, b p, b q] * r ![b k, b l, b p, b q]) +
      2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * r ![b j, b p, b l, b q]) -
      2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * r ![b j, b p, b k, b q]) :=
  (rfl)

/-- Unsymmetrized bilinear component of the reaction contraction in an orthonormal basis `b`. -/
private def reactionRawComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) (i j k l : ι) : ℝ :=
  (∑ p, ∑ q, r ![b i, b j, b p, b q] * s ![b k, b l, b p, b q]) +
  2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * s ![b j, b p, b l, b q]) -
  2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * s ![b j, b p, b k, b q])

private theorem sum_comm_four_two {α β : Type*} [Fintype α] [Fintype β]
    (f : α → α → α → α → β → β → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, f i j k l p q) =
      ∑ p, ∑ q, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l p q := by
  trans (∑ i, ∑ j, ∑ k, ∑ p, ∑ q, ∑ l, f i j k l p q)
  · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  trans (∑ i, ∑ j, ∑ p, ∑ q, ∑ k, ∑ l, f i j k l p q)
  · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  trans (∑ i, ∑ p, ∑ q, ∑ j, ∑ k, ∑ l, f i j k l p q)
  · exact Finset.sum_congr rfl fun _ _ ↦ by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

private theorem sum_bilin_12_34 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (A B : BilinForm ℝ V) (u v z w : V) :
    (∑ i, ∑ j, ∑ k, ∑ l, (A (b i) (b j) * B (b k) (b l)) *
      (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ)) = A u v * B z w := by
  have hpair (C : BilinForm ℝ V) (x y : V) :
      ∑ k, ∑ l, C (b k) (b l) * (⟪b k, x⟫_ℝ * ⟪b l, y⟫_ℝ) = C x y := by
    calc _ = ∑ k, (∑ l, C (b k) (b l) * ⟪b l, y⟫_ℝ) * ⟪b k, x⟫_ℝ :=
          Finset.sum_congr rfl fun k _ ↦ by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ ↦ by ring
      _ = ∑ k, C.flip y (b k) * ⟪b k, x⟫_ℝ := by
          simp_rw [b.sum_apply_mul_inner (C _), LinearMap.BilinForm.flip_apply]
      _ = C x y := b.sum_apply_mul_inner (C.flip y) x
  calc _ = ∑ i, ∑ j, (A (b i) (b j) * (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ)) *
        (∑ k, ∑ l, B (b k) (b l) * (⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ)) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
    _ = (∑ i, ∑ j, A (b i) (b j) * (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ)) * B z w := by
        simp_rw [hpair B z w, ← Finset.sum_mul]
    _ = A u v * B z w := by rw [hpair A u v]

private theorem sum_bilin_13_24 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (A B : BilinForm ℝ V) (u v z w : V) :
    (∑ i, ∑ j, ∑ k, ∑ l, (A (b i) (b k) * B (b j) (b l)) *
      (⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ)) = A u z * B v w := by
  calc _ = ∑ i, ∑ k, ∑ j, ∑ l, (A (b i) (b k) * B (b j) (b l)) *
        (⟪b i, u⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b l, w⟫_ℝ) :=
        Finset.sum_congr rfl fun i _ ↦ by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦
            Finset.sum_congr rfl fun l _ ↦ by ring
    _ = A u z * B v w := sum_bilin_12_34 b A B u z v w

private theorem abs_sum_mul_le_card_sq {ι : Type*} [Fintype ι]
    {B : ℝ} {f g : ι → ι → ℝ} {A C : ℝ} (hA : 0 ≤ A)
    (hf : ∀ p q, |f p q| ≤ A) (hg : ∀ p q, |g p q| ≤ C) (hBC : A * C ≤ B) :
    |∑ p, ∑ q, f p q * g p q| ≤ (Fintype.card ι : ℝ) ^ 2 * B := by
  have h1 : |∑ p, ∑ q, f p q * g p q| ≤ ∑ _p : ι, ∑ _q : ι, B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ ↦ ?_)
    rw [abs_mul]
    exact (mul_le_mul (hf p q) (hg p q) (abs_nonneg _) hA).trans hBC
  refine h1.trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

private theorem abs_apply_basis_two_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (m : Fin 4 → V) (p q : ι) :
    |r ![m 0, m 1, b p, b q]| ≤ ‖r‖ * (‖m 0‖ * ‖m 1‖) ∧
      |r ![m 0, b p, m 2, b q]| ≤ ‖r‖ * (‖m 0‖ * ‖m 2‖) ∧
      |r ![m 0, b p, m 3, b q]| ≤ ‖r‖ * (‖m 0‖ * ‖m 3‖) ∧
      |r ![m 1, b p, m 2, b q]| ≤ ‖r‖ * (‖m 1‖ * ‖m 2‖) ∧
      |r ![m 1, b p, m 3, b q]| ≤ ‖r‖ * (‖m 1‖ * ‖m 3‖) ∧
      |r ![m 2, m 3, b p, b q]| ≤ ‖r‖ * (‖m 2‖ * ‖m 3‖) := by
  have bound (x y z w : V) : |r ![x, y, z, w]| ≤ ‖r‖ * ‖x‖ * ‖y‖ * ‖z‖ * ‖w‖ := by
    simpa only [Real.norm_eq_abs, Fin.prod_univ_four, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, ← mul_assoc] using r.le_opNorm ![x, y, z, w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [b.orthonormal.1 p, b.orthonormal.1 q, mul_assoc] using bound (m 0) (m 1) (b p) (b q)
  · simpa [b.orthonormal.1 p, b.orthonormal.1 q, mul_assoc] using bound (m 0) (b p) (m 2) (b q)
  · simpa [b.orthonormal.1 p, b.orthonormal.1 q, mul_assoc] using bound (m 0) (b p) (m 3) (b q)
  · simpa [b.orthonormal.1 p, b.orthonormal.1 q, mul_assoc] using bound (m 1) (b p) (m 2) (b q)
  · simpa [b.orthonormal.1 p, b.orthonormal.1 q, mul_assoc] using bound (m 1) (b p) (m 3) (b q)
  · simpa [b.orthonormal.1 p, b.orthonormal.1 q, mul_assoc] using bound (m 2) (m 3) (b p) (b q)

private theorem sum_real_inner_mul_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (x y : V) : ∑ p, ⟪x, b p⟫_ℝ * ⟪y, b p⟫_ℝ = ⟪x, y⟫_ℝ := by
  simpa only [real_inner_comm (b _)] using b.sum_inner_mul_inner x y

private theorem sum_real_inner_pair {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (x₁ y₁ x₂ y₂ : V) :
    (∑ p, ∑ q, ⟪x₁, b p⟫_ℝ * ⟪y₁, b p⟫_ℝ * (⟪x₂, b q⟫_ℝ * ⟪y₂, b q⟫_ℝ)) =
      ⟪x₁, y₁⟫_ℝ * ⟪x₂, y₂⟫_ℝ := by
  calc _ = (∑ p, ⟪x₁, b p⟫_ℝ * ⟪y₁, b p⟫_ℝ) * ∑ q, ⟪x₂, b q⟫_ℝ * ⟪y₂, b q⟫_ℝ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ ↦ (Finset.mul_sum ..).symm
    _ = ⟪x₁, y₁⟫_ℝ * ⟪x₂, y₂⟫_ℝ := by
        rw [sum_real_inner_mul_inner b, sum_real_inner_mul_inner b]

private theorem sub_swap_first_third {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (u v x y : V) : r ![v, x, u, y] - r ![u, x, v, y] = -r ![u, v, x, y] := by
  have hc := hr.cyclic_eq_zero u v x y
  have ha := hr.antisymm_first x u v y
  linarith

private theorem sub_swap_second_fourth {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (z w x y : V) : r ![z, x, w, y] - r ![z, y, w, x] = r ![z, w, x, y] := by
  have hc := hr.cyclic_eq_zero w z x y
  have ha1 := hr.antisymm_first x w z y
  have ha2 := hr.antisymm_first z w x y
  have hs := hr.swap_pairs z y w x
  linarith

/-- One cyclic piece of the first Bianchi identity for `reactionTensor`: for an algebraic curvature
tensor `r`, first Bianchi and antisymmetry in `(p, q)` collapse
`2 ∑_pq (r(v, b p, u, b q) - r(u, b p, v, b q)) r(z, b p, w, b q)` to
`-∑_pq r(u, v, b p, b q) r(z, w, b p, b q)`. -/
private theorem reactionTensor_cyclic_piece {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (u v z w : V) :
    (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![v, b p, u, b q] * r ![z, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![z, b p, w, b q] * r ![u, b p, v, b q]) = 0 := by
  have hpair :
      2 * (∑ p, ∑ q, r ![v, b p, u, b q] * r ![z, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![z, b p, w, b q] * r ![u, b p, v, b q]) =
      -2 * ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q] := by
    have hinner :
        (∑ p, ∑ q, r ![v, b p, u, b q] * r ![z, b p, w, b q]) -
          (∑ p, ∑ q, r ![z, b p, w, b q] * r ![u, b p, v, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q] := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun q _ ↦ by
        linear_combination r ![z, b p, w, b q] * sub_swap_first_third hr u v (b p) (b q)
    linarith
  have hswap :
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b q, w, b p] := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q _ ↦ by rw [hr.antisymm_last u v (b q) (b p), neg_mul]
  have hdouble :
      2 * (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) =
        ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
    have hsub :
        (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) -
          (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b q, w, b p]) =
        ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [← mul_sub, sub_swap_second_fourth hr]
    linarith
  linarith

end OrthonormalHelpers

section Reaction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The reaction tensor `Q(r)` of the curvature evolution `D_t R = Δ R + Q(R)`, expanded in the
standard orthonormal basis of `V`: `Q(r) = ∑_ijkl Q(r)_ijkl ⟪b i, ·⟫ ⟪b j, ·⟫ ⟪b k, ·⟫ ⟪b l, ·⟫`.
Its basis independence is `reactionTensor_apply_orthonormalBasis`. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionComponent (stdOrthonormalBasis ℝ V) r i j k l •
      coordFourTensor (stdOrthonormalBasis ℝ V) i j k l

/-- Unfolding expansion of `reactionTensor` in `stdOrthonormalBasis ℝ V`. -/
theorem reactionTensor_def (r : FourTensor V) :
    reactionTensor r =
      ∑ i, ∑ j, ∑ k, ∑ l,
        reactionComponent (stdOrthonormalBasis ℝ V) r i j k l •
          coordFourTensor (stdOrthonormalBasis ℝ V) i j k l :=
  (rfl)

/-- Unsymmetrized bilinear four-tensor whose diagonal `s = r` is definitionally
`reactionTensor r`. -/
private def reactionRaw (r s : FourTensor V) : FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionRawComponent (stdOrthonormalBasis ℝ V) r s i j k l •
      coordFourTensor (stdOrthonormalBasis ℝ V) i j k l

private theorem reactionRaw_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionRaw r s ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) := by
  set e := stdOrthonormalBasis ℝ V
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
      (∑ p, ∑ q, r ![e i, e j, e p, e q] * s ![e k, e l, e p, e q]) *
        (⟪e i, u⟫_ℝ * ⟪e j, v⟫_ℝ * ⟪e k, z⟫_ℝ * ⟪e l, w⟫_ℝ)) =
      ∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q] := by
    calc _ = ∑ p, ∑ q, slice34 r u v (e p) (e q) * slice34 s z w (e p) (e q) := by
          simp_rw [Finset.sum_mul]
          rw [sum_comm_four_two]
          exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦
            sum_bilin_12_34 e (slice12 r (e p) (e q)) (slice12 s (e p) (e q)) u v z w
      _ = ∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q] :=
          e.sum_sum_apply_mul_apply_eq b e b (slice34 r u v) (slice34 s z w)
  have h2 (z' w' : V) :
      (∑ i, ∑ j, ∑ k, ∑ l,
        (∑ p, ∑ q, r ![e i, e p, e k, e q] * s ![e j, e p, e l, e q]) *
          (⟪e i, u⟫_ℝ * ⟪e j, v⟫_ℝ * ⟪e k, z'⟫_ℝ * ⟪e l, w'⟫_ℝ)) =
        ∑ p, ∑ q, r ![u, b p, z', b q] * s ![v, b p, w', b q] := by
    calc _ = ∑ p, ∑ q, slice24 r u z' (e p) (e q) * slice24 s v w' (e p) (e q) := by
          simp_rw [Finset.sum_mul]
          rw [sum_comm_four_two]
          exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦
            sum_bilin_13_24 e (slice13 r (e p) (e q)) (slice13 s (e p) (e q)) u v z' w'
      _ = ∑ p, ∑ q, r ![u, b p, z', b q] * s ![v, b p, w', b q] :=
          e.sum_sum_apply_mul_apply_eq b e b (slice24 r u z') (slice24 s v w')
  have h3 : (∑ i, ∑ j, ∑ k, ∑ l,
      (∑ p, ∑ q, r ![e i, e p, e l, e q] * s ![e j, e p, e k, e q]) *
        (⟪e i, u⟫_ℝ * ⟪e j, v⟫_ℝ * ⟪e k, z⟫_ℝ * ⟪e l, w⟫_ℝ)) =
      ∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q] := by
    calc _ = ∑ i, ∑ j, ∑ l, ∑ k,
          (∑ p, ∑ q, r ![e i, e p, e l, e q] * s ![e j, e p, e k, e q]) *
            (⟪e i, u⟫_ℝ * ⟪e j, v⟫_ℝ * ⟪e l, w⟫_ℝ * ⟪e k, z⟫_ℝ) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
      _ = ∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q] := h2 w z
  simp only [reactionRaw, reactionRawComponent, sum_apply, smul_apply, coordFourTensor_apply,
    smul_eq_mul, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [mul_assoc (2 : ℝ), ← Finset.mul_sum]
  rw [h1, h2 z w, h3]

/-- **Basis independence of the reaction tensor**: in every orthonormal basis `b` of `V`, `Q(r)` is
the contraction
`Q(r)(u, v, z, w) = ∑_pq r(u, v, b p, b q) r(z, w, b p, b q) +
2 ∑_pq r(u, b p, z, b q) r(v, b p, w, b q) - 2 ∑_pq r(u, b p, w, b q) r(v, b p, z, b q)`. -/
theorem reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) :=
  reactionRaw_apply_orthonormalBasis b r r u v z w

/-- Evaluating `reactionTensor r` on four vectors of an orthonormal basis `b` recovers
`reactionComponent b r`. -/
@[simp]
theorem reactionTensor_apply_orthonormalBasis_vec {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (i j k l : ι) :
    reactionTensor r ![b i, b j, b k, b l] = reactionComponent b r i j k l :=
  reactionTensor_apply_orthonormalBasis b r (b i) (b j) (b k) (b l)

/-- In every orthonormal basis `b`, `reactionTensor r` expands as the sum of
`reactionComponent b r i j k l • coordFourTensor b i j k l`. -/
theorem reactionTensor_eq_sum_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) :
    reactionTensor r =
      ∑ i, ∑ j, ∑ k, ∑ l, reactionComponent b r i j k l • coordFourTensor b i j k l := by
  conv_lhs => rw [← sum_smul_coordFourTensor b (reactionTensor r)]
  simp only [reactionTensor_apply_orthonormalBasis_vec]

private theorem norm_reactionRaw_le (r s : FourTensor V) :
    ‖reactionRaw r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by
  let b := stdOrthonormalBasis ℝ V
  refine (reactionRaw r s).opNorm_le_bound (by positivity) fun m ↦ ?_
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, reactionRaw_apply_orthonormalBasis b, Fin.prod_univ_four]
  simp only [Real.norm_eq_abs, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  have hb1 : |∑ p, ∑ q, r ![m 0, m 1, b p, b q] * s ![m 2, m 3, b p, b q]| ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)) := by
    simpa [b] using abs_sum_mul_le_card_sq (by positivity)
      (fun p q ↦ (abs_apply_basis_two_le b r m p q).1)
      (fun p q ↦ (abs_apply_basis_two_le b s m p q).2.2.2.2.2) (le_of_eq (by ring))
  have hb2 : |∑ p, ∑ q, r ![m 0, b p, m 2, b q] * s ![m 1, b p, m 3, b q]| ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)) := by
    simpa [b] using abs_sum_mul_le_card_sq (by positivity)
      (fun p q ↦ (abs_apply_basis_two_le b r m p q).2.1)
      (fun p q ↦ (abs_apply_basis_two_le b s m p q).2.2.2.2.1) (le_of_eq (by ring))
  have hb3 : |∑ p, ∑ q, r ![m 0, b p, m 3, b q] * s ![m 1, b p, m 2, b q]| ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)) := by
    simpa [b] using abs_sum_mul_le_card_sq (by positivity)
      (fun p q ↦ (abs_apply_basis_two_le b r m p q).2.2.1)
      (fun p q ↦ (abs_apply_basis_two_le b s m p q).2.2.2.1) (le_of_eq (by ring))
  have htri (a c d : ℝ) : |a + 2 * c - 2 * d| ≤ |a| + 2 * |c| + 2 * |d| := by
    calc |a + 2 * c - 2 * d|
        ≤ |a + 2 * c| + |2 * d| := abs_sub _ _
      _ ≤ (|a| + |2 * c|) + |2 * d| := by gcongr; exact abs_add_le _ _
      _ = |a| + 2 * |c| + 2 * |d| := by
          simp only [abs_mul, abs_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2), add_assoc]
  exact (htri _ _ _).trans (by linarith)

/-- Unbundled symmetric bilinear form underlying `reactionBilinear`. -/
private def reactionBilinearₗ : FourTensor V →ₗ[ℝ] FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.mk₂ ℝ (fun r s ↦ (1 / 2 : ℝ) • (reactionRaw r s + reactionRaw s r))
    (fun r₁ r₂ s ↦ ext_vec fun u v z w ↦ by
      let b := stdOrthonormalBasis ℝ V
      simp only [smul_apply, add_apply, smul_eq_mul, reactionRaw_apply_orthonormalBasis b,
        add_mul, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c r s ↦ ext_vec fun u v z w ↦ by
      let b := stdOrthonormalBasis ℝ V
      simp only [smul_apply, add_apply, smul_eq_mul, reactionRaw_apply_orthonormalBasis b,
        mul_assoc, mul_left_comm _ c, ← Finset.mul_sum]
      ring)
    (fun r s₁ s₂ ↦ ext_vec fun u v z w ↦ by
      let b := stdOrthonormalBasis ℝ V
      simp only [smul_apply, add_apply, smul_eq_mul, reactionRaw_apply_orthonormalBasis b,
        add_mul, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c r s ↦ ext_vec fun u v z w ↦ by
      let b := stdOrthonormalBasis ℝ V
      simp only [smul_apply, add_apply, smul_eq_mul, reactionRaw_apply_orthonormalBasis b,
        mul_assoc, mul_left_comm _ c, ← Finset.mul_sum]
      ring)

private theorem norm_reactionBilinearₗ_le (r s : FourTensor V) :
    ‖reactionBilinearₗ r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by
  have hdef : reactionBilinearₗ r s = (1 / 2 : ℝ) • (reactionRaw r s + reactionRaw s r) := rfl
  rw [hdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hadd := (norm_add_le (reactionRaw r s) (reactionRaw s r)).trans
    (add_le_add (norm_reactionRaw_le r s) (norm_reactionRaw_le s r))
  linarith

variable (V) in
/-- The symmetric continuous bilinear polarization of `reactionTensor`, characterized by
`reactionBilinear V r s = reactionBilinear V s r` and `reactionBilinear V r r = reactionTensor r`.
-/
def reactionBilinear : FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V :=
  reactionBilinearₗ.mkContinuous₂ (5 * (Module.finrank ℝ V : ℝ) ^ 2) norm_reactionBilinearₗ_le

/-- Orthonormal-basis contraction formula for the symmetric bilinear polarization
`reactionBilinear`. -/
theorem reactionBilinear_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinear V r s ![u, v, z, w] =
      (1 / 2 : ℝ) * ((∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
        (∑ p, ∑ q, s ![u, v, b p, b q] * r ![z, w, b p, b q])) +
      ((∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) +
        (∑ p, ∑ q, s ![u, b p, z, b q] * r ![v, b p, w, b q])) -
      ((∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) +
        (∑ p, ∑ q, s ![u, b p, w, b q] * r ![v, b p, z, b q])) := by
  have hval : reactionBilinear V r s = (1 / 2 : ℝ) • (reactionRaw r s + reactionRaw s r) := rfl
  rw [hval]
  simp only [smul_apply, add_apply, smul_eq_mul, reactionRaw_apply_orthonormalBasis b]
  ring

/-- `reactionBilinear` is symmetric in its two four-tensor arguments. -/
theorem reactionBilinear_comm (r s : FourTensor V) :
    reactionBilinear V r s = reactionBilinear V s r :=
  ext_vec fun u v z w ↦ by
    rw [reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
      reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
    ring

/-- On the diagonal, `reactionBilinear V r r` recovers `reactionTensor r`. -/
@[simp]
theorem reactionBilinear_self (r : FourTensor V) :
    reactionBilinear V r r = reactionTensor r :=
  ext_vec fun u v z w ↦ by
    rw [reactionBilinear_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
      reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
    ring

/-- `reactionTensor` vanishes at `0`. -/
@[simp]
theorem reactionTensor_zero : reactionTensor (0 : FourTensor V) = 0 := by
  rw [← reactionBilinear_self]
  simp

/-- `reactionTensor` is even: `Q(-r) = Q(r)`. -/
@[simp]
theorem reactionTensor_neg (r : FourTensor V) : reactionTensor (-r) = reactionTensor r := by
  rw [← reactionBilinear_self, ← reactionBilinear_self r]
  simp

/-- **Homogeneity of degree two**: `Q(c • r) = c ^ 2 • Q(r)`. -/
theorem reactionTensor_smul (c : ℝ) (r : FourTensor V) :
    reactionTensor (c • r) = c ^ 2 • reactionTensor r := by
  rw [← reactionBilinear_self, map_smul, map_smul, smul_apply, smul_smul, ← sq,
    reactionBilinear_self]

/-- Quadratic binomial expansion of `reactionTensor (r + s)`. -/
theorem reactionTensor_add (r s : FourTensor V) :
    reactionTensor (r + s) =
      reactionTensor r + (2 : ℝ) • reactionBilinear V r s + reactionTensor s := by
  rw [← reactionBilinear_self, map_add, map_add, add_apply, add_apply,
    reactionBilinear_comm s r, reactionBilinear_self, reactionBilinear_self, two_smul]
  abel

/-- Quadratic binomial expansion of `reactionTensor (r - s)`. -/
theorem reactionTensor_sub (r s : FourTensor V) :
    reactionTensor (r - s) =
      reactionTensor r - (2 : ℝ) • reactionBilinear V r s + reactionTensor s := by
  rw [sub_eq_add_neg, reactionTensor_add, map_neg, reactionTensor_neg, sub_eq_add_neg, smul_neg]

/-- Difference factorization `Q(r) - Q(s) = B(r + s, r - s)` via the symmetric polarization. -/
theorem reactionTensor_sub_reactionTensor (r s : FourTensor V) :
    reactionTensor r - reactionTensor s = reactionBilinear V (r + s) (r - s) := by
  rw [map_add, add_apply, map_sub, map_sub, reactionBilinear_comm s r,
    reactionBilinear_self, reactionBilinear_self]
  abel

/-- Polarization identity recovering `reactionBilinear` from `reactionTensor`. -/
theorem reactionBilinear_eq_smul_sub (r s : FourTensor V) :
    reactionBilinear V r s =
      (1 / 2 : ℝ) • (reactionTensor (r + s) - reactionTensor r - reactionTensor s) := by
  rw [reactionTensor_add]
  ext m
  simp only [smul_apply, sub_apply, add_apply, smul_eq_mul]
  ring

/-- `reactionBilinear` is equivariant under linear isometric equivalences. -/
theorem reactionBilinear_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V)
    (r s : FourTensor V) :
    reactionBilinear W
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionBilinear V r s).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  ext_vec fun u v z w ↦ by
    let b := stdOrthonormalBasis ℝ W
    rw [reactionBilinear_apply_orthonormalBasis b, compContinuousLinearMap_apply_vec,
      reactionBilinear_apply_orthonormalBasis (b.map e)]
    simp only [compContinuousLinearMap_apply_vec, OrthonormalBasis.map_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

/-- **`O(n)`-equivariance of the reaction tensor**: pulling back `r` along a linear isometric
equivalence `e : W ≃ₗᵢ[ℝ] V` and applying `reactionTensor` agrees with pulling back
`reactionTensor r` along `e`. -/
theorem reactionTensor_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  rw [← reactionBilinear_self, ← reactionBilinear_self r,
    reactionBilinear_compContinuousLinearMap_linearIsometryEquiv]

/-- **Curvature symmetries of `reactionTensor`**: if `r` is an algebraic curvature tensor, then so
is `reactionTensor r`. -/
theorem IsAlgebraicCurvature.reactionTensor {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.reactionTensor r) := by
  let b := stdOrthonormalBasis ℝ V
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩
  · simp only [reactionTensor_apply_orthonormalBasis b]
    have ha : (∑ p, ∑ q, r ![v, u, b p, b q] * r ![z, w, b p, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp_rw [hr.antisymm_first v u, neg_mul, Finset.sum_neg_distrib]
    have hc (x y : V) : (∑ p, ∑ q, r ![v, b p, x, b q] * r ![u, b p, y, b q]) =
        ∑ p, ∑ q, r ![u, b p, y, b q] * r ![v, b p, x, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [ha, hc z w, hc w z]
    ring
  · simp only [reactionTensor_apply_orthonormalBasis b]
    have ha : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, z, b p, b q]) =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp_rw [hr.antisymm_first w z, mul_neg, Finset.sum_neg_distrib]
    rw [ha]
    ring
  · simp only [reactionTensor_apply_orthonormalBasis b]
    have ha : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
        ∑ p, ∑ q, r ![z, w, b p, b q] * r ![u, v, b p, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    have hc (x y : V) : (∑ p, ∑ q, r ![u, b p, x, b q] * r ![v, b p, y, b q]) =
        ∑ p, ∑ q, r ![x, b p, u, b q] * r ![y, b p, v, b q] := by
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ by
        rw [hr.swap_pairs u (b p) x (b q), hr.swap_pairs v (b p) y (b q)]
    have hcomm : (∑ p, ∑ q, r ![w, b p, u, b q] * r ![z, b p, v, b q]) =
        ∑ p, ∑ q, r ![z, b p, v, b q] * r ![w, b p, u, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [ha, hc z w, hc w z, hcomm]
  · simp only [reactionTensor_apply_orthonormalBasis b]
    linear_combination reactionTensor_cyclic_piece b hr u v z w +
      reactionTensor_cyclic_piece b hr v z u w +
      reactionTensor_cyclic_piece b hr z u v w

/-- **The reaction tensor of an algebraic curvature tensor is an algebraic curvature tensor**: `Q`
preserves the pair skew-symmetries, pair interchange, and the first Bianchi identity
(Hamilton's `Q(R) = 2 (R² + R#)` on the curvature-operator side). -/
theorem reactionTensor_mem (r : FourTensor V) (hr : r ∈ algebraicCurvatureSubmodule V) :
    reactionTensor r ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr
    (IsAlgebraicCurvature.reactionTensor (mem_algebraicCurvatureSubmodule.mp hr))

/-- The symmetric polarization `reactionBilinear` preserves `IsAlgebraicCurvature`. -/
theorem IsAlgebraicCurvature.reactionBilinear {r s : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hs : IsAlgebraicCurvature s) : IsAlgebraicCurvature (FourTensor.reactionBilinear V r s) := by
  let S := algebraicCurvatureSubmodule V
  have hr' : r ∈ S := mem_algebraicCurvatureSubmodule.mpr hr
  have hs' : s ∈ S := mem_algebraicCurvatureSubmodule.mpr hs
  rw [← mem_algebraicCurvatureSubmodule, reactionBilinear_eq_smul_sub]
  exact S.smul_mem _ <| S.sub_mem
    (S.sub_mem (reactionTensor_mem (r + s) (S.add_mem hr' hs')) (reactionTensor_mem r hr'))
    (reactionTensor_mem s hs')

/-- `reactionBilinear V` maps pairs in `algebraicCurvatureSubmodule V` into
`algebraicCurvatureSubmodule V`. -/
theorem reactionBilinear_mem {r s : FourTensor V} (hr : r ∈ algebraicCurvatureSubmodule V)
    (hs : s ∈ algebraicCurvatureSubmodule V) :
    reactionBilinear V r s ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr
    ((mem_algebraicCurvatureSubmodule.mp hr).reactionBilinear
      (mem_algebraicCurvatureSubmodule.mp hs))

/-- The quadratic reaction map restricted to the submodule of algebraic curvature tensors. -/
def algebraicCurvatureReaction (r : algebraicCurvatureSubmodule V) :
    algebraicCurvatureSubmodule V :=
  ⟨reactionTensor r.1, reactionTensor_mem r.1 r.2⟩

/-- Unfolding equation for `algebraicCurvatureReaction` as a subtype constructor. -/
theorem algebraicCurvatureReaction_def (r : algebraicCurvatureSubmodule V) :
    algebraicCurvatureReaction r = ⟨reactionTensor r.1, reactionTensor_mem r.1 r.2⟩ :=
  (rfl)

/-- Coercing `algebraicCurvatureReaction r` to `FourTensor V` gives `reactionTensor r.1`. -/
@[simp]
theorem coe_algebraicCurvatureReaction (r : algebraicCurvatureSubmodule V) :
    (algebraicCurvatureReaction r : FourTensor V) = reactionTensor r.1 :=
  (rfl)

/-- `algebraicCurvatureReaction` vanishes at `0`. -/
@[simp]
theorem algebraicCurvatureReaction_zero :
    algebraicCurvatureReaction (0 : algebraicCurvatureSubmodule V) = 0 :=
  Subtype.ext reactionTensor_zero

/-- `algebraicCurvatureReaction` is even. -/
@[simp]
theorem algebraicCurvatureReaction_neg (r : algebraicCurvatureSubmodule V) :
    algebraicCurvatureReaction (-r) = algebraicCurvatureReaction r :=
  Subtype.ext (reactionTensor_neg r.1)

/-- `algebraicCurvatureReaction` is homogeneous of degree two. -/
theorem algebraicCurvatureReaction_smul (c : ℝ) (r : algebraicCurvatureSubmodule V) :
    algebraicCurvatureReaction (c • r) = c ^ 2 • algebraicCurvatureReaction r :=
  Subtype.ext (reactionTensor_smul c r.1)

section Regularity

/-- Explicit operator-norm bound on `reactionBilinear V r s`:
`‖reactionBilinear V r s‖ ≤ 5 * (finrank ℝ V)² * ‖r‖ * ‖s‖`. -/
theorem norm_reactionBilinear_apply_le (r s : FourTensor V) :
    ‖reactionBilinear V r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ :=
  norm_reactionBilinearₗ_le r s

/-- Quadratic operator-norm bound on `reactionTensor`:
`‖reactionTensor r‖ ≤ 5 * (finrank ℝ V)² * ‖r‖²`. -/
theorem norm_reactionTensor_le (r : FourTensor V) :
    ‖reactionTensor r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ ^ 2 := by
  rw [← reactionBilinear_self, sq ‖r‖, ← mul_assoc]
  exact norm_reactionBilinear_apply_le r r

/-- Explicit dimension-dependent difference bound for `reactionTensor`:
`‖reactionTensor r - reactionTensor s‖ ≤ 5 * (finrank ℝ V)² * (‖r‖ + ‖s‖) * ‖r - s‖`. -/
theorem norm_reactionTensor_sub_le (r s : FourTensor V) :
    ‖reactionTensor r - reactionTensor s‖ ≤
      5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖s‖) * ‖r - s‖ := by
  rw [reactionTensor_sub_reactionTensor]
  calc ‖reactionBilinear V (r + s) (r - s)‖
      ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r + s‖ * ‖r - s‖ :=
        norm_reactionBilinear_apply_le (r + s) (r - s)
    _ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖s‖) * ‖r - s‖ := by
        gcongr
        exact norm_add_le r s

/-- Uncurried `reactionBilinear V` is a bounded bilinear map on `FourTensor V × FourTensor V`. -/
theorem isBoundedBilinearMap_reactionBilinear :
    IsBoundedBilinearMap ℝ (fun p : FourTensor V × FourTensor V ↦ reactionBilinear V p.1 p.2) where
  add_left r₁ r₂ s := by simp
  smul_left c r s := by simp
  add_right r s₁ s₂ := by simp
  smul_right c r s := by simp
  bound := ⟨5 * (Module.finrank ℝ V : ℝ) ^ 2 + 1, by positivity, fun r s ↦
    (norm_reactionBilinear_apply_le r s).trans (by
      have : 0 ≤ ‖r‖ * ‖s‖ := by positivity
      nlinarith)⟩

/-- `reactionTensor` is `C^n` (in particular `C^∞`) on `FourTensor V`. -/
@[fun_prop]
theorem contDiff_reactionTensor {n : WithTop ℕ∞} : ContDiff ℝ n (reactionTensor (V := V)) := by
  have h : (reactionTensor (V := V)) =
      (fun p : FourTensor V × FourTensor V ↦ reactionBilinear V p.1 p.2) ∘ fun r ↦ (r, r) :=
    funext fun r ↦ (reactionBilinear_self r).symm
  rw [h]
  exact (isBoundedBilinearMap_reactionBilinear (V := V)).contDiff.comp (by fun_prop)

/-- `reactionTensor` is continuous on `FourTensor V`. -/
@[fun_prop]
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := ⊤)).continuous

/-- Strict Fréchet derivative of `reactionTensor` at `r`: `(2 : ℝ) • reactionBilinear V r`. -/
theorem hasStrictFDerivAt_reactionTensor (r : FourTensor V) :
    HasStrictFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r := by
  have h : (reactionTensor (V := V)) =
      (fun p : FourTensor V × FourTensor V ↦ reactionBilinear V p.1 p.2) ∘ fun s ↦ (s, s) :=
    funext fun s ↦ (reactionBilinear_self s).symm
  rw [h]
  let idL := ContinuousLinearMap.id ℝ (FourTensor V)
  have hd : HasStrictFDerivAt (fun s : FourTensor V ↦ (s, s)) (idL.prod idL) r :=
    (hasStrictFDerivAt_id r).prodMk (hasStrictFDerivAt_id r)
  refine ((isBoundedBilinearMap_reactionBilinear.hasStrictFDerivAt (r, r)).comp r hd).congr_fderiv
    ?_
  ext s m
  simp [idL, IsBoundedBilinearMap.deriv, reactionBilinear_comm s r, two_smul]

/-- The Fréchet derivative of `reactionTensor` at `r` is `(2 : ℝ) • reactionBilinear V r`. -/
theorem hasFDerivAt_reactionTensor (r : FourTensor V) :
    HasFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r :=
  (hasStrictFDerivAt_reactionTensor r).hasFDerivAt

/-- **Bounded-set Lipschitz estimate**: on the closed ball `Metric.closedBall 0 R`, `reactionTensor`
is Lipschitz with constant `10 * R * (finrank ℝ V)²`. -/
theorem lipschitzOnWith_reactionTensor_closedBall (R : ℝ≥0) :
    LipschitzOnWith (10 * R * (Module.finrank ℝ V : ℝ≥0) ^ 2) (reactionTensor (V := V))
      (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun r hr s hs ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_zero_right] at hr hs
  refine (norm_reactionTensor_sub_le r s).trans ?_
  push_cast
  have hsum : ‖r‖ + ‖s‖ ≤ 2 * (R : ℝ) := by linarith
  calc 5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖s‖) * ‖r - s‖
      ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * (2 * (R : ℝ)) * ‖r - s‖ := by gcongr
    _ = 10 * (R : ℝ) * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r - s‖ := by ring

/-- `reactionTensor` is locally Lipschitz on `FourTensor V`. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 1)).locallyLipschitz

/-- `algebraicCurvatureReaction` is `C^n` (in particular `C^∞`) on `algebraicCurvatureSubmodule V`.
-/
@[fun_prop]
theorem contDiff_algebraicCurvatureReaction {n : WithTop ℕ∞} :
    ContDiff ℝ n (algebraicCurvatureReaction (V := V)) := by
  obtain ⟨T, hT⟩ := (algebraicCurvatureSubmodule V).exists_isCompl
  have htop := Submodule.IsCompl.isTopCompl_of_isClosed hT isClosed_algebraicCurvatureSubmodule
    (Submodule.isClosed_of_finiteDimensional T)
  let p := (algebraicCurvatureSubmodule V).projectionOntoL T htop
  have heq : (algebraicCurvatureReaction (V := V)) =
      fun r ↦ p (reactionTensor ((algebraicCurvatureSubmodule V).subtypeL r)) := by
    ext r : 1
    exact (Submodule.projectionOnto_apply_left hT (algebraicCurvatureReaction r)).symm
  rw [heq]
  fun_prop

/-- `algebraicCurvatureReaction` is continuous on `algebraicCurvatureSubmodule V`. -/
@[fun_prop]
theorem continuous_algebraicCurvatureReaction :
    Continuous (algebraicCurvatureReaction (V := V)) :=
  (contDiff_algebraicCurvatureReaction (n := ⊤)).continuous

/-- On `Metric.closedBall 0 R` in `algebraicCurvatureSubmodule V`, `algebraicCurvatureReaction` is
Lipschitz with constant `10 * R * (finrank ℝ V)²`. -/
theorem lipschitzOnWith_algebraicCurvatureReaction_closedBall (R : ℝ≥0) :
    LipschitzOnWith (10 * R * (Module.finrank ℝ V : ℝ≥0) ^ 2) (algebraicCurvatureReaction (V := V))
      (Metric.closedBall 0 R) :=
  LipschitzOnWith.of_dist_le_mul fun r hr s hs ↦
    (lipschitzOnWith_reactionTensor_closedBall R).dist_le_mul r.1 hr s.1 hs

/-- `algebraicCurvatureReaction` is locally Lipschitz on `algebraicCurvatureSubmodule V`. -/
theorem locallyLipschitz_algebraicCurvatureReaction :
    LocallyLipschitz (algebraicCurvatureReaction (V := V)) :=
  (contDiff_algebraicCurvatureReaction (n := 1)).locallyLipschitz

end Regularity

section ModelTensors

private theorem sum_constantCurvature_interlaced {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (u v z w : V) :
    (∑ p, ∑ q, constantCurvature V ![u, b p, z, b q] * constantCurvature V ![v, b p, w, b q]) =
      ((Fintype.card ι : ℝ) - 2) * (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ) + ⟪u, v⟫_ℝ * ⟪z, w⟫_ℝ := by
  have hdiag : (∑ p, ∑ q, ⟪b p, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) = (Fintype.card ι : ℝ) := by
    calc _ = ∑ p, ⟪b p, b p⟫_ℝ :=
          Finset.sum_congr rfl fun p _ ↦ sum_real_inner_mul_inner b (b p) (b p)
      _ = (Fintype.card ι : ℝ) := by simp [b.orthonormal.1]
  have hmix (x y : V) : (∑ p, ∑ q, ⟪b p, b q⟫_ℝ * ⟪x, b q⟫_ℝ * ⟪b p, y⟫_ℝ) = ⟪x, y⟫_ℝ := by
    calc _ = ∑ p, (∑ q, ⟪x, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) * ⟪b p, y⟫_ℝ :=
          Finset.sum_congr rfl fun p _ ↦ by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun q _ ↦ by ring
      _ = ∑ p, ⟪x, b p⟫_ℝ * ⟪b p, y⟫_ℝ := by simp_rw [sum_real_inner_mul_inner b x]
      _ = ⟪x, y⟫_ℝ := b.sum_inner_mul_inner x y
  have hexp :
      (∑ p, ∑ q, constantCurvature V ![u, b p, z, b q] * constantCurvature V ![v, b p, w, b q]) =
      ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ * (∑ p, ∑ q, ⟪b p, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) -
      ⟪u, z⟫_ℝ * (∑ p, ∑ q, ⟪b p, b q⟫_ℝ * ⟪v, b q⟫_ℝ * ⟪b p, w⟫_ℝ) -
      ⟪v, w⟫_ℝ * (∑ p, ∑ q, ⟪b p, b q⟫_ℝ * ⟪u, b q⟫_ℝ * ⟪b p, z⟫_ℝ) +
      (∑ p, ∑ q, ⟪z, b p⟫_ℝ * ⟪w, b p⟫_ℝ * (⟪u, b q⟫_ℝ * ⟪v, b q⟫_ℝ)) := by
    simp_rw [constantCurvature_apply, real_inner_comm (b _) z, real_inner_comm (b _) w,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [real_inner_comm z (b p), real_inner_comm w (b p)]
      ring
  rw [hexp, hdiag, hmix v w, hmix u z, sum_real_inner_pair b]
  ring

/-- **Constant-curvature reaction**: on `constantCurvature V`, `reactionTensor` acts as scalar
multiplication by `2 * (finrank ℝ V - 1)` (in every dimension, including `finrank = 0, 1` where
`constantCurvature V = 0`). -/
@[simp]
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  let b := stdOrthonormalBasis ℝ V
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul, constantCurvature_apply]
  have h1 : (∑ p, ∑ q, constantCurvature V ![u, v, b p, b q] *
      constantCurvature V ![z, w, b p, b q]) =
        2 * (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ) := by
    have hexp :
        (∑ p, ∑ q, constantCurvature V ![u, v, b p, b q] *
          constantCurvature V ![z, w, b p, b q]) =
        (∑ p, ∑ q, ⟪u, b p⟫_ℝ * ⟪z, b p⟫_ℝ * (⟪v, b q⟫_ℝ * ⟪w, b q⟫_ℝ)) -
        (∑ p, ∑ q, ⟪u, b p⟫_ℝ * ⟪w, b p⟫_ℝ * (⟪v, b q⟫_ℝ * ⟪z, b q⟫_ℝ)) -
        (∑ p, ∑ q, ⟪v, b p⟫_ℝ * ⟪z, b p⟫_ℝ * (⟪u, b q⟫_ℝ * ⟪w, b q⟫_ℝ)) +
        (∑ p, ∑ q, ⟪v, b p⟫_ℝ * ⟪w, b p⟫_ℝ * (⟪u, b q⟫_ℝ * ⟪z, b q⟫_ℝ)) := by
      simp_rw [constantCurvature_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring
    rw [hexp, sum_real_inner_pair b, sum_real_inner_pair b, sum_real_inner_pair b,
      sum_real_inner_pair b]
    ring
  have h2 (z' w' : V) :
      (∑ p, ∑ q, constantCurvature V ![u, b p, z', b q] *
        constantCurvature V ![v, b p, w', b q]) =
      ((Module.finrank ℝ V : ℝ) - 2) * (⟪u, z'⟫_ℝ * ⟪v, w'⟫_ℝ) + ⟪u, v⟫_ℝ * ⟪z', w'⟫_ℝ := by
    simpa [b] using sum_constantCurvature_interlaced b u v z' w'
  rw [h1, h2 z w, h2 w z, real_inner_comm w z]
  ring

/-- Along the constant-sectional-curvature line `κ • constantCurvature V`,
`Q(κ I) = 2 (finrank ℝ V - 1) κ² I`. -/
theorem reactionTensor_smul_constantCurvature (κ : ℝ) :
    reactionTensor (κ • constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1) * κ ^ 2) • constantCurvature V := by
  rw [reactionTensor_smul, reactionTensor_constantCurvature, smul_smul]
  congr 1
  ring

/-- Ricci contraction of the rank-one plane curvature tensor `planeCurvature x y`. -/
theorem ricci_planeCurvature (x y u v : V) :
    ricci (planeCurvature x y) u v =
      ‖y‖ ^ 2 * ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ -
        ⟪x, y⟫_ℝ * (⟪x, u⟫_ℝ * ⟪y, v⟫_ℝ + ⟪y, u⟫_ℝ * ⟪x, v⟫_ℝ) +
        ‖x‖ ^ 2 * ⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ V
  rw [ricci_apply_orthonormalBasis b]
  have hnorm (z : V) : ∑ i, ⟪z, b i⟫_ℝ * ⟪z, b i⟫_ℝ = ‖z‖ ^ 2 := by
    rw [sum_real_inner_mul_inner b, real_inner_self_eq_norm_sq]
  have hexp :
      (∑ i, planeCurvature x y ![b i, u, b i, v]) =
        ⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ * (∑ i, ⟪x, b i⟫_ℝ * ⟪x, b i⟫_ℝ) -
        (⟪x, u⟫_ℝ * ⟪y, v⟫_ℝ + ⟪y, u⟫_ℝ * ⟪x, v⟫_ℝ) * (∑ i, ⟪x, b i⟫_ℝ * ⟪y, b i⟫_ℝ) +
        ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * (∑ i, ⟪y, b i⟫_ℝ * ⟪y, b i⟫_ℝ) := by
    simp_rw [planeCurvature_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hexp, hnorm x, hnorm y, sum_real_inner_mul_inner b x y]
  ring

/-- For an orthonormal pair `(x, y)`, `ricci (planeCurvature x y)` is the orthogonal projection
form `⟪x, u⟫ ⟪x, v⟫ + ⟪y, u⟫ ⟪y, v⟫` onto `span {x, y}`. -/
theorem _root_.Orthonormal.ricci_planeCurvature {x y : V} (h : Orthonormal ℝ ![x, y]) (u v : V) :
    ricci (planeCurvature x y) u v = ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ := by
  have hx : ‖x‖ = 1 := h.1 0
  have hy : ‖y‖ = 1 := h.1 1
  have hxy : ⟪x, y⟫_ℝ = 0 := h.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [FourTensor.ricci_planeCurvature, hx, hy, hxy]
  ring

/-- Scalar contraction of `planeCurvature x y`: twice the Gram determinant `‖x‖² ‖y‖² - ⟪x, y⟫²`. -/
theorem scalar_planeCurvature (x y : V) :
    scalar (planeCurvature x y) = 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫_ℝ ^ 2) := by
  let b := stdOrthonormalBasis ℝ V
  rw [scalar_apply, bilinFormTrace_eq_sum _ b]
  have hnorm (z : V) : ∑ i, ⟪z, b i⟫_ℝ * ⟪z, b i⟫_ℝ = ‖z‖ ^ 2 := by
    rw [sum_real_inner_mul_inner b, real_inner_self_eq_norm_sq]
  have hexp :
      (∑ i, ricci (planeCurvature x y) (b i) (b i)) =
        ‖y‖ ^ 2 * (∑ i, ⟪x, b i⟫_ℝ * ⟪x, b i⟫_ℝ) -
        2 * ⟪x, y⟫_ℝ * (∑ i, ⟪x, b i⟫_ℝ * ⟪y, b i⟫_ℝ) +
        ‖x‖ ^ 2 * (∑ i, ⟪y, b i⟫_ℝ * ⟪y, b i⟫_ℝ) := by
    simp_rw [ricci_planeCurvature, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hexp, hnorm x, hnorm y, sum_real_inner_mul_inner b x y]
  ring

/-- For an orthonormal pair `(x, y)`, `planeCurvature x y` has scalar curvature `2`. -/
theorem _root_.Orthonormal.scalar_planeCurvature {x y : V} (h : Orthonormal ℝ ![x, y]) :
    scalar (planeCurvature x y) = 2 := by
  have hx : ‖x‖ = 1 := h.1 0
  have hy : ‖y‖ = 1 := h.1 1
  have hxy : ⟪x, y⟫_ℝ = 0 := h.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [FourTensor.scalar_planeCurvature, hx, hy, hxy]
  norm_num

/-- **Rank-one plane reaction**: on `planeCurvature x y`, the second and third contractions of
`reactionTensor` are equal (`R# = 0` for a decomposable bivector) and the first contraction scales
by `2 * (‖x‖² ‖y‖² - ⟪x, y⟫²)`. -/
theorem reactionTensor_planeCurvature (x y : V) :
    reactionTensor (planeCurvature x y) =
      (2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫_ℝ ^ 2)) • planeCurvature x y := by
  let b := stdOrthonormalBasis ℝ V
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul]
  let α : V → V → ℝ := fun a c ↦ ⟪x, a⟫_ℝ * ⟪y, c⟫_ℝ - ⟪x, c⟫_ℝ * ⟪y, a⟫_ℝ
  have hcancel :
      (∑ p, ∑ q, planeCurvature x y ![u, b p, z, b q] * planeCurvature x y ![v, b p, w, b q]) =
        ∑ p, ∑ q, planeCurvature x y ![u, b p, w, b q] * planeCurvature x y ![v, b p, z, b q] :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      simp only [planeCurvature_apply]
      ring
  have hnorm_sq : (∑ p, ∑ q, α (b p) (b q) * α (b p) (b q)) =
      2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫_ℝ ^ 2) := by
    have hexp : (∑ p, ∑ q, α (b p) (b q) * α (b p) (b q)) =
        (∑ p, ∑ q, ⟪x, b p⟫_ℝ * ⟪x, b p⟫_ℝ * (⟪y, b q⟫_ℝ * ⟪y, b q⟫_ℝ)) -
        2 * (∑ p, ∑ q, ⟪x, b p⟫_ℝ * ⟪y, b p⟫_ℝ * (⟪x, b q⟫_ℝ * ⟪y, b q⟫_ℝ)) +
        (∑ p, ∑ q, ⟪y, b p⟫_ℝ * ⟪y, b p⟫_ℝ * (⟪x, b q⟫_ℝ * ⟪x, b q⟫_ℝ)) := by
      simp_rw [α, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring
    rw [hexp, sum_real_inner_pair b, sum_real_inner_pair b, sum_real_inner_pair b,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have h1 : (∑ p, ∑ q, planeCurvature x y ![u, v, b p, b q] *
      planeCurvature x y ![z, w, b p, b q]) =
      2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫_ℝ ^ 2) * planeCurvature x y ![u, v, z, w] := by
    calc _ = (∑ p, ∑ q, α (b p) (b q) * α (b p) (b q)) * (α u v * α z w) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ ↦ by simp only [planeCurvature_apply, α]; ring
      _ = 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫_ℝ ^ 2) * planeCurvature x y ![u, v, z, w] := by
          rw [hnorm_sq, planeCurvature_apply]
  rw [hcancel, h1]
  ring

/-- For an orthonormal pair `(x, y)` (the unit `S² × ℝⁿ⁻²` curvature model),
`Q(planeCurvature x y) = 2 • planeCurvature x y`. -/
theorem _root_.Orthonormal.reactionTensor_planeCurvature {x y : V} (h : Orthonormal ℝ ![x, y]) :
    reactionTensor (planeCurvature x y) = (2 : ℝ) • planeCurvature x y := by
  have hx : ‖x‖ = 1 := h.1 0
  have hy : ‖y‖ = 1 := h.1 1
  have hxy : ⟪x, y⟫_ℝ = 0 := h.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [FourTensor.reactionTensor_planeCurvature, hx, hy, hxy]
  congr 1
  norm_num

end ModelTensors

end Reaction

end TauCeti.FourTensor
