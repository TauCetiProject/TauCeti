/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# The curvature four-tensor of a connection at a point

For a connection `∇` on the tangent bundle of a manifold with a fibre metric, the curvature
four-tensor at `x` is the continuous four-linear form on `T_x M`

`r(u, v, z, w) = ⟪R(u, v)w, z⟫`,

an element of `TauCeti.FourTensor (T_x M)`. It is the metric-lowered Riemann tensor
`CovariantDerivative.riemannCurvatureTensor` with its last two arguments interchanged, so that
`r(u, v, u, v)` is the numerator of the sectional curvature of the plane spanned by `u, v`
and is positive on the round sphere.

For a metric-compatible torsion-free connection, in particular the Levi-Civita connection of the
fibre metric, `r` lies in `TauCeti.FourTensor.algebraicCurvatureSubmodule (T_x M)`. This places
the curvature of a Riemannian manifold at each point in the fixed space of algebraic curvature
tensors, where curvature conditions are stated as conditions on a finite-dimensional vector
space. Its Ricci and scalar contractions `TauCeti.FourTensor.ricci` and
`TauCeti.FourTensor.scalar` are the Ricci tensor and the scalar curvature of the connection, its
values on pairs `(u, v, u, v)` are sectional curvature times the Gram determinant, and its values
on pure bivectors are those of the curvature operator
`CovariantDerivative.curvatureEndomorphism` on the exterior square. A connection whose curvature
has the constant-curvature form `R(w, u)v = κ (⟪u, v⟫ w - ⟪w, v⟫ u)` at `x` has curvature
four-tensor `κ` times `TauCeti.FourTensor.constantCurvature`. Evaluated on four `C^n` vector
fields, the curvature four-tensor is a `C^n` function.

## Main definitions

* `CovariantDerivative.curvatureFourTensor`: the curvature four-tensor at a point.

## Main statements

* `CovariantDerivative.IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor`: for a
  metric-compatible torsion-free connection the curvature four-tensor is an algebraic curvature
  tensor.
* `CovariantDerivative.curvatureFourTensor_leviCivitaConnection_mem_algebraicCurvatureSubmodule`:
  the Levi-Civita connection has curvature four-tensor in the submodule of algebraic curvature
  tensors at every point.
* `CovariantDerivative.ricci_curvatureFourTensor` and
  `CovariantDerivative.scalar_curvatureFourTensor`: the contractions are the Ricci tensor and the
  scalar curvature.
* `CovariantDerivative.curvatureFourTensor_apply_eq_sectionalCurvature_mul`: on a linearly
  independent pair, `r(u, v, u, v)` is sectional curvature times the Gram determinant.
* `CovariantDerivative.inner_curvatureEndomorphism_ιMulti_eq_curvatureFourTensor`: the curvature
  operator on pure bivectors.
* `CovariantDerivative.curvatureFourTensor_eq_smul_constantCurvature`: constant curvature.
* `CovariantDerivative.contMDiff_curvatureFourTensor_apply`: smoothness on smooth vector fields.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8.
* S. Brendle and R. Schoen, *Manifolds with 1/4-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), §2, for the convention `r(u, v, z, w) = ⟪R(u, v)w, z⟫`.
-/

public section

open Bundle TauCeti
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The curvature four-tensor of `cov` at `x`, `r(u, v, z, w) = ⟪R(u, v)w, z⟫`: the
metric-lowered Riemann tensor `riemannCurvatureTensor` with its last two arguments interchanged,
as a continuous four-linear form on the tangent space. -/
def curvatureFourTensor (x : M) : FourTensor (TangentSpace I x) :=
  FourTensor.ofLinearMap₄ ((cov.riemannCurvatureTensor x).compr₂ LinearMap.lflip.toLinearMap)

/-- Evaluation of the curvature four-tensor: `r(u, v, z, w) = ⟪R(u, v)w, z⟫`. -/
@[simp]
theorem curvatureFourTensor_apply (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = ⟪curvature x u v w, z⟫_ℝ := by
  simp [curvatureFourTensor, FourTensor.ofLinearMap₄_apply]

/-- The curvature four-tensor is the metric-lowered Riemann tensor with its last two arguments
interchanged. -/
theorem curvatureFourTensor_apply_eq_riemannCurvatureTensor (x : M)
    (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = cov.riemannCurvatureTensor x u v w z := by
  rw [curvatureFourTensor_apply, riemannCurvatureTensor_apply]

/-- In an orthonormal basis `(eᵢ)`, the Ricci contraction of the curvature four-tensor is the
Ricci tensor of the connection: `∑ᵢ ⟪R(eᵢ, u)v, eᵢ⟫ = Ric(u, v)`. No metric compatibility or
torsion condition is needed. -/
@[simp]
theorem ricci_curvatureFourTensor (x : M) :
    FourTensor.ricci (cov.curvatureFourTensor x) = cov.ricciTensor x := by
  ext u v
  rw [FourTensor.ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ (TangentSpace I x)),
    cov.ricciTensor_eq_sum_inner x (stdOrthonormalBasis ℝ (TangentSpace I x))]
  simp only [curvatureFourTensor_apply, real_inner_comm]

/-- The scalar contraction of the curvature four-tensor is the scalar curvature of the
connection. -/
@[simp]
theorem scalar_curvatureFourTensor (x : M) :
    FourTensor.scalar (cov.curvatureFourTensor x) = cov.scalarCurvature x := by
  rw [FourTensor.scalar_apply, ricci_curvatureFourTensor, scalarCurvature_apply]

/-- If the curvature of `cov` at `x` has the constant-curvature form
`R(w, u)v = κ (⟪u, v⟫ w - ⟪w, v⟫ u)`, its curvature four-tensor is `κ` times the
constant-curvature tensor. -/
theorem curvatureFourTensor_eq_smul_constantCurvature (x : M) {κ : ℝ}
    (h : ∀ w u v : TangentSpace I x, curvature x w u v = κ • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u)) :
    cov.curvatureFourTensor x = κ • FourTensor.constantCurvature (TangentSpace I x) := by
  refine FourTensor.ext_vec fun u v z w ↦ ?_
  rw [smul_apply, curvatureFourTensor_apply, smul_eq_mul]
  exact FourTensor.inner_eq_mul_constantCurvature h _ _ _ _

section MetricCompatible

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

variable {cov} in
/-- The curvature four-tensor of a metric-compatible torsion-free connection is an algebraic
curvature tensor: it is antisymmetric in each pair of arguments, symmetric under interchanging the
pairs, and satisfies the first Bianchi identity. -/
theorem IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor
    (hcov : IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) : (cov.curvatureFourTensor x).IsAlgebraicCurvature := by
  have h₁ := cov.riemannCurvatureTensor_antisymm_first x
  have h₂ := IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x
  have h₃ := IsMetricCompatible.riemannCurvatureTensor_swap_pairs cov hcov ht x
  have h₄ := cov.riemannCurvatureTensor_cyclic_eq_zero ht x
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [curvatureFourTensor_apply_eq_riemannCurvatureTensor]
  · exact h₁ u v w z
  · exact h₂ u v w z
  · rw [h₃, h₁, h₂, neg_neg]
  · -- The Bianchi identity of the four-tensor is that of the Riemann tensor with its last two
    -- arguments interchanged.
    linear_combination h₂ u v w z + h₂ v z w u + h₂ z u w v - h₄ u v z w

variable (hcov : IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)

/-- Sectional curvature is the quotient of `r(u, v, u, v)` by the Gram determinant of `u, v`.
This holds on all pairs, both sides taking the junk value `0` on dependent pairs. -/
theorem sectionalCurvature_eq_curvatureFourTensor_div (x : M) (u v : TangentSpace I x) :
    cov.sectionalCurvature hcov x u v =
      cov.curvatureFourTensor x ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det := by
  rw [sectionalCurvature_apply, curvatureFourTensor_apply]

/-- On a linearly independent pair `u, v`, `r(u, v, u, v)` is the sectional curvature of the
plane they span times the Gram determinant of `u, v`. -/
theorem curvatureFourTensor_apply_eq_sectionalCurvature_mul (x : M) {u v : TangentSpace I x}
    (huv : LinearIndependent ℝ ![u, v]) :
    cov.curvatureFourTensor x ![u, v, u, v] =
      cov.sectionalCurvature hcov x u v * (Matrix.gram ℝ ![u, v]).det := by
  rw [sectionalCurvature_eq_curvatureFourTensor_div,
    div_mul_cancel₀ _ (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr huv)]

/-- The curvature operator on the exterior square pairs pure bivectors through the curvature
four-tensor: `⟪Rop(u₀ ∧ u₁), v₀ ∧ v₁⟫ = r(u₀, u₁, v₀, v₁)`. -/
theorem inner_curvatureEndomorphism_ιMulti_eq_curvatureFourTensor (x : M)
    (u v : Fin 2 → TangentSpace I x) :
    ⟪cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 u),
      exteriorPower.ιMulti ℝ 2 v⟫_ℝ = cov.curvatureFourTensor x ![u 0, u 1, v 0, v 1] := by
  rw [inner_curvatureEndomorphism_ιMulti, curvatureFourTensor_apply]

end MetricCompatible

/-- Evaluated on four `C^n` vector fields, `n ≤ ∞`, the curvature four-tensor is a `C^n` function
on the manifold. -/
theorem contMDiff_curvatureFourTensor_apply {n : ℕ∞ω} (hn : n ≤ ∞)
    [IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _)]
    {X Y Z W : Π x : M, TangentSpace I x} (hX : CMDiff n (T% X)) (hY : CMDiff n (T% Y))
    (hZ : CMDiff n (T% Z)) (hW : CMDiff n (T% W)) :
    CMDiff n fun x ↦ cov.curvatureFourTensor x ![X x, Y x, Z x, W x] := by
  simp only [curvatureFourTensor_apply]
  -- The bundle argument of `ContMDiff.inner_bundle` is not inferred through `TangentSpace`.
  exact ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id)
    (cov.contMDiff_curvatureTensor (f := id) hn hX hY hW) hZ

/-- The curvature four-tensor of the Levi-Civita connection of the fibre metric is an algebraic
curvature tensor at every point. -/
theorem curvatureFourTensor_leviCivitaConnection_mem_algebraicCurvatureSubmodule
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] (x : M) :
    (leviCivitaConnection I M).curvatureFourTensor x ∈
      FourTensor.algebraicCurvatureSubmodule (TangentSpace I x) :=
  FourTensor.mem_algebraicCurvatureSubmodule.mpr <|
    (isMetricCompatible_leviCivitaConnection I).isAlgebraicCurvature_curvatureFourTensor
      (torsion_leviCivitaConnection_eq_zero I) x

end CovariantDerivative
