/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Curvature of a metric-compatible connection

The curvature endomorphisms of a metric-compatible connection are skew-adjoint:
`⟪R(X,Y)σ, τ⟫ = -⟪σ, R(X,Y)τ⟫`. The first theorem applies to `C^n` fields and
`C^(n + 1)` sections for `1 ≤ n`, under the corresponding finite regularity hypotheses;
the second specializes it to the smooth pointwise curvature tensor on arbitrary fibre vectors.

Under these hypotheses this is antisymmetry in the last two arguments of the
metric-lowered Riemann tensor. Together with antisymmetry in the first two arguments,
it makes the sectional-curvature numerator transform by the square of the determinant
under a change of basis of a tangent plane. No torsion-free hypothesis is required:
the result holds for any metric-compatible connection on a finite-rank real bundle satisfying
the stated manifold, bundle, metric, and base-model assumptions.

The metric and curvature conventions are those of J. M. Lee, *Introduction to Riemannian
Manifolds*, 2nd ed., Springer GTM 176 (2018), equation (5.1) and Chapter 7, pp. 196–198:
`R(X,Y)σ = ∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X,Y] σ`.
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {cov : CovariantDerivative I F V}

/-- A `C^n` metric-compatible connection has skew-adjoint curvature on `C^n` fields and
`C^(n + 1)` sections, for `1 ≤ n`. The base model may be infinite-dimensional, provided it is
complete. -/
theorem IsMetricCompatible.inner_curvatureOperator_eq_neg [CompleteSpace E]
    {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle 1 F V I]
    (hn : 1 ≤ n)
    [hmetric : let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) (by simp)
      IsContMDiffRiemannianBundle I 2 F V]
    [hreg : let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) (by simp)
      ContMDiffCovariantDerivative cov n]
    (hcov : cov.IsMetricCompatible)
    {X Y : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x}
    (hX : let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) (by simp)
      CMDiff n (T% X))
    (hY : let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) (by simp)
      CMDiff n (T% Y))
    (hσ : CMDiff (n + 1) (T% σ)) (hτ : CMDiff (n + 1) (T% τ)) (x : M) :
    inner ℝ (cov.curvatureOperator X Y σ x) (τ x) =
      -inner ℝ (σ x) (cov.curvatureOperator X Y τ x) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) (by simp)
  change IsContMDiffRiemannianBundle I 2 F V at hmetric
  change ContMDiffCovariantDerivative cov n at hreg
  change CMDiff n (T% X) at hX
  change CMDiff n (T% Y) at hY
  let _ : IsContMDiffRiemannianBundle I 2 F V := hmetric
  let _ : ContMDiffCovariantDerivative cov n := hreg
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := by
    calc
      2 = 1 + 1 := by norm_num
      _ ≤ n + 1 := by simpa [add_comm] using add_le_add_right hn (1 : ℕ∞ω)
  have hmin : minSmoothness ℝ 2 ≤ n + 1 := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact h2
  let _ : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := n + 1) hmin
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hn)
  have hcomm := mvfderiv_mlieBracket
    ((hσ.of_le (m := 2) h2).inner_bundle
      (hτ.of_le (m := 2) h2)).contMDiffAt (by simp)
    (hX.mdifferentiable hn0 x) (hY.mdifferentiable hn0 x)
  rw [hcov.mvfderiv_inner_eq (mlieBracket I X Y)
      (hσ.mdifferentiable (by simp) x) (hτ.mdifferentiable (by simp) x),
    hcov.mvfderiv_mvfderiv_inner hn hY hσ hτ x,
    hcov.mvfderiv_mvfderiv_inner hn hX hσ hτ x] at hcomm
  simp only [curvatureOperator_apply, inner_sub_left, inner_sub_right]
  linarith

/-- Every pointwise curvature endomorphism of a smooth metric-compatible connection is
skew-adjoint. For the tangent bundle, this is the last-pair antisymmetry of the Riemann
curvature tensor after lowering its output index with the metric. -/
theorem IsMetricCompatible.inner_curvatureTensor_eq_neg
    [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]
    [ContMDiffCovariantDerivative cov ∞]
    [IsContMDiffRiemannianBundle I 2 F V]
    [FiniteDimensional ℝ E] [T2Space M] (hcov : cov.IsMetricCompatible)
    (x : M) (u v : TangentSpace I x) (w z : V x) :
    inner ℝ (cov.curvatureTensor x u v w) z =
      -inner ℝ w (cov.curvatureTensor x u v z) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  obtain ⟨τ, hτ, rfl⟩ := exists_contMDiff_section_eq I F z
  rw [curvatureTensor_apply cov x hX hY hσ, curvatureTensor_apply cov x hX hY hτ]
  let _ : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  let _ : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  exact hcov.inner_curvatureOperator_eq_neg (n := ∞) (by simp) hX hY hσ hτ x

end CovariantDerivative
