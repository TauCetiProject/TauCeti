/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Pointwise curvature tensors

The curvature of a smooth connection on a finite-rank real vector bundle is a trilinear
map on each fibre. `CovariantDerivative.curvatureTensor` bundles this map, with two
tangent-vector arguments and one bundle-vector argument. On the tangent bundle it is
the pointwise `(1,3)` curvature tensor, ready for contraction or pairing with a metric.

The construction uses globally smooth extensions of fibre vectors and the pointwise
independence theorem `CovariantDerivative.curvatureOperator_congr`. Its characteristic
equation `curvatureTensor_apply` computes it on any smooth fields and section, so callers
do not depend on the chosen extensions. No metric or torsion assumption is needed.

The sign convention is that of J. M. Lee, *Introduction to Riemannian Manifolds*,
2nd ed., Springer GTM 176 (2018), Chapter 7, pp. 196–198:
`R(X,Y)σ = ∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X,Y] σ`.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

private def curvatureValue (x : M) (u v : TangentSpace I x) (w : V x) : V x :=
  cov.curvatureOperator
    (Classical.choose (exists_contMDiff_section_eq I E u))
    (Classical.choose (exists_contMDiff_section_eq I E v))
    (Classical.choose (exists_contMDiff_section_eq I F w)) x

private theorem curvatureValue_eq (x : M)
    {X Y : Π y : M, TangentSpace I y} {σ : Π y : M, V y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    curvatureValue cov x (X x) (Y x) (σ x) = cov.curvatureOperator X Y σ x := by
  exact curvatureOperator_congr
    (Classical.choose_spec (exists_contMDiff_section_eq I E (X x))).1 hX
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Y x))).1 hY
    (Classical.choose_spec (exists_contMDiff_section_eq I F (σ x))).1 hσ
    (Classical.choose_spec (exists_contMDiff_section_eq I E (X x))).2
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Y x))).2
    (Classical.choose_spec (exists_contMDiff_section_eq I F (σ x))).2

private theorem curvatureValue_add_first (x : M) (u u' v : TangentSpace I x) (w : V x) :
    curvatureValue cov x (u + u') v w =
      curvatureValue cov x u v w + curvatureValue cov x u' v w := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨X', hX', rfl⟩ := exists_contMDiff_section_eq I E u'
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  have h := congrFun (curvatureOperator_add_first (cov := cov) hX hX' hσ (Y := Y)) x
  simp only [Pi.add_apply] at h
  rw [← curvatureValue_eq cov x (hX.add_section hX') hY hσ,
    ← curvatureValue_eq cov x hX hY hσ, ← curvatureValue_eq cov x hX' hY hσ] at h
  exact h

private theorem curvatureValue_smul_first (x : M) (c : ℝ) (u v : TangentSpace I x)
    (w : V x) :
    curvatureValue cov x (c • u) v w = c • curvatureValue cov x u v w := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  have h := congrFun (curvatureOperator_smul_first (cov := cov)
    (f := fun _ ↦ c) contMDiff_const hX hσ (Y := Y)) x
  simp only [Pi.smul_apply'] at h
  rw [← curvatureValue_eq cov x (contMDiff_const.smul_section hX) hY hσ,
    ← curvatureValue_eq cov x hX hY hσ] at h
  exact h

private theorem curvatureValue_add_second (x : M) (u v v' : TangentSpace I x) (w : V x) :
    curvatureValue cov x u (v + v') w =
      curvatureValue cov x u v w + curvatureValue cov x u v' w := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨Y', hY', rfl⟩ := exists_contMDiff_section_eq I E v'
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  have h := congrFun (curvatureOperator_add_second (cov := cov) hY hY' hσ (X := X)) x
  simp only [Pi.add_apply] at h
  rw [← curvatureValue_eq cov x hX (hY.add_section hY') hσ,
    ← curvatureValue_eq cov x hX hY hσ, ← curvatureValue_eq cov x hX hY' hσ] at h
  exact h

private theorem curvatureValue_smul_second (x : M) (c : ℝ) (u v : TangentSpace I x)
    (w : V x) :
    curvatureValue cov x u (c • v) w = c • curvatureValue cov x u v w := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  have h := congrFun (curvatureOperator_smul_second (cov := cov)
    (f := fun _ ↦ c) contMDiff_const hY hσ (X := X)) x
  simp only [Pi.smul_apply'] at h
  rw [← curvatureValue_eq cov x hX (contMDiff_const.smul_section hY) hσ,
    ← curvatureValue_eq cov x hX hY hσ] at h
  exact h

private theorem curvatureValue_add_section (x : M) (u v : TangentSpace I x) (w w' : V x) :
    curvatureValue cov x u v (w + w') =
      curvatureValue cov x u v w + curvatureValue cov x u v w' := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  obtain ⟨τ, hτ, rfl⟩ := exists_contMDiff_section_eq I F w'
  have h := congrFun (curvatureOperator_add_section (cov := cov) hX hY hσ hτ) x
  simp only [Pi.add_apply] at h
  rw [← curvatureValue_eq cov x hX hY (hσ.add_section hτ),
    ← curvatureValue_eq cov x hX hY hσ, ← curvatureValue_eq cov x hX hY hτ] at h
  exact h

private theorem curvatureValue_smul_section (x : M) (c : ℝ) (u v : TangentSpace I x)
    (w : V x) :
    curvatureValue cov x u v (c • w) = c • curvatureValue cov x u v w := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  have h := congrFun (curvatureOperator_smul_section (cov := cov)
    (f := fun _ ↦ c) contMDiff_const hX hY hσ) x
  simp only [Pi.smul_apply'] at h
  rw [← curvatureValue_eq cov x hX hY (contMDiff_const.smul_section hσ),
    ← curvatureValue_eq cov x hX hY hσ] at h
  exact h

/-- The pointwise curvature tensor of a smooth connection, linear in two tangent vectors
and one bundle vector. On the tangent bundle this is the `(1,3)` curvature tensor. -/
def curvatureTensor (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x →ₗ[ℝ] V x :=
  LinearMap.mk₂ ℝ
    (fun u v ↦
      { toFun := curvatureValue cov x u v
        map_add' := curvatureValue_add_section cov x u v
        map_smul' := fun c w ↦ curvatureValue_smul_section cov x c u v w })
    (fun u u' v ↦ LinearMap.ext fun w ↦ curvatureValue_add_first cov x u u' v w)
    (fun c u v ↦ LinearMap.ext fun w ↦ curvatureValue_smul_first cov x c u v w)
    (fun u v v' ↦ LinearMap.ext fun w ↦ curvatureValue_add_second cov x u v v' w)
    (fun c u v ↦ LinearMap.ext fun w ↦ curvatureValue_smul_second cov x c u v w)

/-- The pointwise tensor agrees with the curvature operator on any globally smooth
vector fields and bundle section. -/
theorem curvatureTensor_apply (x : M)
    {X Y : Π y : M, TangentSpace I y} {σ : Π y : M, V y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    cov.curvatureTensor x (X x) (Y x) (σ x) = cov.curvatureOperator X Y σ x :=
  curvatureValue_eq cov x hX hY hσ

/-- Evaluation on smooth sections uniquely characterizes the pointwise curvature tensor. -/
theorem eq_curvatureTensor_iff (x : M)
    (R : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x →ₗ[ℝ] V x) :
    R = cov.curvatureTensor x ↔
      ∀ (X Y : Π y : M, TangentSpace I y) (σ : Π y : M, V y),
        CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) → CMDiff ∞ (T% σ) →
          R (X x) (Y x) (σ x) = cov.curvatureOperator X Y σ x := by
  constructor
  · rintro rfl X Y σ hX hY hσ
    exact curvatureTensor_apply cov x hX hY hσ
  · intro h
    ext u v w
    obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
    obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
    obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
    rw [curvatureTensor_apply cov x hX hY hσ]
    exact h X Y σ hX hY hσ

/-- Swapping the two tangent-vector arguments negates the curvature endomorphism. -/
theorem curvatureTensor_antisymm (x : M) (u v : TangentSpace I x) :
    cov.curvatureTensor x u v = -cov.curvatureTensor x v u := by
  ext w
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  simp only [LinearMap.neg_apply, curvatureTensor_apply cov x hX hY hσ,
    curvatureTensor_apply cov x hY hX hσ]
  exact congrFun (curvatureOperator_antisymm cov X Y σ) x

/-- The curvature endomorphism vanishes when its tangent-vector arguments coincide. -/
@[simp]
theorem curvatureTensor_self (x : M) (u : TangentSpace I x) :
    cov.curvatureTensor x u u = 0 := by
  ext w
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  simp [curvatureTensor_apply cov x hX hX hσ]

end CovariantDerivative
