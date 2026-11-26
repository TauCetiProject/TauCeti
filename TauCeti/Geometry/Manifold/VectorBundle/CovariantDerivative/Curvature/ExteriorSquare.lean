/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import Mathlib.Analysis.InnerProductSpace.Symmetric
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic

/-!
# Curvature as an endomorphism of the exterior square

The metric-lowered curvature tensor determines an endomorphism of Mathlib's second exterior
power of each tangent space, with its Gram inner product. Its convention is
`⟪Rop(u ∧ v), w ∧ z⟫ = ⟪R(u,v)z,w⟫`, so constant sectional curvature `κ` gives `κ Id`.
For a metric-compatible torsion-free connection this endomorphism is symmetric. Sectional
curvature is its Rayleigh quotient on decomposable bivectors, not on arbitrary bivectors.
Its operator norm controls every curvature pairing and the vector `R(u,v)w`, without a
curvature-sign hypothesis.

The construction is pointwise; it does not install a new exterior bundle or metric.
The sign convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, second edition,
Chapter 8. The inner product is Mathlib's `exteriorPower.inner_ιMulti_ιMulti`.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

private def exteriorCurvatureForm (x : M) :
    LinearMap.BilinForm ℝ (⋀[ℝ]^2 (TangentSpace I x)) :=
  -(cov.riemannCurvatureTensor x).exteriorSquareBilinear
    (fun u w z ↦ by simp)
    -- Ascribe IsAlt explicitly to preserve the proof type for the exterior-square API.
    (fun u v ↦ show (cov.riemannCurvatureTensor x u v).IsAlt from fun w ↦
      CharZero.eq_neg_self_iff.mp
        (IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x u v w w))

/-- The curvature endomorphism on the second exterior power, with
`⟪Rop(u ∧ v), w ∧ z⟫ = ⟪R(u,v)z,w⟫`. -/
def curvatureEndomorphism (x : M) :
    Module.End ℝ (⋀[ℝ]^2 (TangentSpace I x)) :=
  (InnerProductSpace.toDual ℝ (⋀[ℝ]^2 (TangentSpace I x))).symm.toLinearEquiv.toLinearMap ∘ₗ
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ cov.exteriorCurvatureForm hcov x)

private theorem inner_curvatureEndomorphism (x : M)
    (a b : ⋀[ℝ]^2 (TangentSpace I x)) :
    ⟪cov.curvatureEndomorphism hcov x a, b⟫ = cov.exteriorCurvatureForm hcov x a b := by
  simp [curvatureEndomorphism, InnerProductSpace.toDual_symm_apply]

/-- The curvature endomorphism paired against a pure wedge recovers the curvature tensor. -/
@[simp]
theorem inner_curvatureEndomorphism_ιMulti (x : M) (u v : Fin 2 → TangentSpace I x) :
    ⟪cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 u),
      exteriorPower.ιMulti ℝ 2 v⟫ =
      ⟪cov.curvatureTensor x (u 0) (u 1) (v 1), v 0⟫ := by
  rw [inner_curvatureEndomorphism]
  simp only [exteriorCurvatureForm, LinearMap.neg_apply,
    LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  rw [IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov,
    neg_neg, riemannCurvatureTensor_apply]

/-- Every curvature pairing is bounded by the operator norm times the norms of its two pure
bivectors. Metric compatibility suffices; no curvature sign is assumed. -/
theorem abs_inner_curvatureTensor_le_norm_curvatureEndomorphism_mul_norm_ιMulti
    (x : M) (u v w z : TangentSpace I x) :
    |⟪cov.curvatureTensor x u v w, z⟫| ≤
      ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ * ‖exteriorPower.ιMulti ℝ 2 ![z, w]‖ := by
  let A := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  let a := exteriorPower.ιMulti ℝ 2 ![u, v]
  let b := exteriorPower.ιMulti ℝ 2 ![z, w]
  have hab : |⟪A a, b⟫| ≤ ‖A‖ * ‖a‖ * ‖b‖ :=
    (abs_real_inner_le_norm _ _).trans <|
      mul_le_mul_of_nonneg_right (A.le_opNorm a) (norm_nonneg b)
  simpa only [A, a, b, LinearMap.coe_toContinuousLinearMap',
    inner_curvatureEndomorphism_ιMulti, Matrix.cons_val_zero, Matrix.cons_val_one] using hab

/-- Every curvature pairing is bounded by the operator norm of the curvature endomorphism times
all four vector norms. Metric compatibility suffices; no curvature sign is assumed. -/
theorem abs_inner_curvatureTensor_le_norm_curvatureEndomorphism_mul
    (x : M) (u v w z : TangentSpace I x) :
    |⟪cov.curvatureTensor x u v w, z⟫| ≤
      ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
  calc
    _ ≤ ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ * ‖exteriorPower.ιMulti ℝ 2 ![z, w]‖ :=
      cov.abs_inner_curvatureTensor_le_norm_curvatureEndomorphism_mul_norm_ιMulti hcov x u v w z
    _ ≤ ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        (‖u‖ * ‖v‖) * (‖z‖ * ‖w‖) := by
      gcongr
      · exact exteriorPower.norm_ιMulti_two_le u v
      · exact exteriorPower.norm_ιMulti_two_le z w
    _ = _ := by ring

/-- The vector `R(u,v)w` is bounded by the curvature operator norm times `‖u ∧ v‖ * ‖w‖`,
without a curvature-sign hypothesis. -/
theorem norm_curvatureTensor_le_norm_curvatureEndomorphism_mul_norm_ιMulti
    (x : M) (u v w : TangentSpace I x) :
    ‖cov.curvatureTensor x u v w‖ ≤
      ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ * ‖w‖ := by
  calc
    ‖cov.curvatureTensor x u v w‖ = ‖innerSL ℝ (cov.curvatureTensor x u v w)‖ :=
      (innerSL_apply_norm ℝ _).symm
    _ ≤ _ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z ↦ ?_
      calc
        ‖innerSL ℝ (cov.curvatureTensor x u v w) z‖ ≤
            ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
              ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ * ‖exteriorPower.ιMulti ℝ 2 ![z, w]‖ := by
          simpa only [innerSL_apply_apply, Real.norm_eq_abs] using
            cov.abs_inner_curvatureTensor_le_norm_curvatureEndomorphism_mul_norm_ιMulti
              hcov x u v w z
        _ ≤ ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
            ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ * (‖z‖ * ‖w‖) := by
          gcongr
          exact exteriorPower.norm_ιMulti_two_le z w
        _ = _ := by ring

/-- The actual vector `R(u,v)w` is bounded by the operator norm of the curvature endomorphism
multiplied by the three input norms, without a curvature-sign hypothesis. -/
theorem norm_curvatureTensor_le_norm_curvatureEndomorphism_mul
    (x : M) (u v w : TangentSpace I x) :
    ‖cov.curvatureTensor x u v w‖ ≤
      ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
  calc
    _ ≤ ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ * ‖w‖ :=
      cov.norm_curvatureTensor_le_norm_curvatureEndomorphism_mul_norm_ιMulti hcov x u v w
    _ ≤ ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        (‖u‖ * ‖v‖) * ‖w‖ := by
      gcongr
      exact exteriorPower.norm_ιMulti_two_le u v
    _ = _ := by ring

/-- The pure-wedge pairing uniquely characterizes the curvature endomorphism. -/
theorem curvatureEndomorphism_eq_iff (x : M)
    (A : Module.End ℝ (⋀[ℝ]^2 (TangentSpace I x))) :
    cov.curvatureEndomorphism hcov x = A ↔
      ∀ u v : Fin 2 → TangentSpace I x,
        ⟪A (exteriorPower.ιMulti ℝ 2 u), exteriorPower.ιMulti ℝ 2 v⟫ =
          ⟪cov.curvatureTensor x (u 0) (u 1) (v 1), v 0⟫ := by
  constructor
  · rintro rfl u v
    exact cov.inner_curvatureEndomorphism_ιMulti hcov x u v
  · intro h
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro u
    apply (InnerProductSpace.toDual ℝ (⋀[ℝ]^2 (TangentSpace I x))).injective
    apply ContinuousLinearMap.coe_injective
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa using (cov.inner_curvatureEndomorphism_ιMulti hcov x u v).trans (h u v).symm

/-- For a metric-compatible torsion-free connection, the curvature endomorphism is symmetric. -/
theorem isSymmetric_curvatureEndomorphism (ht : cov.torsion = 0) (x : M) :
    (cov.curvatureEndomorphism hcov x).IsSymmetric := by
  have hflip : (cov.exteriorCurvatureForm hcov x).flip = cov.exteriorCurvatureForm hcov x := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [LinearMap.BilinForm.flip, LinearMap.BilinForm.flip_apply,
      exteriorCurvatureForm, LinearMap.neg_apply]
    exact congrArg Neg.neg (LinearMap.congr_fun₂
      (LinearMap.flip_exteriorSquareBilinear _ _ _
        (IsMetricCompatible.riemannCurvatureTensor_swap_pairs cov hcov ht x)) a b)
  intro a b
  rw [real_inner_comm (cov.curvatureEndomorphism hcov x b) a,
    inner_curvatureEndomorphism, inner_curvatureEndomorphism]
  exact (LinearMap.congr_fun₂ hflip a b).symm

/-- Sectional curvature is the Rayleigh quotient of the curvature endomorphism on a pure
bivector. This equality also holds on dependent pairs, with both quotients interpreted in `ℝ`. -/
theorem sectionalCurvature_eq_curvatureEndomorphism (x : M) (u v : TangentSpace I x) :
    cov.sectionalCurvature hcov x u v =
      ⟪cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 ![u, v]),
        exteriorPower.ιMulti ℝ 2 ![u, v]⟫ /
          ⟪exteriorPower.ιMulti ℝ 2 ![u, v], exteriorPower.ιMulti ℝ 2 ![u, v]⟫ := by
  rw [sectionalCurvature_apply, inner_curvatureEndomorphism_ιMulti,
    exteriorPower.inner_ιMulti_self]
  rfl

variable {cov} in
/-- Constant sectional curvature gives scalar multiplication on the whole exterior square,
not merely its decomposable elements. No lower dimension bound is needed for this implication. -/
theorem HasSectionalCurvatureAt.curvatureEndomorphism_eq_smul_id
    {hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov} {x : M} {κ : ℝ}
    (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0) :
    cov.curvatureEndomorphism hcov x = κ • LinearMap.id := by
  rw [curvatureEndomorphism_eq_iff]
  intro u v
  rw [h.curvatureTensor_eq_smul_inner_sub ht]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left,
    inner_sub_left, exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_two]
  simp [Matrix.of_apply, real_inner_comm, mul_sub, mul_comm]

/-- For a torsion-free metric-compatible connection, constant sectional curvature at a point
is equivalent to a scalar curvature endomorphism. In dimensions below two both conditions hold
for every scalar; neither condition asserts uniqueness of that scalar. -/
theorem hasSectionalCurvatureAt_iff_curvatureEndomorphism_eq_smul_id
    (ht : cov.torsion = 0) (x : M) (κ : ℝ) :
    cov.HasSectionalCurvatureAt hcov x κ ↔
      cov.curvatureEndomorphism hcov x = κ • LinearMap.id := by
  constructor
  · exact fun h ↦ h.curvatureEndomorphism_eq_smul_id ht
  · intro h
    rw [hasSectionalCurvatureAt_iff]
    intro u v huv
    rw [sectionalCurvature_eq_curvatureEndomorphism, h]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left,
      exteriorPower.inner_ιMulti_self]
    exact mul_div_cancel_right₀ κ (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr huv)

end CovariantDerivative
