/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.GramPair
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

/-!
# Sectional curvature

For a metric-compatible connection, the sectional curvature of the tangent plane spanned by
linearly independent vectors `u, v` is

`<R(u, v)v, u> / det(Gram(u, v))`.

This file defines that quotient for a smooth metric-compatible connection on a Riemannian tangent
bundle and packages the pointwise and global constant-sectional-curvature predicates.  The
quotient is defined for all pairs, as is conventional for an algebraic API; the geometric
predicates quantify only over linearly independent pairs, where the Gram determinant is strictly
positive.  Metric compatibility supplies the curvature symmetries that make the quotient
independent of the chosen basis of the tangent plane; no torsion-free hypothesis is needed.

The constant-curvature tensor `R(w, u)v = κ * (<u, v> * w - <w, v> * u)` has sectional
curvature `κ`, fixing the sign convention and providing the form used to state constant negative
curvature.

The definition and convention follow J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 8, pp. 250–254 (Proposition 8.36).  The curvature convention is
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.

## Main definitions

* `CovariantDerivative.sectionalCurvature`: sectional curvature evaluated on two spanning vectors.
* `CovariantDerivative.HasSectionalCurvatureAt`: every tangent two-plane at a point has a given
  sectional curvature.
* `CovariantDerivative.HasConstantSectionalCurvature`: every tangent two-plane at every point has
  the same sectional curvature.
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold Matrix

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The sectional curvature evaluated on the tangent vectors `u` and `v`:
`<R(u,v)v,u> / det(Gram(u,v))`.

Its geometric use is on linearly independent vectors.  Defining the quotient on all pairs makes
it an ordinary real-valued function; the constant-curvature predicates below impose linear
independence explicitly. -/
def sectionalCurvature (_hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (x : M)
    (u v : TangentSpace I x) : ℝ :=
  inner ℝ (curvature x u v v) u / (Matrix.gram ℝ ![u, v]).det

/-- The defining quotient for sectional curvature. -/
@[simp]
theorem sectionalCurvature_apply (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (x : M)
    (u v : TangentSpace I x) :
    cov.sectionalCurvature hcov x u v =
      inner ℝ (curvature x u v v) u / (Matrix.gram ℝ ![u, v]).det :=
  (rfl)

/-- On an orthonormal pair, sectional curvature is just `<R(u,v)v,u>`. -/
theorem sectionalCurvature_eq_of_orthonormal (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)
    (x : M) (u v : TangentSpace I x)
    (h : Orthonormal ℝ ![u, v]) :
    cov.sectionalCurvature hcov x u v = inner ℝ (curvature x u v v) u := by
  rw [sectionalCurvature_apply, (Matrix.gram_eq_one_iff_orthonormal.mpr h), Matrix.det_one,
    div_one]

/-- Rescaling either spanning vector by a nonzero scalar does not change sectional curvature. -/
theorem sectionalCurvature_smul_smul (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)
    (x : M) (u v : TangentSpace I x) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    cov.sectionalCurvature hcov x (a • u) (b • v) =
      cov.sectionalCurvature hcov x u v := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, Matrix.real_det_gram_fin_two,
    Matrix.real_det_gram_fin_two]
  simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right]
  field_simp [ha, hb]

/-- Adding a multiple of the first spanning vector to the second does not change sectional
curvature. -/
theorem sectionalCurvature_add_smul_right (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)
    (x : M) (u v : TangentSpace I x) (a : ℝ) :
    cov.sectionalCurvature hcov x u (v + a • u) =
      cov.sectionalCurvature hcov x u v := by
  have hzero : inner ℝ (curvature x u v u) u = 0 := by
    apply CharZero.eq_neg_self_iff.mp
    simpa [real_inner_comm] using hcov.inner_curvatureTensor_eq_neg x u v u u
  rw [sectionalCurvature_apply, sectionalCurvature_apply, Matrix.real_det_gram_fin_two,
    Matrix.real_det_gram_fin_two]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    cov.curvatureTensor_self, LinearMap.zero_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_zero_left, hzero]
  rw [real_inner_comm v u]
  ring

variable {cov} in
/-- For a metric-compatible connection, sectional curvature is symmetric in its two spanning
vectors. -/
theorem IsMetricCompatible.sectionalCurvature_comm
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (x : M) (u v : TangentSpace I x) :
    cov.sectionalCurvature hcov x u v = cov.sectionalCurvature hcov x v u := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, Matrix.real_det_gram_fin_two,
    Matrix.real_det_gram_fin_two, cov.curvatureTensor_antisymm x v u]
  simp only [LinearMap.neg_apply, inner_neg_left]
  rw [hcov.inner_curvatureTensor_eq_neg x u v u v,
    real_inner_comm (curvature x u v v) u, real_inner_comm v u]
  ring

/-- A connection has sectional curvature `k` at `x` when every tangent two-plane at `x` has
sectional curvature `k`. -/
def HasSectionalCurvatureAt (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (x : M) (k : ℝ) : Prop :=
  ∀ (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
    cov.sectionalCurvature hcov x u v = k

/-- The pointwise characterization of having prescribed sectional curvature. -/
theorem hasSectionalCurvatureAt_iff (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (x : M) (k : ℝ) :
    cov.HasSectionalCurvatureAt hcov x k ↔
      ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
        cov.sectionalCurvature hcov x u v = k :=
  Iff.rfl

variable {cov} in
/-- Evaluate the prescribed sectional curvature of a linearly independent tangent pair. -/
theorem HasSectionalCurvatureAt.sectionalCurvature_eq
    {hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov} {x : M} {k : ℝ}
    (h : cov.HasSectionalCurvatureAt hcov x k) (u v : TangentSpace I x)
    (huv : LinearIndependent ℝ ![u, v]) : cov.sectionalCurvature hcov x u v = k :=
  h u v huv

/-- A connection has constant sectional curvature `k` when it has sectional curvature `k` at
every point. -/
def HasConstantSectionalCurvature (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (k : ℝ) : Prop :=
  ∀ x : M, cov.HasSectionalCurvatureAt hcov x k

/-- The pointwise characterization of constant sectional curvature. -/
theorem hasConstantSectionalCurvature_iff (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (k : ℝ) :
    cov.HasConstantSectionalCurvature hcov k ↔
      ∀ x : M, cov.HasSectionalCurvatureAt hcov x k :=
  Iff.rfl

variable {cov} in
/-- Constant sectional curvature specializes to the prescribed curvature at each point. -/
theorem HasConstantSectionalCurvature.hasSectionalCurvatureAt
    {hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov} {k : ℝ}
    (h : cov.HasConstantSectionalCurvature hcov k) (x : M) :
    cov.HasSectionalCurvatureAt hcov x k :=
  h x

/-- The algebraic constant-curvature tensor with parameter `k` has sectional curvature `k` on
every tangent two-plane at the point. -/
theorem hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov) (x : M) (k : ℝ)
    (h : ∀ w u v : TangentSpace I x, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.HasSectionalCurvatureAt hcov x k := by
  intro u v huv
  rw [sectionalCurvature_apply, h u v v,
    div_eq_iff (Matrix.det_gram_ne_zero_iff_linearIndependent.2 huv),
    Matrix.real_det_gram_fin_two]
  simp only [inner_sub_left, real_inner_smul_left]
  rw [real_inner_comm v u]
  ring

/-- If the curvature tensor has the constant-curvature form with the same parameter at every
point, then the connection has constant sectional curvature with that parameter. -/
theorem hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov) (k : ℝ)
    (h : ∀ (x : M) (w u v : TangentSpace I x), curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.HasConstantSectionalCurvature hcov k := fun x =>
  cov.hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub hcov x k (h x)

/-- A connection whose curvature tensor vanishes everywhere has constant sectional curvature
zero. -/
theorem hasConstantSectionalCurvature_zero_of_curvatureTensor_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov) (h : ∀ x : M, curvature x = 0) :
    cov.HasConstantSectionalCurvature hcov 0 := by
  apply cov.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub hcov 0
  intro x w u v
  simp [h x]

end CovariantDerivative
