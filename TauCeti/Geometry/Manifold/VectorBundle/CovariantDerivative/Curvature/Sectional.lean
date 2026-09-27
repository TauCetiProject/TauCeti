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

The sectional curvature of the tangent plane spanned by linearly independent vectors `u, v` is

`<R(u, v)v, u> / det(Gram(u, v))`.

This file defines that quotient for a smooth connection on a Riemannian tangent bundle and packages
the pointwise and global constant-sectional-curvature predicates.  The quotient is defined for all
pairs, as is conventional for an algebraic API; the geometric predicates quantify only over
linearly independent pairs, where the Gram determinant is strictly positive.

The constant-curvature tensor `R(w, u)v = κ * (<u, v> * w - <w, v> * u)` has sectional
curvature `κ`, fixing the sign convention and providing the form used to state constant negative
curvature.

The definition and convention follow J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 8, §1.  The curvature convention is
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
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The sectional curvature evaluated on the tangent vectors `u` and `v`:
`<R(u,v)v,u> / det(Gram(u,v))`.

Its geometric use is on linearly independent vectors.  Defining the quotient on all pairs makes
it an ordinary real-valued function; the constant-curvature predicates below impose linear
independence explicitly. -/
def sectionalCurvature (x : M) (u v : TangentSpace I x) : ℝ :=
  inner ℝ (curvature x u v v) u / (Matrix.gram ℝ ![u, v]).det

/-- The defining quotient for sectional curvature. -/
theorem sectionalCurvature_apply (x : M) (u v : TangentSpace I x) :
    cov.sectionalCurvature x u v =
      inner ℝ (curvature x u v v) u / (Matrix.gram ℝ ![u, v]).det :=
  (rfl)

/-- On an orthonormal pair, sectional curvature is just `<R(u,v)v,u>`. -/
theorem sectionalCurvature_eq_of_orthonormal (x : M) (u v : TangentSpace I x)
    (h : Orthonormal ℝ ![u, v]) :
    cov.sectionalCurvature x u v = inner ℝ (curvature x u v v) u := by
  rw [sectionalCurvature_apply, (Matrix.gram_eq_one_iff_orthonormal.mpr h), Matrix.det_one,
    div_one]

/-- Rescaling either spanning vector by a nonzero scalar does not change sectional curvature. -/
theorem sectionalCurvature_smul_smul (x : M) (u v : TangentSpace I x) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    cov.sectionalCurvature x (a • u) (b • v) = cov.sectionalCurvature x u v := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, Matrix.det_gram_fin_two,
    Matrix.det_gram_fin_two]
  simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right]
  field_simp [ha, hb]

/-- For a metric-compatible connection, sectional curvature is symmetric in its two spanning
vectors. -/
theorem IsMetricCompatible.sectionalCurvature_comm
    [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (x : M) (u v : TangentSpace I x) :
    cov.sectionalCurvature x u v = cov.sectionalCurvature x v u := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, Matrix.det_gram_fin_two,
    Matrix.det_gram_fin_two, cov.curvatureTensor_antisymm x v u]
  simp only [LinearMap.neg_apply, inner_neg_left]
  rw [hcov.inner_curvatureTensor_eq_neg x u v u v, real_inner_comm u]
  rw [real_inner_comm v u]
  simp only [neg_neg, mul_comm]

/-- A connection has sectional curvature `k` at `x` when every tangent two-plane at `x` has
sectional curvature `k`. -/
def HasSectionalCurvatureAt (x : M) (k : ℝ) : Prop :=
  ∀ (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
    cov.sectionalCurvature x u v = k

/-- Evaluate the prescribed sectional curvature of a linearly independent tangent pair. -/
theorem HasSectionalCurvatureAt.sectionalCurvature_eq {x : M} {k : ℝ}
    (h : cov.HasSectionalCurvatureAt x k) (u v : TangentSpace I x)
    (huv : LinearIndependent ℝ ![u, v]) : cov.sectionalCurvature x u v = k :=
  h u v huv

/-- A connection has constant sectional curvature `k` when it has sectional curvature `k` at
every point. -/
def HasConstantSectionalCurvature (k : ℝ) : Prop :=
  ∀ x : M, cov.HasSectionalCurvatureAt x k

/-- Constant sectional curvature specializes to the prescribed curvature at each point. -/
theorem HasConstantSectionalCurvature.hasSectionalCurvatureAt {k : ℝ}
    (h : cov.HasConstantSectionalCurvature k) (x : M) : cov.HasSectionalCurvatureAt x k :=
  h x

/-- The algebraic constant-curvature tensor with parameter `k` has sectional curvature `k` on
every tangent two-plane at the point. -/
theorem hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub (x : M) (k : ℝ)
    (h : ∀ w u v : TangentSpace I x, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.HasSectionalCurvatureAt x k := by
  intro u v huv
  have hden : inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 ≠ 0 :=
    ((TauCeti.real_inner_mul_inner_self_sub_sq_pos_iff_linearIndependent u v).2 huv).ne'
  rw [sectionalCurvature_apply, h u v v, Matrix.det_gram_fin_two]
  rw [div_eq_iff hden]
  simp only [inner_sub_left, real_inner_smul_left]
  rw [real_inner_comm v u]
  ring

/-- If the curvature tensor has the constant-curvature form with the same parameter at every
point, then the connection has constant sectional curvature with that parameter. -/
theorem hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub (k : ℝ)
    (h : ∀ (x : M) (w u v : TangentSpace I x), curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.HasConstantSectionalCurvature k := fun x =>
  cov.hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub x k (h x)

/-- A connection whose curvature tensor vanishes everywhere has constant sectional curvature
zero. -/
theorem hasConstantSectionalCurvature_zero_of_curvatureTensor_eq_zero
    (h : ∀ x : M, curvature x = 0) : cov.HasConstantSectionalCurvature 0 := by
  apply cov.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub 0
  intro x w u v
  simp [h x]

end CovariantDerivative
