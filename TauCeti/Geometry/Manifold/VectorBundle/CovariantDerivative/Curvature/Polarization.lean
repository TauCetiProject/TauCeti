/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
import TauCeti.LinearAlgebra.BilinearForm.KulkarniNomizu

/-!
# Sectional curvature determines the curvature tensor

For a metric-compatible torsion-free connection on a Riemannian tangent bundle, the
metric-lowered curvature tensor `Rm(u, v, w, z) = ⟨R(u, v)w, z⟩` is antisymmetric in each pair of
arguments and satisfies the first Bianchi identity. By the polarization identity
`LinearMap.six_mul_apply_eq_of_cyclic_eq_zero` it is therefore determined by the numerators
`⟨R(u, v)v, u⟩` of the sectional curvatures, and in fact by their values on linearly independent
pairs `u, v`, which are the pairs spanning a tangent two-plane
(`CovariantDerivative.IsMetricCompatible.riemannCurvatureTensor_eq_of_forall_linearIndependent`).

In particular, the tangent two-planes at a point all have sectional curvature `κ` exactly when
the curvature tensor there has the constant-curvature form

`R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)`.

So constant sectional curvature `κ` is equivalent to the constant-curvature tensor equation
`Bundle.RiemannianMetric.IsConstantCurvatureTensor`, and it forces `Ric = (n - 1) κ g` and
`Scal = n (n - 1) κ` in dimension `n`. In dimension at most one there are no tangent two-planes,
so every `κ` is a sectional curvature
(`CovariantDerivative.hasSectionalCurvatureAt_of_finrank_le_one`), and correspondingly the
constant-curvature equation then holds for every `κ`. From dimension two on the sectional
curvature at a point is unique (`CovariantDerivative.HasSectionalCurvatureAt.eq_of_one_lt_finrank`).

## Main results

* `CovariantDerivative.hasSectionalCurvatureAt_iff_curvatureTensor_eq_smul_inner_sub`: sectional
  curvature `κ` at a point is the constant-curvature form of the curvature tensor there.
* `CovariantDerivative.hasConstantSectionalCurvature_iff_isConstantCurvatureTensor`: the global
  version.
* `CovariantDerivative.HasSectionalCurvatureAt.ricciTensor_eq` and
  `CovariantDerivative.HasSectionalCurvatureAt.scalarCurvature_eq`: the Ricci and scalar curvature
  of a point of sectional curvature `κ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 8, Propositions 8.31 and 8.36.
-/

public section

open Bundle LinearMap.BilinForm
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- At a point where every tangent two-plane has sectional curvature `κ`, the curvature tensor of
a metric-compatible torsion-free connection has the constant-curvature form
`R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)`. -/
theorem HasSectionalCurvatureAt.curvatureTensor_eq_smul_inner_sub
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0)
    (w u v : TangentSpace I x) :
    curvature x w u v = κ • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) := by
  set g := innerₗ (TangentSpace I x)
  have hg : LinearMap.BilinForm.IsSymm g := isSymm_iff.mpr isSymm_inner
  have hκg : LinearMap.BilinForm.IsSymm ((κ / 2) • g) := isSymm_def.2 fun a b ↦ by
    simp only [LinearMap.smul_apply, hg.eq a b]
  -- The constant-curvature tensor is `(κ / 2) g ⊙ g`.
  have hRm : cov.riemannCurvatureTensor x = kulkarniNomizu ((κ / 2) • g) g :=
    hcov.riemannCurvatureTensor_eq_of_forall_linearIndependent ht x
      (kulkarniNomizu_antisymm_first _ _) (kulkarniNomizu_antisymm_last _ _)
      (IsSymm.kulkarniNomizu_cyclic_eq_zero hκg hg) fun a b hab ↦ by
        have hab' := h.sectionalCurvature_eq a b hab
        rw [sectionalCurvature_apply,
          div_eq_iff (Matrix.det_gram_ne_zero_iff_linearIndependent.2 hab),
          Matrix.real_det_gram_fin_two] at hab'
        simp only [riemannCurvatureTensor_apply, hab', kulkarniNomizu_apply, LinearMap.smul_apply,
          smul_eq_mul, g, innerₗ_apply_apply, real_inner_comm b a]
        ring
  refine ext_inner_right ℝ fun z ↦ ?_
  have hz := congrArg (fun T ↦ T w u v z) hRm
  simp only [riemannCurvatureTensor_apply, kulkarniNomizu_apply, LinearMap.smul_apply,
    smul_eq_mul, g, innerₗ_apply_apply] at hz
  simp only [hz, inner_smul_left, inner_sub_left, RCLike.conj_to_real]
  ring

variable (cov) in
/-- For a metric-compatible torsion-free connection, every tangent two-plane at `x` has sectional
curvature `κ` if and only if the curvature tensor at `x` has the constant-curvature form
`R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)`. -/
theorem hasSectionalCurvatureAt_iff_curvatureTensor_eq_smul_inner_sub
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (x : M) (κ : ℝ) :
    cov.HasSectionalCurvatureAt hcov x κ ↔
      ∀ w u v : TangentSpace I x, curvature x w u v = κ • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) :=
  ⟨fun h ↦ h.curvatureTensor_eq_smul_inner_sub ht,
    cov.hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub hcov x κ⟩

variable (cov) in
/-- A metric-compatible torsion-free connection has constant sectional curvature `κ` if and only
if its curvature tensor is the constant-curvature tensor `R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)` at
every point. Applied to the Levi-Civita connection, this identifies constant sectional curvature
of a Riemannian manifold with the constant-curvature equation. -/
theorem hasConstantSectionalCurvature_iff_isConstantCurvatureTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (κ : ℝ) :
    cov.HasConstantSectionalCurvature hcov κ ↔
      (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).IsConstantCurvatureTensor cov
        inferInstance κ := by
  -- The metric `⟨RiemannianBundle.g⟩` installed by `isConstantCurvatureTensor_iff` is the ambient
  -- `RiemannianBundle` instance up to structure eta, so the two sides agree definitionally.
  rw [hasConstantSectionalCurvature_iff, RiemannianMetric.isConstantCurvatureTensor_iff]
  exact forall_congr' fun x ↦
    hasSectionalCurvatureAt_iff_curvatureTensor_eq_smul_inner_sub cov hcov ht x κ

/-- At a point where every tangent two-plane has sectional curvature `κ`, the Ricci tensor of a
metric-compatible torsion-free connection is `(n - 1) κ g` in dimension `n`. -/
theorem HasSectionalCurvatureAt.ricciTensor_eq
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0) :
    cov.ricciTensor x =
      ((Module.finrank ℝ (TangentSpace I x) - 1 : ℝ) * κ) • innerₗ (TangentSpace I x) :=
  cov.ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub x κ
    (h.curvatureTensor_eq_smul_inner_sub ht)

/-- At a point where every tangent two-plane has sectional curvature `κ`, the scalar curvature of
a metric-compatible torsion-free connection is `n (n - 1) κ` in dimension `n`. -/
theorem HasSectionalCurvatureAt.scalarCurvature_eq
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0) :
    cov.scalarCurvature x = (Module.finrank ℝ (TangentSpace I x) : ℝ) *
      (Module.finrank ℝ (TangentSpace I x) - 1) * κ :=
  cov.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub x κ
    (h.curvatureTensor_eq_smul_inner_sub ht)

end CovariantDerivative
