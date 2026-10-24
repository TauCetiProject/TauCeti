/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.KulkarniNomizu
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Schouten
import TauCeti.LinearAlgebra.Multilinear.CurvatureDimThree

/-!
# The Weyl curvature tensor of a smooth connection

The Weyl tensor is the part of the Riemann curvature tensor left after removing the
Kulkarni–Nomizu product of the Schouten tensor `P` with the metric `g`:

`W = Rm - P ⊙ g`, so that `Rm = W + P ⊙ g`,

with `Rm(u, v, w, z) = ⟨R(u, v)w, z⟩` and
`(P ⊙ g)(u, v, w, z) = P(u, z) g(v, w) + P(v, w) g(u, z) - P(u, w) g(v, z) - P(v, z) g(u, w)`.
It is the conformally invariant part of the curvature, and its vanishing characterizes local
conformal flatness in dimension at least `4`. In dimension `3` the Weyl tensor of a
metric-compatible connection vanishes identically, so there the Riemann curvature is
`Rm = P ⊙ g` and is determined by the Ricci curvature.

For a metric-compatible torsion-free connection `W` has all the algebraic symmetries of `Rm`.
Away from dimension `2`, the Ricci contraction of `W` vanishes for every smooth connection: the
Schouten tensor is defined precisely so that `P ⊙ g` carries all of the Ricci curvature. In
particular a space of constant curvature has vanishing Weyl tensor.

## Main declarations

* `CovariantDerivative.weylTensor`: the Weyl curvature tensor.
* `CovariantDerivative.IsMetricCompatible.weylTensor_swap_pairs` and
  `CovariantDerivative.IsMetricCompatible.weylTensor_cyclic_eq_zero`: pair interchange and the
  first Bianchi identity.
* `CovariantDerivative.sum_weylTensor_eq_zero`: the Weyl tensor is trace-free.
* `CovariantDerivative.weylTensor_eq_zero_of_finrank_le_one`: the Weyl tensor vanishes in
  dimension at most `1`.
* `CovariantDerivative.weylTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub`: constant
  curvature implies vanishing Weyl tensor.
* `CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three`: the Weyl
  tensor vanishes in dimension `3`.
* `IsMetricCompatible.riemannCurvatureTensor_eq_kulkarniNomizu_of_finrank_eq_three`:
  hence `Rm = P ⊙ g` in dimension `3`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open Bundle LinearMap.BilinForm
open scoped ContDiff Manifold

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

/-- The Weyl curvature tensor `W = Rm - P ⊙ g`, where `Rm` is the metric-lowered Riemann
curvature tensor, `P` the Schouten tensor and `⊙` the Kulkarni–Nomizu product. -/
def weylTensor (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ]
      TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  -- Built with `LinearMap.mk₂` because instance search does not find the subtraction on
  -- quadrilinear maps of `TangentSpace I x` directly.
  LinearMap.mk₂ ℝ
    (fun u v ↦ cov.riemannCurvatureTensor x u v -
      kulkarniNomizu (cov.schoutenTensor x) (innerₗ (TangentSpace I x)) u v)
    (fun u u' v ↦ by ext w z; simp only [map_add, LinearMap.add_apply, LinearMap.sub_apply]; ring)
    (fun c u v ↦ by
      ext w z; simp only [map_smul, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]; ring)
    (fun u v v' ↦ by ext w z; simp only [map_add, LinearMap.add_apply, LinearMap.sub_apply]; ring)
    (fun c u v ↦ by
      ext w z; simp only [map_smul, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]; ring)

/-- Evaluation of the Weyl curvature tensor. -/
@[simp]
theorem weylTensor_apply (x : M) (u v w z : TangentSpace I x) :
    cov.weylTensor x u v w z =
      cov.riemannCurvatureTensor x u v w z -
        kulkarniNomizu (cov.schoutenTensor x) (innerₗ _) u v w z :=
  (rfl)

/-- The Weyl tensor is antisymmetric in its first pair of arguments. -/
theorem weylTensor_antisymm_first (x : M) (u v w z : TangentSpace I x) :
    cov.weylTensor x u v w z = -cov.weylTensor x v u w z := by
  rw [weylTensor_apply, weylTensor_apply, cov.riemannCurvatureTensor_antisymm_first x u v,
    kulkarniNomizu_antisymm_first]
  ring

/-- Away from dimension `2`, the Weyl tensor is trace-free: in an orthonormal basis, contracting
its first and fourth arguments gives zero. -/
theorem sum_weylTensor_eq_zero {ι : Type*} [Fintype ι] (x : M)
    (hn : Module.finrank ℝ (TangentSpace I x) ≠ 2)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    ∑ j, cov.weylTensor x (b j) u v (b j) = 0 := by
  simp only [weylTensor_apply, Finset.sum_sub_distrib,
    ← cov.ricciTensor_eq_sum_riemannCurvatureTensor x b, sum_kulkarniNomizu_innerₗ]
  rw [cov.ricciTensor_eq_smul_schoutenTensor_add x hn]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  ring

/-- On a base of tangent dimension at most one, the Weyl tensor of every smooth connection
vanishes. -/
theorem weylTensor_eq_zero_of_finrank_le_one (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) ≤ 1) : cov.weylTensor x = 0 := by
  -- The curvature vanishes, and with it `Rm`, `Ric`, `Scal` and `P`.
  have hR := cov.curvatureTensor_eq_zero_of_finrank_le_one x hdim
  have hs := cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x hR
  ext u v w z
  simp [hR, hs]

/-- A space of constant curvature `R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)` has vanishing Weyl tensor,
away from dimension `2`. -/
theorem weylTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub (x : M) (k : ℝ)
    (hn : Module.finrank ℝ (TangentSpace I x) ≠ 2)
    (h : ∀ w u v, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.weylTensor x = 0 := by
  rcases le_or_gt (Module.finrank ℝ (TangentSpace I x)) 1 with h1 | h3
  · exact cov.weylTensor_eq_zero_of_finrank_le_one x h1
  ext u v w z
  rw [weylTensor_apply,
    cov.schoutenTensor_eq_of_curvatureTensor_eq_smul_inner_sub x k (by omega) h,
    riemannCurvatureTensor_apply, h]
  simp only [kulkarniNomizu_apply, LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul,
    inner_smul_left, inner_sub_left, RCLike.conj_to_real, LinearMap.zero_apply]
  ring

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- For a metric-compatible connection, the Weyl tensor is antisymmetric in its last pair of
arguments. -/
theorem IsMetricCompatible.weylTensor_antisymm_last
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (u v w z : TangentSpace I x) :
    cov.weylTensor x u v w z = -cov.weylTensor x u v z w := by
  rw [weylTensor_apply, weylTensor_apply,
    IsMetricCompatible.riemannCurvatureTensor_antisymm_last (cov := cov) hcov x u v w z,
    kulkarniNomizu_antisymm_last]
  ring

/-- For a metric-compatible torsion-free connection, the cyclic sum of the first three
arguments of the Weyl tensor vanishes. -/
theorem IsMetricCompatible.weylTensor_cyclic_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v w z : TangentSpace I x) :
    cov.weylTensor x u v w z + cov.weylTensor x v w u z + cov.weylTensor x w u v z = 0 := by
  have hP := isSymm_iff.mpr (IsMetricCompatible.schoutenTensor_isSymm (cov := cov) hcov ht x)
  have hg := isSymm_iff.mpr (isSymm_inner (E := TangentSpace I x))
  have hR := cov.riemannCurvatureTensor_cyclic_eq_zero ht x u v w z
  have hK := hP.kulkarniNomizu_cyclic_eq_zero hg u v w z
  simp only [weylTensor_apply]
  linear_combination hR - hK

/-- The Weyl tensor of a metric-compatible torsion-free connection is unchanged when its two
pairs of arguments are interchanged. -/
theorem IsMetricCompatible.weylTensor_swap_pairs
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v w z : TangentSpace I x) :
    cov.weylTensor x u v w z = cov.weylTensor x w z u v := by
  have hP := isSymm_iff.mpr (IsMetricCompatible.schoutenTensor_isSymm (cov := cov) hcov ht x)
  rw [weylTensor_apply, weylTensor_apply,
    IsMetricCompatible.riemannCurvatureTensor_swap_pairs (cov := cov) hcov ht x u v w z,
    hP.kulkarniNomizu_swap_pairs (isSymm_iff.mpr isSymm_inner)]

/-- In dimension `3`, the Weyl tensor of a metric-compatible connection vanishes. -/
theorem IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (hn : Module.finrank ℝ (TangentSpace I x) = 3) :
    cov.weylTensor x = 0 :=
  LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three
    (two_ne_zero (α := ℝ)).isUnit.isRegular.left
    (stdOrthonormalBasis ℝ (TangentSpace I x)).toBasis (by simpa using hn)
    (cov.weylTensor_antisymm_first x)
    (IsMetricCompatible.weylTensor_antisymm_last (cov := cov) hcov x)
    fun u v ↦ by
      simpa only [OrthonormalBasis.coe_toBasis] using
        cov.sum_weylTensor_eq_zero x (by omega) (stdOrthonormalBasis ℝ _) u v

/-- In dimension `3`, the curvature tensor of a metric-compatible connection is the
Kulkarni–Nomizu product `Rm = P ⊙ g` of its Schouten tensor with the metric, so it is determined
by the Ricci curvature. -/
theorem IsMetricCompatible.riemannCurvatureTensor_eq_kulkarniNomizu_of_finrank_eq_three
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (hn : Module.finrank ℝ (TangentSpace I x) = 3) (u v w z : TangentSpace I x) :
    cov.riemannCurvatureTensor x u v w z =
      kulkarniNomizu (cov.schoutenTensor x) (innerₗ _) u v w z := by
  have h := IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three (cov := cov) hcov x hn
  rw [← sub_eq_zero, ← weylTensor_apply, h]
  simp only [LinearMap.zero_apply]

end CovariantDerivative
