/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Decomposition
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Pointwise algebraic curvature tensors and isometric frame pullbacks on manifolds

At each point `x` of a Riemannian manifold, the metric-lowered curvature of a smooth connection on
the tangent bundle defines a continuous four-tensor
`CovariantDerivative.curvatureFourTensor cov x : TauCeti.FourTensor (TangentSpace I x)` with

`cov.curvatureFourTensor x ![u, v, z, w] = ⟪cov.curvatureTensor x u v w, z⟫`.

For a metric-compatible torsion-free connection (in particular for the Levi-Civita connection),
this four-tensor belongs to `TauCeti.FourTensor.algebraicCurvatureSubmodule (TangentSpace I x)`,
and its algebraic invariants (`ricci`, `scalar`, `schouten`, `weyl`, `curvatureOperator`, and the
Rayleigh quotient against `constantCurvature`) agree with the geometric curvature tensors
(`ricciTensor`, `scalarCurvature`, `schoutenTensor`, `weylTensor`, `curvatureEndomorphism`, and
`sectionalCurvature`).

Pulling `curvatureFourTensor x` back along a linear isometric frame
`ι : V ≃ₗᵢ[ℝ] TangentSpace I x` transports the pointwise curvature into the fixed finite-dimensional
vector space `TauCeti.FourTensor.algebraicCurvatureSubmodule V`. Two isometric frames at `x` differ
by an orthogonal transformation of `V`, so membership of the pulled-back curvature in any
`O(V)`-invariant subset (such as an `O(V)`-invariant curvature cone) is independent of the chosen
isometric frame. Along `C^k` frame families, the pulled-back curvature map into `FourTensor V` and
`algebraicCurvatureSubmodule V` is `C^k`; moreover, for a finite-regularity `C^(k + 2)` Riemannian
metric on a `C^(k + 3)` manifold, the Levi-Civita curvature pairings in any `C^(k + 2)` local frame
already have regularity `C^k`.

Finally, `Bundle.ContMDiffRiemannianMetric` is equipped with direct metric-indexed curvature entry
points (`ricciTensor`, `sectionalCurvature`, `curvatureFourTensor`, and
`pullbackAlgebraicCurvature`) complementing the existing
`Bundle.ContMDiffRiemannianMetric.scalarCurvature` and
`Bundle.ContMDiffRiemannianMetric.IsConstantCurvatureTensor`.

## Main definitions

* `TauCeti.FourTensor.algebraicCurvatureCompCLM`: continuous linear pullback of
  `algebraicCurvatureSubmodule` along a continuous linear map.
* `CovariantDerivative.curvatureFourTensor`: the `(0, 4)` curvature tensor at `x` as an element of
  `FourTensor (TangentSpace I x)`.
* `CovariantDerivative.IsMetricCompatible.pullbackAlgebraicCurvature`: pullback of the pointwise
  curvature of a metric-compatible torsion-free connection along `ι : V ≃ₗᵢ[ℝ] TangentSpace I x`
  into `algebraicCurvatureSubmodule V`.
* `CovariantDerivative.localFrameCurvatureFourTensor`: the `FourTensor V` of the Levi-Civita
  `curvatureOperator` in a local frame on an open set, defined for finite-regularity metrics.
* `Bundle.ContMDiffRiemannianMetric.ricciTensor`,
  `Bundle.ContMDiffRiemannianMetric.sectionalCurvature`,
  `Bundle.ContMDiffRiemannianMetric.curvatureFourTensor`, and
  `Bundle.ContMDiffRiemannianMetric.pullbackAlgebraicCurvature`.

## Main results

* `CovariantDerivative.IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor`, together with
  dictionary lemmas identifying `ricci`, `scalar`, `schouten`, `weyl`, `curvatureOperator`, and
  `sectionalCurvature`.
* `CovariantDerivative.IsMetricCompatible.pullbackAlgebraicCurvature_mem_iff_of_orthogonalInvariant`
  shows that
  membership in an `O(V)`-invariant set of `algebraicCurvatureSubmodule V` does not depend on the
  choice of isometric frame `ι : V ≃ₗᵢ[ℝ] TangentSpace I x`.
* `CovariantDerivative.contMDiffWithinAt_curvatureFourTensor_frame` and
  `CovariantDerivative.IsMetricCompatible.contMDiffWithinAt_algebraicCurvature_frame`: `C^k`
  regularity of frame pullbacks.
* `CovariantDerivative.contMDiffOn_inner_curvatureOperator_leviCivitaConnection` and
  `CovariantDerivative.contMDiffOn_localFrameCurvatureFourTensor_leviCivitaConnection`: `C^k`
  regularity of local-frame curvature components for a `C^(k + 2)` metric on a `C^(k + 3)` manifold.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), §§1.G–1.H.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176,
  Springer (2018), Chs. 7–8.
-/

public section

open Bundle FiberBundle Set VectorField
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace TauCeti.FourTensor

section PullbackSubmodule

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Pullback of algebraic curvature tensors along a continuous linear map `f : W →L[ℝ] V`, bundled
as a continuous linear map between the curvature submodules. -/
def algebraicCurvatureCompCLM (f : W →L[ℝ] V) :
    algebraicCurvatureSubmodule V →L[ℝ] algebraicCurvatureSubmodule W :=
  ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ : Fin 4 ↦ f).comp
    (algebraicCurvatureSubmodule V).subtypeL).codRestrict (algebraicCurvatureSubmodule W)
    fun r ↦ compContinuousLinearMap_mem_algebraicCurvatureSubmodule r.2 f

/-- Coercion of `algebraicCurvatureCompCLM f r` to `FourTensor W` is precomposition with `f` in
all four slots. -/
@[simp]
theorem coe_algebraicCurvatureCompCLM (f : W →L[ℝ] V) (r : algebraicCurvatureSubmodule V) :
    (algebraicCurvatureCompCLM f r : FourTensor W) =
      r.1.compContinuousLinearMap fun _ ↦ f :=
  (rfl)

/-- Pulling back algebraic curvature tensors along the identity map is the identity. -/
@[simp]
theorem algebraicCurvatureCompCLM_id :
    algebraicCurvatureCompCLM (ContinuousLinearMap.id ℝ V) = ContinuousLinearMap.id ℝ _ := by
  ext r m
  simp

/-- Contravariant functoriality of `algebraicCurvatureCompCLM` under composition. -/
theorem algebraicCurvatureCompCLM_comp (f : W →L[ℝ] V) (g : U →L[ℝ] W) :
    algebraicCurvatureCompCLM (f.comp g) =
      (algebraicCurvatureCompCLM g).comp (algebraicCurvatureCompCLM f) := by
  ext r m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

end PullbackSubmodule

section SmoothnessCriteria

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]

/-- Basis four-tensor `(m₀, m₁, m₂, m₃) ↦ ∏ j, coord(idx j)(m j)` on a finite-dimensional real
normed space `V`. -/
private def basisFourTensor (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    (idx : Fin 4 → Fin (Module.finrank ℝ V)) : FourTensor V :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).compContinuousLinearMap
    fun j ↦ (b.coord (idx j)).toContinuousLinearMap

private theorem eq_sum_basisFourTensor (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    (r : FourTensor V) :
    r = ∑ idx : Fin 4 → Fin (Module.finrank ℝ V),
      r (fun j ↦ b (idx j)) • basisFourTensor b idx := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (fun _ : Fin 4 ↦ b) fun v ↦ ?_
  change r (fun i ↦ b (v i)) =
    (∑ idx, r (fun j ↦ b (idx j)) • basisFourTensor b idx) (fun i ↦ b (v i))
  rw [sum_apply, Finset.sum_eq_single v]
  · simp only [smul_apply, basisFourTensor,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, List.ofFn_zero,
      List.prod_cons, List.prod_nil, mul_one, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul]
  · intro idx _ hne
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    simp only [smul_apply, basisFourTensor,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, List.ofFn_zero,
      List.prod_cons, List.prod_nil, mul_one, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
    fin_cases j <;> (dsimp at hj; simp [Finsupp.single_eq_of_ne hj])
  · intro hv
    exact absurd (Finset.mem_univ v) hv

/-- A map into `FourTensor V` (with `V` finite-dimensional) is `C^k` within `s` at `p` as soon as
its evaluations on all fixed quadruples `(u, v, z, w)` are `C^k`. -/
theorem contMDiffWithinAt_of_apply {k : ℕ∞ω} {Φ : P → FourTensor V} {s : Set P} {p : P}
    (hΦ : ∀ u v z w : V, ContMDiffWithinAt J 𝓘(ℝ) k (fun q ↦ Φ q ![u, v, z, w]) s p) :
    ContMDiffWithinAt J 𝓘(ℝ, FourTensor V) k Φ s p := by
  let b := Module.finBasis ℝ V
  have hfun : Φ = fun q ↦ ∑ idx : Fin 4 → Fin (Module.finrank ℝ V),
      Φ q ![b (idx 0), b (idx 1), b (idx 2), b (idx 3)] • basisFourTensor b idx := by
    funext q
    conv_lhs => rw [eq_sum_basisFourTensor b (Φ q)]
    refine Finset.sum_congr rfl fun idx _ ↦ ?_
    have htuple : (fun j : Fin 4 ↦ b (idx j)) = ![b (idx 0), b (idx 1), b (idx 2), b (idx 3)] := by
      funext j; fin_cases j <;> rfl
    rw [htuple]
  rw [hfun]
  exact ContMDiffWithinAt.sum fun idx _ ↦
    (hΦ (b (idx 0)) (b (idx 1)) (b (idx 2)) (b (idx 3))).smul contMDiffWithinAt_const

/-- A map into `algebraicCurvatureSubmodule V` (with `V` finite-dimensional) is `C^k` within `s` at
`p` as soon as its underlying `FourTensor V`-valued map is `C^k`. -/
theorem contMDiffWithinAt_algebraicCurvatureSubmodule {k : ℕ∞ω}
    {ψ : P → algebraicCurvatureSubmodule V} {s : Set P} {p : P}
    (hψ : ContMDiffWithinAt J 𝓘(ℝ, FourTensor V) k (fun q ↦ (ψ q : FourTensor V)) s p) :
    ContMDiffWithinAt J 𝓘(ℝ, algebraicCurvatureSubmodule V) k ψ s p := by
  let b := Module.finBasis ℝ V
  obtain ⟨rCompl, hrCompl⟩ := (algebraicCurvatureSubmodule V).exists_isCompl
  let proj := (algebraicCurvatureSubmodule V).projectionOnto rCompl hrCompl
  have hfun : ψ = fun q ↦ ∑ idx : Fin 4 → Fin (Module.finrank ℝ V),
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 ↦ V) ℝ (fun j ↦ b (idx j))
        (ψ q : FourTensor V)) • proj (basisFourTensor b idx) := by
    funext q
    have hq := ((algebraicCurvatureSubmodule V).projectionOnto_apply_left hrCompl (ψ q)).symm
    conv_lhs => rw [hq, eq_sum_basisFourTensor b (ψ q : FourTensor V)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun idx _ ↦ proj.map_smul _ _
  rw [hfun]
  refine ContMDiffWithinAt.sum fun idx _ ↦ ?_
  let evL := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 ↦ V) ℝ (fun j ↦ b (idx j))
  exact (((evL.contDiff.contMDiff.of_le le_top).contMDiffAt).comp_contMDiffWithinAt p hψ).smul
    contMDiffWithinAt_const

end SmoothnessCriteria

end TauCeti.FourTensor

namespace CovariantDerivative

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- The `(0, 4)` curvature tensor of a smooth connection at `x` packaged as a continuous four-tensor
`TauCeti.FourTensor (TangentSpace I x)`, with convention
`cov.curvatureFourTensor x ![u, v, z, w] = ⟪cov.curvatureTensor x u v w, z⟫`. -/
def curvatureFourTensor (x : M) : TauCeti.FourTensor (TangentSpace I x) :=
  TauCeti.FourTensor.ofLinearMap₄ <|
    LinearMap.mk₂ ℝ
      (fun u v ↦ (cov.riemannCurvatureTensor x u v).flip)
      (fun u₁ u₂ v ↦ by ext z w; simp)
      (fun c u v ↦ by ext z w; simp)
      (fun u v₁ v₂ ↦ by ext z w; simp)
      (fun c u v ↦ by ext z w; simp)

/-- `curvatureFourTensor` agrees with `riemannCurvatureTensor` with its last two arguments swapped
to match the `FourTensor` convention `r(u, v, z, w) = ⟪R(u, v)w, z⟫`. -/
theorem curvatureFourTensor_eq_riemannCurvatureTensor (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = cov.riemannCurvatureTensor x u v w z := by
  simp [curvatureFourTensor]

/-- Evaluation of `curvatureFourTensor` on `(u, v, z, w)`. -/
@[simp]
theorem curvatureFourTensor_apply (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = ⟪cov.curvatureTensor x u v w, z⟫ := by
  rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor, cov.riemannCurvatureTensor_apply]

/-- `curvatureFourTensor` is always antisymmetric in its first pair of arguments. -/
theorem curvatureFourTensor_antisymm_first (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = -cov.curvatureFourTensor x ![v, u, z, w] := by
  simp_rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor]
  exact cov.riemannCurvatureTensor_antisymm_first x u v w z

/-- The algebraic Ricci contraction of `curvatureFourTensor` is `cov.ricciTensor`. -/
@[simp]
theorem ricci_curvatureFourTensor (x : M) :
    TauCeti.FourTensor.ricci (cov.curvatureFourTensor x) = cov.ricciTensor x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  ext u v
  rw [TauCeti.FourTensor.ricci_apply_orthonormalBasis b,
    cov.ricciTensor_eq_sum_riemannCurvatureTensor x b]
  simp_rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor]

/-- The algebraic scalar contraction of `curvatureFourTensor` is `cov.scalarCurvature`. -/
@[simp]
theorem scalar_curvatureFourTensor (x : M) :
    TauCeti.FourTensor.scalar (cov.curvatureFourTensor x) = cov.scalarCurvature x := by
  rw [TauCeti.FourTensor.scalar_apply, cov.ricci_curvatureFourTensor, cov.scalarCurvature_apply]

/-- The algebraic Schouten form of `curvatureFourTensor` is `cov.schoutenTensor`. -/
@[simp]
theorem schouten_curvatureFourTensor (x : M) :
    TauCeti.FourTensor.schouten (cov.curvatureFourTensor x) = cov.schoutenTensor x := by
  ext u v
  rw [TauCeti.FourTensor.schouten_apply_apply, cov.ricci_curvatureFourTensor,
    cov.scalar_curvatureFourTensor, cov.schoutenTensor_apply]

/-- Away from dimension `2`, the algebraic Weyl component of `curvatureFourTensor` evaluates to
`cov.weylTensor`. -/
theorem weyl_curvatureFourTensor_apply (x : M)
    (hn : Module.finrank ℝ (TangentSpace I x) ≠ 2) (u v z w : TangentSpace I x) :
    TauCeti.FourTensor.weyl (cov.curvatureFourTensor x) ![u, v, z, w] =
      cov.weylTensor x u v w z := by
  rw [TauCeti.FourTensor.weyl_eq_sub_kulkarniNomizu_schouten hn,
    sub_apply, cov.curvatureFourTensor_eq_riemannCurvatureTensor,
    TauCeti.FourTensor.kulkarniNomizu_apply_eq, cov.schouten_curvatureFourTensor,
    cov.weylTensor_apply]

section MetricCompatible

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- For a metric-compatible connection, `curvatureFourTensor` is antisymmetric in its last pair of
arguments. -/
theorem IsMetricCompatible.curvatureFourTensor_antisymm_last
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = -cov.curvatureFourTensor x ![u, v, w, z] := by
  simp_rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor]
  exact IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x u v w z

/-- **The curvature four-tensor of a metric-compatible torsion-free connection is an algebraic
curvature tensor at every point.** -/
theorem IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) :
    TauCeti.FourTensor.IsAlgebraicCurvature (cov.curvatureFourTensor x) where
  antisymm_first := cov.curvatureFourTensor_antisymm_first x
  antisymm_last := IsMetricCompatible.curvatureFourTensor_antisymm_last cov hcov x
  swap_pairs u v z w := by
    simp_rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor]
    rw [IsMetricCompatible.riemannCurvatureTensor_swap_pairs cov hcov ht x u v w z,
      cov.riemannCurvatureTensor_antisymm_first x w z u v,
      IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x z w u v, neg_neg]
  cyclic_eq_zero u v z w := by
    have h := cov.riemannCurvatureTensor_cyclic_eq_zero ht x u v z w
    rw [IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x u v z w,
      IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x v z u w,
      IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x z u v w] at h
    simp only [curvatureFourTensor_eq_riemannCurvatureTensor]
    linear_combination -h

/-- The bivector curvature operator of `cov.curvatureFourTensor x` agrees with
`cov.curvatureEndomorphism hcov x`. -/
@[simp]
theorem curvatureOperator_curvatureFourTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) :
    TauCeti.FourTensor.curvatureOperator (cov.curvatureFourTensor x) =
      cov.curvatureEndomorphism hcov x := by
  symm
  rw [cov.curvatureEndomorphism_eq_iff hcov x]
  intro u v
  have hu : u = ![u 0, u 1] := (FinVec.etaExpand_eq u).symm
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  conv_lhs => rw [hu, hv]
  rw [TauCeti.FourTensor.inner_curvatureOperator_ιMulti_of_antisymm
      (cov.curvatureFourTensor_antisymm_first x)
      (IsMetricCompatible.curvatureFourTensor_antisymm_last cov hcov x),
    cov.curvatureFourTensor_apply]

/-- Sectional curvature is the ratio of `curvatureFourTensor` to `constantCurvature` on
`(u, v, u, v)`. -/
theorem sectionalCurvature_eq_curvatureFourTensor_div_constantCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (u v : TangentSpace I x) :
    cov.sectionalCurvature hcov x u v =
      cov.curvatureFourTensor x ![u, v, u, v] /
        TauCeti.FourTensor.constantCurvature (TangentSpace I x) ![u, v, u, v] := by
  rw [cov.sectionalCurvature_apply, Matrix.real_det_gram_fin_two,
    real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v,
    TauCeti.FourTensor.constantCurvature_apply_self, cov.curvatureFourTensor_apply]

/-- Pullback of the pointwise curvature of a metric-compatible torsion-free connection along a
linear isometric frame `ι : V ≃ₗᵢ[ℝ] TangentSpace I x` into
`TauCeti.FourTensor.algebraicCurvatureSubmodule V`. -/
def IsMetricCompatible.pullbackAlgebraicCurvature {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (ι : V ≃ₗᵢ[ℝ] TangentSpace I x) :
    TauCeti.FourTensor.algebraicCurvatureSubmodule V :=
  ⟨(cov.curvatureFourTensor x).compContinuousLinearMap
      fun _ ↦ ι.toLinearIsometry.toContinuousLinearMap,
    TauCeti.FourTensor.mem_algebraicCurvatureSubmodule.mpr <|
      (IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor cov hcov ht
        x).compContinuousLinearMap ι.toLinearIsometry.toContinuousLinearMap⟩

/-- Evaluating `IsMetricCompatible.pullbackAlgebraicCurvature` on `![u, v, z, w]` gives the metric
inner product `⟪cov.curvatureTensor x (ι u) (ι v) (ι w), ι z⟫`. -/
@[simp]
theorem IsMetricCompatible.coe_pullbackAlgebraicCurvature_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (ι : V ≃ₗᵢ[ℝ] TangentSpace I x) (u v z w : V) :
    (IsMetricCompatible.pullbackAlgebraicCurvature cov hcov ht x ι : TauCeti.FourTensor V)
        ![u, v, z, w] =
      ⟪cov.curvatureTensor x (ι u) (ι v) (ι w), ι z⟫ := by
  rw [IsMetricCompatible.pullbackAlgebraicCurvature, Submodule.coe_mk,
    TauCeti.FourTensor.compContinuousLinearMap_apply_vec, cov.curvatureFourTensor_apply]
  rfl

/-- Changing the isometric frame at `x` from `ι₁` to `ι₂` transforms
`pullbackAlgebraicCurvature` by the orthogonal transformation `ι₂.trans ι₁.symm ∈ O(V)`. -/
theorem IsMetricCompatible.pullbackAlgebraicCurvature_change_frame {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (ι₁ ι₂ : V ≃ₗᵢ[ℝ] TangentSpace I x) :
    IsMetricCompatible.pullbackAlgebraicCurvature cov hcov ht x ι₂ =
      TauCeti.FourTensor.algebraicCurvatureCompCLM
        (ι₂.trans ι₁.symm).toLinearIsometry.toContinuousLinearMap
        (IsMetricCompatible.pullbackAlgebraicCurvature cov hcov ht x ι₁) := by
  ext m
  simp only [TauCeti.FourTensor.coe_algebraicCurvatureCompCLM,
    IsMetricCompatible.pullbackAlgebraicCurvature,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Frame independence for `O(V)`-invariant curvature sets and cones**: if a subset
`S : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V)` is stable under the pullback action of
`V ≃ₗᵢ[ℝ] V`, then whether `pullbackAlgebraicCurvature` lies in `S` does not depend on the choice
of isometric frame `ι : V ≃ₗᵢ[ℝ] TangentSpace I x`. -/
theorem IsMetricCompatible.pullbackAlgebraicCurvature_mem_iff_of_orthogonalInvariant {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) {S : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V)}
    (hS : ∀ (g : V ≃ₗᵢ[ℝ] V) (r : TauCeti.FourTensor.algebraicCurvatureSubmodule V),
      r ∈ S → TauCeti.FourTensor.algebraicCurvatureCompCLM
        g.toLinearIsometry.toContinuousLinearMap r ∈ S)
    (x : M) (ι₁ ι₂ : V ≃ₗᵢ[ℝ] TangentSpace I x) :
    IsMetricCompatible.pullbackAlgebraicCurvature cov hcov ht x ι₁ ∈ S ↔
      IsMetricCompatible.pullbackAlgebraicCurvature cov hcov ht x ι₂ ∈ S := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [IsMetricCompatible.pullbackAlgebraicCurvature_change_frame cov hcov ht x ι₁ ι₂]
    exact hS (ι₂.trans ι₁.symm) _ h
  · rw [IsMetricCompatible.pullbackAlgebraicCurvature_change_frame cov hcov ht x ι₂ ι₁]
    exact hS (ι₁.trans ι₂.symm) _ h

end MetricCompatible

/-! ### `C^k` dependence of frame pullbacks of curvature -/

section SmoothFramePullback

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]
  {k : ℕ∞ω} [IsContMDiffRiemannianBundle I k E (TangentSpace I : M → Type _)]
  {f : P → M} {L : ∀ p, V →L[ℝ] TangentSpace I (f p)}

/-- Pulling `cov.curvatureFourTensor` back along a family of continuous linear maps
`L : ∀ p, V →L[ℝ] TangentSpace I (f p)` whose vector evaluations have `C^k` tangent-bundle lifts
gives a `C^k` map into `FourTensor V` within `s` at `p`, for `k ≤ ∞`. -/
theorem contMDiffWithinAt_curvatureFourTensor_frame {s : Set P} {p : P} (hk : k ≤ ∞)
    (hL : ∀ u : V, ContMDiffWithinAt J I.tangent k
      (fun q ↦ TotalSpace.mk' E (f q) (L q u)) s p) :
    ContMDiffWithinAt J 𝓘(ℝ, TauCeti.FourTensor V) k
      (fun q ↦ (cov.curvatureFourTensor (f q)).compContinuousLinearMap fun _ ↦ L q) s p := by
  refine TauCeti.FourTensor.contMDiffWithinAt_of_apply fun u v z w ↦ ?_
  have hcurv := cov.contMDiffWithinAt_curvatureTensor hk (hL u) (hL v) (hL w)
  have hinner := ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) (b := f) hcurv (hL z)
  have hfun : (fun q ↦
      ((cov.curvatureFourTensor (f q)).compContinuousLinearMap fun _ ↦ L q) ![u, v, z, w]) =
      fun q ↦ ⟪cov.curvatureTensor (f q) (L q u) (L q v) (L q w), L q z⟫ := by
    funext q
    rw [TauCeti.FourTensor.compContinuousLinearMap_apply_vec, cov.curvatureFourTensor_apply]
  rw [hfun]
  exact hinner

/-- Pointwise `ContMDiffAt` form of `contMDiffWithinAt_curvatureFourTensor_frame`. -/
theorem contMDiffAt_curvatureFourTensor_frame {p : P} (hk : k ≤ ∞)
    (hL : ∀ u : V, ContMDiffAt J I.tangent k (fun q ↦ TotalSpace.mk' E (f q) (L q u)) p) :
    ContMDiffAt J 𝓘(ℝ, TauCeti.FourTensor V) k
      (fun q ↦ (cov.curvatureFourTensor (f q)).compContinuousLinearMap fun _ ↦ L q) p := by
  rw [← contMDiffWithinAt_univ] at *
  exact cov.contMDiffWithinAt_curvatureFourTensor_frame hk fun u ↦ hL u

/-- Set-wise `ContMDiffOn` form of `contMDiffWithinAt_curvatureFourTensor_frame`. -/
theorem contMDiffOn_curvatureFourTensor_frame {s : Set P} (hk : k ≤ ∞)
    (hL : ∀ u : V, ContMDiffOn J I.tangent k (fun q ↦ TotalSpace.mk' E (f q) (L q u)) s) :
    ContMDiffOn J 𝓘(ℝ, TauCeti.FourTensor V) k
      (fun q ↦ (cov.curvatureFourTensor (f q)).compContinuousLinearMap fun _ ↦ L q) s :=
  fun p hp ↦ cov.contMDiffWithinAt_curvatureFourTensor_frame hk fun u ↦ hL u p hp

/-- Global `ContMDiff` form of `contMDiffWithinAt_curvatureFourTensor_frame`. -/
theorem contMDiff_curvatureFourTensor_frame (hk : k ≤ ∞)
    (hL : ∀ u : V, ContMDiff J I.tangent k (fun q ↦ TotalSpace.mk' E (f q) (L q u))) :
    ContMDiff J 𝓘(ℝ, TauCeti.FourTensor V) k
      (fun q ↦ (cov.curvatureFourTensor (f q)).compContinuousLinearMap fun _ ↦ L q) :=
  fun p ↦ cov.contMDiffAt_curvatureFourTensor_frame hk fun u ↦ hL u p

/-- For a metric-compatible torsion-free connection, pulling `cov.curvatureFourTensor` back along a
`C^k` frame family gives a `C^k` map into `TauCeti.FourTensor.algebraicCurvatureSubmodule V`. -/
theorem IsMetricCompatible.contMDiffWithinAt_algebraicCurvature_frame
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) {s : Set P} {p : P} (hk : k ≤ ∞)
    (hL : ∀ u : V, ContMDiffWithinAt J I.tangent k
      (fun q ↦ TotalSpace.mk' E (f q) (L q u)) s p) :
    ContMDiffWithinAt J 𝓘(ℝ, TauCeti.FourTensor.algebraicCurvatureSubmodule V) k
      (fun q ↦ (⟨(cov.curvatureFourTensor (f q)).compContinuousLinearMap fun _ ↦ L q,
        TauCeti.FourTensor.mem_algebraicCurvatureSubmodule.mpr <|
          (IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor cov hcov ht
            (f q)).compContinuousLinearMap (L q)⟩ :
        TauCeti.FourTensor.algebraicCurvatureSubmodule V)) s p :=
  TauCeti.FourTensor.contMDiffWithinAt_algebraicCurvatureSubmodule
    (cov.contMDiffWithinAt_curvatureFourTensor_frame hk hL)

/-- Set-wise `ContMDiffOn` form of
`IsMetricCompatible.contMDiffWithinAt_algebraicCurvature_frame`. -/
theorem IsMetricCompatible.contMDiffOn_algebraicCurvature_frame
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) {s : Set P} (hk : k ≤ ∞)
    (hL : ∀ u : V, ContMDiffOn J I.tangent k (fun q ↦ TotalSpace.mk' E (f q) (L q u)) s) :
    ContMDiffOn J 𝓘(ℝ, TauCeti.FourTensor.algebraicCurvatureSubmodule V) k
      (fun q ↦ (⟨(cov.curvatureFourTensor (f q)).compContinuousLinearMap fun _ ↦ L q,
        TauCeti.FourTensor.mem_algebraicCurvatureSubmodule.mpr <|
          (IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor cov hcov ht
            (f q)).compContinuousLinearMap (L q)⟩ :
        TauCeti.FourTensor.algebraicCurvatureSubmodule V)) s :=
  fun p hp ↦ IsMetricCompatible.contMDiffWithinAt_algebraicCurvature_frame cov hcov ht hk
    fun u ↦ hL u p hp

end SmoothFramePullback

end Pointwise

/-! ### Finite-regularity `C^k` curvature in local frames for `C^(k + 2)` metrics -/

section FiniteRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Finite-regularity curvature smoothness**: on a `C^m` manifold with a `C^r` Riemannian metric,
once `k + 3 ≤ m` and `k + 2 ≤ r`, the Levi-Civita `curvatureOperator` of three `C^(k + 2)` vector
fields on an open set `u` is a `C^k` vector field on `u`. -/
theorem contMDiffOn_curvatureOperator_leviCivitaConnection {k m r : ℕ∞ω}
    [IsManifold I m M] [IsContMDiffRiemannianBundle I r E (fun x : M ↦ TangentSpace I x)]
    {u : Set M} (hu : IsOpen u) (hm : k + 3 ≤ m) (hr : k + 2 ≤ r)
    {X Y W : Π x : M, TangentSpace I x}
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (X y)) u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (Y y)) u)
    (hW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (W y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) k
      (fun y ↦ TotalSpace.mk' E y ((leviCivitaConnection I M).curvatureOperator X Y W y)) u := by
  have hm1 : (k + 1) + 2 ≤ m := by
    calc (k + 1) + 2 = k + (1 + 2) := add_assoc k 1 2
      _ = k + 3 := by norm_num
      _ ≤ m := hm
  have hr1 : (k + 1) + 1 ≤ r := by
    calc (k + 1) + 1 = k + (1 + 1) := add_assoc k 1 1
      _ = k + 2 := by norm_num
      _ ≤ r := hr
  have hm0 : k + 2 ≤ m := (show k + 2 ≤ k + 3 by gcongr; norm_num).trans hm
  have hr0 : k + 1 ≤ r := (show k + 1 ≤ k + 2 by gcongr; norm_num).trans hr
  have hW1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((k + 1) + 1)
      (fun y ↦ TotalSpace.mk' E y (W y)) u := by
    rwa [add_assoc, one_add_one_eq_two]
  have hcovW := contMDiffOn_leviCivitaConnection hu hm1 hr1 hW1
  have hX1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 1) (fun y ↦ TotalSpace.mk' E y (X y)) u :=
    hX.of_le (by gcongr; norm_num)
  have hY1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) u :=
    hY.of_le (by gcongr; norm_num)
  have hX0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) k (fun y ↦ TotalSpace.mk' E y (X y)) u :=
    hX.of_le le_self_add
  have hY0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) k (fun y ↦ TotalSpace.mk' E y (Y y)) u :=
    hY.of_le le_self_add
  have hYW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 1)
      (fun y ↦ TotalSpace.mk' E y (leviCivitaConnection I M W y (Y y))) u :=
    hcovW.clm_bundle_apply hY1
  have hXW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 1)
      (fun y ↦ TotalSpace.mk' E y (leviCivitaConnection I M W y (X y))) u :=
    hcovW.clm_bundle_apply hX1
  have hXYW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) k
      (fun y ↦ TotalSpace.mk' E y
        (leviCivitaConnection I M (fun z ↦ leviCivitaConnection I M W z (Y z)) y (X y))) u :=
    (contMDiffOn_leviCivitaConnection hu hm0 hr0 hYW).clm_bundle_apply hX0
  have hYXW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) k
      (fun y ↦ TotalSpace.mk' E y
        (leviCivitaConnection I M (fun z ↦ leviCivitaConnection I M W z (X z)) y (Y y))) u :=
    (contMDiffOn_leviCivitaConnection hu hm0 hr0 hXW).clm_bundle_apply hY0
  have hman_succ : IsManifold I ((k + 1) + 1 + 1) M := by
    refine IsManifold.of_le (n := m) ?_
    calc (k + 1) + 1 + 1 = k + (1 + 1 + 1) := by simp only [add_assoc]
      _ = k + 3 := by norm_num
      _ ≤ m := hm
  have hmin : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := 2) (by simp)
  have hX1' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((k + 1) + 1)
      (fun y ↦ TotalSpace.mk' E y (X y)) u := by
    rwa [add_assoc, one_add_one_eq_two]
  have hY1' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((k + 1) + 1)
      (fun y ↦ TotalSpace.mk' E y (Y y)) u := by
    rwa [add_assoc, one_add_one_eq_two]
  have hbr : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 1)
      (fun y ↦ TotalSpace.mk' E y (mlieBracket I X Y y)) u := by
    have hbrw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 1)
        (fun y ↦ TotalSpace.mk' E y (mlieBracketWithin I X Y u y)) u := fun y hy ↦
      (hX1' y hy).mlieBracketWithin_vectorField (hY1' y hy) hu.uniqueMDiffOn hy (by simp)
    exact hbrw.congr fun y hy ↦ by rw [mlieBracketWithin_of_isOpen hu hy]
  have hbrW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) k
      (fun y ↦ TotalSpace.mk' E y (leviCivitaConnection I M W y (mlieBracket I X Y y))) u :=
    (hcovW.of_le le_self_add).clm_bundle_apply (hbr.of_le le_self_add)
  have _ : ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I :=
    have : IsManifold I (k + 1) M :=
      IsManifold.of_le (n := m) ((show k + 1 ≤ k + 2 by gcongr; norm_num).trans hm0)
    TangentBundle.contMDiffVectorBundle
  exact ((hXYW.sub_section hYXW).sub_section hbrW).congr fun y _ ↦
    congrArg (TotalSpace.mk' E y) (by simp only [curvatureOperator_apply, Pi.sub_apply])

/-- On a `C^m` manifold with a `C^r` Riemannian metric (`k + 3 ≤ m`, `k + 2 ≤ r`), the
metric-lowered Levi-Civita curvature pairing `x ↦ ⟪R(X, Y)W x, Z x⟫` of four `C^(k + 2)` vector
fields on an open set `u` is `C^k` on `u`. -/
theorem contMDiffOn_inner_curvatureOperator_leviCivitaConnection {k m r : ℕ∞ω}
    [IsManifold I m M] [IsContMDiffRiemannianBundle I r E (fun x : M ↦ TangentSpace I x)]
    {u : Set M} (hu : IsOpen u) (hm : k + 3 ≤ m) (hr : k + 2 ≤ r)
    {X Y Z W : Π x : M, TangentSpace I x}
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (X y)) u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (Y y)) u)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (Z y)) u)
    (hW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (W y)) u) :
    ContMDiffOn I 𝓘(ℝ) k
      (fun y ↦ ⟪(leviCivitaConnection I M).curvatureOperator X Y W y, Z y⟫) u := by
  have hmetric : IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := r) (le_self_add.trans hr)
  have hcurv := contMDiffOn_curvatureOperator_leviCivitaConnection hu hm hr hX hY hW
  intro y hy
  exact ContMDiffWithinAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := id) (hcurv y hy) ((hZ.of_le le_self_add) y hy)

variable (I) in
/-- Given a basis `b : Module.Basis ι ℝ V` of a finite-dimensional normed space `V` and a family of
vector fields `s : ι → Π x : M, TangentSpace I x`, `localFrameCurvatureFourTensor I b s x` is the
four-tensor on `V` whose values on basis vectors are
`⟪(leviCivitaConnection I M).curvatureOperator (s i) (s j) (s w) x, s z x⟫`. -/
def localFrameCurvatureFourTensor {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (b : Module.Basis ι ℝ V) (s : ι → Π x : M, TangentSpace I x)
    (x : M) : TauCeti.FourTensor V :=
  TauCeti.FourTensor.ofLinearMap₄ <|
    b.constr ℝ fun i ↦ b.constr ℝ fun j ↦ b.constr ℝ fun z ↦ b.constr ℝ fun w ↦
      ⟪(leviCivitaConnection I M).curvatureOperator (s i) (s j) (s w) x, s z x⟫

/-- On basis elements of `b`, `localFrameCurvatureFourTensor I b s x` evaluates to the metric
pairing of the Levi-Civita `curvatureOperator` on the frame sections `s`. -/
@[simp]
theorem localFrameCurvatureFourTensor_basis {V ι : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (b : Module.Basis ι ℝ V)
    (s : ι → Π x : M, TangentSpace I x) (x : M) (i j z w : ι) :
    localFrameCurvatureFourTensor I b s x ![b i, b j, b z, b w] =
      ⟪(leviCivitaConnection I M).curvatureOperator (s i) (s j) (s w) x, s z x⟫ := by
  simp [localFrameCurvatureFourTensor]

private theorem linearMap_apply_eq_sum_repr {V α ι : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommMonoid α] [Module ℝ α] [Fintype ι] (b : Module.Basis ι ℝ V) (L : V →ₗ[ℝ] α) (v : V) :
    L v = ∑ i, b.repr v i • L (b i) := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ L.map_smul _ _

/-- **Local-frame `FourTensor V` regularity for `C^(k + 2)` metrics**: if `s` is a family of
`C^(k + 2)` vector fields on an open set `u` (for example a `C^(k + 2)` local orthonormal frame of
a `C^(k + 2)` metric), then `localFrameCurvatureFourTensor I b s` is `C^k` on `u`. -/
theorem contMDiffOn_localFrameCurvatureFourTensor_leviCivitaConnection
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {k m r : ℕ∞ω} [IsManifold I m M]
    [IsContMDiffRiemannianBundle I r E (fun x : M ↦ TangentSpace I x)]
    (b : Module.Basis ι ℝ V) {s : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hu : IsOpen u) (hm : k + 3 ≤ m) (hr : k + 2 ≤ r)
    (hs : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) (k + 2) (fun y ↦ TotalSpace.mk' E y (s i y)) u) :
    ContMDiffOn I 𝓘(ℝ, TauCeti.FourTensor V) k (localFrameCurvatureFourTensor I b s) u := by
  let _ : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  intro x hx
  refine TauCeti.FourTensor.contMDiffWithinAt_of_apply fun v₀ v₁ v₂ v₃ ↦ ?_
  let T (y : M) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    b.constr ℝ fun i ↦ b.constr ℝ fun j ↦ b.constr ℝ fun z ↦ b.constr ℝ fun w ↦
      ⟪(leviCivitaConnection I M).curvatureOperator (s i) (s j) (s w) y, s z y⟫
  have hexp (y : M) : localFrameCurvatureFourTensor I b s y ![v₀, v₁, v₂, v₃] =
      ∑ i, ∑ j, ∑ z, ∑ w,
        b.repr v₀ i * b.repr v₁ j * b.repr v₂ z * b.repr v₃ w *
          ⟪(leviCivitaConnection I M).curvatureOperator (s i) (s j) (s w) y, s z y⟫ := by
    change TauCeti.FourTensor.ofLinearMap₄ (T y) ![v₀, v₁, v₂, v₃] = _
    rw [TauCeti.FourTensor.ofLinearMap₄_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [linearMap_apply_eq_sum_repr b (T y) v₀]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [linearMap_apply_eq_sum_repr b (T y (b i)) v₁]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [linearMap_apply_eq_sum_repr b (T y (b i) (b j)) v₂]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [linearMap_apply_eq_sum_repr b (T y (b i) (b j) (b z)) v₃]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    simp only [T, Module.Basis.constr_basis, smul_eq_mul]
    ring
  simp only [hexp]
  exact ContMDiffWithinAt.sum fun i _ ↦ ContMDiffWithinAt.sum fun j _ ↦
    ContMDiffWithinAt.sum fun z _ ↦ ContMDiffWithinAt.sum fun w _ ↦
      contMDiffWithinAt_const.mul
        (contMDiffOn_inner_curvatureOperator_leviCivitaConnection hu hm hr
          (hs i) (hs j) (hs z) (hs w) x hx)

/-- For a smooth metric and a local family of smooth vector fields `s` on an open set `u`,
`localFrameCurvatureFourTensor I b s x` agrees on `u` with pulling `curvatureFourTensor x` back
along `b.constr ℝ (fun i ↦ s i x)`. -/
theorem localFrameCurvatureFourTensor_eq_compContinuousLinearMap
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [T2Space M] [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (b : Module.Basis ι ℝ V) {s : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hu : IsOpen u)
    (hs : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (s i y)) u)
    {x : M} (hx : x ∈ u) :
    localFrameCurvatureFourTensor I b s x =
      ((leviCivitaConnection I M).curvatureFourTensor x).compContinuousLinearMap
        fun _ ↦ (b.constr ℝ fun i ↦ s i x).toContinuousLinearMap := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (fun _ : Fin 4 ↦ b) fun idx ↦ ?_
  have htuple : (fun l : Fin 4 ↦ b (idx l)) =
      ![b (idx 0), b (idx 1), b (idx 2), b (idx 3)] := by
    funext l; fin_cases l <;> rfl
  change localFrameCurvatureFourTensor I b s x (fun l ↦ b (idx l)) =
    (((leviCivitaConnection I M).curvatureFourTensor x).compContinuousLinearMap
      fun _ ↦ (b.constr ℝ fun i ↦ s i x).toContinuousLinearMap) (fun l ↦ b (idx l))
  rw [htuple, localFrameCurvatureFourTensor_basis,
    TauCeti.FourTensor.compContinuousLinearMap_apply_vec]
  simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.constr_basis,
    curvatureFourTensor_apply]
  rw [(leviCivitaConnection I M).curvatureTensor_apply_of_contMDiffOn x hu hx
    (hs (idx 0)) (hs (idx 1)) (hs (idx 3))]

end FiniteRegularity

end CovariantDerivative

/-! ### Metric-indexed curvature API on `Bundle.ContMDiffRiemannianMetric` -/

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The Ricci tensor of a smooth Riemannian metric `g`: the Ricci tensor of its Levi-Civita
connection. -/
def ricciTensor (x : M) : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).ricciTensor x

/-- Definitional unfolding of `Bundle.ContMDiffRiemannianMetric.ricciTensor`. -/
theorem ricciTensor_def (x : M) :
    g.ricciTensor x =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x :=
  (rfl)

/-- If the installed fibre metric is `g`, `g.ricciTensor` is that of the Levi-Civita connection. -/
theorem ricciTensor_eq_ricciTensor_leviCivitaConnection
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (x : M) :
    g.ricciTensor x = (CovariantDerivative.leviCivitaConnection I M).ricciTensor x := by
  obtain ⟨_⟩ := inst
  subst hg
  rfl

/-- The Ricci tensor of a smooth Riemannian metric is symmetric. -/
theorem ricciTensor_comm (x : M) (u v : TangentSpace I x) :
    g.ricciTensor x u v = g.ricciTensor x v u := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact CovariantDerivative.IsMetricCompatible.ricciTensor_comm
    (CovariantDerivative.leviCivitaConnection I M)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I)
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) x u v

/-- The sectional curvature of a smooth Riemannian metric `g` at `x` on spanning vectors `u, v`. -/
def sectionalCurvature (x : M) (u v : TangentSpace I x) : ℝ :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v

/-- Definitional unfolding of `Bundle.ContMDiffRiemannianMetric.sectionalCurvature`. -/
theorem sectionalCurvature_def (x : M) (u v : TangentSpace I x) :
    g.sectionalCurvature x u v =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v :=
  (rfl)

/-- If the installed fibre metric is `g`, `g.sectionalCurvature` agrees with the sectional
curvature of the Levi-Civita connection. -/
theorem sectionalCurvature_eq_sectionalCurvature_leviCivitaConnection
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (x : M) (u v : TangentSpace I x) :
    g.sectionalCurvature x u v =
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v := by
  obtain ⟨_⟩ := inst
  subst hg
  rfl

/-- The `(0, 4)` curvature four-tensor of a smooth Riemannian metric `g` at `x`. -/
def curvatureFourTensor (x : M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    TauCeti.FourTensor (TangentSpace I x) :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).curvatureFourTensor x

/-- `g.curvatureFourTensor x` is an algebraic curvature tensor for `g`. -/
theorem isAlgebraicCurvature_curvatureFourTensor (x : M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    TauCeti.FourTensor.IsAlgebraicCurvature (g.curvatureFourTensor x) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact CovariantDerivative.IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor
    (CovariantDerivative.leviCivitaConnection I M)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I)
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) x

/-- The Ricci contraction of `g.curvatureFourTensor x` is `g.ricciTensor x`. -/
@[simp]
theorem ricci_curvatureFourTensor (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      TauCeti.FourTensor.ricci (g.curvatureFourTensor x)) = g.ricciTensor x := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).ricci_curvatureFourTensor x

/-- The scalar contraction of `g.curvatureFourTensor x` is `g.scalarCurvature x`. -/
@[simp]
theorem scalar_curvatureFourTensor (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      TauCeti.FourTensor.scalar (g.curvatureFourTensor x)) = g.scalarCurvature x := by
  rw [g.scalarCurvature_def]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).scalar_curvatureFourTensor x

/-- `g` has constant-curvature tensor `κ` if and only if `g.curvatureFourTensor x` equals
`κ • constantCurvature` at every point `x`. -/
theorem isConstantCurvatureTensor_iff_curvatureFourTensor_eq (κ : ℝ) :
    g.IsConstantCurvatureTensor κ ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      ∀ x : M, g.curvatureFourTensor x =
        κ • TauCeti.FourTensor.constantCurvature (TangentSpace I x) := by
  rw [g.isConstantCurvatureTensor_iff]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  refine ⟨fun h x ↦ ?_, fun h x w u v ↦ ?_⟩
  · ext m
    have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
    rw [hm, curvatureFourTensor, CovariantDerivative.curvatureFourTensor_apply, smul_apply,
      smul_eq_mul]
    exact TauCeti.FourTensor.inner_eq_mul_constantCurvature (h x) (m 0) (m 1) (m 2) (m 3)
  · refine ext_inner_right ℝ fun z ↦ ?_
    have hx := congrArg (fun r : TauCeti.FourTensor (TangentSpace I x) ↦ r ![w, u, z, v]) (h x)
    rw [curvatureFourTensor, CovariantDerivative.curvatureFourTensor_apply, smul_apply,
      TauCeti.FourTensor.constantCurvature_apply, smul_eq_mul] at hx
    rw [hx, real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    ring

/-- Pullback of the curvature of a smooth Riemannian metric `g` at `x` along a continuous linear
frame `L : V →L[ℝ] TangentSpace I x` into `TauCeti.FourTensor.algebraicCurvatureSubmodule V`. Note
that neither `L` nor the codomain depends on installing `g` as a typeclass instance. -/
def pullbackAlgebraicCurvature {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : M) (L : V →L[ℝ] TangentSpace I x) :
    TauCeti.FourTensor.algebraicCurvatureSubmodule V :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  ⟨(g.curvatureFourTensor x).compContinuousLinearMap fun _ ↦ L,
    TauCeti.FourTensor.mem_algebraicCurvatureSubmodule.mpr <|
      (g.isAlgebraicCurvature_curvatureFourTensor x).compContinuousLinearMap L⟩

/-- Evaluating `g.pullbackAlgebraicCurvature x L` on `![u, v, z, w]` gives the `g`-inner product
of the Levi-Civita curvature `(leviCivitaConnection I M).curvatureTensor x (L u) (L v) (L w)` with
`L z`. -/
@[simp]
theorem coe_pullbackAlgebraicCurvature_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : M) (L : V →L[ℝ] TangentSpace I x) (u v z w : V) :
    (g.pullbackAlgebraicCurvature x L : TauCeti.FourTensor V) ![u, v, z, w] =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      g.inner x
        ((CovariantDerivative.leviCivitaConnection I M).curvatureTensor x (L u) (L v) (L w))
        (L z) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [pullbackAlgebraicCurvature, Submodule.coe_mk,
    TauCeti.FourTensor.compContinuousLinearMap_apply_vec, curvatureFourTensor,
    CovariantDerivative.curvatureFourTensor_apply]
  exact g.inner_riemannianBundle x _ _

/-- Along any `C^k` frame family `L : ∀ p, V →L[ℝ] TangentSpace I (f p)` (`k ≤ ∞`),
`p ↦ g.pullbackAlgebraicCurvature (f p) (L p)` is `C^k`. -/
theorem contMDiffOn_pullbackAlgebraicCurvature {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    {P : Type*} [TopologicalSpace P] [ChartedSpace K P]
    {k : ℕ∞ω} (hk : k ≤ ∞) {f : P → M} {L : ∀ p, V →L[ℝ] TangentSpace I (f p)} {s : Set P}
    (hL : ∀ u : V, ContMDiffOn J I.tangent k (fun q ↦ TotalSpace.mk' E (f q) (L q u)) s) :
    ContMDiffOn J 𝓘(ℝ, TauCeti.FourTensor.algebraicCurvatureSubmodule V) k
      (fun q ↦ g.pullbackAlgebraicCurvature (f q) (L q)) s := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) hk
  exact CovariantDerivative.IsMetricCompatible.contMDiffOn_algebraicCurvature_frame
    (CovariantDerivative.leviCivitaConnection I M)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I)
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) hk hL

end Bundle.ContMDiffRiemannianMetric
