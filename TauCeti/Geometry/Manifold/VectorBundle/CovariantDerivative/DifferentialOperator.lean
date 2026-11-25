/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# Covariant derivatives as first-order differential operators on smooth sections

Let `∇` be a smooth connection on a vector bundle `V` over a `C¹` manifold `M`. Both the full
bundled connection `∇ : Cₛ^∞(V) →ₗ[𝕜] Cₛ^∞(Hom(TM, V))`
(`CovariantDerivative.smoothCovariantDerivative`) and the directional covariant derivative `∇_X`
along a smooth vector field `X` (`CovariantDerivative.alongVectorField`) are first-order
differential operators in Grothendieck's sense (`TauCeti.differentialOperators`): by the Leibniz
rule, `[∇, f] σ = df • σ` and `[∇_X, a] σ = X(a) σ`.

## Main results

* `CovariantDerivative.smulCommutator_smoothCovariantDerivative_apply` and
  `CovariantDerivative.smoothCovariantDerivative_mem_differentialOperators_one`: `[∇, f] σ x v =
  df(v) • σ x`, so `∇` has differential-operator order at most one.
* `CovariantDerivative.alongVectorField_mem_differentialOperators_one`: `∇_X` is a differential
  operator of order at most one.
* `CovariantDerivative.tsupport_alongVectorField_apply_subset`: `∇_X` does not enlarge supports.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped ContDiff Manifold

namespace CovariantDerivative

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- The commutator `[∇, f] σ` acts on `v` by `df(v) • σ x`: the principal symbol of `∇`. -/
theorem smulCommutator_smoothCovariantDerivative_apply
    (f : C^∞⟮I, M; 𝕜⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) (v : TangentSpace I x) :
    smulCommutator 𝕜 f cov.smoothCovariantDerivative σ x v = d% f x v • σ x := by
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    sub_apply, ContMDiffSection.smul_apply, smul_apply,
    smoothCovariantDerivative_smul, add_sub_cancel_left]

/-- A smooth covariant derivative has differential-operator order at most `1`. -/
theorem smoothCovariantDerivative_mem_differentialOperators_one :
    cov.smoothCovariantDerivative ∈
      differentialOperators 𝕜 C^∞⟮I, M; 𝕜⟯ Cₛ^∞⟮I; F, V⟯
        Cₛ^∞⟮I; E →L[𝕜] F, fun x ↦ TangentSpace I x →L[𝕜] V x⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦
    mem_differentialOperators_zero_iff.2 fun g σ ↦ ContMDiffSection.ext fun x ↦ ?_
  ext v
  simp only [ContMDiffSection.smul_apply, smul_apply,
    smulCommutator_smoothCovariantDerivative_apply, smul_comm (d% f x v) (g x)]

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative along a smooth vector field is a differential operator of order at
most one: its commutator with multiplication by `a` is multiplication by `X(a)`. -/
theorem alongVectorField_mem_differentialOperators_one :
    cov.alongVectorField X ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun a ↦
    mem_differentialOperators_zero_iff.2 fun b σ ↦ ContMDiffSection.ext fun x ↦ ?_
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, alongVectorField_smul]
  module

variable [FiniteDimensional ℝ E] [T2Space M]

/-- The covariant derivative along a smooth vector field does not enlarge supports. -/
theorem tsupport_alongVectorField_apply_subset (σ : Cₛ^∞⟮I; F, V⟯) :
    (cov.alongVectorField X σ).tsupport ⊆ σ.tsupport :=
  tsupport_differentialOperators_section_apply_subset
    (cov.alongVectorField_mem_differentialOperators_one X) σ

end Real

end CovariantDerivative
