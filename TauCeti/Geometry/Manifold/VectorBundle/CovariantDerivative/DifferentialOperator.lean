/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# The covariant derivative along a vector field is a first-order differential operator

Let `∇` be a smooth connection on a vector bundle `V` over a smooth manifold `M`, and let `X` be a
smooth vector field. The covariant derivative along `X`, `∇_X σ = ∇σ(X)`
(`CovariantDerivative.alongVectorField`), is a first-order differential operator on the smooth
sections of `V` in Grothendieck's sense: by the Leibniz rule `∇_X (a σ) = a ∇_X σ + X(a) σ`
(`CovariantDerivative.alongVectorField_smul`), its commutator with multiplication by a smooth
function `a` is multiplication by `X(a)`. In particular `∇_X` does not enlarge supports.

## Main results

* `CovariantDerivative.alongVectorField_mem_differentialOperators_one`: `∇_X` is a differential
  operator of order at most one.
* `CovariantDerivative.tsupport_alongVectorField_apply_subset`: `∇_X` does not enlarge supports.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped ContDiff Manifold

namespace CovariantDerivative

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

end CovariantDerivative
