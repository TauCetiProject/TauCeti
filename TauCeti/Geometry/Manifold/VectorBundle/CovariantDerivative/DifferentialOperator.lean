/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.DiracType
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The covariant derivative along a vector field is a first-order differential operator

Let `∇` be a smooth connection on a vector bundle `V` over a smooth manifold `M`, and let `X` be a
smooth vector field. The covariant derivative along `X`, `∇_X σ = ∇σ(X)`
(`CovariantDerivative.alongVectorField`), is a first-order differential operator on the smooth
sections of `V` in Grothendieck's sense: by the Leibniz rule `∇_X (a σ) = a ∇_X σ + X(a) σ`
(`CovariantDerivative.alongVectorField_smul`), its commutator with multiplication by a smooth
function `a` is multiplication by `X(a)`. In particular `∇_X` does not enlarge supports, and its
geometric principal symbol is `σ_geom(∇_X)(ξ) = ξ(X) Id`.

If every tangent vector is `v = ⟪X, v⟫ X`, as for a unit vector field on a one-dimensional
Riemannian manifold such as the rotation field of the circle, then `ξ(X)² = ‖ξ‖²` for every
covector `ξ`, so `∇_X` is of Dirac type for every fibre metric on `V`.

## Main results

* `CovariantDerivative.alongVectorField_mem_differentialOperators_one`: `∇_X` is a differential
  operator of order at most one.
* `CovariantDerivative.tsupport_alongVectorField_apply_subset`: `∇_X` does not enlarge supports.
* `CovariantDerivative.sectionPrincipalSymbol_alongVectorField`: the principal symbol of `∇_X` is
  `ξ ↦ ξ(X) Id`.
* `CovariantDerivative.isDiracType_alongVectorField`: if `X` spans every tangent line with unit
  length, then `∇_X` is of Dirac type.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

noncomputable section

open Bundle TauCeti Riemannian.Tensor
open scoped ContDiff Manifold RealInnerProductSpace

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

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- **The principal symbol of `∇_X`.** The geometric principal symbol of the covariant derivative
along a smooth vector field `X` is `σ_geom(∇_X)(ξ) = ξ(X) Id`. -/
@[simp]
theorem sectionPrincipalSymbol_alongVectorField {x : M} (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
        ⟨cov.alongVectorField X, cov.alongVectorField_mem_differentialOperators_one X⟩ ξ =
      ξ (X x) • LinearMap.id := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv_of_order_one,
    alongVectorField_smul, add_sub_cancel_left, LinearMap.smul_apply, LinearMap.id_apply]

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- **`∇_X` is of Dirac type along a field spanning every tangent line with unit length.** If at
every interior point each tangent vector is `v = ⟪X, v⟫ X`, then `ξ(X)² = ‖ξ‖²` for every covector
`ξ`, and the principal symbol `ξ(X) Id` of `∇_X` satisfies the Clifford relation
`σ(ξ)* σ(ξ) = ‖ξ‖² Id` for every fibre metric on `V`. -/
theorem isDiracType_alongVectorField
    (hX : ∀ x, I.IsInteriorPoint x → ∀ v : TangentSpace I x, v = ⟪X x, v⟫ • X x) :
    IsDiracType ⟨cov.alongVectorField X, cov.alongVectorField_mem_differentialOperators_one X⟩ := by
  refine isDiracType_iff.2 fun x hx ξ v w ↦ ?_
  -- With `u = ξ♯`, the hypothesis `u = ⟪X, u⟫ X` gives `‖ξ‖² = ⟪u, u⟫ = ⟪u, X⟫² = ξ(X)²`.
  have hξ : ‖ξ‖ ^ 2 = ξ (X x) ^ 2 := by
    rw [norm_sq_eq_apply_rieszDual, hX x hx (rieszDual (I := I) x ξ), map_smul, smul_eq_mul,
      real_inner_comm, inner_rieszDual, sq]
  simp only [sectionPrincipalSymbol_alongVectorField, LinearMap.smul_apply, LinearMap.id_apply,
    real_inner_smul_left, real_inner_smul_right, hξ]
  ring

end CovariantDerivative
