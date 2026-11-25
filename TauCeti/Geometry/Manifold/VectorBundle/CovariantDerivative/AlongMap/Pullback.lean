/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Pullback
/-!
# The pullback of a covariant derivative

For a continuous map `f : N → M` and a covariant derivative `cov` on a vector bundle `B` over
`M`, a section of the pullback bundle `f *ᵖ B` is a section of `B` along `f`, and covariant
differentiation along `f` (`CovariantDerivative.alongMap`) is a covariant derivative on
`f *ᵖ B`: `CovariantDerivative.pullback cov f`. For an isometric immersion `f` of Riemannian
manifolds and the Levi-Civita connection of the target, this is the pullback ambient connection
on `f *ᵖ TM` from which the second fundamental form, the shape operator and the normal
connection are obtained.

The differentiability hypotheses of a covariant derivative concern the total-space section
`T% σ` of the pullback bundle. In the preferred trivialization of the pullback bundle, which is the
pullback of the preferred trivialization of `B` at `f x`, its coordinate reading agrees near `x`
with the coordinate reading `sectionCoord` used by `alongMap`
(`TauCeti.Manifold.mdifferentiableAt_sectionCoord_of_mdifferentiableAt_pullback`). Hence the
additivity and Leibniz laws of `alongMap` give those of the pullback.

## Main declarations

* `CovariantDerivative.pullback`: the pullback of a covariant derivative along a continuous map.
* `CovariantDerivative.pullback_apply`: it is covariant differentiation along the map.
* `CovariantDerivative.pullback_apply_comp`: on a pulled-back section it is the ambient covariant
  derivative composed with the differential of the map.

## References

* C. Bär, [*Differential Geometry*, Section 2.4, Proposition 2.4.4]
  (https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Lehrmaterialien/DiffGeo.pdf):
  covariant differentiation of vector fields along maps.
-/

public section
open Bundle
open scoped Manifold Topology
noncomputable section
namespace CovariantDerivative
open TauCeti.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [FiniteDimensional 𝕜 F₀]
  {B : M → Type*} [TopologicalSpace (TotalSpace F₀ B)]
  [∀ x, AddCommGroup (B x)] [∀ x, Module 𝕜 (B x)] [∀ x, TopologicalSpace (B x)]
  [∀ x, IsTopologicalAddGroup (B x)] [∀ x, ContinuousSMul 𝕜 (B x)]
  [FiberBundle F₀ B] [VectorBundle 𝕜 F₀ B] [ContMDiffVectorBundle 1 F₀ B I]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N]

variable (cov : CovariantDerivative I F₀ B) (f : C(N, M))

/-- The pullback of a covariant derivative `cov` on `B` along a continuous map `f`: the covariant
derivative on the pullback bundle `f *ᵖ B` given by covariant differentiation along `f`. -/
def pullback : CovariantDerivative J F₀ ((f : N → M) *ᵖ B) where
  toFun σ x := cov.alongMap J f σ x
  isCovariantDerivativeOnUniv :=
    { add := fun hσ hσ' _ ↦ cov.alongMap_add f _ _
        (mdifferentiableAt_sectionCoord_of_mdifferentiableAt_pullback f hσ)
        (mdifferentiableAt_sectionCoord_of_mdifferentiableAt_pullback f hσ')
      leibniz := fun hσ hg _ ↦ cov.alongMap_smul f _ _ hg
        (mdifferentiableAt_sectionCoord_of_mdifferentiableAt_pullback f hσ) }

/-- The pullback of a covariant derivative is covariant differentiation along the map. -/
@[simp]
theorem pullback_apply (σ : ∀ x, ((f : N → M) *ᵖ B) x) (x : N) :
    cov.pullback (J := J) f σ x = cov.alongMap J f σ x :=
  (rfl)

/-- For a map differentiable at `x` and a section of `B` differentiable into the total space at
`f x`, the pullback covariant derivative of the pulled-back section is the covariant derivative of
the section composed with the differential of the map. -/
theorem pullback_apply_comp {X : ∀ y, B y} {x : N} (hf : MDifferentiableAt J I f x)
    (hX : MDifferentiableAt I (I.prod 𝓘(𝕜, F₀)) (T% X) (f x)) :
    cov.pullback (J := J) f (fun y ↦ X (f y)) x = (cov X (f x)).comp (mfderiv J I f x) :=
  cov.alongMap_pullback f hf hX

end CovariantDerivative
