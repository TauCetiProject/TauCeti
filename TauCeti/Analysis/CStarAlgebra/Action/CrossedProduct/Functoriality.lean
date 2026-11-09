/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap

/-!
# Functoriality of full crossed products

An equivariant nonunital coefficient homomorphism induces a nonunital star-algebra
homomorphism of full crossed products. On compactly supported coefficients it acts pointwise.
The induced maps preserve identities and composition, and pulling back a covariant pair
commutes with its extended integrated form.

We use the full-seminorm estimate `Hom.fullSeminorm_convolutionMap_le` to extend the
compact-support map by continuity. Both coefficient algebras lie in the same universe, so the
source and target full seminorms use the same indexing universe for covariant representations.
No nondegeneracy, unitality, separability or global σ-finiteness is assumed.

## Main definitions and results

* `TauCeti.CStarAction.Hom.fullCrossedProductMap`: the induced homomorphism.
* `TauCeti.CStarAction.Hom.fullCrossedProductMap_of`: its compact-support formula.
* `TauCeti.CStarAction.Hom.fullCrossedProductMap_id` and
  `TauCeti.CStarAction.Hom.fullCrossedProductMap_comp`: the functor laws.
* `TauCeti.CStarAction.CovariantRepresentation.integratedFull_fullCrossedProductMap_apply`:
  compatibility with
  integration of covariant pairs.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for functoriality of full
crossed products. The constructions extend Tau Ceti's `Hom.convolutionMap` and use
`CovariantRepresentation.comap` for the universal-seminorm estimate.
-/

public section

noncomputable section

open MeasureTheory UniformSpace

namespace TauCeti.CStarAction

universe u v

variable {G : Type u} {A B C : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}
  (μ : Measure G) [μ.IsHaarMeasure]

namespace Hom

open FullCrossedProduct

variable (φ : Hom α β)

/-- The nonunital star-algebra homomorphism of full crossed products induced by an equivariant
coefficient homomorphism. Its value on compact-support coefficients is given by
`fullCrossedProductMap_of`. -/
def fullCrossedProductMap : FullCrossedProduct α μ →⋆ₙₐ[ℂ] FullCrossedProduct β μ :=
  lift ((of β μ).comp (φ.convolutionMap μ))
    (fun f => by simpa using φ.fullSeminorm_convolutionMap_le μ f)

/-- The induced full crossed-product map acts pointwise on compact-support coefficients. -/
@[simp]
theorem fullCrossedProductMap_of (f : ConvolutionAlgebra α μ) :
    φ.fullCrossedProductMap μ (of α μ f) = of β μ (φ.convolutionMap μ f) :=
  lift_of _ _ f

/-- The compact-support inclusion is natural under equivariant coefficient maps. -/
@[simp]
theorem fullCrossedProductMap_comp_of :
    (φ.fullCrossedProductMap μ).comp (of α μ) = (of β μ).comp (φ.convolutionMap μ) :=
  NonUnitalStarAlgHom.ext (φ.fullCrossedProductMap_of μ)

/-- The identity coefficient map induces the identity on the full crossed product. -/
@[simp]
theorem fullCrossedProductMap_id :
    (Hom.id α).fullCrossedProductMap μ = NonUnitalStarAlgHom.id ℂ (FullCrossedProduct α μ) := by
  apply FullCrossedProduct.starAlgHom_ext
  ext f
  simp

/-- Induced full crossed-product maps preserve composition. -/
@[simp]
theorem fullCrossedProductMap_comp (ψ : Hom β γ) :
    (ψ.comp φ).fullCrossedProductMap μ =
      (ψ.fullCrossedProductMap μ).comp (φ.fullCrossedProductMap μ) := by
  apply FullCrossedProduct.starAlgHom_ext
  ext f
  simp

end Hom

namespace CovariantRepresentation

variable {H : Type (max u v)} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (P : CovariantRepresentation β H) (φ : Hom α β)

/-- Pulling back a covariant pair commutes with integrating it on the full crossed product. -/
@[simp]
theorem integratedFull_comp_fullCrossedProductMap :
    (P.integratedFull μ).comp (φ.fullCrossedProductMap μ) = (P.comap φ).integratedFull μ := by
  apply FullCrossedProduct.starAlgHom_ext
  apply NonUnitalStarAlgHom.ext
  intro f
  simpa only [NonUnitalStarAlgHom.comp_apply, Hom.fullCrossedProductMap_of,
    integratedFull_of, integratedStarAlgHom_apply] using
    (P.integratedOperator_comap φ μ f).symm

/-- The value of an integrated form after applying the induced full crossed-product map is
the integrated form of the pulled-back pair. -/
@[simp]
theorem integratedFull_fullCrossedProductMap_apply (x : FullCrossedProduct α μ) :
    P.integratedFull μ (φ.fullCrossedProductMap μ x) = (P.comap φ).integratedFull μ x :=
  DFunLike.congr_fun (P.integratedFull_comp_fullCrossedProductMap μ φ) x

end CovariantRepresentation

end TauCeti.CStarAction
