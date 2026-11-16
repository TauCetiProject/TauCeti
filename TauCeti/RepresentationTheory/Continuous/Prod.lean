/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Subrepresentation
public import TauCeti.RepresentationTheory.Continuous.Basic
public import TauCeti.LinearAlgebra.Quotient.Prod
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Products of continuous representations and intertwining maps

`ContRepresentation.prod` gives the componentwise action on the native topological product.
`ContIntertwiningMap.prodMap` is the corresponding block operator. Its kernel and quotient
cokernel are equivariantly linearly equivalent to the products of the original defects.
These comparisons retain the actual actions and impose no finite-dimensionality condition.

The constructions adapt the direct-sum proof in
[AtiyahSinger/Analysis/EquivariantIndexOperations.lean][source] from Lean-Atiyah-Singer,
using the native product and quotient equivalences.

[source]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/EquivariantIndexOperations.lean
-/

public section

open ContRepresentation

variable {R G E₁ E₂ F₁ F₂ : Type*} [Ring R] [Monoid G]
  [AddCommGroup E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [Module R E₁]
  [AddCommGroup E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂] [Module R E₂]
  [AddCommGroup F₁] [TopologicalSpace F₁] [IsTopologicalAddGroup F₁] [Module R F₁]
  [AddCommGroup F₂] [TopologicalSpace F₂] [IsTopologicalAddGroup F₂] [Module R F₂]

namespace ContRepresentation

/-- The componentwise action of a monoid on a product of topological modules. -/
def prod (π : ContRepresentation R G E₁) (ρ : ContRepresentation R G E₂) :
    ContRepresentation R G (E₁ × E₂) :=
  .ofMonoidHom
    { toFun := fun g ↦ (π g).prodMap (ρ g)
      map_one' := by ext x <;> simp
      map_mul' := by intro g h; ext x <;> simp [map_mul] }

/-- The product action operator is the product of the component action operators. -/
@[simp]
theorem prod_apply (π : ContRepresentation R G E₁) (ρ : ContRepresentation R G E₂) (g : G) :
    π.prod ρ g = (π g).prodMap (ρ g) := (rfl)

/-- Forgetting continuity of a product action gives the product of the forgotten actions. -/
@[simp]
theorem toRepresentation_prod (π : ContRepresentation R G E₁)
    (ρ : ContRepresentation R G E₂) :
    (π.prod ρ).toRepresentation = π.toRepresentation.prod ρ.toRepresentation := by
  ext g v <;> rfl

variable [TopologicalSpace G] in
/-- The product of strongly continuous representations is strongly continuous. -/
theorem continuous_prod_apply {π : ContRepresentation R G E₁}
    {ρ : ContRepresentation R G E₂}
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    (v : E₁ × E₂) : Continuous fun g ↦ π.prod ρ g v :=
  (hπ v.1).prodMk (hρ v.2)

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace G]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The product of representations continuous for the operator norm is continuous for that norm. -/
theorem continuous_prod (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
    (hπ : Continuous π) (hρ : Continuous ρ) : Continuous (π.prod ρ) := by
  exact (hπ.prod_mapL 𝕜 hρ).congr fun g ↦ (prod_apply π ρ g).symm

end ContRepresentation

namespace ContIntertwiningMap

variable {π₁ : ContRepresentation R G E₁} {π₂ : ContRepresentation R G E₂}
  {ρ₁ : ContRepresentation R G F₁} {ρ₂ : ContRepresentation R G F₂}

/-- The block operator formed from two continuous intertwining maps. -/
def prodMap (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) : π₁.prod π₂ →ⁱL ρ₁.prod ρ₂ where
  __ := T.toContinuousLinearMap.prodMap S.toContinuousLinearMap
  isIntertwining' g := by
    apply ContinuousLinearMap.ext
    intro v
    exact Prod.ext (T.isIntertwining g v.1) (S.isIntertwining g v.2)

/-- Forgetting equivariance of a block operator gives the native product operator. -/
@[simp]
theorem toContinuousLinearMap_prodMap (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) :
    (T.prodMap S).toContinuousLinearMap =
      T.toContinuousLinearMap.prodMap S.toContinuousLinearMap := (rfl)

/-- A product of intertwining maps acts componentwise. -/
@[simp]
theorem prodMap_apply (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) (v : E₁ × E₂) :
    T.prodMap S v = (T v.1, S v.2) := by
  rw [← toContinuousLinearMap_apply, toContinuousLinearMap_prodMap]
  rfl

/-- The kernel representation of a block operator is equivalent to the product of its kernels,
via the identity on the underlying pair of vectors. -/
def kerProdEquiv (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) :
    Representation.Equiv (T.prodMap S).kerRepresentation.toRepresentation
      (T.kerRepresentation.prod S.kerRepresentation).toRepresentation := by
  let e : (T.prodMap S).toContinuousLinearMap.ker ≃ₗ[R]
      T.toContinuousLinearMap.ker × S.toContinuousLinearMap.ker :=
    (LinearEquiv.ofEq _ _ (by
    rw [toContinuousLinearMap_prodMap, ContinuousLinearMap.coe_prodMap,
      LinearMap.ker_prodMap])).trans
    (Submodule.prodEquiv T.toContinuousLinearMap.ker S.toContinuousLinearMap.ker)
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro v
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [e, ContRepresentation.toMonoidHom_apply]

/-- The kernel product comparison preserves the underlying pair of vectors. -/
@[simp]
theorem coe_kerProdEquiv_apply (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂)
    (v : (T.prodMap S).toContinuousLinearMap.ker) :
    (((T.kerProdEquiv S v).1 : E₁), ((T.kerProdEquiv S v).2 : E₂)) = (v : E₁ × E₂) := by
  simp [kerProdEquiv]

/-- The quotient cokernel of a block operator is equivariantly equivalent to the product of
its quotient cokernels. The map sends the class of a pair to the pair of its classes. -/
def cokerProdEquiv (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) :
    Representation.Equiv (T.prodMap S).cokerRepresentation.toRepresentation
      (T.cokerRepresentation.prod S.cokerRepresentation).toRepresentation := by
  let e : ((F₁ × F₂) ⧸ (T.prodMap S).toContinuousLinearMap.range) ≃ₗ[R]
      (F₁ ⧸ T.toContinuousLinearMap.range) × (F₂ ⧸ S.toContinuousLinearMap.range) :=
    (Submodule.quotEquivOfEq _ _ (by
    rw [toContinuousLinearMap_prodMap, ContinuousLinearMap.coe_prodMap,
      LinearMap.range_prodMap])).trans
    (Submodule.quotientProdEquiv T.toContinuousLinearMap.range S.toContinuousLinearMap.range)
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v => simp [e, ContRepresentation.toMonoidHom_apply]

/-- The cokernel product comparison sends a quotient representative to its component classes. -/
@[simp]
theorem cokerProdEquiv_apply_mk (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) (v : F₁ × F₂) :
    T.cokerProdEquiv S (Submodule.Quotient.mk v) =
      (Submodule.Quotient.mk v.1, Submodule.Quotient.mk v.2) := by
  simp [cokerProdEquiv]

end ContIntertwiningMap
