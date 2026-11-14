/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Counit
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Unit

/-!
# The biequivalence between equivariant groupoid lifts and normalized transports

Normalizing an equivariant groupoid lift `L` conjugates its joint functors by chosen quasi-inverses
of its prescribed-fiber comparisons, giving the pseudofunctor `normalizationPseudofunctor actions`
from `EquivariantGroupoidLift Γ actions` to the locally discrete bicategory
`LocallyDiscrete (NormalizedTransport Γ actions)`. Reconstructing a lift with identity fiber
comparisons gives the pseudofunctor `reconstructionPseudofunctor actions` in the opposite direction.

Combining the unit equivalence
`normalizationUnitEquiv actions :
  Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions)`
with the counit equivalence
`normalizationCounitEquiv actions :
  (reconstructionPseudofunctor actions).comp (normalizationPseudofunctor actions) ≌
    Pseudofunctor.id (LocallyDiscrete (NormalizedTransport Γ actions))`
packages these mutually quasi-inverse constructions into `normalizationBiequivalence actions`.

## Main definitions

* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): biequivalences, strong transformations, and
  pointwise equivalences in pseudofunctor bicategories.
* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103 (2007): equivariant families of categories over parameter groupoids.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The biequivalence between the bicategory of equivariant groupoid lifts and the locally discrete
bicategory of normalized transports on the prescribed fibers. -/
-- Expose the projections so the unit and counit equations can refer to `functor` and `inverse`.
@[expose] noncomputable def normalizationBiequivalence :
    TauCeti.Biequivalence (EquivariantGroupoidLift Γ actions)
      (LocallyDiscrete (NormalizedTransport Γ actions)) where
  functor := normalizationPseudofunctor actions
  inverse := reconstructionPseudofunctor actions
  unitEquiv := normalizationUnitEquiv actions
  counitEquiv := normalizationCounitEquiv actions

@[simp]
lemma normalizationBiequivalence_functor :
    (normalizationBiequivalence actions).functor = normalizationPseudofunctor actions :=
  (rfl)

@[simp]
lemma normalizationBiequivalence_inverse :
    (normalizationBiequivalence actions).inverse = reconstructionPseudofunctor actions :=
  (rfl)

@[simp]
lemma normalizationBiequivalence_unitEquiv :
    (normalizationBiequivalence actions).unitEquiv = normalizationUnitEquiv actions :=
  (rfl)

@[simp]
lemma normalizationBiequivalence_counitEquiv :
    (normalizationBiequivalence actions).counitEquiv = normalizationCounitEquiv actions :=
  (rfl)

end TauCeti.EquivariantGroupoidLift
