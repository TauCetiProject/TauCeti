/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.BaseChange
public import TauCeti.AlgebraicGeometry.Compactification.Refinement
public import TauCeti.AlgebraicGeometry.Compactification.Uniqueness
public import TauCeti.CategoryTheory.Filtered.Comparison

/-!
# Compactifications form a cofiltered category

The compactifications of a fixed morphism `f : X ⟶ S` form a cofiltered category, possibly
empty. Two compactifications are refined by their common refinement. Two parallel maps out of a
compactification `C` agree after precomposition with the map to `C` from the common refinement
of `C` with itself, because that refinement is dense and maps out of a dense compactification
are unique. The full subcategory of dense compactifications is cofiltered in the same way.
Both categories are cofiltered as soon as a compactification exists, for example by Nagata's
theorem for separated finite-type morphisms over a qcqs base.

Consequently a functor out of compactifications that sends every refinement map to an
isomorphism has canonical comparison isomorphisms between its values at any two
compactifications, `CategoryTheory.Functor.cofilteredComparison`. They may be computed through
any common refinement and satisfy the identity, inverse and cocycle laws. They are compatible
with base change, `Compactification.cofilteredComparison_hom_comp_app_baseChange`.

## References

* The Stacks Project, Lemma 38.32.1 (tag 0ATU), *Compactifications*.
* The Stacks Project, Lemma 63.9.1, for the use of refinements to compare constructions made
  from different compactifications.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Compactification

/-- Compactifications of a fixed morphism form a cofiltered category, possibly empty. -/
instance : IsCofilteredOrEmpty (Compactification f) where
  cone_objs C₁ C₂ := ⟨_, commonRefinementFst C₁ C₂, commonRefinementSnd C₁ C₂, trivial⟩
  cone_maps C _ _ _ := ⟨_, commonRefinementFst C C, hom_unique _ _⟩

instance [Nonempty (Compactification f)] : IsCofiltered (Compactification f) where

/-- The base-change law for comparison isomorphisms: comparisons between the values of a functor
on compactifications of `f` commute with a natural transformation to the corresponding functor
on the base-changed compactifications. -/
@[reassoc]
theorem cofilteredComparison_hom_comp_app_baseChange {T : Scheme.{u}} {𝒞 : Type*} [Category* 𝒞]
    (g : T ⟶ S) (F : Compactification f ⥤ 𝒞)
    [∀ (C D : Compactification f) (h : C ⟶ D), IsIso (F.map h)]
    (F' : Compactification (pullback.snd f g) ⥤ 𝒞)
    [∀ (C D : Compactification (pullback.snd f g)) (h : C ⟶ D), IsIso (F'.map h)]
    (τ : F ⟶ baseChangeFunctor g ⋙ F') (C₁ C₂ : Compactification f) :
    (F.cofilteredComparison C₁ C₂).hom ≫ τ.app C₂ =
      τ.app C₁ ≫ (F'.cofilteredComparison (C₁.baseChange g) (C₂.baseChange g)).hom :=
  F.cofilteredComparison_hom_comp_app (baseChangeFunctor g) F' τ C₁ C₂

end Compactification

namespace DenseCompactification

open Compactification

/-- Dense compactifications of a fixed morphism form a cofiltered category, possibly empty. -/
instance : IsCofilteredOrEmpty (DenseCompactification f) where
  cone_objs D₁ D₂ := ⟨_, (commonRefinementFan D₁ D₂).fst, (commonRefinementFan D₁ D₂).snd, trivial⟩
  cone_maps D _ _ _ := ⟨D, 𝟙 D, Subsingleton.elim _ _⟩

instance [h : Nonempty (Compactification f)] : IsCofiltered (DenseCompactification f) where
  nonempty := h.map fun C ↦ commonRefinement C C

end DenseCompactification

end TauCeti
