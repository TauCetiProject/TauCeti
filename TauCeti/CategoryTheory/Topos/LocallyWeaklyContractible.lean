/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.CategoryTheory.Topos.Quasicompact

/-!
# Locally weakly contractible topoi

An object `U` of a topos is *weakly contractible* when every epimorphism onto `U` splits. Since
epimorphisms of a topos are stable under base change, these are exactly the projective objects,
and we use Mathlib's `CategoryTheory.Projective`. A topos is *locally weakly contractible* when
every object is covered by coherent (quasicompact and quasiseparated) weakly contractible
objects. The pro-étale topos of a scheme is the motivating example.

In a locally weakly contractible topos, sections over the coherent weakly contractible objects
detect epimorphisms (`TauCeti.Topos.IsLocallyWeaklyContractible.epi_iff_exists_lift`). This is
the hypothesis under which Bhatt and Scholze show that a topos is replete, so that inverse limits
of sheaves behave as in the category of sets, and that the free abelian sheaves on its coherent
weakly contractible objects compactly generate its derived category: sections over them are exact,
and commute with direct sums by quasicompactness. Coherence is part of the definition for this
second application; it is stronger than asking for a cover by weakly contractible objects alone.

The definitions make sense in any category, in which covers are effective epimorphic families,
as for `TauCeti.Topos.IsQuasicompact`. In a Grothendieck topos every epimorphism is effective, and
a cover is the same as an epimorphism from a coproduct
(`TauCeti.Topos.IsLocallyWeaklyContractible.exists_effectiveEpi_sigmaDesc`).

## Main definitions

* `TauCeti.Topos.IsLocallyWeaklyContractible C`: every object of `C` has an effective epimorphic
  family from quasicompact, quasiseparated, projective objects.

## Main results

* `TauCeti.Topos.IsLocallyWeaklyContractible.exists_effectiveEpi_sigmaDesc`: every object is the
  target of an effective epimorphism from a coproduct of such objects.
* `TauCeti.Topos.IsLocallyWeaklyContractible.epi_iff_exists_lift`: a morphism is an epimorphism
  if and only if every morphism to its target from a coherent weakly contractible object lifts.
* `TauCeti.Topos.isLocallyWeaklyContractible_type`: the topos of sets is locally weakly
  contractible, every set being covered by its points.

The topos of `G`-sets, covered by free transitive `G`-sets, is another example; see
`TauCeti.CategoryTheory.Topos.Action`.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Definition 3.2.1, Example 3.2.2
  and Proposition 3.2.3.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti.Topos

variable (C : Type u) [Category.{v} C]

/-- A category, meant to be a topos, is *locally weakly contractible* if every object is covered
by coherent weakly contractible objects: it is the target of an effective epimorphic family whose
sources are quasicompact, quasiseparated and projective. -/
class IsLocallyWeaklyContractible : Prop where
  exists_effectiveEpiFamily (X : C) : ∃ (ι : Type v) (U : ι → C) (π : (i : ι) → U i ⟶ X),
    EffectiveEpiFamily U π ∧
      ∀ i, IsQuasicompact (U i) ∧ IsQuasiseparated (U i) ∧ Projective (U i)

variable {C}

namespace IsLocallyWeaklyContractible

variable [IsLocallyWeaklyContractible C]

/-- In a locally weakly contractible category with coproducts, every object is the target of an
effective epimorphism from a coproduct of quasicompact, quasiseparated, projective objects. -/
theorem exists_effectiveEpi_sigmaDesc [HasCoproducts.{v} C] (X : C) :
    ∃ (ι : Type v) (U : ι → C) (π : (i : ι) → U i ⟶ X), EffectiveEpi (Sigma.desc π) ∧
      ∀ i, IsQuasicompact (U i) ∧ IsQuasiseparated (U i) ∧ Projective (U i) := by
  obtain ⟨ι, U, π, _, hU⟩ := exists_effectiveEpiFamily X
  exact ⟨ι, U, π, inferInstance, hU⟩

/-- In a locally weakly contractible category, a morphism `f : X ⟶ Y` is an epimorphism if and
only if every morphism to `Y` from a quasicompact, quasiseparated, projective object factors
through `f`. Thus sections over the coherent weakly contractible objects detect epimorphisms. -/
theorem epi_iff_exists_lift {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ (U : C), IsQuasicompact U → IsQuasiseparated U → Projective U →
      ∀ g : U ⟶ Y, ∃ h : U ⟶ X, h ≫ f = g := by
  refine ⟨fun _ U _ _ _ g ↦ Projective.factors g f, fun hf ↦ ⟨fun {Z} a b hab ↦ ?_⟩⟩
  obtain ⟨ι, U, π, _, hU⟩ := exists_effectiveEpiFamily Y
  choose h hh using fun i ↦ hf (U i) (hU i).1 (hU i).2.1 (hU i).2.2 (π i)
  refine EffectiveEpiFamily.hom_ext U π a b fun i ↦ ?_
  rw [← hh i, Category.assoc, Category.assoc, hab]

end IsLocallyWeaklyContractible

/-- The topos of sets is locally weakly contractible: every set is covered by its points, which
are finite, hence quasicompact, and projective by the axiom of choice. -/
instance isLocallyWeaklyContractible_type : IsLocallyWeaklyContractible (Type u) where
  exists_effectiveEpiFamily X :=
    ⟨X, fun _ ↦ PUnit, fun x ↦ TypeCat.ofHom fun _ ↦ x,
      (Types.effectiveEpiFamily_iff _ _).2 fun x ↦ ⟨x, PUnit.unit, rfl⟩,
      fun _ ↦ ⟨(isQuasicompact_iff_finite _).2 inferInstance, isQuasiseparated_type _,
        inferInstance⟩⟩

end TauCeti.Topos
