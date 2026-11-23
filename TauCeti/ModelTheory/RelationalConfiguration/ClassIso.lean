/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.SetTheory.Descriptive.BorelReducibility

/-!
# Borel reducibility of isomorphism on classes of configurations

For a relational language `L` and a carrier `α`, `TauCeti.RelationalConfiguration.classIso K` is the
isomorphism relation of decoded structures restricted to a class `K` of configurations on `α`, which
carries the subtype σ-algebra. This module proves the basic Borel-reducibility results for
`classIso`:

* on the whole coding space, `classIso univ` is Borel bireducible with `isoSetoid L α`
  (`TauCeti.RelationalConfiguration.borelBireducible_classIso_univ`);
* inclusion of a subclass, or corestriction of a measurable map that preserves and reflects
  isomorphism, is a Borel reduction
  (`TauCeti.RelationalConfiguration.borelReducible_classIso_of_subset`,
  `TauCeti.RelationalConfiguration.borelReducible_classIso_of_mapsTo`);
* isomorphism on the empty class reduces to every class, and a class reduces to the empty class
  precisely when it is empty (`TauCeti.RelationalConfiguration.classIso_empty_borelReducible`,
  `TauCeti.RelationalConfiguration.borelReducible_classIso_empty_iff`).

## Main results

* `TauCeti.RelationalConfiguration.borelBireducible_classIso_univ`: on the whole coding space it
  is Borel bireducible with `isoSetoid L α`.
* `TauCeti.RelationalConfiguration.borelReducible_classIso_of_subset`: isomorphism on a subclass is
  Borel reducible to isomorphism on the class.
* `TauCeti.RelationalConfiguration.borelReducible_classIso_of_mapsTo`: a measurable map between
  coding spaces that maps one class into another and preserves and reflects isomorphism on the
  first restricts to a Borel reduction.

## References

* G. Paolini and S. Shelah, *Torsion-free abelian groups are Borel complete*, Ann. of Math. 199
  (2024), arXiv:2102.12371, Fact 1.1 and Definition 1.6 (the isomorphism relation on a class of
  structures with universe `ℕ`, and its subspace Borel structure).
* R. Camerlo and S. Gao, *The completeness of the isomorphism relation for countable Boolean
  algebras*, Trans. Amer. Math. Soc. 353 (2001), §1.
-/

public section

universe u v u' v' w w'

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {α : Type w}
  {K A : Set (RelationalConfiguration L α)}

/-- On the whole coding space, isomorphism restricted to the class `univ` is Borel bireducible
with isomorphism. -/
theorem borelBireducible_classIso_univ :
    (classIso (univ : Set (RelationalConfiguration L α))).BorelBireducible (isoSetoid L α) :=
  -- The inclusion of `univ` and its inverse are both measurable.
  Setoid.borelBireducible_iff.2
    ⟨Setoid.borelReducible_iff.2 ⟨Subtype.val, measurable_subtypeVal, fun _ _ => Iff.rfl⟩,
      Setoid.borelReducible_iff.2
        ⟨fun c => ⟨c, mem_univ c⟩, measurable_id.subtype_mk, fun _ _ => Iff.rfl⟩⟩

/-- **Restriction.** Isomorphism on a subclass, invariant or not, is Borel reducible to
isomorphism on the class, through the inclusion. -/
theorem borelReducible_classIso_of_subset (h : A ⊆ K) :
    (classIso A).BorelReducible (classIso K) := by
  rw [← comap_inclusion_classIso h]
  exact Setoid.borelReducible_comap (measurable_inclusion h) _

/-- **Corestriction.** A measurable map between coding spaces that maps the class `K'` into the
class `K`, and under which two members of `K'` are isomorphic exactly when their images are,
restricts to a Borel reduction of isomorphism on `K'` to isomorphism on `K`. -/
theorem borelReducible_classIso_of_mapsTo {L' : Language.{u', v'}} [L'.IsRelational]
    {β : Type w'} {K' : Set (RelationalConfiguration L' β)}
    {f : RelationalConfiguration L' β → RelationalConfiguration L α} (hf : Measurable f)
    (hK : MapsTo f K' K)
    (hiso : ∀ x ∈ K', ∀ y ∈ K', isoSetoid L' β x y ↔ isoSetoid L α (f x) (f y)) :
    (classIso K').BorelReducible (classIso K) :=
  Setoid.borelReducible_iff.2 ⟨hK.restrict f K' K, (hf.comp measurable_subtypeVal).subtype_mk,
    fun x y => hiso x x.property y y.property⟩

/-- Isomorphism on the empty class is Borel reducible to isomorphism on every class, through the
empty map. -/
theorem classIso_empty_borelReducible {L' : Language.{u', v'}} [L'.IsRelational] {β : Type w'}
    (K : Set (RelationalConfiguration L α)) :
    (classIso (∅ : Set (RelationalConfiguration L' β))).BorelReducible (classIso K) :=
  Setoid.borelReducible_iff.2 ⟨isEmptyElim, measurable_of_empty _, isEmptyElim⟩

/-- Isomorphism on a class is Borel reducible to isomorphism on the empty class exactly when the
class is empty. -/
@[simp]
theorem borelReducible_classIso_empty_iff {L' : Language.{u', v'}} [L'.IsRelational]
    {β : Type w'} :
    (classIso K).BorelReducible (classIso (∅ : Set (RelationalConfiguration L' β))) ↔ K = ∅ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨f, -, -⟩ := Setoid.borelReducible_iff.1 h
    exact eq_empty_iff_forall_notMem.2 fun x hx => (f ⟨x, hx⟩).property
  · rintro rfl
    exact classIso_empty_borelReducible _

end TauCeti.RelationalConfiguration
