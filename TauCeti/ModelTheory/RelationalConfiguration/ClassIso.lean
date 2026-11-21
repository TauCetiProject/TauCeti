/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.SetTheory.Descriptive.BorelReducibility

/-!
# Isomorphism restricted to a class of configurations

For a relational language `L` and a carrier `α`, a *class* is any set `K` of configurations on
`α`, isomorphism invariant or not. Isomorphism on `K` is the isomorphism relation of the decoded
structures, `isoSetoid L α`, pulled back to the subtype `K`, which carries the subtype
σ-algebra. This is the equivalence relation whose position in the Borel reducibility order
measures how hard it is to classify the members of `K` up to isomorphism; for instance, a class
of codes on `ℕ` is Borel complete when the isomorphism relation of every invariant Borel class, in
every countable relational language, is Borel reducible to its own.

The classes are arbitrary sets rather than model classes of sentences, because subclasses that
are not invariant arise when comparing classes: the inclusion of a subclass, or the corestriction
of a measurable map that preserves and reflects isomorphism, is a Borel reduction. On the model
class of an infinitary sentence it is `TauCeti.RelationalConfiguration.isoSetoidOn`, which is
defined through it.

## Main definitions

* `TauCeti.RelationalConfiguration.classIso K`: isomorphism restricted to the class `K`.

## Main results

* `TauCeti.RelationalConfiguration.classIso_apply` and
  `TauCeti.RelationalConfiguration.classIso_iff_exists_perm_smul_eq`: two members of `K` are
  related when their decoded structures are isomorphic, equivalently when they lie in one orbit of
  the logic action of `Equiv.Perm α`.
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

/-- **Isomorphism restricted to a class.** For a set `K` of configurations on `α`, two members of
`K` are related when their decoded structures are isomorphic: the pullback of `isoSetoid L α`
along the inclusion of `K`. It is an abbreviation, so results stated for that pullback apply to
it. -/
abbrev classIso (K : Set (RelationalConfiguration L α)) : Setoid K :=
  (isoSetoid L α).comap Subtype.val

variable {K A : Set (RelationalConfiguration L α)}

/-- Isomorphism on a class is the pullback of isomorphism along the inclusion of the class. -/
theorem classIso_def (K : Set (RelationalConfiguration L α)) :
    classIso K = (isoSetoid L α).comap Subtype.val :=
  (rfl)

/-- Two members of a class are related exactly when they are isomorphic as configurations. -/
@[simp]
theorem classIso_apply {x y : K} : classIso K x y ↔ isoSetoid L α x y :=
  Iff.rfl

/-- Isomorphism on a class is the orbit relation of the logic action, pulled back to the class. -/
theorem classIso_eq_comap_orbitRel :
    classIso K = (MulAction.orbitRel (Equiv.Perm α) _).comap Subtype.val := by
  rw [classIso_def, isoSetoid_eq_orbitRel]

/-- Two members of a class are related exactly when a permutation of the carrier relabels the
first into the second. -/
theorem classIso_iff_exists_perm_smul_eq {x y : K} :
    classIso K x y ↔ ∃ σ : Equiv.Perm α, σ • (x : RelationalConfiguration L α) = y :=
  isoSetoid_iff_exists_perm_smul_eq

/-- On the whole coding space, isomorphism restricted to the class `univ` is Borel bireducible
with isomorphism. -/
theorem borelBireducible_classIso_univ :
    (classIso (univ : Set (RelationalConfiguration L α))).BorelBireducible (isoSetoid L α) :=
  -- The inclusion of `univ` and its inverse are both measurable.
  Setoid.borelBireducible_iff.2
    ⟨Setoid.borelReducible_iff.2 ⟨Subtype.val, measurable_subtypeVal, fun _ _ => Iff.rfl⟩,
      Setoid.borelReducible_iff.2
        ⟨fun c => ⟨c, mem_univ c⟩, measurable_id.subtype_mk, fun _ _ => Iff.rfl⟩⟩

/-- Isomorphism on a subclass is isomorphism on the class, pulled back along the inclusion. -/
theorem comap_inclusion_classIso (h : A ⊆ K) : (classIso K).comap (inclusion h) = classIso A :=
  (rfl)

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
