/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.RepresentationTheory.Induction.Clifford.Basic

/-!
# The constituents of a restriction to a normal subgroup form one orbit

Let `N` be a normal subgroup of `G` and let `ρ` be an irreducible representation of `G` on `V`.
Given one minimal `N`-stable subspace to start from, restricting `ρ` to `N` breaks it into
irreducible constituents (`Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom`; for a
finite-dimensional `V` such a subspace always exists, and then no hypothesis is needed, which is
`Representation.isSemisimpleRepresentation_comp_subtype`).  This file identifies which constituents
occur: **they are the translates of any one of them**, up to isomorphism of `N`-representations.
Equivalently, `G` permutes the isotypic components of the restriction transitively.

The argument is short because the two halves it needs are already in place.  The translates
`Representation.conjSubrep ρ g σ` of a minimal `N`-stable subspace `σ` are again minimal
(`Representation.isAtom_conjSubrep_iff`) and they span (`Representation.iSup_conjSubrep_eq_top`);
and a simple submodule of a module spanned by simple submodules is isomorphic to one of them
(Mathlib's `Submodule.linearEquiv_of_sSup_eq_top`).  The spanning statement is needed in the lattice
of `k[N]`-submodules of the restriction viewed as a `k[N]`-module, where the isotypic machinery
lives, rather than in the lattice of `k`-subspaces where it is proved; that reading is
`Representation.iSup_asSubmodule_conjSubrep_eq_top`, which lives in
`TauCeti/RepresentationTheory/Induction/Clifford/Basic.lean` because the semisimplicity proof there
needs it too.

No invertibility of `Nat.card N` is used: irreducibility of the ambient representation replaces
Maschke's theorem throughout, exactly as in
`TauCeti/RepresentationTheory/Induction/Clifford/Basic.lean`.  The single-orbit statements need no
finiteness either; finiteness is assumed only by `Representation.finite_isotypicComponents`, and
there only of the index of `N` in `G`, because a translate depends only on the coset of `N` it is
taken by.  Finite-dimensionality of `V` is needed only to know that a minimal `N`-stable subspace
exists at all: each of the orbit and isotypic-component statements below takes such a subspace as a
hypothesis, except `Representation.finite_isotypicComponents`, which needs none (without one there
is no isotypic component to count), and
`Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep`, the packaged form of the
theorem, which assumes finite-dimensionality and produces one.

That the constituents share one multiplicity is proved in
`TauCeti/RepresentationTheory/Induction/Clifford/Multiplicity.lean` from the single-orbit
statements below.  The decomposition of the restriction into equally many copies of each conjugate
of one constituent, indexed by the cosets of its inertia group, is not proved here; it is
`FDRep.clifford_restrict_iso` in `TauCeti/RepresentationTheory/Induction/Clifford/Equivalence.lean`.

## Main statements

* `Representation.exists_nonempty_linearEquiv_conjSubrep`: **Clifford's theorem, single
  orbit form.** Any two minimal `N`-stable subspaces of an irreducible representation are
  translates of one another, up to isomorphism of `N`-representations.
* `Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep`: the same statement
  packaged for a finite-dimensional irreducible representation, where the minimal subspace to
  translate is produced rather than assumed.
* `Representation.isotypicComponents_eq_range`: the isotypic components of the restriction
  are exactly the components of the translates of a given minimal `N`-stable subspace, so `G` acts
  transitively on them; `Representation.conjSubrepIsotypicComponent` packages each such
  component, and `Representation.finite_isotypicComponents` shows that there are
  finitely many of them when `N` has finite index in `G`.
* `Representation.isIsotypicOfType_asSubmodule_iff`: the restriction is isotypic exactly
  when every translate of one constituent is isomorphic to it — the case in which the inertia group
  of the constituent is all of `G`.

## Implementation notes

An `N`-constituent is presented as an atom of the lattice of `N`-subrepresentations, as in
`Basic.lean`, and *isomorphic as representations of `N`* is spelled as a `k[N]`-linear equivalence
of the associated submodules of `Representation.asModule (ρ.comp N.subtype)`.  That is what the
isotypic API of `Mathlib/RingTheory/SimpleModule/Isotypic.lean` speaks, and it is the same relation
as an isomorphism of the subrepresentations, transported along
`Subrepresentation.subrepresentationSubmoduleOrderIso`.  That an atom of the one lattice is a simple
module in the other is `Subrepresentation.isSimpleModule_asSubmodule_iff`, in
`TauCeti/RepresentationTheory/Subrepresentation.lean`; it uses neither normality nor irreducibility.
Reading the translate through `Representation.conjSubrepEquiv` turns each statement below into the
classical one about the conjugate representation `{}^g V`.

## References

The mathematics is the classical argument of C. W. Curtis and I. Reiner, *Representation Theory of
Finite Groups and Associative Algebras*, §49.
-/

public section

open scoped MonoidAlgebra

namespace Representation

section Orbit

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **Every irreducible `N`-constituent is a translate of any fixed one.**  If `σ` is a minimal
`N`-stable subspace of an irreducible representation `ρ` and `T` is any simple `k[N]`-submodule of
the restriction, then `T` is isomorphic, as a representation of `N`, to the translate
`conjSubrep ρ g σ` for some `g : G`.

The translates of `σ` are simple and span, so `T` sits inside a sum of simple modules and is
therefore isomorphic to one of them. -/
theorem exists_nonempty_linearEquiv_asSubmodule_conjSubrep [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (T : Submodule k[N] (Representation.asModule (ρ.comp N.subtype)))
    [IsSimpleModule k[N] T] :
    ∃ g : G, Nonempty (T ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) := by
  have hsimple : ∀ m : (Set.range fun g : G => (conjSubrep ρ g σ).asSubmodule),
      IsSimpleModule k[N] m := by
    rintro ⟨_, g, rfl⟩
    exact Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ)
  have hsSup : sSup (Set.range fun g : G => (conjSubrep ρ g σ).asSubmodule) = ⊤ := by
    rw [sSup_range]
    exact iSup_asSubmodule_conjSubrep_eq_top ρ hσ.1
  obtain ⟨_, ⟨g, rfl⟩, he⟩ :=
    Submodule.linearEquiv_of_sSup_eq_top T _ (h := hsimple) hsSup
  exact ⟨g, he⟩

/-- **Clifford's theorem, single-orbit form.**  Any two minimal `N`-stable subspaces of an
irreducible representation are translates of one another, up to isomorphism of representations of
`N`: the irreducible constituents of the restriction to `N` form a single `G`-orbit. -/
theorem exists_nonempty_linearEquiv_conjSubrep [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    ∃ g : G, Nonempty (τ.asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) :=
  have := Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hτ
  exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ τ.asSubmodule

/-- **Clifford's theorem, single-orbit form, packaged.**  The restriction to `N` of a
finite-dimensional irreducible representation has a minimal `N`-stable subspace, and every minimal
`N`-stable subspace is a translate of it up to isomorphism of representations of `N`. -/
theorem exists_isAtom_forall_nonempty_linearEquiv_conjSubrep [ρ.IsIrreducible]
    [FiniteDimensional k V] :
    ∃ σ : Subrepresentation (ρ.comp N.subtype), IsAtom σ ∧
      ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ →
        ∃ g : G, Nonempty (τ.asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) := by
  have : Nontrivial V := Representation.IsIrreducible.nontrivial ‹ρ.IsIrreducible›
  obtain ⟨σ, hσ⟩ := Representation.exists_isAtom (ρ.comp N.subtype)
  exact ⟨σ, hσ, fun _ hτ => exists_nonempty_linearEquiv_conjSubrep ρ hσ hτ⟩

/-- **`G` permutes the isotypic components of the restriction transitively.**  The isotypic
components of the restriction to `N` of an irreducible representation are exactly the components of
the translates of one minimal `N`-stable subspace. -/
theorem isotypicComponents_eq_range [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (Representation.asModule (ρ.comp N.subtype))
      = Set.range fun g : G =>
          isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
            (conjSubrep ρ g σ).asSubmodule := by
  ext c
  constructor
  · rintro ⟨S, _, rfl⟩
    obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ S
    exact ⟨g, e.isotypicComponent_eq.symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, Subrepresentation.isSimpleModule_asSubmodule_iff.mpr
      (isAtom_conjSubrep_iff.mpr hσ), rfl⟩

/-- **The restriction of an irreducible representation to a normal subgroup of finite index has
finitely many isotypic components.**  If the restriction has a simple submodule, its isotypic
components are those of the translates of the corresponding minimal `N`-stable subspace
(`isotypicComponents_eq_range`), and a translate depends only on the coset of `N` it is taken by,
so there is at most one component for each coset.  Neither finiteness of `G` nor
finite-dimensionality of `V` is assumed. -/
theorem finite_isotypicComponents [ρ.IsIrreducible] [N.FiniteIndex] :
    (isotypicComponents k[N] (Representation.asModule (ρ.comp N.subtype))).Finite := by
  obtain h | ⟨_, S, hS, -⟩ := Set.eq_empty_or_nonempty
    (isotypicComponents k[N] (Representation.asModule (ρ.comp N.subtype)))
  · exact h ▸ Set.finite_empty
  obtain ⟨σ, hσ⟩ : ∃ σ : Subrepresentation (ρ.comp N.subtype), IsAtom σ :=
    ⟨_, (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.isAtom_iff S).mpr
      (isSimpleModule_iff_isAtom.mp hS)⟩
  rw [isotypicComponents_eq_range ρ hσ]
  refine (Set.finite_range fun q : G ⧸ N =>
    isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
      (conjSubrep ρ q.out σ).asSubmodule).subset ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  refine ⟨g, ?_⟩
  dsimp only
  rw [hn, ← conjSubrep_conjSubrep, conjSubrep_eq_self_of_mem n.2]

/-- **The restriction is isotypic exactly when one constituent is fixed by all of `G`.**  The
right-hand side says that the inertia group of `σ` is all of `G`; Clifford's theorem then leaves the
restriction with a single isomorphism class of constituents. -/
theorem isIsotypicOfType_asSubmodule_iff [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    IsIsotypicOfType k[N] (Representation.asModule (ρ.comp N.subtype)) σ.asSubmodule ↔
      ∀ g : G, Nonempty ((conjSubrep ρ g σ).asSubmodule ≃ₗ[k[N]] σ.asSubmodule) := by
  constructor
  · intro h g
    have := Subrepresentation.isSimpleModule_asSubmodule_iff (σ := conjSubrep ρ g σ)
      |>.mpr (isAtom_conjSubrep_iff.mpr hσ)
    exact h _
  · intro h m _
    obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ m
    exact ⟨e.trans (h g).some⟩

/-- The isotypic component cut out by the translate of a fixed constituent. -/
noncomputable def conjSubrepIsotypicComponent [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    isotypicComponents k[N] (Representation.asModule (ρ.comp N.subtype)) :=
  ⟨isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
      (conjSubrep ρ g σ).asSubmodule,
    (isotypicComponents_eq_range ρ hσ).symm ▸ Set.mem_range_self g⟩

/-- The underlying submodule of the component indexed by `g` is the isotypic component of the
translated constituent `conjSubrep ρ g σ`. -/
@[simp]
theorem coe_conjSubrepIsotypicComponent [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    (conjSubrepIsotypicComponent ρ σ hσ g :
      Submodule k[N] (Representation.asModule (ρ.comp N.subtype))) =
      isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
        (conjSubrep ρ g σ).asSubmodule :=
  by simp only [conjSubrepIsotypicComponent]

end Orbit

end Representation
