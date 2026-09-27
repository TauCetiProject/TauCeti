/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Surjectivity
public import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The Clifford correspondence as a bijection of isomorphism classes

Let `N` be a normal subgroup of a finite group `G`, let `V` be an irreducible representation of `N`
over an algebraically closed field of characteristic zero, and let `T = inertia V`.  Induction from
`T` to `G` carries an irreducible representation lying over `V` to an irreducible representation
lying over `V` (`FDRep.simple_indFDRep_of_inertia`, `FDRep.liesOver_indFDRep_of_inertia`), it does
so injectively on isomorphism classes
(`FDRep.nonempty_iso_of_liesOver_inertia_of_nonempty_iso_indFDRep`) and it hits every class
(`FDRep.exists_simple_liesOver_inertia_nonempty_iso_indFDRep`).  Those three statements quantify
over representatives; this file packages them as a single bijection

`Irr(T ∣ V) ≃ Irr(G ∣ V)`,

which is the form in which the Clifford correspondence reduces the classification of the
irreducible representations of `G` lying over `V` to the same classification for the inertia group.

The type of isomorphism classes needs no new device.  `TauCeti.SimpleFDRepClasses` is already the
skeleton of the full subcategory of simple objects of `FDRep k G`, so `Irr(G ∣ V)` is the skeleton
of the full subcategory cut out by the conjunction of simplicity and `FDRep.LiesOver`; that
property is `TauCeti.simpleLiesOver` and the skeleton is
`TauCeti.SimpleFDRepClassesOver`, with the constructor, the eliminator, the lift of an
isomorphism-invariant function, and the injection into `TauCeti.SimpleFDRepClasses` that forgets
the constituent.

## Main definitions

* `TauCeti.simpleLiesOver`: being a simple representation lying over a fixed constituent, as a
  property of objects of `FDRep k H`.
* `TauCeti.SimpleFDRepClassesOver`: the isomorphism classes of those representations, `Irr(H ∣ V)`.
* `FDRep.indSimpleFDRepClassesOver`: induction from the inertia group, on isomorphism classes.
* `FDRep.cliffordCorrespondence`: **the Clifford correspondence** `Irr(T ∣ V) ≃ Irr(G ∣ V)`.

## Main statements

* `TauCeti.SimpleFDRepClassesOver.mk_eq_mk_iff`: two representations lying over `V` have the same
  class exactly when they are isomorphic.
* `TauCeti.SimpleFDRepClassesOver.toSimpleFDRepClasses_injective`: the classes over `V` inject into
  all simple-object classes, so no information is lost by remembering the constituent.
* `FDRep.existsUnique_cliffordCorrespondence_eq`: every irreducible of `G` lying over `V` is
  induced from exactly one class of irreducibles of the inertia group lying over `V`.
* `FDRep.card_simpleFDRepClassesOver_inertia`: the two classifications have the same cardinality.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, Wiley (1981), §11.
* [Induction/restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
  Layer 5, the Clifford correspondence `Irr(inertia V ∣ V) ≃ Irr(G ∣ V)`.
-/

public section

open CategoryTheory

attribute [local instance] isIsomorphicSetoid

universe u v w

namespace TauCeti

section Classes

variable {k : Type u} {N : Type v} {H : Type w} [Field k] [Group N] [Group H]

/-- Being a **simple representation lying over `V`** along `φ : N →* H`, as a property of objects
of `FDRep k H`: the property whose full subcategory has `Irr(H ∣ V)` as its skeleton. -/
def simpleLiesOver (φ : N →* H) (V : FDRep k N) : ObjectProperty (FDRep k H) :=
  fun U => Simple U ∧ U.LiesOver φ V

variable {φ : N →* H} {V : FDRep k N}

/-- **The isomorphism classes of the simple representations lying over a fixed constituent**,
written `Irr(H ∣ V)` in the literature: the skeleton of the full subcategory of `FDRep k H` they
span.  It is the indexing type of the Clifford correspondence
`FDRep.cliffordCorrespondence`. -/
def SimpleFDRepClassesOver (φ : N →* H) (V : FDRep k N) : Type _ :=
  Skeleton (ObjectProperty.FullSubcategory (simpleLiesOver φ V))

namespace SimpleFDRepClassesOver

/-- The class of a simple representation lying over `V`. -/
def mk (U : FDRep k H) [hU : Simple U] (h : U.LiesOver φ V) : SimpleFDRepClassesOver φ V :=
  toSkeleton (⟨U, hU, h⟩ : ObjectProperty.FullSubcategory (simpleLiesOver φ V))

/-- Two simple representations lying over `V` have the same class exactly when they are
isomorphic. -/
@[simp]
theorem mk_eq_mk_iff (U U' : FDRep k H) [hU : Simple U] [hU' : Simple U']
    (h : U.LiesOver φ V) (h' : U'.LiesOver φ V) : mk U h = mk U' h' ↔ Nonempty (U ≅ U') :=
  ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso (simpleLiesOver φ V) _ _

/-- To prove a property of every class over `V`, it suffices to prove it on the class of each
simple representation lying over `V`. -/
@[elab_as_elim]
theorem ind {motive : SimpleFDRepClassesOver φ V → Prop}
    (h : ∀ (U : FDRep k H) (hU : Simple U) (hlies : U.LiesOver φ V),
      motive (mk U (hU := hU) hlies))
    (c : SimpleFDRepClassesOver φ V) : motive c :=
  Quotient.ind (fun U ↦ h U.obj U.property.1 U.property.2) c

/-- Define a function on the classes over `V` from a function on simple representations lying over
`V` that is invariant under isomorphism. -/
noncomputable def lift {α : Sort*} (f : ∀ (U : FDRep k H) [Simple U], U.LiesOver φ V → α)
    (hf : ∀ (U U' : FDRep k H) [Simple U] [Simple U'] (h : U.LiesOver φ V)
      (h' : U'.LiesOver φ V), Nonempty (U ≅ U') → f U h = f U' h') :
    SimpleFDRepClassesOver φ V → α :=
  ObjectProperty.skeletonLift _ (fun U ↦ @f U.obj U.property.1 U.property.2)
    fun U U' e ↦ @hf U.obj U'.obj U.property.1 U'.property.1 U.property.2 U'.property.2 e

@[simp]
theorem lift_mk {α : Sort*} {f : ∀ (U : FDRep k H) [Simple U], U.LiesOver φ V → α} {hf}
    (U : FDRep k H) [Simple U] (h : U.LiesOver φ V) : lift f hf (mk U h) = f U h :=
  ObjectProperty.skeletonLift_toSkeleton _ _

/-- Forgetting the constituent: the class of a simple representation lying over `V`, read as a
class of simple representations. -/
noncomputable def toSimpleFDRepClasses :
    SimpleFDRepClassesOver φ V → SimpleFDRepClasses k H :=
  lift (fun U _ _ ↦ SimpleFDRepClasses.mk U)
    fun U U' _ _ _ _ e ↦ (SimpleFDRepClasses.mk_eq_mk_iff U U').mpr e

@[simp]
theorem toSimpleFDRepClasses_mk (U : FDRep k H) [Simple U] (h : U.LiesOver φ V) :
    toSimpleFDRepClasses (mk U h) = SimpleFDRepClasses.mk U :=
  lift_mk (f := fun U _ _ ↦ SimpleFDRepClasses.mk U) U h

/-- **Forgetting the constituent is injective**: the classes over `V` are a subfamily of all
simple-object classes, not a quotient of one. -/
theorem toSimpleFDRepClasses_injective :
    Function.Injective (toSimpleFDRepClasses (φ := φ) (V := V)) := by
  intro a
  induction a using ind with
  | _ U hU hlies =>
  intro b
  induction b using ind with
  | _ U' hU' hlies' =>
  intro hab
  rw [toSimpleFDRepClasses_mk, toSimpleFDRepClasses_mk, SimpleFDRepClasses.mk_eq_mk_iff] at hab
  exact (mk_eq_mk_iff U U' hlies hlies').mpr hab

end SimpleFDRepClassesOver

end Classes

end TauCeti

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {N : Subgroup G} [N.Normal]

omit [Finite G] [IsAlgClosed k] [CharZero k] in
/-- Induction from a finite-index subgroup carries an isomorphism to an isomorphism, being the
action on objects of the functor `TauCeti.indFDRepFunctor`.  It stays private and local: it is
needed only to check that `FDRep.indSimpleFDRepClassesOver` below is well defined, and it is one
composite of `CategoryTheory.Functor.mapIso` with the object projection
`TauCeti.indFDRepFunctor_obj`. -/
private theorem nonempty_iso_indFDRep {S : Subgroup G} [S.FiniteIndex] {A B : FDRep k S}
    (e : A ≅ B) : Nonempty (indFDRep A ≅ indFDRep B) :=
  ⟨(eqToIso (indFDRepFunctor_obj A)).symm ≪≫
    (indFDRepFunctor (k := k) (S := S)).mapIso e ≪≫ eqToIso (indFDRepFunctor_obj B)⟩

/-- **Induction from the inertia group, on isomorphism classes.**  It is well defined because
induction carries isomorphic representations to isomorphic ones, and it lands in the classes over
`V` because induction preserves both irreducibility and lying over `V`. -/
noncomputable def indSimpleFDRepClassesOver (V : FDRep k N) [Simple V] :
    SimpleFDRepClassesOver (Subgroup.inclusion (le_inertia V)) V →
      SimpleFDRepClassesOver N.subtype V :=
  SimpleFDRepClassesOver.lift
    (fun U _ h ↦ SimpleFDRepClassesOver.mk (indFDRep U)
      (hU := simple_indFDRep_of_inertia V U h) (liesOver_indFDRep_of_inertia V U h))
    fun U U' _ _ h h' e ↦
      (SimpleFDRepClassesOver.mk_eq_mk_iff (indFDRep U) (indFDRep U')
          (hU := simple_indFDRep_of_inertia V U h)
          (hU' := simple_indFDRep_of_inertia V U' h')
          (liesOver_indFDRep_of_inertia V U h)
          (liesOver_indFDRep_of_inertia V U' h')).mpr (e.elim nonempty_iso_indFDRep)

@[simp]
theorem indSimpleFDRepClassesOver_mk (V : FDRep k N) [Simple V] (U : FDRep k (inertia V))
    [Simple U] (h : U.LiesOver (Subgroup.inclusion (le_inertia V)) V) :
    indSimpleFDRepClassesOver V (SimpleFDRepClassesOver.mk U h) =
      SimpleFDRepClassesOver.mk (indFDRep U) (hU := simple_indFDRep_of_inertia V U h)
        (liesOver_indFDRep_of_inertia V U h) :=
  SimpleFDRepClassesOver.lift_mk U h

/-- **Induction from the inertia group is injective on the classes over `V`.** -/
theorem indSimpleFDRepClassesOver_injective (V : FDRep k N) [Simple V] :
    Function.Injective (indSimpleFDRepClassesOver V) := by
  intro a
  induction a using SimpleFDRepClassesOver.ind with
  | _ A hA hliesA =>
  intro b
  induction b using SimpleFDRepClassesOver.ind with
  | _ B hB hliesB =>
  intro hab
  rw [indSimpleFDRepClassesOver_mk, indSimpleFDRepClassesOver_mk,
    SimpleFDRepClassesOver.mk_eq_mk_iff] at hab
  exact (SimpleFDRepClassesOver.mk_eq_mk_iff A B hliesA hliesB).mpr
    (nonempty_iso_of_liesOver_inertia_of_nonempty_iso_indFDRep V A B hliesA hliesB hab)

/-- **Induction from the inertia group is surjective on the classes over `V`.** -/
theorem indSimpleFDRepClassesOver_surjective (V : FDRep k N) [Simple V] :
    Function.Surjective (indSimpleFDRepClassesOver V) := by
  intro c
  induction c using SimpleFDRepClassesOver.ind with
  | _ W hW hliesW =>
  obtain ⟨U, hU, hUlies, he⟩ :=
    exists_simple_liesOver_inertia_nonempty_iso_indFDRep V W hliesW
  exact ⟨SimpleFDRepClassesOver.mk U (hU := hU) hUlies,
    (indSimpleFDRepClassesOver_mk V U hUlies).trans
      ((SimpleFDRepClassesOver.mk_eq_mk_iff (indFDRep U) W
        (hU := simple_indFDRep_of_inertia V U hUlies) _ _).mpr he)⟩

/-- **The Clifford correspondence.**  Let `N` be a normal subgroup of a finite group `G` and let
`V` be an irreducible representation of `N` over an algebraically closed field of characteristic
zero.  Induction from the inertia group `T = inertia V` is a bijection

`Irr(T ∣ V) ≃ Irr(G ∣ V)`

from the isomorphism classes of the irreducible representations of `T` lying over `V` onto the
isomorphism classes of the irreducible representations of `G` lying over `V`.  This reduces the
classification of the irreducibles of `G` over `V` to the same classification for `T`, a group in
which the isomorphism class of `V` is stable under conjugation. -/
noncomputable def cliffordCorrespondence (V : FDRep k N) [Simple V] :
    SimpleFDRepClassesOver (Subgroup.inclusion (le_inertia V)) V ≃
      SimpleFDRepClassesOver N.subtype V :=
  Equiv.ofBijective (indSimpleFDRepClassesOver V)
    ⟨indSimpleFDRepClassesOver_injective V, indSimpleFDRepClassesOver_surjective V⟩

@[simp]
theorem cliffordCorrespondence_apply (V : FDRep k N) [Simple V]
    (a : SimpleFDRepClassesOver (Subgroup.inclusion (le_inertia V)) V) :
    cliffordCorrespondence V a = indSimpleFDRepClassesOver V a :=
  (rfl)

/-- **Every irreducible of `G` lying over `V` is induced from exactly one class of irreducibles of
the inertia group lying over `V`.**  This is the Clifford correspondence read as an
existence-and-uniqueness statement about a representative. -/
theorem existsUnique_cliffordCorrespondence_eq (V : FDRep k N) [Simple V] (W : FDRep k G)
    [Simple W] (hW : W.LiesOver N.subtype V) :
    ∃! a : SimpleFDRepClassesOver (Subgroup.inclusion (le_inertia V)) V,
      cliffordCorrespondence V a = SimpleFDRepClassesOver.mk W hW :=
  (cliffordCorrespondence V).bijective.existsUnique _

/-- **The Clifford correspondence counts.**  The irreducibles of `G` lying over `V` and those of
the inertia group lying over `V` are equinumerous up to isomorphism. -/
theorem card_simpleFDRepClassesOver_inertia (V : FDRep k N) [Simple V] :
    Nat.card (SimpleFDRepClassesOver (Subgroup.inclusion (le_inertia V)) V) =
      Nat.card (SimpleFDRepClassesOver N.subtype V) :=
  Nat.card_congr (cliffordCorrespondence V)

end FDRep
