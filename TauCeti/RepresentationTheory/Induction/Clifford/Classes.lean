/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Surjectivity
public import TauCeti.RepresentationTheory.Simple.FDRepClassesOver

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

The type of isomorphism classes is `TauCeti.SimpleFDRepClassesOver`, of
`TauCeti.RepresentationTheory.Simple.FDRepClassesOver`; only induction on those classes is built
here.

## Main definitions

* `FDRep.indSimpleFDRepClassesOver`: induction from the inertia group, on isomorphism classes.
* `FDRep.cliffordCorrespondence`: **the Clifford correspondence** `Irr(T ∣ V) ≃ Irr(G ∣ V)`.

## Main statements

* `FDRep.indSimpleFDRepClassesOver_injective` and
  `FDRep.indSimpleFDRepClassesOver_surjective`: induction from the inertia group is injective and
  surjective on the classes over `V`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, Wiley (1981), §11.
-/

public section

open CategoryTheory

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {N : Subgroup G} [N.Normal]

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
      let _ := simple_indFDRep_of_inertia V U h
      let _ := simple_indFDRep_of_inertia V U' h'
      (SimpleFDRepClassesOver.mk_eq_mk_iff (indFDRep U) (indFDRep U')
        (liesOver_indFDRep_of_inertia V U h) (liesOver_indFDRep_of_inertia V U' h')).mpr
        (e.elim nonempty_iso_indFDRep)

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
  let _ := simple_indFDRep_of_inertia V U hUlies
  exact ⟨SimpleFDRepClassesOver.mk U (hU := hU) hUlies,
    (indSimpleFDRepClassesOver_mk V U hUlies).trans
      ((SimpleFDRepClassesOver.mk_eq_mk_iff (indFDRep U) W
        (liesOver_indFDRep_of_inertia V U hUlies) hliesW).mpr he)⟩

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

end FDRep
