/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Translation
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Abelian
-- Non-public: Fitting's lemma for finite-dimensional endomorphism algebras is used only in a proof.
import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# The quiver of irreducible morphisms of a finite-dimensional algebra

Let `A` be a finite-dimensional algebra over a field `k`. This file specializes
`TauCeti.IrreducibleMorphismQuiver` to the finitely generated `A`-modules,
`IrreducibleMorphismQuiver k fun M : ModuleCat A ↦ Module.Finite A M`. Its vertices are the
isomorphism classes of finitely generated indecomposable `A`-modules, and its arrows index a
`k`-basis of `rad / rad²` between representatives. For `A = kQ/I` over an algebraically closed
field this is the underlying quiver of the Auslander–Reiten quiver of `A`; over other fields the
arrows count dimensions over `k`, not the valuations over the residue division rings.

The instances here make the general API apply without further hypotheses:

* the morphism spaces between representatives are finite-dimensional
  (`ModuleCat.finite_hom_of_finite`), so every arrow set is finite;
* representatives have local endomorphism rings
  (`TauCeti.isLocalRing_end_of_indecomposable`, Fitting's lemma for the finite-dimensional
  endomorphism algebra), so
  `TauCeti.IrreducibleMorphismQuiver.nonempty_arrows_of_iff` and
  `TauCeti.exists_isIrreducibleMorphism_irreducibleMorphismMk_eq` apply to them.

The Auslander–Reiten translate `ModuleCat.arTranslate` is an Auslander–Reiten translation in
the sense of `TauCeti.ARTranslation` (`ModuleCat.arTranslation`). Its partial translation on this
quiver is undefined exactly at the projective vertices and is a bijection from the non-projective
vertices onto the non-injective ones
(`TauCeti.ARTranslation.existsUnique_translate_eq_some_iff`).

No algebraic closedness is assumed.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.4.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), VII.1.
-/

public section

namespace TauCeti.IrreducibleMorphismQuiver

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

/-- The quiver of irreducible morphisms of finitely generated modules has finitely many vertices
exactly when the ring is representation-finite. -/
theorem finite_iff_isRepresentationFinite (k : Type u) (A : Type v) [Ring A] :
    Finite (IrreducibleMorphismQuiver k fun M : ModuleCat.{w} A ↦ Module.Finite A M) ↔
      IsRepresentationFinite.{w} A :=
  (Equiv.finite_iff equivSkeleton).trans (isRepresentationFinite_iff A).symm

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (a : IrreducibleMorphismQuiver k fun M : ModuleCat.{w} A ↦ Module.Finite A M)

instance : Module.Finite A a.representative :=
  a.representative_property.1

instance : IsLocalRing (End a.representative) :=
  isLocalRing_end_of_indecomposable (R := k) a.representative_property.2

/-- For a representation-finite algebra, the quiver of irreducible morphisms of finitely
generated modules has finitely many arrows in total. -/
theorem _root_.TauCeti.IsRepresentationFinite.finite_irreducibleMorphismQuiver_arrows
    (h : IsRepresentationFinite.{w} A) :
    Finite (Σ a b : IrreducibleMorphismQuiver k fun M : ModuleCat.{w} A ↦ Module.Finite A M,
      a ⟶ b) := by
  have := (finite_iff_isRepresentationFinite k A).mpr h
  infer_instance

end TauCeti.IrreducibleMorphismQuiver

namespace ModuleCat

open CategoryTheory TauCeti

universe u v w

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- The Auslander–Reiten translate of finitely generated modules over a finite-dimensional
algebra, as a translation on their isomorphism classes. -/
noncomputable def arTranslation :
    ARTranslation fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M where
  obj M _ := arTranslate k M
  prop_obj _ _ := inferInstance
  nonempty_iso_obj_of_iso _ _ e := nonempty_iso_arTranslate_of_iso k e
  indecomposable_obj_iff M _ hI := indecomposable_arTranslate_iff k M hI
  injective_obj_iff M _ := injective_arTranslate_iff k M
  nonempty_iso_of_nonempty_iso_obj _ _ hiM hiN hpM :=
    (nonempty_iso_arTranslate_iff k hiM hiN hpM).mp
  exists_nonempty_iso_obj N _ hiN hinj := exists_nonempty_iso_arTranslate k N hiN hinj

@[simp]
theorem arTranslation_obj (M : ModuleCat.{max u v w} A) (hM : Module.Finite A M) :
    (arTranslation k A).obj M hM = arTranslate k M :=
  (rfl)

end ModuleCat
