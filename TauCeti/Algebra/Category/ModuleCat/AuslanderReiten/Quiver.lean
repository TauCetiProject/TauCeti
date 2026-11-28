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
-- Non-public: Fitting's lemma is used only in a proof.
import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# The quiver of irreducible morphisms of an Artin algebra

Let `A` be an Artin algebra, finite as a module over a commutative Artinian ring `R`.
This file specializes `TauCeti.IrreducibleMorphismQuiver` to the finitely generated `A`-modules,
`IrreducibleMorphismQuiver R fun M : ModuleCat A ↦ Module.Finite A M`. Its vertices are the
isomorphism classes of finitely generated indecomposable `A`-modules. Representatives have local
endomorphism rings by Fitting's lemma over an Artin algebra
(`TauCeti.isLocalRing_end_of_indecomposable`), so the irreducible morphism spaces between them
carry the residue division ring actions used to define their valuations.

The Auslander–Reiten translate `ModuleCat.arTranslate`
is an Auslander–Reiten translation in the sense of `TauCeti.ARTranslation`
(`ModuleCat.arTranslation`). On isomorphism classes, translation is undefined exactly at the
projective vertices and bijects the non-projective vertices with the non-injective ones
(`TauCeti.ARTranslation.existsUnique_translate_eq_some_iff`).

When the base is a field `k`, the arrows of the unvalued quiver index a `k`-basis of `rad / rad²`
between representatives. These spaces are finite-dimensional (`ModuleCat.finite_hom_of_finite`),
and `TauCeti.IsRepresentationFinite.finite_irreducibleMorphismQuiver_arrows` gives finitely many
arrows in total for a representation-finite algebra. For `A = kQ/I` over an algebraically closed
field this is the underlying quiver of the Auslander–Reiten quiver of `A`. Ordinary linear duality
is the case where the dualizing module is `k` itself.

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

variable {k : Type u} {A : Type v} [Ring A]
  (a : IrreducibleMorphismQuiver k fun M : ModuleCat.{w} A ↦ Module.Finite A M)

/-- A representative of a vertex in the quiver of finite modules is finitely generated. -/
instance : Module.Finite A a.representative :=
  a.representative_property.1

variable [CommRing k] [IsArtinianRing k] [Algebra k A] [Module.Finite k A] in
/-- A vertex representative over an Artin algebra has local endomorphism ring. -/
instance : IsLocalRing (End a.representative) :=
  isLocalRing_end_of_indecomposable (R := k) a.representative_property.2

/-- For a representation-finite algebra, the quiver of irreducible morphisms of finitely
generated modules has finitely many arrows in total. -/
theorem _root_.TauCeti.IsRepresentationFinite.finite_irreducibleMorphismQuiver_arrows
    [Field k] [Algebra k A] [FiniteDimensional k A] (h : IsRepresentationFinite.{w} A) :
    Finite (Σ a b : IrreducibleMorphismQuiver k fun M : ModuleCat.{w} A ↦ Module.Finite A M,
      a ⟶ b) := by
  have := (finite_iff_isRepresentationFinite k A).mpr h
  infer_instance

end TauCeti.IrreducibleMorphismQuiver

namespace ModuleCat

open CategoryTheory TauCeti

universe u v w

variable (R : Type u) (A : Type v) [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]
  (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

/-- The Auslander–Reiten translate `D Tr` for an Artin algebra, as a partial translation on
isomorphism classes of finitely generated indecomposable modules. The dual is taken into the
injective base module `E`, with the Matlis dualizing condition `hE`. -/
noncomputable def arTranslation :
    ARTranslation fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M where
  obj M _ := arTranslate R E M
  prop_obj _ _ := by
    have := finite_of_forall_isMaximal hE
    infer_instance
  nonempty_iso_obj_of_iso _ _ e := nonempty_iso_arTranslate_of_iso R E e
  indecomposable_obj_iff M _ hI := indecomposable_arTranslate_iff hE M hI
  injective_obj_iff M _ := injective_arTranslate_iff hE M
  nonempty_iso_of_nonempty_iso_obj _ _ hiM hiN hpM :=
    (nonempty_iso_arTranslate_iff hE hiM hiN hpM).mp
  exists_nonempty_iso_obj N _ hiN hinj := exists_nonempty_iso_arTranslate hE N hiN hinj

/-- The object operation of the translation computes the chosen Matlis dual transpose. -/
@[simp]
theorem arTranslation_obj (M : ModuleCat.{max u v w} A) (hM : Module.Finite A M) :
    (arTranslation R A E hE).obj M hM = arTranslate R E M :=
  (rfl)

end ModuleCat
