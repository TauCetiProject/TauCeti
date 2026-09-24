/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Irreducible morphisms

A morphism `f : X ⟶ Y` is **irreducible** when it is neither a split monomorphism nor a split
epimorphism, and every factorization `f = g ≫ h` has `g` a split mono or `h` a split epi. So `f`
admits no "genuine" intermediate object: any object `Z` it factors through contains `X` as a
retract, split off by the first factor `g : X ⟶ Z`, or contains `Y` as a retract, split off by
the second factor `h : Z ⟶ Y`.

Irreducible morphisms are what the arrows of the Auslander-Reiten quiver of a finite-dimensional
algebra record. An arrow there is not an individual irreducible morphism: what governs the arrows
from indecomposable finite-dimensional modules `[X]` to `[Y]` is the space of irreducible morphisms
`X ⟶ Y`, the quotient `rad(X, Y) / rad²(X, Y)`. This is a bimodule over the division rings
`End(Y) / rad End(Y)` and
`End(X) / rad End(X)`. Over an algebraically closed field those division rings are the field
itself, and then the arrows represent a basis, so their number is the dimension of that space;
over a general field the quiver is a valued one, carrying the two one-sided dimensions of the
bimodule instead. The components of the maps in an almost-split sequence, after decomposing
the middle term into indecomposable summands, are irreducible morphisms. Nothing in the definition
is special to modules, so this file develops the notion for an arbitrary category and specializes
only where the statement forces it.

## Main results

* `TauCeti.IsIrreducibleMorphism`: the definition, with `TauCeti.isIrreducibleMorphism_iff`
  spelling out its three clauses as the introduction and elimination rule.
* `TauCeti.IsIrreducibleMorphism.not_isIso`: an irreducible morphism is not an isomorphism.
* `TauCeti.IsIrreducibleMorphism.comp_iso` and `TauCeti.IsIrreducibleMorphism.iso_comp`,
  with the `iff` forms `TauCeti.isIrreducibleMorphism_comp_iso_iff` and
  `TauCeti.isIrreducibleMorphism_iso_comp_iff`: irreducibility only depends on the morphism up to
  isomorphisms of its source and target, so it descends to the arrows of a skeleton.
* `TauCeti.not_isIrreducibleMorphism_zero`: **a zero morphism is never irreducible**, and its
  consequence `TauCeti.IsIrreducibleMorphism.ne_zero`.
* `TauCeti.IsIrreducibleMorphism.mono_or_epi`: **an irreducible morphism with an image in a category
  with equalizers is a monomorphism or an epimorphism**, and by
  `TauCeti.IsIrreducibleMorphism.not_mono_and_epi` never both in a balanced category, so there,
  as in an abelian category, `TauCeti.IsIrreducibleMorphism.mono_iff_not_epi` is a genuine
  dichotomy.

The split-morphism cancellation lemmas include `TauCeti.isSplitMono_of_isSplitMono_comp` and
`TauCeti.isSplitEpi_of_isSplitEpi_comp`.

## Implementation notes

The definition is a conjunction; the three components are available as
`TauCeti.IsIrreducibleMorphism.not_isSplitMono`,
`TauCeti.IsIrreducibleMorphism.not_isSplitEpi` and `TauCeti.IsIrreducibleMorphism.factors`, so
that no proof has to project through `And` by hand. The body of the definition is not exposed
outside this module, so `⟨_, _, _⟩` is not available to establish it downstream;
`TauCeti.isIrreducibleMorphism_iff` is the introduction rule.

The factorization property quantifies over all objects of the ambient category. In applications
to finite-dimensional representations, choose the category of finite-dimensional representations
as the ambient category. Irreducibility is inherited by a full subcategory containing the source
and target, but irreducibility in that subcategory need not imply irreducibility in the larger
category.

The dichotomy `mono_or_epi` is proved by feeding the image factorization `f = e ≫ i` to the
definition: `e` is epi (the category has equalizers), so if it splits it is an isomorphism and `f`
is mono; `i` is mono, so if it splits it is an isomorphism and `f` is epi.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.5.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Cancelling a split morphism off a composite -/

/-- The first factor of a split monomorphism is a split monomorphism. -/
theorem isSplitMono_of_isSplitMono_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSplitMono (f ≫ g)] : IsSplitMono f :=
  IsSplitMono.mk' ⟨g ≫ retraction (f ≫ g), by rw [← Category.assoc]; exact IsSplitMono.id _⟩

/-- The second factor of a split epimorphism is a split epimorphism. -/
theorem isSplitEpi_of_isSplitEpi_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSplitEpi (f ≫ g)] : IsSplitEpi g :=
  IsSplitEpi.mk' ⟨section_ (f ≫ g) ≫ f, by rw [Category.assoc]; exact IsSplitEpi.id _⟩

/-- If postcomposition with an isomorphism is a split epimorphism, the original morphism is
also a split epimorphism. -/
theorem isSplitEpi_of_isSplitEpi_comp_iso {X Y Y' : C} (f : X ⟶ Y) (e : Y ≅ Y')
    [IsSplitEpi (f ≫ e.hom)] : IsSplitEpi f := by
  have h : (f ≫ e.hom) ≫ e.inv = f := by simp
  rw [← h]
  infer_instance

/-- If precomposition with an isomorphism is a split monomorphism, the original morphism is
also a split monomorphism. -/
theorem isSplitMono_of_isSplitMono_iso_comp {X' X Y : C} (e : X' ≅ X) (f : X ⟶ Y)
    [IsSplitMono (e.hom ≫ f)] : IsSplitMono f := by
  have h : e.inv ≫ e.hom ≫ f = f := by simp
  rw [← h]
  infer_instance

/-! ### Irreducible morphisms -/

/-- **An irreducible morphism**: one that is neither a split monomorphism nor a split
epimorphism, and admits only split factorizations: in every factorization
`f = g ≫ h`, either `g` is a split mono or `h` is a split epi.

The two negative clauses are what makes the notion nonvacuous: without them every isomorphism
would qualify. With them, an irreducible morphism is in particular not an isomorphism
(`TauCeti.IsIrreducibleMorphism.not_isIso`) and not zero
(`TauCeti.IsIrreducibleMorphism.ne_zero`). -/
def IsIrreducibleMorphism {X Y : C} (f : X ⟶ Y) : Prop :=
  ¬ IsSplitMono f ∧ ¬ IsSplitEpi f ∧
    ∀ (Z : C) (g : X ⟶ Z) (h : Z ⟶ Y), g ≫ h = f → IsSplitMono g ∨ IsSplitEpi h

variable {X Y : C} {f : X ⟶ Y}

/-- **The three clauses of irreducibility**, spelled out. This is both the introduction rule —
the body of `TauCeti.IsIrreducibleMorphism` is not exposed outside this module, so `⟨_, _, _⟩`
does not establish it there — and the elimination rule in a single statement; the individual
components are also available as `TauCeti.IsIrreducibleMorphism.not_isSplitMono`,
`TauCeti.IsIrreducibleMorphism.not_isSplitEpi` and `TauCeti.IsIrreducibleMorphism.factors`. -/
theorem isIrreducibleMorphism_iff :
    IsIrreducibleMorphism f ↔ ¬ IsSplitMono f ∧ ¬ IsSplitEpi f ∧
      ∀ (Z : C) (g : X ⟶ Z) (h : Z ⟶ Y), g ≫ h = f → IsSplitMono g ∨ IsSplitEpi h :=
  Iff.rfl

/-- An irreducible morphism is not a split monomorphism. -/
theorem IsIrreducibleMorphism.not_isSplitMono (hf : IsIrreducibleMorphism f) :
    ¬ IsSplitMono f := hf.1

/-- An irreducible morphism is not a split epimorphism. -/
theorem IsIrreducibleMorphism.not_isSplitEpi (hf : IsIrreducibleMorphism f) :
    ¬ IsSplitEpi f := hf.2.1

/-- **The factorization property.** In any factorization of an irreducible morphism, the first
factor is a split mono or the second is a split epi. -/
theorem IsIrreducibleMorphism.factors (hf : IsIrreducibleMorphism f) {Z : C} (g : X ⟶ Z)
    (h : Z ⟶ Y) (hgh : g ≫ h = f) : IsSplitMono g ∨ IsSplitEpi h := hf.2.2 Z g h hgh

/-- In a factorization of an irreducible morphism, if the second factor is not a split
epimorphism, the first is a split monomorphism. -/
theorem IsIrreducibleMorphism.isSplitMono_of_not_isSplitEpi (hf : IsIrreducibleMorphism f)
    {Z : C} {g : X ⟶ Z} {h : Z ⟶ Y} (hgh : g ≫ h = f) (hh : ¬ IsSplitEpi h) : IsSplitMono g :=
  (hf.factors g h hgh).resolve_right hh

/-- In a factorization of an irreducible morphism, if the first factor is not a split
monomorphism, the second is a split epimorphism. -/
theorem IsIrreducibleMorphism.isSplitEpi_of_not_isSplitMono (hf : IsIrreducibleMorphism f)
    {Z : C} {g : X ⟶ Z} {h : Z ⟶ Y} (hgh : g ≫ h = f) (hg : ¬ IsSplitMono g) : IsSplitEpi h :=
  (hf.factors g h hgh).resolve_left hg

/-- An irreducible morphism is not an isomorphism. -/
theorem IsIrreducibleMorphism.not_isIso (hf : IsIrreducibleMorphism f) : ¬ IsIso f :=
  fun _ => hf.not_isSplitMono inferInstance

/-- An identity is not irreducible. -/
@[simp]
theorem not_isIrreducibleMorphism_id (X : C) : ¬ IsIrreducibleMorphism (𝟙 X) :=
  fun hf => hf.not_isIso inferInstance

/-! ### Invariance under isomorphisms of the source and the target -/

/-- **Postcomposing an irreducible morphism with an isomorphism keeps it irreducible.** -/
theorem IsIrreducibleMorphism.comp_iso (hf : IsIrreducibleMorphism f) {Y' : C} (e : Y ≅ Y') :
    IsIrreducibleMorphism (f ≫ e.hom) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_comp f e.hom),
    fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp_iso f e), fun Z g h hgh => ?_⟩
  have hgh' : g ≫ h ≫ e.inv = f := by simp [reassoc_of% hgh]
  rcases hf.factors g (h ≫ e.inv) hgh' with hsplit | hsplit
  · exact Or.inl hsplit
  · refine Or.inr ?_
    have hh : h = (h ≫ e.inv) ≫ e.hom := by simp
    rw [hh]
    infer_instance

/-- **Precomposing an irreducible morphism with an isomorphism keeps it irreducible.** -/
theorem IsIrreducibleMorphism.iso_comp (hf : IsIrreducibleMorphism f) {X' : C} (e : X' ≅ X) :
    IsIrreducibleMorphism (e.hom ≫ f) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_iso_comp e f),
    fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp e.hom f), fun Z g h hgh => ?_⟩
  have hgh' : (e.inv ≫ g) ≫ h = f := by simp [hgh]
  rcases hf.factors (e.inv ≫ g) h hgh' with hsplit | hsplit
  · refine Or.inl ?_
    have hg : g = e.hom ≫ e.inv ≫ g := by simp
    rw [hg]
    infer_instance
  · exact Or.inr hsplit

/-- Irreducibility is invariant under an isomorphism of the target. -/
@[simp]
theorem isIrreducibleMorphism_comp_iso_iff {Y' : C} (e : Y ≅ Y') :
    IsIrreducibleMorphism (f ≫ e.hom) ↔ IsIrreducibleMorphism f := by
  refine ⟨fun hf => ?_, fun hf => hf.comp_iso e⟩
  have h : (f ≫ e.hom) ≫ e.symm.hom = f := by simp
  exact h ▸ hf.comp_iso e.symm

/-- Irreducibility is invariant under an isomorphism of the source. -/
@[simp]
theorem isIrreducibleMorphism_iso_comp_iff {X' : C} (e : X' ≅ X) :
    IsIrreducibleMorphism (e.hom ≫ f) ↔ IsIrreducibleMorphism f := by
  refine ⟨fun hf => ?_, fun hf => hf.iso_comp e⟩
  have h : e.symm.hom ≫ e.hom ≫ f = f := by simp
  exact h ▸ hf.iso_comp e.symm

/-! ### Zero morphisms -/

section Zero

variable [HasZeroMorphisms C]

/-- A zero morphism is never irreducible, in any category with zero morphisms. -/
@[simp]
theorem not_isIrreducibleMorphism_zero (X Y : C) : ¬ IsIrreducibleMorphism (0 : X ⟶ Y) := by
  intro hf
  rcases hf.factors (0 : X ⟶ X) (0 : X ⟶ Y) zero_comp with h | h
  · have hid : (0 : X ⟶ X) ≫ retraction (0 : X ⟶ X) = 𝟙 X := IsSplitMono.id _
    rw [zero_comp] at hid
    exact hf.not_isSplitMono (IsSplitMono.mk' ⟨0, by rw [zero_comp, hid]⟩)
  · exact hf.not_isSplitEpi h

/-- An irreducible morphism is nonzero. -/
theorem IsIrreducibleMorphism.ne_zero (hf : IsIrreducibleMorphism f) : f ≠ 0 :=
  fun h => not_isIrreducibleMorphism_zero X Y (h ▸ hf)

end Zero

/-! ### The monomorphism/epimorphism dichotomy -/

/-- **An irreducible morphism of a balanced category is not both a monomorphism and an
epimorphism**. -/
theorem IsIrreducibleMorphism.not_mono_and_epi [Balanced C] (hf : IsIrreducibleMorphism f) :
    ¬ (Mono f ∧ Epi f) := fun ⟨_, _⟩ => hf.not_isIso (isIso_of_mono_of_epi f)

/-- An irreducible morphism with an image in a category with equalizers is a monomorphism or an
epimorphism. -/
theorem IsIrreducibleMorphism.mono_or_epi [HasEqualizers C] [HasImage f]
    (hf : IsIrreducibleMorphism f) : Mono f ∨ Epi f := by
  rcases hf.factors (factorThruImage f) (image.ι f) (image.fac f) with h | h
  · refine Or.inl ?_
    have : IsIso (factorThruImage f) := isIso_of_epi_of_isSplitMono _
    rw [← image.fac f]
    infer_instance
  · refine Or.inr ?_
    have : IsIso (image.ι f) := isIso_of_mono_of_isSplitEpi _
    rw [← image.fac f]
    infer_instance

/-- An irreducible morphism with an image in a balanced category with equalizers is a
monomorphism exactly when it fails to be an epimorphism. -/
theorem IsIrreducibleMorphism.mono_iff_not_epi [HasEqualizers C] [HasImage f] [Balanced C]
    (hf : IsIrreducibleMorphism f) : Mono f ↔ ¬ Epi f :=
  ⟨fun hm he => hf.not_mono_and_epi ⟨hm, he⟩, fun he => hf.mono_or_epi.resolve_right he⟩

/-- An irreducible morphism with an image in a balanced category with equalizers is an
epimorphism exactly when it fails to be a monomorphism. -/
theorem IsIrreducibleMorphism.epi_iff_not_mono [HasEqualizers C] [HasImage f] [Balanced C]
    (hf : IsIrreducibleMorphism f) : Epi f ↔ ¬ Mono f :=
  ⟨fun he hm => hf.not_mono_and_epi ⟨hm, he⟩, fun hm => hf.mono_or_epi.resolve_left hm⟩

end TauCeti
