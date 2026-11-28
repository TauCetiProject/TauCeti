/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.AbelianVariety
public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.Isogeny.BaseChange
import TauCeti.AlgebraicGeometry.GroupScheme.FaithfullyFlat

/-!
# Isogenies of abelian schemes

An isogeny of abelian schemes is a homomorphism that is finite, flat and surjective on
underlying schemes. For a finite surjective homomorphism, flatness follows by checking the
fibres over the base. This gives the finite-surjective criterion, even over nonreduced bases,
and identifies the relative predicate with the isogenies of abelian varieties under the field
equivalence.

The predicate uses `GroupScheme.isogenies` via the forgetful functor to group schemes, so
isogenies of abelian schemes can be used directly with group-scheme constructions.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.AbelianScheme

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S T : Scheme.{u}} {A B C : AbelianScheme S}

/-- The morphism property of being an isogeny of abelian schemes over `S`. -/
def isogenies (S : Scheme.{u}) : MorphismProperty (AbelianScheme S) :=
  (GroupScheme.isogenies S).inverseImage toGrpFunctor

/-- The abelian-scheme isogeny property is pulled back from group schemes. -/
theorem isogenies_eq_inverseImage (S : Scheme.{u}) :
    isogenies S = (GroupScheme.isogenies S).inverseImage toGrpFunctor := (rfl)

/-- An isogeny of abelian schemes is a finite flat surjective homomorphism. -/
abbrev IsIsogeny (f : A ⟶ B) : Prop := isogenies S f

/-- Finiteness and surjectivity characterize isogenies of abelian schemes over any base. -/
theorem isIsogeny_iff_isFinite_and_surjective (f : A ⟶ B) :
    IsIsogeny f ↔ IsFinite (toOverHom f).left ∧ Surjective (toOverHom f).left := by
  rw [IsIsogeny, isogenies_eq_inverseImage, MorphismProperty.inverseImage_iff]
  refine (GroupScheme.isIsogeny_iff (toGrpFunctor.map f)).trans ?_
  rw [toGrpFunctor_map_hom_hom]
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun ⟨hf, hs⟩ ↦
    ⟨hf, (toOverHom f).flat_left_of_finite_of_surjective, hs⟩⟩

/-- Isogenies of abelian schemes contain identities and are closed under composition. -/
instance : (isogenies S).IsMultiplicative := by
  unfold isogenies
  infer_instance

/-- Being an isogeny of abelian schemes is invariant under isomorphisms of arrows. -/
instance : (isogenies S).RespectsIso := by
  unfold isogenies
  infer_instance

/-- The identity homomorphism of an abelian scheme is an isogeny. -/
@[simp]
theorem isIsogeny_id (A : AbelianScheme S) : IsIsogeny (𝟙 A) :=
  (isogenies S).id_mem A

/-- Every isomorphism of abelian schemes is an isogeny. -/
theorem isIsogeny_of_isIso (f : A ⟶ B) [IsIso f] : IsIsogeny f :=
  (isogenies S).of_isIso f

namespace IsIsogeny

/-- The underlying scheme morphism of an abelian-scheme isogeny is finite. -/
theorem isFinite {f : A ⟶ B} (hf : IsIsogeny f) : IsFinite (toOverHom f).left :=
  (isIsogeny_iff_isFinite_and_surjective f).mp hf |>.1

/-- The underlying scheme morphism of an abelian-scheme isogeny is flat. -/
theorem flat {f : A ⟶ B} (hf : IsIsogeny f) : Flat (toOverHom f).left := by
  rw [IsIsogeny, isogenies_eq_inverseImage, MorphismProperty.inverseImage_iff] at hf
  rw [← toGrpFunctor_map_hom_hom]
  exact GroupScheme.IsIsogeny.flat hf

/-- The underlying scheme morphism of an abelian-scheme isogeny is surjective. -/
theorem surjective {f : A ⟶ B} (hf : IsIsogeny f) : Surjective (toOverHom f).left :=
  (isIsogeny_iff_isFinite_and_surjective f).mp hf |>.2

/-- A composite of abelian-scheme isogenies is an isogeny. -/
theorem comp {f : A ⟶ B} {g : B ⟶ C} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (f ≫ g) :=
  (isogenies S).comp_mem f g hf hg

/-- Arbitrary base change preserves isogenies of abelian schemes. -/
theorem baseChange {f : A ⟶ B} (hf : IsIsogeny f) (p : T ⟶ S) :
    IsIsogeny ((baseChangeFunctor p).map f) := by
  simp only [IsIsogeny, isogenies_eq_inverseImage, MorphismProperty.inverseImage_iff] at hf ⊢
  exact GroupScheme.IsIsogeny.baseChange p hf

end IsIsogeny

/-- The functor to abelian varieties over a field preserves and reflects isogenies. -/
theorem isIsogeny_toAbelianVarietyFunctor_map_iff {k : Type u} [Field k]
    {X Y : AbelianScheme (Spec (.of k))} (f : X ⟶ Y) :
    AbelianVariety.IsIsogeny (toAbelianVarietyFunctor.map f) ↔ IsIsogeny f := by
  rw [AbelianVariety.isIsogeny_iff, isIsogeny_iff_isFinite_and_surjective]
  have h : AbelianVariety.Hom.toSchemeHom (toAbelianVarietyFunctor.map f) = (toOverHom f).left :=
    congrArg Over.Hom.left (toOverHom_toAbelianVarietyFunctor_map f)
  exact h ▸ Iff.rfl

end

end TauCeti.AlgebraicGeometry.AbelianScheme
