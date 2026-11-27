/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.AbelianVariety
public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny
public import TauCeti.AlgebraicGeometry.GroupScheme.Isogeny.BaseChange
import TauCeti.AlgebraicGeometry.GroupScheme.Flat
import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

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

variable {S T : Scheme.{u}} {A B : AbelianScheme S}

/-- A homomorphism of abelian schemes is locally of finite presentation. -/
instance locallyOfFinitePresentation_toOverHom_left (f : A ⟶ B) :
    LocallyOfFinitePresentation (toOverHom f).left := by
  let g := toOverHom f
  let : LocallyOfFinitePresentation (g.left ≫ B.toOver.hom) :=
    (Over.w g).symm ▸ inferInstanceAs (LocallyOfFinitePresentation A.toOver.hom)
  exact locallyOfFinitePresentation_of_comp g.left B.toOver.hom

/-- The morphism property of being an isogeny of abelian schemes over `S`. -/
def isogenies (S : Scheme.{u}) : MorphismProperty (AbelianScheme S) :=
  (GroupScheme.isogenies S).inverseImage toGrpFunctor

/-- An isogeny of abelian schemes is a finite flat surjective homomorphism. -/
abbrev IsIsogeny (f : A ⟶ B) : Prop := isogenies S f

/-- Isogenies of abelian schemes are exactly the maps whose underlying group-scheme
homomorphisms are isogenies. -/
theorem isIsogeny_iff_toGrpFunctor_map (f : A ⟶ B) :
    IsIsogeny f ↔ GroupScheme.IsIsogeny (toGrpFunctor.map f) :=
  (Iff.rfl)

/-- An abelian-scheme homomorphism is an isogeny precisely when its underlying morphism
of schemes is finite, flat and surjective. -/
theorem isIsogeny_iff (f : A ⟶ B) :
    IsIsogeny f ↔
      IsFinite (toOverHom f).left ∧ Flat (toOverHom f).left ∧ Surjective (toOverHom f).left :=
  (isIsogeny_iff_toGrpFunctor_map f).trans (GroupScheme.isIsogeny_iff (toGrpFunctor.map f))

/-- Finiteness and surjectivity characterize isogenies of abelian schemes over any base. -/
@[simp]
theorem isIsogeny_iff_isFinite_surjective (f : A ⟶ B) :
    IsIsogeny f ↔ IsFinite (toOverHom f).left ∧ Surjective (toOverHom f).left := by
  rw [isIsogeny_iff]
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

/-- Arbitrary base change preserves isogenies of abelian schemes. -/
theorem IsIsogeny.baseChange {f : A ⟶ B} (hf : IsIsogeny f) (p : T ⟶ S) :
    IsIsogeny ((baseChangeFunctor p).map f) :=
  (isIsogeny_iff_toGrpFunctor_map _).mpr
    (GroupScheme.IsIsogeny.baseChange p ((isIsogeny_iff_toGrpFunctor_map f).mp hf))

/-- The functor to abelian varieties over a field preserves and reflects isogenies. -/
theorem isIsogeny_toAbelianVarietyFunctor_map_iff {k : Type u} [Field k]
    {X Y : AbelianScheme (Spec (.of k))} (f : X ⟶ Y) :
    AbelianVariety.IsIsogeny (toAbelianVarietyFunctor.map f) ↔ IsIsogeny f := by
  rw [AbelianVariety.isIsogeny_iff, isIsogeny_iff_isFinite_surjective]
  have h : AbelianVariety.Hom.toSchemeHom (toAbelianVarietyFunctor.map f) = (toOverHom f).left :=
    congrArg Over.Hom.left (toOverHom_toAbelianVarietyFunctor_map f)
  exact h ▸ Iff.rfl

end

end TauCeti.AlgebraicGeometry.AbelianScheme
