/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.CategoryTheory.DG.FullSubcategory
public import TauCeti.CategoryTheory.DG.HomotopyCategory

/-!
# Quasi-equivalences of differential graded categories

A DG functor is quasi-fully faithful when it induces a quasi-isomorphism on every Hom complex.
A quasi-equivalence additionally reaches every target object up to isomorphism in the homotopy
category. Full DG subcategories furnish a basic example: their inclusions are quasi-equivalences
exactly when each ambient object is isomorphic in `H⁰` to an object of the subcategory.

## References

* B. Keller, *Deriving DG categories*, Section 2.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
-/

public section

open CategoryTheory HomologicalComplex

namespace TauCeti

universe v u₁ u₂ u₃

variable {R : Type v} [CommRing R]
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [DGCategory R C] [DGCategory R D] [DGCategory R E]

namespace DGFunctor

/-- A DG functor is quasi-fully faithful if its map on each Hom complex is a
quasi-isomorphism, in every cohomological degree. -/
def IsQuasiFullyFaithful
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) : Prop :=
  ∀ X Y : C, QuasiIso (F.map X Y)

/-- A quasi-fully-faithful DG functor induces an isomorphism on the cohomology of each Hom
complex in every degree. -/
theorem IsQuasiFullyFaithful.isIso_homologyMap
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : IsQuasiFullyFaithful F) (X Y : C) (n : ℤ) :
    IsIso (homologyMap (F.map X Y) n) := by
  exact (quasiIsoAt_iff_isIso_homologyMap (F.map X Y) n).mp ((hF X Y).quasiIsoAt n)

/-- The identity DG functor is quasi-fully faithful. -/
theorem isQuasiFullyFaithful_id :
    IsQuasiFullyFaithful (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C) := by
  intro X Y
  change QuasiIso (𝟙 _)
  exact quasiIso_of_isIso _

/-- Composition preserves quasi-full faithfulness. -/
theorem IsQuasiFullyFaithful.comp
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    {G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) D E}
    (hF : IsQuasiFullyFaithful F) (hG : IsQuasiFullyFaithful G) :
    IsQuasiFullyFaithful (F.comp (CochainComplex (ModuleCat.{v} R) ℤ) G) := by
  intro X Y
  rw [EnrichedFunctor.comp_map]
  exact quasiIso_comp (F.map X Y) (G.map (F.obj X) (F.obj Y))
    (hφ := hF X Y) (hφ' := hG (F.obj X) (F.obj Y))

/-- A DG functor is a quasi-equivalence when it is a quasi-isomorphism on all Hom complexes
and every target object is isomorphic in `H⁰` to an object in its image. -/
def IsQuasiEquivalence
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) : Prop :=
  IsQuasiFullyFaithful F ∧
    ∀ Y : D, ∃ X : C,
      Nonempty (DGHomotopyCategory.of R (F.obj X) ≅ DGHomotopyCategory.of R Y)

/-- A quasi-equivalence is quasi-fully faithful. -/
theorem IsQuasiEquivalence.isQuasiFullyFaithful
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : IsQuasiEquivalence F) : IsQuasiFullyFaithful F := hF.1

/-- A quasi-equivalence reaches every target object up to isomorphism in `H⁰`. -/
theorem IsQuasiEquivalence.essentiallySurjective
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : IsQuasiEquivalence F) (Y : D) :
    ∃ X : C, Nonempty (DGHomotopyCategory.of R (F.obj X) ≅
      DGHomotopyCategory.of R Y) := hF.2 Y

/-- The identity DG functor is a quasi-equivalence. -/
theorem isQuasiEquivalence_id :
    IsQuasiEquivalence (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C) := by
  refine ⟨isQuasiFullyFaithful_id, ?_⟩
  intro Y
  exact ⟨Y, ⟨Iso.refl _⟩⟩

end DGFunctor

namespace DGFullSubcategory

variable {P : C → Prop}

/-- The inclusion of a full DG subcategory is quasi-fully faithful: its maps on Hom complexes
are identity maps. -/
theorem isQuasiFullyFaithful_inclusion :
    DGFunctor.IsQuasiFullyFaithful (inclusion (R := R) (P := P)) := by
  intro X Y
  rw [inclusion_map]
  infer_instance

/-- Inclusion of a full DG subcategory is a quasi-equivalence precisely when every ambient
object is isomorphic in `H⁰` to an object satisfying its predicate. -/
theorem isQuasiEquivalence_inclusion_iff :
    DGFunctor.IsQuasiEquivalence (inclusion (R := R) (P := P)) ↔
      ∀ Y : C, ∃ X : C, P X ∧
        Nonempty (DGHomotopyCategory.of R X ≅ DGHomotopyCategory.of R Y) := by
  constructor
  · intro h Y
    obtain ⟨X, hX⟩ := h.2 Y
    exact ⟨X.obj, X.property, by simpa only [inclusion_obj] using hX⟩
  · intro h
    refine ⟨isQuasiFullyFaithful_inclusion (R := R) (P := P), ?_⟩
    intro Y
    obtain ⟨X, hX, e⟩ := h Y
    exact ⟨⟨X, hX⟩, by simpa only [inclusion_obj] using e⟩

end DGFullSubcategory

end TauCeti
