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
public import TauCeti.CategoryTheory.DG.Functor

/-!
# Quasi-equivalences of differential graded categories

A DG functor is quasi-fully faithful when it induces a quasi-isomorphism on every Hom complex.
A quasi-equivalence additionally reaches every target object up to isomorphism in the homotopy
category. Full DG subcategories furnish a basic example: their inclusions are quasi-equivalences
exactly when each ambient object is isomorphic in `H⁰` to an object of the subcategory.

On homotopy categories, a quasi-fully faithful DG functor `F` induces a fully faithful functor
`H⁰(F)`, and a quasi-equivalence induces an equivalence `H⁰(C) ≌ H⁰(D)`. The converse fails:
`H⁰(F)` only sees the degree-zero cohomology of the Hom complexes.

## Main results

* `CategoryTheory.EnrichedFunctor.IsQuasiFullyFaithful.full_mapDGHomotopyCategory` and
  `CategoryTheory.EnrichedFunctor.IsQuasiFullyFaithful.faithful_mapDGHomotopyCategory`: a
  quasi-fully faithful DG functor induces a fully faithful functor on homotopy categories.
* `CategoryTheory.EnrichedFunctor.isQuasiEquivalence_iff_isQuasiFullyFaithful_and_essSurj`:
  a quasi-equivalence is a quasi-fully faithful DG functor whose induced functor on homotopy
  categories is essentially surjective.
* `CategoryTheory.EnrichedFunctor.IsQuasiEquivalence.isEquivalence_mapDGHomotopyCategory`: a
  quasi-equivalence induces an equivalence of homotopy categories.
* `TauCeti.DGFullSubcategory.isQuasiEquivalence_inclusion_iff`: when the inclusion of a full DG
  subcategory is a quasi-equivalence.

## References

* B. Keller, *Deriving DG categories*, Section 2.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
-/

public section

open CategoryTheory HomologicalComplex

universe v u₁ u₂ u₃

variable {R : Type v} [CommRing R]
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [TauCeti.DGCategory R C] [TauCeti.DGCategory R D] [TauCeti.DGCategory R E]

namespace CategoryTheory.EnrichedFunctor

/-- A DG functor is quasi-fully faithful if its map on each Hom complex is a
quasi-isomorphism, in every cohomological degree. -/
def IsQuasiFullyFaithful
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) : Prop :=
  ∀ X Y : C, QuasiIso (F.map X Y)

/-- A quasi-fully-faithful DG functor induces an isomorphism on the cohomology of each Hom
complex in every degree. -/
theorem IsQuasiFullyFaithful.isIso_homologyMap
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : EnrichedFunctor.IsQuasiFullyFaithful F) (X Y : C) (n : ℤ) :
    IsIso (homologyMap (F.map X Y) n) := by
  exact (quasiIsoAt_iff_isIso_homologyMap (F.map X Y) n).mp ((hF X Y).quasiIsoAt n)

/-- A DG functor is quasi-fully faithful exactly when it induces isomorphisms on all Hom
cohomology groups. -/
theorem isQuasiFullyFaithful_iff_isIso_homologyMap
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    IsQuasiFullyFaithful F ↔
      ∀ (X Y : C) (n : ℤ), IsIso (homologyMap (F.map X Y) n) := by
  constructor
  · intro hF X Y n
    exact hF.isIso_homologyMap X Y n
  · intro hF X Y
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap (F.map X Y) n).mpr (hF X Y n)

/-- The identity DG functor is quasi-fully faithful. -/
@[simp]
theorem isQuasiFullyFaithful_id :
    EnrichedFunctor.IsQuasiFullyFaithful
      (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C) := by
  intro X Y
  -- `EnrichedFunctor.id` defines `map` to be the identity morphism; expose that
  -- definitional reduction so the isomorphism instance for identities applies.
  change QuasiIso (𝟙 _)
  exact quasiIso_of_isIso _

/-- Composition preserves quasi-full faithfulness. -/
theorem IsQuasiFullyFaithful.comp
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    {G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) D E}
    (hF : EnrichedFunctor.IsQuasiFullyFaithful F)
    (hG : EnrichedFunctor.IsQuasiFullyFaithful G) :
    EnrichedFunctor.IsQuasiFullyFaithful (F.comp (CochainComplex (ModuleCat.{v} R) ℤ) G) := by
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
      Nonempty (TauCeti.DGHomotopyCategory.of R (F.obj X) ≅
        TauCeti.DGHomotopyCategory.of R Y)

/-- A quasi-equivalence is quasi-fully faithful. -/
theorem IsQuasiEquivalence.isQuasiFullyFaithful
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : EnrichedFunctor.IsQuasiEquivalence F) :
    EnrichedFunctor.IsQuasiFullyFaithful F := hF.1

/-- A quasi-equivalence reaches every target object up to isomorphism in `H⁰`. -/
theorem IsQuasiEquivalence.essentiallySurjective
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : EnrichedFunctor.IsQuasiEquivalence F) (Y : D) :
    ∃ X : C, Nonempty (TauCeti.DGHomotopyCategory.of R (F.obj X) ≅
      TauCeti.DGHomotopyCategory.of R Y) := hF.2 Y

/-- The identity DG functor is a quasi-equivalence. -/
@[simp]
theorem isQuasiEquivalence_id :
    EnrichedFunctor.IsQuasiEquivalence
      (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C) := by
  refine ⟨isQuasiFullyFaithful_id, ?_⟩
  intro Y
  exact ⟨Y, ⟨Iso.refl _⟩⟩

/-! ### The induced functor on homotopy categories -/

/-- A quasi-fully faithful DG functor induces a bijection on every Hom of homotopy categories. -/
theorem IsQuasiFullyFaithful.mapDGHomotopyCategory_map_bijective
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : EnrichedFunctor.IsQuasiFullyFaithful F) (X Y : TauCeti.DGHomotopyCategory R C) :
    Function.Bijective (F.mapDGHomotopyCategory.map : (X ⟶ Y) → _) := by
  have := hF.isIso_homologyMap (TauCeti.DGHomotopyCategory.underlying R X)
    (TauCeti.DGHomotopyCategory.underlying R Y) 0
  -- The action of `H⁰(F)` on morphisms is the map induced on degree-zero cohomology.
  exact ConcreteCategory.bijective_of_isIso (homologyMap (F.map _ _) 0)

/-- A quasi-fully faithful DG functor induces a full functor on homotopy categories. -/
theorem IsQuasiFullyFaithful.full_mapDGHomotopyCategory
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : EnrichedFunctor.IsQuasiFullyFaithful F) : F.mapDGHomotopyCategory.Full :=
  ⟨fun {X Y} ↦ (hF.mapDGHomotopyCategory_map_bijective X Y).2⟩

/-- A quasi-fully faithful DG functor induces a faithful functor on homotopy categories. -/
theorem IsQuasiFullyFaithful.faithful_mapDGHomotopyCategory
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : EnrichedFunctor.IsQuasiFullyFaithful F) : F.mapDGHomotopyCategory.Faithful :=
  ⟨fun {X Y} ↦ (hF.mapDGHomotopyCategory_map_bijective X Y).1⟩

/-- A DG functor is a quasi-equivalence exactly when it is quasi-fully faithful and the functor
it induces on homotopy categories is essentially surjective. -/
theorem isQuasiEquivalence_iff_isQuasiFullyFaithful_and_essSurj
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    IsQuasiEquivalence F ↔ IsQuasiFullyFaithful F ∧ F.mapDGHomotopyCategory.EssSurj := by
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ⟨fun Y ↦ ?_⟩, fun h Y ↦ ?_⟩
  · obtain ⟨X, ⟨e⟩⟩ := h (TauCeti.DGHomotopyCategory.underlying R Y)
    -- `H⁰(F)` sends `X` to `F X`, and `Y` is the object of `H⁰(D)` on its underlying object.
    exact ⟨TauCeti.DGHomotopyCategory.of R X, ⟨e⟩⟩
  · obtain ⟨X, ⟨e⟩⟩ := h.mem_essImage (TauCeti.DGHomotopyCategory.of R Y)
    -- As above, `H⁰(F)` sends `X` to the object on `F` of its underlying object.
    exact ⟨TauCeti.DGHomotopyCategory.underlying R X, ⟨e⟩⟩

/-- A quasi-equivalence of DG categories induces an equivalence of homotopy categories. -/
theorem IsQuasiEquivalence.isEquivalence_mapDGHomotopyCategory
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : EnrichedFunctor.IsQuasiEquivalence F) : F.mapDGHomotopyCategory.IsEquivalence where
  faithful := hF.isQuasiFullyFaithful.faithful_mapDGHomotopyCategory
  full := hF.isQuasiFullyFaithful.full_mapDGHomotopyCategory
  essSurj := ((isQuasiEquivalence_iff_isQuasiFullyFaithful_and_essSurj F).1 hF).2

end CategoryTheory.EnrichedFunctor

namespace TauCeti

namespace DGFullSubcategory

variable {P : C → Prop}

/-- The inclusion of a full DG subcategory is quasi-fully faithful: its maps on Hom complexes
are identity maps. -/
@[simp]
theorem isQuasiFullyFaithful_inclusion :
    EnrichedFunctor.IsQuasiFullyFaithful (inclusion (R := R) (P := P)) := by
  intro X Y
  rw [inclusion_map]
  infer_instance

/-- Inclusion of a full DG subcategory is a quasi-equivalence precisely when every ambient
object is isomorphic in `H⁰` to an object satisfying its predicate. -/
@[simp]
theorem isQuasiEquivalence_inclusion_iff :
    EnrichedFunctor.IsQuasiEquivalence (inclusion (R := R) (P := P)) ↔
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
