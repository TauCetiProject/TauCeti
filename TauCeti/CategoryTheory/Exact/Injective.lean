/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Opposite
public import TauCeti.CategoryTheory.Exact.Projective

/-!
# Relative injectives in an exact category

This file develops injectivity relative to a Quillen exact structure. An object is injective when
maps into it extend across the inflations of the chosen structure. Thus the notion depends on the
exact structure: every object is injective for the split structure, while the canonical structure
on an abelian category recovers Mathlib's ordinary injective objects.

Relative injectivity is the formal dual of relative projectivity. The equivalence is made explicit
by `TauCeti.ExactStructure.isInjective_iff_isProjective_op`, so results about projectives can be
transported through the opposite exact structure without maintaining parallel hypotheses.

The splitting API is also dual. A conflation whose first term is injective splits because its
inflation has a retraction.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>, Sections 11–12.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C}

/-- The objects injective relative to `E`: maps into such an object extend across every inflation
of the exact structure. -/
def isInjective (E : ExactStructure C) : ObjectProperty C := fun I =>
  ∀ ⦃X Y : C⦄ {i : X ⟶ Y}, E.IsInflation i → ∀ f : X ⟶ I, ∃ g : Y ⟶ I, i ≫ g = f

/-- The defining extension property for relative injectivity. -/
theorem isInjective_iff {I : C} :
    E.isInjective I ↔
      ∀ ⦃X Y : C⦄ {i : X ⟶ Y}, E.IsInflation i → ∀ f : X ⟶ I, ∃ g : Y ⟶ I, i ≫ g = f :=
  Iff.rfl

namespace isInjective

/-- The chosen extension of `f : X ⟶ I` across an inflation `i : X ⟶ Y`. -/
noncomputable def factorThru {I : C} (hI : E.isInjective I) {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) (f : X ⟶ I) : Y ⟶ I :=
  (hI hi f).choose

@[reassoc (attr := simp)]
theorem comp_factorThru {I : C} (hI : E.isInjective I) {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) (f : X ⟶ I) : i ≫ hI.factorThru hi f = f :=
  (hI hi f).choose_spec

end isInjective

/-- Relative injectivity is invariant under isomorphism. -/
instance : (E.isInjective).IsClosedUnderIsomorphisms where
  of_iso e hI _ _ _ hi f :=
    ⟨hI.factorThru hi (f ≫ e.inv) ≫ e.hom, by simp⟩

/-- A zero object is injective relative to every exact structure. -/
instance : (E.isInjective).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by
    intro _ _ _ _ f
    exact ⟨0, (isZero_zero C).eq_of_tgt _ f⟩⟩

/-- A binary direct sum of relatively injective objects is relatively injective. -/
theorem isInjective_biprod {I₁ I₂ : C} (h₁ : E.isInjective I₁) (h₂ : E.isInjective I₂) :
    E.isInjective (I₁ ⊞ I₂) := by
  intro X Y i hi f
  refine ⟨biprod.lift (h₁.factorThru hi (f ≫ biprod.fst))
    (h₂.factorThru hi (f ≫ biprod.snd)), ?_⟩
  apply biprod.hom_ext <;> simp

/-- Relative injectives are closed under binary products; in a preadditive category these are
biproducts. -/
instance : (E.isInjective).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod (E.isInjective)
    fun _ _ h₁ h₂ ↦ isInjective_biprod h₁ h₂

/-- A conflation with injective first term splits. The retraction of its inflation is the extension
of the identity of that term. -/
noncomputable def splittingOfInjective (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₁ : E.isInjective S.X₁) : S.Splitting :=
  let r := h₁.factorThru (E.isInflation_f hS) (𝟙 S.X₁)
  let h := E.isKernelCokernelPair S hS
  {
    r := r
    s := h.desc (𝟙 S.X₂ - r ≫ S.f) (by
      dsimp only [r]
      simp)
    f_r := h₁.comp_factorThru (E.isInflation_f hS) (𝟙 S.X₁)
    s_g := by
      have := h.epi_g
      rw [← cancel_epi S.g]
      simp
    id := by simp
  }

@[simp]
theorem splittingOfInjective_r (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₁ : E.isInjective S.X₁) :
    (E.splittingOfInjective hS h₁).r =
      h₁.factorThru (E.isInflation_f hS) (𝟙 S.X₁) :=
  (rfl)

@[simp]
theorem splittingOfInjective_s (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₁ : E.isInjective S.X₁) :
    (E.splittingOfInjective hS h₁).s = (E.isKernelCokernelPair S hS).desc
      (𝟙 S.X₂ - h₁.factorThru (E.isInflation_f hS) (𝟙 S.X₁) ≫ S.f) (by simp) :=
  (rfl)

/-- Every object is injective for the split exact structure. -/
@[simp]
theorem split_isInjective (X : C) : (ExactStructure.split C).isInjective X := by
  intro Y Z i hi f
  obtain ⟨W, e, he⟩ := (ExactStructure.split_isInflation_iff i).mp hi
  exact ⟨e.hom ≫ biprod.fst ≫ f, by simp only [← Category.assoc, he, biprod.inl_fst,
    Category.id_comp]⟩

/-- For the canonical exact structure of an abelian category, relative injectivity is Mathlib's
ordinary categorical injectivity. -/
@[simp]
theorem abelian_isInjective_iff {A : Type u} [Category.{v} A] [Abelian A] (X : A) :
    (ExactStructure.abelian A).isInjective X ↔ Injective X := by
  constructor
  · exact fun h ↦ ⟨fun f i hi ↦ h ((abelian_isInflation_iff i).mpr hi) f⟩
  · intro h Y Z i hi f
    have : Mono i := (abelian_isInflation_iff i).mp hi
    exact h.factors f i

/-- Relative injectivity in `C` is relative projectivity in the opposite exact category. -/
theorem isInjective_iff_isProjective_op (I : C) :
    E.isInjective I ↔ E.op.isProjective (Opposite.op I) := by
  constructor
  · rw [isProjective_iff]
    intro hI X Y p hp f
    rw [isInjective_iff] at hI
    obtain ⟨g, hg⟩ := hI ((E.op_isDeflation_iff p).mp hp) f.unop
    exact ⟨g.op, Quiver.Hom.unop_inj (by simpa using hg)⟩
  · rw [isInjective_iff]
    intro hI X Y i hi f
    rw [isProjective_iff] at hI
    obtain ⟨g, hg⟩ := hI ((E.op_isDeflation_iff i.op).mpr (by simpa)) f.op
    exact ⟨g.unop, Quiver.Hom.op_inj (by simpa using hg)⟩

/-- Relative projectivity in `C` is relative injectivity in the opposite exact category. -/
theorem isProjective_iff_isInjective_op (P : C) :
    E.isProjective P ↔ E.op.isInjective (Opposite.op P) := by
  constructor
  · rw [isInjective_iff]
    intro hP X Y i hi f
    rw [isProjective_iff] at hP
    obtain ⟨g, hg⟩ := hP ((E.op_isInflation_iff i).mp hi) f.unop
    exact ⟨g.op, Quiver.Hom.unop_inj (by simpa using hg)⟩
  · rw [isProjective_iff]
    intro hP X Y p hp f
    rw [isInjective_iff] at hP
    obtain ⟨g, hg⟩ := hP ((E.op_isInflation_iff p.op).mpr (by simpa)) f.op
    exact ⟨g.unop, Quiver.Hom.op_inj (by simpa using hg)⟩

end ExactStructure

end TauCeti
