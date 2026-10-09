/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Irreducible
public import TauCeti.CategoryTheory.AlmostSplit.Minimal
import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Irreducible components of almost-split sequences

For an almost-split sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, the irreducible maps into `C` are exactly
the composites of split monomorphisms into `B` with the final map. Dually, the irreducible maps
out of `A` are exactly the composites of the initial map with split epimorphisms out of `B`.
Thus the retracts of the middle term determine the possible endpoints of arrows in the
Auslander–Reiten quiver: an irreducible map `X ⟶ C` exists exactly when one `A ⟶ X` exists.
This is the support of the mesh relation; it does not compute arrow multiplicities.

The results use local endomorphism rings for the ends and require only that the tested object
is nonzero. In categories of finite-length modules the locality assumptions are supplied by
indecomposability and Fitting's lemma. Minimality of the maps is derived from the almost-split
sequence, rather than assumed separately.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, V.5.
-/

public section

open CategoryTheory TauCeti

universe v u

namespace CategoryTheory.ShortComplex.IsAlmostSplit

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
  {S : ShortComplex C} {X : C}
  [IsLocalRing (End S.X₁)] [IsLocalRing (End S.X₃)]

/-- Restricting the final map of an almost-split sequence to a retract of its middle term
gives an irreducible morphism when the retract is nonzero. -/
theorem isIrreducibleMorphism_comp_g (hS : S.IsAlmostSplit)
    (hX : ¬ Limits.IsZero X) (i : X ⟶ S.X₂) [IsSplitMono i] : IsIrreducibleMorphism (i ≫ S.g) := by
  apply hS.isRightAlmostSplit_g.isIrreducibleMorphism_comp_of_isSplitMono
    hS.isIso_of_comp_g_eq i
  have hrad := comp_mem_jacobsonRadical_left i
    (mem_jacobsonRadical_iff_not_isSplitEpi.mpr hS.isRightAlmostSplit_g.not_isSplitEpi)
  intro hi
  have hradId : 𝟙 X ∈ jacobsonRadical X X := by
    simpa only [IsSplitMono.id] using comp_mem_jacobsonRadical_right hrad (retraction (i ≫ S.g))
  exact hX ((Limits.IsZero.iff_id_eq_zero X).mpr
    (id_eq_zero_of_isIso_of_mem_jacobsonRadical hradId))

/-- Projecting the initial map of an almost-split sequence onto a retract of its middle term
gives an irreducible morphism when the retract is nonzero. -/
theorem isIrreducibleMorphism_f_comp (hS : S.IsAlmostSplit)
    (hX : ¬ Limits.IsZero X) (p : S.X₂ ⟶ X) [IsSplitEpi p] : IsIrreducibleMorphism (S.f ≫ p) := by
  apply hS.isLeftAlmostSplit_f.isIrreducibleMorphism_comp_of_isSplitEpi
    hS.isIso_of_f_comp_eq p
  have hrad := comp_mem_jacobsonRadical_right
    (mem_jacobsonRadical_iff_not_isSplitMono.mpr hS.isLeftAlmostSplit_f.not_isSplitMono) p
  intro hp
  have hradId : 𝟙 X ∈ jacobsonRadical X X := by
    simpa only [IsSplitEpi.id] using comp_mem_jacobsonRadical_left (section_ (S.f ≫ p)) hrad
  exact hX ((Limits.IsZero.iff_id_eq_zero X).mpr
    (id_eq_zero_of_isIso_of_mem_jacobsonRadical hradId))

/-- A morphism into the right-hand end is irreducible exactly when it is the restriction of
the final map to a retract of the middle term. -/
theorem isIrreducibleMorphism_iff_exists_isSplitMono (hS : S.IsAlmostSplit)
    (hX : ¬ Limits.IsZero X) (g : X ⟶ S.X₃) :
    IsIrreducibleMorphism g ↔ ∃ i : X ⟶ S.X₂, IsSplitMono i ∧ i ≫ S.g = g := by
  refine ⟨hS.isRightAlmostSplit_g.exists_isSplitMono_of_isIrreducibleMorphism, ?_⟩
  rintro ⟨i, hi, rfl⟩
  exact hS.isIrreducibleMorphism_comp_g hX i

/-- A morphism out of the left-hand end is irreducible exactly when it is the projection of
the initial map onto a retract of the middle term. -/
theorem isIrreducibleMorphism_iff_exists_isSplitEpi (hS : S.IsAlmostSplit)
    (hX : ¬ Limits.IsZero X) (g : S.X₁ ⟶ X) :
    IsIrreducibleMorphism g ↔ ∃ p : S.X₂ ⟶ X, IsSplitEpi p ∧ S.f ≫ p = g := by
  refine ⟨hS.isLeftAlmostSplit_f.exists_isSplitEpi_of_isIrreducibleMorphism, ?_⟩
  rintro ⟨p, hp, rfl⟩
  exact hS.isIrreducibleMorphism_f_comp hX p

/-- The support of the Auslander–Reiten mesh relation: a nonzero object admits an
irreducible morphism into the right-hand end exactly when it admits one out of the left-hand end. -/
theorem exists_isIrreducibleMorphism_into_iff_out_of (hS : S.IsAlmostSplit)
    (hX : ¬ Limits.IsZero X) :
    (∃ g : X ⟶ S.X₃, IsIrreducibleMorphism g) ↔
      ∃ g : S.X₁ ⟶ X, IsIrreducibleMorphism g := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨i, hi, -⟩ := hS.isRightAlmostSplit_g.exists_isSplitMono_of_isIrreducibleMorphism hg
    exact ⟨S.f ≫ retraction i, hS.isIrreducibleMorphism_f_comp hX (retraction i)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨p, hp, -⟩ := hS.isLeftAlmostSplit_f.exists_isSplitEpi_of_isIrreducibleMorphism hg
    exact ⟨section_ p ≫ S.g, hS.isIrreducibleMorphism_comp_g hX (section_ p)⟩

end CategoryTheory.ShortComplex.IsAlmostSplit
