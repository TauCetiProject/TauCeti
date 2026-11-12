/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Sequence

/-!
# Almost-split sequences and equivalences

Equivalences preserve and reflect almost-split morphisms and almost-split sequences.
The essential surjectivity is needed for preservation: the factorization property must hold
for every object of the target category. This allows almost-split sequences to be transported
between module categories and equivalent categories of representations.
-/

public section

open TauCeti CategoryTheory.Limits

namespace CategoryTheory.Functor

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D) [F.IsEquivalence] {X Y : C} (f : X ⟶ Y)

/-- An equivalence preserves and reflects right almost-split morphisms. -/
@[simp]
theorem isRightAlmostSplit_map_iff : IsRightAlmostSplit (F.map f) ↔ IsRightAlmostSplit f := by
  classical
  constructor
  · intro hf
    refine isRightAlmostSplit_iff.mpr ⟨fun hs ↦ hf.not_isSplitEpi
      ((F.isSplitEpi_iff f).mpr hs), fun Z g hg ↦ ?_⟩
    obtain ⟨h, hh⟩ := hf.factors (F.obj Z) (F.map g)
      (fun hs ↦ hg ((F.isSplitEpi_iff g).mp hs))
    exact ⟨F.preimage h, F.map_injective (by simpa using hh)⟩
  · intro hf
    refine isRightAlmostSplit_iff.mpr ⟨fun hs ↦ hf.not_isSplitEpi
      ((F.isSplitEpi_iff f).mp hs), fun Z g hg ↦ ?_⟩
    let e := F.objObjPreimageIso Z
    let g' := F.preimage (e.hom ≫ g)
    have hg' : ¬ IsSplitEpi g' := by
      intro hs
      have : IsSplitEpi (e.hom ≫ g) := by simpa [g'] using (F.isSplitEpi_iff g').mpr hs
      exact hg (isSplitEpi_of_isSplitEpi_comp e.hom g)
    obtain ⟨h, hh⟩ := hf.factors _ g' hg'
    refine ⟨e.inv ≫ F.map h, ?_⟩
    rw [Category.assoc, ← F.map_comp, hh]
    simp [g']

/-- An equivalence preserves and reflects left almost-split morphisms. -/
@[simp]
theorem isLeftAlmostSplit_map_iff : IsLeftAlmostSplit (F.map f) ↔ IsLeftAlmostSplit f := by
  simpa only [Functor.op_map, Quiver.Hom.unop_op, isRightAlmostSplit_op_iff] using
    F.op.isRightAlmostSplit_map_iff f.op

end CategoryTheory.Functor

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) [S.HasHomology] (F : C ⥤ D) [F.IsEquivalence]
  [F.PreservesZeroMorphisms]

/-- An equivalence preserving zero morphisms preserves and reflects almost-split sequences. -/
@[simp]
theorem isAlmostSplit_map_iff : (S.map F).IsAlmostSplit ↔ S.IsAlmostSplit := by
  constructor
  · intro h
    exact ⟨{ exact := (S.exact_map_iff_of_faithful F).mp h.shortExact.exact
             mono_f := F.mono_of_mono_map h.shortExact.mono_f
             epi_g := F.epi_of_epi_map h.shortExact.epi_g },
      (F.isLeftAlmostSplit_map_iff S.f).mp h.isLeftAlmostSplit_f,
      (F.isRightAlmostSplit_map_iff S.g).mp h.isRightAlmostSplit_g⟩
  · intro h
    have := h.shortExact.mono_f
    have := h.shortExact.epi_g
    exact ⟨h.shortExact.map F,
      (F.isLeftAlmostSplit_map_iff S.f).mpr h.isLeftAlmostSplit_f,
      (F.isRightAlmostSplit_map_iff S.g).mpr h.isRightAlmostSplit_g⟩

end CategoryTheory.ShortComplex
