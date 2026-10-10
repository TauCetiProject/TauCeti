/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Uniqueness
import TauCeti.CategoryTheory.Exact.Abelian
import TauCeti.CategoryTheory.Exact.BaseChange

/-!
# Minimal morphisms and almost-split sequences

In an abelian category, a short exact sequence whose final map is right almost split and
right minimal is almost split. Dually, left almost splitness and left minimality of the
initial map suffice. These criteria let a construction of an almost-split sequence supply
only one of its two lifting properties.

Minimality is stated explicitly: an endomorphism fixing the specified map is invertible.
This agrees with the convention in `TauCeti.CategoryTheory.AlmostSplit.Irreducible`.
No finite-length or locality hypothesis is needed for either criterion. Conversely, the maps
of an almost-split sequence are minimal when the opposite end has a local endomorphism ring.

The pushout argument uses `TauCeti.ExactStructure.conflation_cobaseChange` for the
canonical exact structure of an abelian category.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, V.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C}

/-- In a short exact sequence, right almost splitness and right minimality of the final
map imply left almost splitness of the initial map. -/
theorem IsRightAlmostSplit.isLeftAlmostSplit_of_minimal (hg : IsRightAlmostSplit S.g)
    (hS : S.ShortExact) (hmin : ∀ b : S.X₂ ⟶ S.X₂, b ≫ S.g = S.g → IsIso b) :
    IsLeftAlmostSplit S.f := by
  have := hS.mono_f
  have := hS.epi_g
  refine isLeftAlmostSplit_iff.mpr ⟨?_, fun X h hh ↦ ?_⟩
  · intro hf
    exact hg.not_isSplitEpi
      (ShortComplex.Splitting.ofExactOfRetraction S hS.exact
        (retraction S.f) (IsSplitMono.id S.f) inferInstance).isSplitEpi_g
  · let sq := IsPushout.of_hasPushout S.f h
    let q := cobaseChangeπ S sq
    have hT : (cobaseChange S sq).ShortExact :=
      (ExactStructure.abelian_conflation _).mp
        ((ExactStructure.abelian C).conflation_cobaseChange
          ((ExactStructure.abelian_conflation S).mpr hS) sq)
    rw [cobaseChange_def] at hT
    -- If the pushout splits, its retraction extends `h` across `S.f`.
    by_cases hq : IsSplitEpi q
    · let s := ShortComplex.Splitting.ofExactOfSection _ hT.exact
        (section_ q) (IsSplitEpi.id q) hT.mono_f
      exact ⟨pushout.inl S.f h ≫ s.r, by
        rw [← Category.assoc, pushout.condition, Category.assoc, s.f_r, Category.comp_id]⟩
    -- Otherwise factor its final map through `S.g`; minimality inverts the comparison.
    · obtain ⟨t, ht⟩ := hg.factors (pushout S.f h) q hq
      let b := pushout.inl S.f h ≫ t
      have hb : b ≫ S.g = S.g := by
        simp only [b, Category.assoc, ht, q, inl_cobaseChangeπ]
      have := hmin b hb
      have hinv : inv b ≫ S.g = S.g := by
        calc
          inv b ≫ S.g = inv b ≫ (b ≫ S.g) := congrArg (inv b ≫ ·) hb.symm
          _ = S.g := by simp
      have hz : (pushout.inr S.f h ≫ t ≫ inv b) ≫ S.g = 0 := by
        simp only [Category.assoc, hinv, ht, q, inr_cobaseChangeπ]
      obtain ⟨r, hr⟩ := hS.exact.lift' (pushout.inr S.f h ≫ t ≫ inv b) hz
      have hhr : h ≫ r = 𝟙 S.X₁ := by
        apply (cancel_mono S.f).mp
        rw [Category.assoc, hr, ← Category.assoc h, ← pushout.condition]
        have hinl : pushout.inl S.f h ≫ t ≫ inv b = 𝟙 S.X₂ := by
          simpa only [b, Category.assoc] using IsIso.hom_inv_id b
        simp only [Category.assoc, hinl, Category.comp_id, Category.id_comp]
      exact (hh (IsSplitMono.mk' ⟨r, hhr⟩)).elim

/-- In a short exact sequence, left almost splitness and left minimality of the initial
map imply right almost splitness of the final map. -/
theorem IsLeftAlmostSplit.isRightAlmostSplit_of_minimal (hf : IsLeftAlmostSplit S.f)
    (hS : S.ShortExact) (hmin : ∀ b : S.X₂ ⟶ S.X₂, S.f ≫ b = S.f → IsIso b) :
    IsRightAlmostSplit S.g := by
  -- Use the underlying opposite objects so `unop_comp` does not have to reduce
  -- the object projections of the opposite short complex.
  have hminop (b : Opposite.op S.X₂ ⟶ Opposite.op S.X₂)
      (hb : b ≫ S.f.op = S.f.op) : IsIso b := by
    have := hmin b.unop (by
      simpa only [unop_comp, Quiver.Hom.unop_op] using congrArg Quiver.Hom.unop hb)
    exact (isIso_unop_iff b).mp inferInstance
  exact isLeftAlmostSplit_op_iff.mp
    ((isRightAlmostSplit_op_iff.mpr hf).isLeftAlmostSplit_of_minimal hS.op hminop)

end TauCeti

namespace CategoryTheory.ShortComplex

section Balanced

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S : ShortComplex C}

namespace IsAlmostSplit

/-- The final map of an almost-split sequence is right minimal when the left-hand end has
a local endomorphism ring. -/
theorem isIso_of_comp_g_eq (hS : S.IsAlmostSplit) [IsLocalRing (End S.X₁)]
    (b : S.X₂ ⟶ S.X₂) (hb : b ≫ S.g = S.g) : IsIso b := by
  have := hS.shortExact.mono_f
  obtain ⟨a, ha⟩ := hS.shortExact.exact.lift' (S.f ≫ b) (by simp [hb])
  let φ : S ⟶ S := ⟨a, b, 𝟙 S.X₃, ha, by simp [hb]⟩
  have : IsIso φ := hS.isLeftAlmostSplit_f.isIso_of_τ₃_eq_id hS.shortExact φ (by rfl)
  exact ((ShortComplex.π₂ : ShortComplex C ⥤ C).mapIso (asIso φ)).isIso_hom

/-- The initial map of an almost-split sequence is left minimal when the right-hand end has
a local endomorphism ring. -/
theorem isIso_of_f_comp_eq (hS : S.IsAlmostSplit) [IsLocalRing (End S.X₃)]
    (b : S.X₂ ⟶ S.X₂) (hb : S.f ≫ b = S.f) : IsIso b := by
  have := hS.shortExact.epi_g
  obtain ⟨c, hc⟩ := hS.shortExact.exact.desc' (b ≫ S.g) (by simp [← Category.assoc, hb])
  let φ : S ⟶ S := ⟨𝟙 S.X₁, b, c, by simp [hb], hc.symm⟩
  have : IsIso φ := hS.isRightAlmostSplit_g.isIso_of_τ₁_eq_id hS.shortExact φ (by rfl)
  exact ((ShortComplex.π₂ : ShortComplex C ⥤ C).mapIso (asIso φ)).isIso_hom

end IsAlmostSplit

end Balanced

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C}

/-- A short exact sequence with a right minimal right almost split final map is almost
split. -/
theorem ShortExact.isAlmostSplit_of_isRightAlmostSplit (hS : S.ShortExact)
    (hg : TauCeti.IsRightAlmostSplit S.g)
    (hmin : ∀ b : S.X₂ ⟶ S.X₂, b ≫ S.g = S.g → IsIso b) : S.IsAlmostSplit :=
  ⟨hS, hg.isLeftAlmostSplit_of_minimal hS hmin, hg⟩

/-- A short exact sequence with a left minimal left almost split initial map is almost
split. -/
theorem ShortExact.isAlmostSplit_of_isLeftAlmostSplit (hS : S.ShortExact)
    (hf : TauCeti.IsLeftAlmostSplit S.f)
    (hmin : ∀ b : S.X₂ ⟶ S.X₂, S.f ≫ b = S.f → IsIso b) : S.IsAlmostSplit :=
  ⟨hS, hf, hf.isRightAlmostSplit_of_minimal hS hmin⟩

end CategoryTheory.ShortComplex
