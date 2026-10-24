/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Uniqueness
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.CategoryTheory.Exact.Abelian

/-!
# Minimal morphisms and almost-split sequences

In an abelian category, a short exact sequence whose final map is right almost split and
right minimal is almost split. Dually, left almost splitness and left minimality of the
initial map suffice. These criteria let a construction of an almost-split sequence supply
only one of its two lifting properties.

Minimality is stated explicitly: an endomorphism fixing the specified map is invertible.
This agrees with the convention in `TauCeti.CategoryTheory.AlmostSplit.Irreducible`.
No finite-length or locality hypothesis is needed when minimality is supplied. If the opposite
end has a local endomorphism ring, non-splitness already implies minimality, so a single
almost-split lifting property suffices. Conversely, the maps of an almost-split sequence are
minimal when the opposite end has a local endomorphism ring.

The pushout argument uses `TauCeti.shortExact_cobaseChange`.

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
  refine isLeftAlmostSplit_iff.mpr ⟨?_, fun X h hh ↦ ?_⟩
  · exact fun hf ↦ hg.not_isSplitEpi ((isSplitMono_f_iff_isSplitEpi_g hS).mp hf)
  · let sq := IsPushout.of_hasPushout S.f h
    let q := cobaseChangeπ S sq
    have hT := shortExact_cobaseChange hS sq
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
    (b : S.X₂ ⟶ S.X₂) (hb : b ≫ S.g = S.g) : IsIso b :=
  hS.shortExact.isIso_of_comp_g_eq hS.isLeftAlmostSplit_f.not_isSplitMono b hb

/-- The initial map of an almost-split sequence is left minimal when the right-hand end has
a local endomorphism ring. -/
theorem isIso_of_f_comp_eq (hS : S.IsAlmostSplit) [IsLocalRing (End S.X₃)]
    (b : S.X₂ ⟶ S.X₂) (hb : S.f ≫ b = S.f) : IsIso b :=
  hS.shortExact.isIso_of_f_comp_eq hS.isRightAlmostSplit_g.not_isSplitEpi b hb

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

/-- A short exact sequence with local left-hand endomorphism ring is almost split exactly
when its final map is right almost split. No separate minimality assumption is needed. -/
theorem ShortExact.isAlmostSplit_iff_isRightAlmostSplit (hS : S.ShortExact)
    [IsLocalRing (End S.X₁)] : S.IsAlmostSplit ↔ TauCeti.IsRightAlmostSplit S.g := by
  refine ⟨fun h ↦ h.isRightAlmostSplit_g, fun hg ↦ ?_⟩
  have hf : ¬ IsSplitMono S.f := fun hf ↦
    hg.not_isSplitEpi ((TauCeti.isSplitMono_f_iff_isSplitEpi_g hS).mp hf)
  exact hS.isAlmostSplit_of_isRightAlmostSplit hg (hS.isIso_of_comp_g_eq hf)

/-- A short exact sequence with local right-hand endomorphism ring is almost split exactly
when its initial map is left almost split. No separate minimality assumption is needed. -/
theorem ShortExact.isAlmostSplit_iff_isLeftAlmostSplit (hS : S.ShortExact)
    [IsLocalRing (End S.X₃)] : S.IsAlmostSplit ↔ TauCeti.IsLeftAlmostSplit S.f := by
  refine ⟨fun h ↦ h.isLeftAlmostSplit_f, fun hf ↦ ?_⟩
  have hg : ¬ IsSplitEpi S.g := fun hg ↦
    hf.not_isSplitMono ((TauCeti.isSplitMono_f_iff_isSplitEpi_g hS).mpr hg)
  exact hS.isAlmostSplit_of_isLeftAlmostSplit hf (hS.isIso_of_f_comp_eq hg)

end CategoryTheory.ShortComplex

namespace TauCeti

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Two right minimal right almost-split morphisms `f : X ⟶ Y` and `g : X' ⟶ Y`
have an isomorphism `e : X ≅ X'` satisfying `e.hom ≫ g = f`. -/
theorem IsRightAlmostSplit.exists_iso_of_minimal {X X' Y : C}
    {f : X ⟶ Y} {g : X' ⟶ Y} (hf : IsRightAlmostSplit f) (hg : IsRightAlmostSplit g)
    (hminf : ∀ b : X ⟶ X, b ≫ f = f → IsIso b)
    (hming : ∀ b : X' ⟶ X', b ≫ g = g → IsIso b) :
    ∃ e : X ≅ X', e.hom ≫ g = f := by
  obtain ⟨a, hag⟩ := hg.factors X f hf.not_isSplitEpi
  obtain ⟨b, hbf⟩ := hf.factors X' g hg.not_isSplitEpi
  have hab : (a ≫ b) ≫ f = f := by
    rw [Category.assoc, hbf, hag]
  have hba : (b ≫ a) ≫ g = g := by
    rw [Category.assoc, hag, hbf]
  have : IsIso (a ≫ b) := hminf (a ≫ b) hab
  have : IsIso (b ≫ a) := hming (b ≫ a) hba
  have : Mono a := mono_of_mono a b
  have : IsSplitEpi a := IsSplitEpi.mk' ⟨inv (b ≫ a) ≫ b, by simp [Category.assoc]⟩
  have : IsIso a := isIso_of_mono_of_isSplitEpi a
  exact ⟨asIso a, hag⟩

end TauCeti
