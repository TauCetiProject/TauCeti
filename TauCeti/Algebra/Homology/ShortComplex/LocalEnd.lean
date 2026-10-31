/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Non-split exact sequences with a local endomorphism ring

In a non-split short exact sequence, locality of the endomorphism ring at the left-hand end
makes the final map right minimal. Dually, locality at the right-hand end makes the initial
map left minimal. These facts let one construct almost-split sequences by establishing only
one lifting property, without separately assuming minimality of the middle map.

The underlying rigidity statement is stronger: an endomorphism of an exact short complex
fixing one end is invertible at the other end if that end has a local endomorphism ring and
the adjacent map does not split. Short exactness then gives invertibility of the whole
endomorphism by the short five lemma.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, V.1.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S : ShortComplex C}

/-- An endomorphism of an exact short complex fixing the right-hand end is invertible on the
left-hand end if its endomorphism ring is local and the initial monomorphism does not split. -/
theorem Exact.isIso_τ₁_of_τ₃_eq_id (hS : S.Exact) [Mono S.f] [IsLocalRing (End S.X₁)]
    (hf : ¬ IsSplitMono S.f) (φ : S ⟶ S) (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ.τ₁ := by
  have hker : (𝟙 S.X₂ - φ.τ₂) ≫ S.g = 0 := by
    simp [sub_comp, φ.comm₂₃, hφ]
  obtain ⟨γ, hγ⟩ := hS.lift' (𝟙 S.X₂ - φ.τ₂) hker
  have hfγ : S.f ≫ γ = 𝟙 S.X₁ - φ.τ₁ := by
    apply (cancel_mono S.f).mp
    simp [Category.assoc, hγ, comp_sub, sub_comp, φ.comm₁₂]
  have hnot : ¬ IsIso (𝟙 S.X₁ - φ.τ₁) := fun h ↦
    hf (IsSplitMono.mk' ⟨γ ≫ inv (𝟙 S.X₁ - φ.τ₁), by
      rw [← Category.assoc, hfγ, IsIso.hom_inv_id]⟩)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (R := End S.X₁) (.of φ.τ₁) with h | h
  · exact (isUnit_iff_isIso _).mp h
  · exact absurd ((isUnit_iff_isIso _).mp h) hnot

/-- An endomorphism of a non-split short exact sequence fixing the right-hand end is invertible
when the left-hand end has a local endomorphism ring. -/
theorem ShortExact.isIso_of_τ₃_eq_id (hS : S.ShortExact) [IsLocalRing (End S.X₁)]
    (hf : ¬ IsSplitMono S.f) (φ : S ⟶ S) (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ := by
  have := hS.mono_f
  have : IsIso φ.τ₁ := hS.exact.isIso_τ₁_of_τ₃_eq_id hf φ hφ
  have : IsIso φ.τ₃ := hφ ▸ inferInstanceAs (IsIso (𝟙 S.X₃))
  have : IsIso φ.τ₂ := isIso₂_of_shortExact_of_isIso₁₃ φ hS hS
  exact isIso_of_isIso φ

/-- An endomorphism of an exact short complex fixing the left-hand end is invertible on the
right-hand end if its endomorphism ring is local and the final epimorphism does not split. -/
theorem Exact.isIso_τ₃_of_τ₁_eq_id (hS : S.Exact) [Epi S.g] [IsLocalRing (End S.X₃)]
    (hg : ¬ IsSplitEpi S.g) (φ : S ⟶ S) (hφ : φ.τ₁ = 𝟙 S.X₁) : IsIso φ.τ₃ := by
  have hcoker : S.f ≫ (𝟙 S.X₂ - φ.τ₂) = 0 := by
    simp [comp_sub, ← φ.comm₁₂, hφ]
  obtain ⟨γ, hγ⟩ := hS.desc' (𝟙 S.X₂ - φ.τ₂) hcoker
  have hγg : γ ≫ S.g = 𝟙 S.X₃ - φ.τ₃ := by
    apply (cancel_epi S.g).mp
    rw [← Category.assoc, hγ]
    simp [sub_comp, comp_sub, φ.comm₂₃]
  have hnot : ¬ IsIso (𝟙 S.X₃ - φ.τ₃) := fun h ↦
    hg (IsSplitEpi.mk' ⟨inv (𝟙 S.X₃ - φ.τ₃) ≫ γ, by
      rw [Category.assoc, hγg, IsIso.inv_hom_id]⟩)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (R := End S.X₃) (.of φ.τ₃) with h | h
  · exact (isUnit_iff_isIso _).mp h
  · exact absurd ((isUnit_iff_isIso _).mp h) hnot

/-- An endomorphism of a non-split short exact sequence fixing the left-hand end is invertible
when the right-hand end has a local endomorphism ring. -/
theorem ShortExact.isIso_of_τ₁_eq_id (hS : S.ShortExact) [IsLocalRing (End S.X₃)]
    (hg : ¬ IsSplitEpi S.g) (φ : S ⟶ S) (hφ : φ.τ₁ = 𝟙 S.X₁) : IsIso φ := by
  have := hS.epi_g
  have : IsIso φ.τ₃ := hS.exact.isIso_τ₃_of_τ₁_eq_id hg φ hφ
  have : IsIso φ.τ₁ := hφ ▸ inferInstanceAs (IsIso (𝟙 S.X₁))
  have : IsIso φ.τ₂ := isIso₂_of_shortExact_of_isIso₁₃ φ hS hS
  exact isIso_of_isIso φ

/-- The final map of a non-split short exact sequence is right minimal if the left-hand end
has a local endomorphism ring. -/
theorem ShortExact.isIso_of_comp_g_eq (hS : S.ShortExact) [IsLocalRing (End S.X₁)]
    (hf : ¬ IsSplitMono S.f) (b : S.X₂ ⟶ S.X₂) (hb : b ≫ S.g = S.g) : IsIso b := by
  have := hS.mono_f
  obtain ⟨a, ha⟩ := hS.exact.lift' (S.f ≫ b) (by simp [hb])
  let φ : S ⟶ S := ⟨a, b, 𝟙 S.X₃, ha, by simp [hb]⟩
  have : IsIso φ := hS.isIso_of_τ₃_eq_id hf φ rfl
  exact ((π₂ : ShortComplex C ⥤ C).mapIso (asIso φ)).isIso_hom

/-- The initial map of a non-split short exact sequence is left minimal if the right-hand end
has a local endomorphism ring. -/
theorem ShortExact.isIso_of_f_comp_eq (hS : S.ShortExact) [IsLocalRing (End S.X₃)]
    (hg : ¬ IsSplitEpi S.g) (b : S.X₂ ⟶ S.X₂) (hb : S.f ≫ b = S.f) : IsIso b := by
  have := hS.epi_g
  obtain ⟨c, hc⟩ := hS.exact.desc' (b ≫ S.g) (by simp [← Category.assoc, hb])
  let φ : S ⟶ S := ⟨𝟙 S.X₁, b, c, by simp [hb], hc.symm⟩
  have : IsIso φ := hS.isIso_of_τ₁_eq_id hg φ rfl
  exact ((π₂ : ShortComplex C ⥤ C).mapIso (asIso φ)).isIso_hom

end CategoryTheory.ShortComplex
