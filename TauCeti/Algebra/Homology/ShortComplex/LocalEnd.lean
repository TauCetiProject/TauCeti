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

The underlying rigidity statement is stronger: an endomorphism of a short complex fixing one
end is invertible at the other end if that end has a local endomorphism ring, the adjacent map
does not split, and that map has the universal property of a kernel or a cokernel, with no
balancedness assumption on the category. Short exactness then gives invertibility of the whole
endomorphism by the short five lemma.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, V.1.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {S : ShortComplex C}

/-- An endomorphism of a short complex whose initial map is a kernel of its final map and does not
split, vanishing at the right-hand end, is not invertible at the left-hand end: its middle
component factors through the initial map, which it would split. -/
theorem not_isIso_τ₁_of_τ₃_eq_zero (hS : IsLimit (KernelFork.ofι S.f S.zero))
    (hf : ¬ IsSplitMono S.f) (φ : S ⟶ S) (hφ : φ.τ₃ = 0) : ¬ IsIso φ.τ₁ := by
  intro h
  have : Mono S.f := mono_of_isLimit_fork hS
  obtain ⟨(γ : S.X₂ ⟶ S.X₁), (hγ : γ ≫ S.f = _)⟩ :=
    KernelFork.IsLimit.lift' hS φ.τ₂ (by rw [φ.comm₂₃, hφ, comp_zero])
  have hfγ : S.f ≫ γ = φ.τ₁ := by
    apply (cancel_mono S.f).mp
    rw [Category.assoc, hγ, φ.comm₁₂]
  exact hf (IsSplitMono.mk' ⟨γ ≫ inv φ.τ₁, by rw [← Category.assoc, hfγ, IsIso.hom_inv_id]⟩)

/-- An endomorphism of a short complex whose final map is a cokernel of its initial map and does
not split, vanishing at the left-hand end, is not invertible at the right-hand end: its middle
component factors through the final map, which it would split. -/
theorem not_isIso_τ₃_of_τ₁_eq_zero (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    (hg : ¬ IsSplitEpi S.g) (φ : S ⟶ S) (hφ : φ.τ₁ = 0) : ¬ IsIso φ.τ₃ := by
  intro h
  have : Epi S.g := epi_of_isColimit_cofork hS
  obtain ⟨(γ : S.X₃ ⟶ S.X₂), (hγ : S.g ≫ γ = _)⟩ :=
    CokernelCofork.IsColimit.desc' hS φ.τ₂ (by rw [← φ.comm₁₂, hφ, zero_comp])
  have hγg : γ ≫ S.g = φ.τ₃ := by
    apply (cancel_epi S.g).mp
    rw [← Category.assoc, hγ, φ.comm₂₃]
  exact hg (IsSplitEpi.mk' ⟨inv φ.τ₃ ≫ γ, by rw [Category.assoc, hγg, IsIso.inv_hom_id]⟩)

/-- An endomorphism of a short complex whose initial map is a kernel of its final map, fixing the
right-hand end, is invertible on the left-hand end if its endomorphism ring is local and the
initial map does not split. -/
theorem isIso_τ₁_of_τ₃_eq_id (hS : IsLimit (KernelFork.ofι S.f S.zero)) [IsLocalRing (End S.X₁)]
    (hf : ¬ IsSplitMono S.f) (φ : S ⟶ S) (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ.τ₁ := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (R := End S.X₁) (.of φ.τ₁) with h | h
  · exact (isUnit_iff_isIso _).mp h
  · refine absurd ?_ (not_isIso_τ₁_of_τ₃_eq_zero hS hf (𝟙 S - φ) (by simp [hφ]))
    simpa using (isUnit_iff_isIso _).mp h

/-- An endomorphism of a short complex whose final map is a cokernel of its initial map, fixing the
left-hand end, is invertible on the right-hand end if its endomorphism ring is local and the final
map does not split. -/
theorem isIso_τ₃_of_τ₁_eq_id (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    [IsLocalRing (End S.X₃)] (hg : ¬ IsSplitEpi S.g) (φ : S ⟶ S) (hφ : φ.τ₁ = 𝟙 S.X₁) :
    IsIso φ.τ₃ := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (R := End S.X₃) (.of φ.τ₃) with h | h
  · exact (isUnit_iff_isIso _).mp h
  · refine absurd ?_ (not_isIso_τ₃_of_τ₁_eq_zero hS hg (𝟙 S - φ) (by simp [hφ]))
    simpa using (isUnit_iff_isIso _).mp h

variable [Balanced C]

/-- An endomorphism of a non-split short exact sequence fixing the right-hand end is invertible
when the left-hand end has a local endomorphism ring. -/
theorem ShortExact.isIso_of_τ₃_eq_id (hS : S.ShortExact) [IsLocalRing (End S.X₁)]
    (hf : ¬ IsSplitMono S.f) (φ : S ⟶ S) (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ := by
  have := hS.mono_f
  have : IsIso φ.τ₁ := isIso_τ₁_of_τ₃_eq_id hS.fIsKernel hf φ hφ
  have : IsIso φ.τ₃ := hφ ▸ inferInstanceAs (IsIso (𝟙 S.X₃))
  have : IsIso φ.τ₂ := isIso₂_of_shortExact_of_isIso₁₃ φ hS hS
  exact isIso_of_isIso φ

/-- An endomorphism of a non-split short exact sequence fixing the left-hand end is invertible
when the right-hand end has a local endomorphism ring. -/
theorem ShortExact.isIso_of_τ₁_eq_id (hS : S.ShortExact) [IsLocalRing (End S.X₃)]
    (hg : ¬ IsSplitEpi S.g) (φ : S ⟶ S) (hφ : φ.τ₁ = 𝟙 S.X₁) : IsIso φ := by
  have := hS.epi_g
  have : IsIso φ.τ₃ := isIso_τ₃_of_τ₁_eq_id hS.gIsCokernel hg φ hφ
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
