/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Basic
public import TauCeti.CategoryTheory.AlmostSplit.Sequence

/-!
# Uniqueness of the almost-split sequence at a given end

An almost-split sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is determined by its right-hand end `C`: two
almost-split sequences with isomorphic right-hand ends are isomorphic as short complexes, so in
particular their left-hand ends and their middle terms are isomorphic.  This file proves that,
the uniqueness half of the Auslander-Reiten theorem, and proves it in the sharper form that
*every* morphism of almost-split sequences invertible at the right-hand end is invertible.

Two inputs beyond the definition are needed, and both are hypotheses rather than ambient
assumptions.  The category is asked to be preadditive and balanced, which is what makes the
left-hand end of a short exact sequence a kernel of its second map (`ShortComplex.Exact.lift'`
is stated only for a balanced category) and lets a morphism that is both monic and epic be
inverted.  And the endomorphism ring of each left-hand end is asked to be **local**, the
Krull-Schmidt input: an almost-split sequence has an indecomposable left-hand end
(`TauCeti.IsLeftAlmostSplit.indecomposable`), and over a finite-dimensional algebra an
indecomposable module has a local endomorphism ring, but indecomposability by itself is the weaker
statement that the ring has no idempotents other than `0` and `1`, which does not suffice.

The three lemmas the argument runs on need only one half of the almost-split condition — short
exactness together with `TauCeti.IsLeftAlmostSplit` or `TauCeti.IsRightAlmostSplit` — so they are
stated in those namespaces; the results about an almost-split sequence are their corollaries.

## Main results

* `TauCeti.IsLeftAlmostSplit.isIso_τ₁_of_τ₃_eq_id`: **an endomorphism of a short exact sequence
  with left almost split first map that is the identity on the right-hand end is an isomorphism on
  the left-hand end**, and `TauCeti.IsLeftAlmostSplit.isIso_of_τ₃_eq_id`: it is then an
  isomorphism of short complexes.  This is the engine of the file.
* `TauCeti.IsRightAlmostSplit.exists_hom_τ₃_eq_of_not_isSplitEpi`: **the comparison morphism.** A
  map into the right-hand end of a short exact sequence with right almost split second map, whose
  composite with the first sequence's `g` is not a split epimorphism, is the third component of a
  morphism of short complexes; `CategoryTheory.ShortComplex.IsAlmostSplit.exists_hom_τ₃_eq` is the
  case of an isomorphism between the right-hand ends of two almost-split sequences.
* `CategoryTheory.ShortComplex.IsAlmostSplit.isIso_of_isIso_τ₃`: **a morphism of almost-split
  sequences invertible at the right-hand end is invertible**, the sharp form of uniqueness.
* `CategoryTheory.ShortComplex.IsAlmostSplit.exists_iso_τ₃_eq`: **uniqueness.** An isomorphism
  between the right-hand ends of two almost-split sequences is realized by an isomorphism of the
  sequences, so the sequence is unique *under* its right-hand end; the plainer statement is
  `CategoryTheory.ShortComplex.IsAlmostSplit.nonempty_iso`, with
  `CategoryTheory.ShortComplex.IsAlmostSplit.nonempty_iso_X₁` and `.nonempty_iso_X₂` the
  statements about the left-hand ends and the middle terms that the Auslander-Reiten theorem is
  usually quoted in.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.13.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S S' : ShortComplex C}

/-! ### Endomorphisms fixing the right-hand end -/

/-- **An endomorphism of a short exact sequence with left almost split first map acting as the
identity on the right-hand end is an isomorphism on the left-hand end.**  This is the engine of
the uniqueness statements below. -/
theorem IsLeftAlmostSplit.isIso_τ₁_of_τ₃_eq_id (hf : IsLeftAlmostSplit S.f) (hS : S.ShortExact)
    [IsLocalRing (End S.X₁)] (φ : S ⟶ S) (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ.τ₁ := by
  have hmono := hS.mono_f
  -- `𝟙 - φ.τ₂` is killed by `S.g`, because `φ` is the identity on `S.X₃`.
  have hker : (𝟙 S.X₂ - φ.τ₂) ≫ S.g = 0 := by
    rw [sub_comp, Category.id_comp, φ.comm₂₃, hφ, Category.comp_id, sub_self]
  obtain ⟨γ, hγ⟩ := hS.exact.lift' (𝟙 S.X₂ - φ.τ₂) hker
  -- Composing with the monomorphism `S.f` identifies `S.f ≫ γ` with `𝟙 - φ.τ₁`.
  have hfγ : S.f ≫ γ = 𝟙 S.X₁ - φ.τ₁ := by
    refine (cancel_mono S.f).mp ?_
    rw [Category.assoc, hγ, comp_sub, Category.comp_id, sub_comp, Category.id_comp, φ.comm₁₂]
  -- Were `𝟙 - φ.τ₁` invertible, `S.f` would be a split monomorphism.
  have hnot : ¬ IsIso (𝟙 S.X₁ - φ.τ₁) := fun h =>
    hf.not_isSplitMono
      (IsSplitMono.mk' ⟨γ ≫ inv (𝟙 S.X₁ - φ.τ₁), by rw [← Category.assoc, hfγ, IsIso.hom_inv_id]⟩)
  -- In a local ring one of `a` and `1 - a` is a unit, and here it is not the second.
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (R := End S.X₁) φ.τ₁ with h | h
  · exact (isUnit_iff_isIso _).mp h
  · exact absurd ((isUnit_iff_isIso _).mp h) hnot

/-- **An endomorphism of a short exact sequence with left almost split first map acting as the
identity on the right-hand end is an isomorphism.** -/
theorem IsLeftAlmostSplit.isIso_of_τ₃_eq_id (hf : IsLeftAlmostSplit S.f) (hS : S.ShortExact)
    [IsLocalRing (End S.X₁)] (φ : S ⟶ S) (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ := by
  have : IsIso φ.τ₁ := hf.isIso_τ₁_of_τ₃_eq_id hS φ hφ
  have : IsIso φ.τ₃ := hφ ▸ inferInstanceAs (IsIso (𝟙 S.X₃))
  have : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hS
  exact ShortComplex.isIso_of_isIso φ

/-! ### The comparison morphism -/

/-- **A map `e` into the right-hand end of a short exact sequence `S'` whose second map is right
almost split extends to a morphism of short complexes `S ⟶ S'`, as soon as `S.g ≫ e` is not a
split epimorphism.**  No hypothesis on `S` beyond its being a short complex is needed. -/
theorem IsRightAlmostSplit.exists_hom_τ₃_eq_of_not_isSplitEpi (hg : IsRightAlmostSplit S'.g)
    (hS' : S'.ShortExact) (e : S.X₃ ⟶ S'.X₃) (he : ¬ IsSplitEpi (S.g ≫ e)) :
    ∃ φ : S ⟶ S', φ.τ₃ = e := by
  have hmono := hS'.mono_f
  -- `S.g ≫ e` factors through the right almost split map `S'.g`.
  obtain ⟨β, hβ⟩ := hg.factors S.X₂ (S.g ≫ e) he
  -- The resulting map of middle terms carries `S.f` into the kernel of `S'.g`, which is `S'.f`.
  have hzero : (S.f ≫ β) ≫ S'.g = 0 := by
    rw [Category.assoc, hβ, ← Category.assoc, S.zero, zero_comp]
  obtain ⟨α, hα⟩ := hS'.exact.lift' (S.f ≫ β) hzero
  exact ⟨⟨α, β, e, hα, hβ⟩, rfl⟩

end TauCeti

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S S' : ShortComplex C}

namespace IsAlmostSplit

/-! ### Uniqueness -/

/-- **An isomorphism between the right-hand ends of two almost-split sequences is the third
component of a morphism of short complexes between them.** -/
theorem exists_hom_τ₃_eq (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) (e : S.X₃ ≅ S'.X₃) :
    ∃ φ : S ⟶ S', φ.τ₃ = e.hom :=
  hS'.isRightAlmostSplit_g.exists_hom_τ₃_eq_of_not_isSplitEpi hS'.shortExact e.hom
    (hS.isRightAlmostSplit_g.comp_iso e).not_isSplitEpi

/-- **A morphism of almost-split sequences that is invertible at the right-hand end is
invertible**, the sharp form of uniqueness. -/
theorem isIso_of_isIso_τ₃ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    [IsLocalRing (End S.X₁)] [IsLocalRing (End S'.X₁)] (φ : S ⟶ S') [IsIso φ.τ₃] : IsIso φ := by
  -- Compose `φ` with a comparison morphism running the other way; both composites are the
  -- identity on the right-hand end, hence isomorphisms on the left-hand ends.
  obtain ⟨ψ, hψ⟩ := hS'.exists_hom_τ₃_eq hS (asIso φ.τ₃).symm
  have hcomp : IsIso ((φ ≫ ψ).τ₁) :=
    hS.isLeftAlmostSplit_f.isIso_τ₁_of_τ₃_eq_id hS.shortExact (φ ≫ ψ) (by simp [hψ])
  have hcomp' : IsIso ((ψ ≫ φ).τ₁) :=
    hS'.isLeftAlmostSplit_f.isIso_τ₁_of_τ₃_eq_id hS'.shortExact (ψ ≫ φ) (by simp [hψ])
  rw [comp_τ₁] at hcomp hcomp'
  -- So `φ.τ₁` has a left and a right inverse, hence is monic and epic, hence invertible.
  have hmf : φ.τ₁ ≫ ψ.τ₁ ≫ inv (φ.τ₁ ≫ ψ.τ₁) = 𝟙 S.X₁ := by
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hef : (inv (ψ.τ₁ ≫ φ.τ₁) ≫ ψ.τ₁) ≫ φ.τ₁ = 𝟙 S'.X₁ := by
    rw [Category.assoc, IsIso.inv_hom_id]
  have : Mono φ.τ₁ := mono_of_mono_fac hmf
  have : Epi φ.τ₁ := epi_of_epi_fac hef
  have : IsIso φ.τ₁ := isIso_of_mono_of_epi φ.τ₁
  have : IsIso φ.τ₂ := isIso₂_of_shortExact_of_isIso₁₃ φ hS.shortExact hS'.shortExact
  exact isIso_of_isIso φ

/-- **Uniqueness of the almost-split sequence at a given right-hand end, in its sharp form**: an
isomorphism between the right-hand ends of two almost-split sequences is realized by an
isomorphism of the sequences themselves.  The sequence ending at an object is therefore determined
up to isomorphism *under* that object, not merely up to abstract isomorphism. -/
theorem exists_iso_τ₃_eq (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) [IsLocalRing (End S.X₁)]
    [IsLocalRing (End S'.X₁)] (e : S.X₃ ≅ S'.X₃) : ∃ f : S ≅ S', f.hom.τ₃ = e.hom := by
  obtain ⟨φ, hφ⟩ := hS.exists_hom_τ₃_eq hS' e
  have : IsIso φ.τ₃ := hφ ▸ inferInstanceAs (IsIso e.hom)
  have := hS.isIso_of_isIso_τ₃ hS' φ
  exact ⟨asIso φ, hφ⟩

/-- **Uniqueness of the almost-split sequence at a given right-hand end**: two almost-split
sequences whose right-hand ends are isomorphic are isomorphic as short complexes. -/
theorem nonempty_iso (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) [IsLocalRing (End S.X₁)]
    [IsLocalRing (End S'.X₁)] (e : S.X₃ ≅ S'.X₃) : Nonempty (S ≅ S') :=
  (hS.exists_iso_τ₃_eq hS' e).elim fun f _ => ⟨f⟩

/-- **The left-hand ends of two almost-split sequences with isomorphic right-hand ends are
isomorphic**: the object `τ M` of the Auslander-Reiten theorem is determined by `M` up to
isomorphism. -/
theorem nonempty_iso_X₁ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) [IsLocalRing (End S.X₁)]
    [IsLocalRing (End S'.X₁)] (e : S.X₃ ≅ S'.X₃) : Nonempty (S.X₁ ≅ S'.X₁) :=
  (hS.nonempty_iso hS' e).map fun f => π₁.mapIso f

/-- **The middle terms of two almost-split sequences with isomorphic right-hand ends are
isomorphic**: the middle term of the Auslander-Reiten sequence ending at `M`, which carries the
irreducible morphisms into `M`, is determined by `M` up to isomorphism. -/
theorem nonempty_iso_X₂ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) [IsLocalRing (End S.X₁)]
    [IsLocalRing (End S'.X₁)] (e : S.X₃ ≅ S'.X₃) : Nonempty (S.X₂ ≅ S'.X₂) :=
  (hS.nonempty_iso hS' e).map fun f => π₂.mapIso f

end IsAlmostSplit

end CategoryTheory.ShortComplex
