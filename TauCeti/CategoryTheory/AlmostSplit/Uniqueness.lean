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
left-hand end of a short exact sequence a kernel of its second map and lets a morphism that is
both monic and epic be inverted.  And the endomorphism ring of each left-hand end is asked to be
**local**, the Krull-Schmidt input: an almost-split sequence has an indecomposable left-hand end
(`TauCeti.IsLeftAlmostSplit.indecomposable`), and over a finite-dimensional algebra an
indecomposable module has a local endomorphism ring, but indecomposability by itself is the weaker
statement that the ring has no idempotents other than `0` and `1`, which does not suffice.

The proof is the classical one, and it turns on a single lemma.  Let `φ` be an endomorphism of an
almost-split sequence `S` acting as the identity on `S.X₃`.  Then `𝟙 - φ.τ₂` is killed by `S.g`,
so it factors as `γ ≫ S.f`, and comparing the two ways of composing with the monomorphism `S.f`
gives `S.f ≫ γ = 𝟙 - φ.τ₁`.  Were `𝟙 - φ.τ₁` invertible, `γ` composed with its inverse would
retract `S.f`, contradicting that `S.f` is left almost split and so is *not* a split
monomorphism.  In a local ring one of `a` and `1 - a` is a unit; here it cannot be the second, so
it is the first, and `φ.τ₁` is an isomorphism.  A morphism between two almost-split sequences
invertible on the right is then handled by composing it with a comparison morphism running the
other way, which the right almost split property of the second sequence produces.

## Main results

* `CategoryTheory.ShortComplex.IsAlmostSplit.isIso_τ₁_of_τ₃_eq_id`: **an endomorphism of an
  almost-split sequence that is the identity on the right-hand end is an isomorphism on the
  left-hand end**, and `CategoryTheory.ShortComplex.IsAlmostSplit.isIso_of_τ₃_eq_id`: it is then
  an isomorphism of short complexes.  This is the engine of the file.
* `CategoryTheory.ShortComplex.IsAlmostSplit.exists_hom_τ₃_eq`: **the comparison morphism.** An
  isomorphism between the right-hand ends of two almost-split sequences is the third component of
  a morphism of short complexes between them.
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
* [Quiver-representation roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md),
  Layer 6, sublayer 6E, "existence and uniqueness of almost-split sequences", of which this is the
  uniqueness half.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TauCeti

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S S' : ShortComplex C}

namespace IsAlmostSplit

/-! ### Endomorphisms fixing the right-hand end -/

/-- **An endomorphism of an almost-split sequence acting as the identity on the right-hand end is
an isomorphism on the left-hand end.**

This is the whole content of uniqueness.  The endomorphism `𝟙 - φ` of the sequence vanishes on the
right-hand end, hence factors through the kernel `S.f` of `S.g`, and monicity of `S.f` transports
the factorization back to `𝟙 - φ.τ₁ = S.f ≫ γ`.  A factorization of an *isomorphism* through
`S.f` would retract it, which the left almost split clause forbids; so `𝟙 - φ.τ₁` is not
invertible, and locality of the endomorphism ring leaves `φ.τ₁` invertible. -/
theorem isIso_τ₁_of_τ₃_eq_id (hS : S.IsAlmostSplit) [IsLocalRing (End S.X₁)] (φ : S ⟶ S)
    (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ.τ₁ := by
  have hmono := hS.shortExact.mono_f
  -- `𝟙 - φ.τ₂` is killed by `S.g`, because `φ` is the identity on `S.X₃`.
  have hker : (𝟙 S.X₂ - φ.τ₂) ≫ S.g = 0 := by
    rw [sub_comp, Category.id_comp, φ.comm₂₃, hφ, Category.comp_id, sub_self]
  obtain ⟨γ, hγ⟩ := hS.shortExact.exact.lift' (𝟙 S.X₂ - φ.τ₂) hker
  -- Composing with the monomorphism `S.f` identifies `S.f ≫ γ` with `𝟙 - φ.τ₁`.
  have hfγ : S.f ≫ γ = 𝟙 S.X₁ - φ.τ₁ := by
    refine (cancel_mono S.f).mp ?_
    rw [Category.assoc, hγ, comp_sub, Category.comp_id, sub_comp, Category.id_comp, φ.comm₁₂]
  -- Were `𝟙 - φ.τ₁` invertible, `S.f` would be a split monomorphism.
  have hnot : ¬ IsIso (𝟙 S.X₁ - φ.τ₁) := fun h =>
    hS.isLeftAlmostSplit_f.not_isSplitMono
      (IsSplitMono.mk' ⟨γ ≫ inv (𝟙 S.X₁ - φ.τ₁), by rw [← Category.assoc, hfγ, IsIso.hom_inv_id]⟩)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (R := End S.X₁) φ.τ₁ with h | h
  · exact (isUnit_iff_isIso _).mp h
  · exact absurd ((isUnit_iff_isIso _).mp h) hnot

/-- **An endomorphism of an almost-split sequence acting as the identity on the right-hand end is
an isomorphism**, by the five lemma applied to
`CategoryTheory.ShortComplex.IsAlmostSplit.isIso_τ₁_of_τ₃_eq_id`. -/
theorem isIso_of_τ₃_eq_id (hS : S.IsAlmostSplit) [IsLocalRing (End S.X₁)] (φ : S ⟶ S)
    (hφ : φ.τ₃ = 𝟙 S.X₃) : IsIso φ := by
  have : IsIso φ.τ₁ := hS.isIso_τ₁_of_τ₃_eq_id φ hφ
  have : IsIso φ.τ₃ := hφ ▸ inferInstanceAs (IsIso (𝟙 S.X₃))
  have : IsIso φ.τ₂ := isIso₂_of_shortExact_of_isIso₁₃ φ hS.shortExact hS.shortExact
  exact isIso_of_isIso φ

/-! ### The comparison morphism -/

/-- **An isomorphism between the right-hand ends of two almost-split sequences extends to a
morphism of short complexes.**

The composite `S.g ≫ e.hom` is not a split epimorphism — a section of it would, read through
`e`, section `S.g` — so it factors through the right almost split map `S'.g`.  The resulting map
of middle terms carries `S.f` into the kernel of `S'.g`, which is `S'.f`, and that lift is the
component on the left-hand ends. -/
theorem exists_hom_τ₃_eq (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) (e : S.X₃ ≅ S'.X₃) :
    ∃ φ : S ⟶ S', φ.τ₃ = e.hom := by
  have hmono := hS'.shortExact.mono_f
  have hne : ¬ IsSplitEpi (S.g ≫ e.hom) := by
    intro h
    refine hS.isRightAlmostSplit_g.not_isSplitEpi
      (IsSplitEpi.mk' ⟨e.hom ≫ section_ (S.g ≫ e.hom), ?_⟩)
    have hsec : section_ (S.g ≫ e.hom) ≫ S.g = e.inv := by
      rw [← Category.comp_id (section_ (S.g ≫ e.hom) ≫ S.g), ← e.hom_inv_id, ← Category.assoc,
        Category.assoc (section_ (S.g ≫ e.hom)), IsSplitEpi.id, Category.id_comp]
    rw [Category.assoc, hsec, e.hom_inv_id]
  obtain ⟨β, hβ⟩ := hS'.isRightAlmostSplit_g.factors S.X₂ (S.g ≫ e.hom) hne
  have hzero : (S.f ≫ β) ≫ S'.g = 0 := by
    rw [Category.assoc, hβ, ← Category.assoc, S.zero, zero_comp]
  obtain ⟨α, hα⟩ := hS'.shortExact.exact.lift' (S.f ≫ β) hzero
  exact ⟨⟨α, β, e.hom, hα, hβ⟩, rfl⟩

/-! ### Uniqueness -/

/-- **A morphism of almost-split sequences that is invertible at the right-hand end is
invertible.**

Compose it with a comparison morphism running the other way, supplied by
`CategoryTheory.ShortComplex.IsAlmostSplit.exists_hom_τ₃_eq`.  Both composites are the identity on
the right-hand end, so both are isomorphisms on the left-hand end; the given morphism therefore has
a left and a right inverse there, hence is monic and epic, hence — the category being balanced —
invertible on the left-hand ends, and the five lemma finishes. -/
theorem isIso_of_isIso_τ₃ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    [IsLocalRing (End S.X₁)] [IsLocalRing (End S'.X₁)] (φ : S ⟶ S') [IsIso φ.τ₃] : IsIso φ := by
  obtain ⟨ψ, hψ⟩ := hS'.exists_hom_τ₃_eq hS (asIso φ.τ₃).symm
  have hcomp : IsIso ((φ ≫ ψ).τ₁) :=
    hS.isIso_τ₁_of_τ₃_eq_id (φ ≫ ψ) (by simp [hψ])
  have hcomp' : IsIso ((ψ ≫ φ).τ₁) :=
    hS'.isIso_τ₁_of_τ₃_eq_id (ψ ≫ φ) (by simp [hψ])
  rw [comp_τ₁] at hcomp hcomp'
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
isomorphism of the sequences themselves.  The sequence ending at an object is unique not merely up
to abstract isomorphism but *under* that object, which is what makes the Auslander-Reiten translate
and the middle term functorial in it. -/
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
isomorphic**: the object `τ M` of the Auslander-Reiten theorem is determined by `M`. -/
theorem nonempty_iso_X₁ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) [IsLocalRing (End S.X₁)]
    [IsLocalRing (End S'.X₁)] (e : S.X₃ ≅ S'.X₃) : Nonempty (S.X₁ ≅ S'.X₁) :=
  (hS.nonempty_iso hS' e).map fun f => π₁.mapIso f

/-- **The middle terms of two almost-split sequences with isomorphic right-hand ends are
isomorphic**: the middle term of the Auslander-Reiten sequence ending at `M`, which carries the
irreducible morphisms into `M`, is determined by `M`. -/
theorem nonempty_iso_X₂ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) [IsLocalRing (End S.X₁)]
    [IsLocalRing (End S'.X₁)] (e : S.X₃ ≅ S'.X₃) : Nonempty (S.X₂ ≅ S'.X₂) :=
  (hS.nonempty_iso hS' e).map fun f => π₂.mapIso f

end IsAlmostSplit

end CategoryTheory.ShortComplex
