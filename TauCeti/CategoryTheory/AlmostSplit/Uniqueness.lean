/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.LocalEnd
public import TauCeti.CategoryTheory.AlmostSplit.Sequence

/-!
# Uniqueness of the almost-split sequence at a given end

An almost-split sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is determined by its right-hand end `C`:
every almost-split sequence with an isomorphic right-hand end is isomorphic to it. No
locality or finiteness hypothesis is needed. The left-hand end of an almost-split sequence
automatically has a local endomorphism ring (`TauCeti.IsLeftAlmostSplit.isLocalRing_end`),
because its endomorphisms that are not split monomorphisms are exactly those factoring through
the left almost split map, and so are closed under addition.

More sharply, every morphism of almost-split sequences that is invertible at the right-hand
end is invertible. A comparison in the reverse direction makes the composite invertible at the
first sequence's left-hand end by locality. This makes the original map on left-hand ends a
split monomorphism; the left almost-split lifting property of the second sequence then makes it
an isomorphism (`TauCeti.IsLeftAlmostSplit.isIso_of_isSplitMono_of_comm`).

The ambient category is preadditive and balanced, so exactness supplies the kernel lifts
used to construct comparison maps and the short five lemma applies.

The rigidity input only needs non-splitness, not either lifting property. It is developed in
`TauCeti.Algebra.Homology.ShortComplex.LocalEnd`, for exact short complexes with a local
endomorphism ring at the end opposite the fixed component. The same general results also
supply the minimality criteria used to construct almost-split sequences.

## Main results

* `TauCeti.IsRightAlmostSplit.exists_hom_τ₃_eq_of_not_isSplitEpi`: **the comparison morphism.** A
  map into the right-hand end of an exact short complex with monic first map and right almost split
  second map, whose composite with the first sequence's `g` is not a split epimorphism, is the third
  component of a morphism of short complexes;
  `CategoryTheory.ShortComplex.IsAlmostSplit.exists_hom_τ₃_eq` is the case of an isomorphism
  between the right-hand ends of two almost-split sequences.
* `CategoryTheory.ShortComplex.IsAlmostSplit.isIso_of_isIso_τ₃`: **a morphism between two
  almost-split sequences that is invertible at the right-hand end is invertible**, the sharp form
  of uniqueness.
* `CategoryTheory.ShortComplex.IsAlmostSplit.exists_iso_τ₃_eq`: **uniqueness.** An isomorphism
  between the right-hand ends of two almost-split sequences is realized by an isomorphism of the
  sequences. Such a sequence is unique *under* its right-hand end; the plainer statement is
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

/-! ### The comparison morphism -/

/-- **A map `e` into the right-hand end of an exact short complex `S'` with monic first map and
right almost split second map extends to a morphism of short complexes `S ⟶ S'`, as soon as
`S.g ≫ e` is not a split epimorphism.**  No hypothesis on `S` beyond its being a short complex is
needed. -/
theorem IsRightAlmostSplit.exists_hom_τ₃_eq_of_not_isSplitEpi (hg : IsRightAlmostSplit S'.g)
    (hS' : S'.Exact) [Mono S'.f] (e : S.X₃ ⟶ S'.X₃) (he : ¬ IsSplitEpi (S.g ≫ e)) :
    ∃ φ : S ⟶ S', φ.τ₃ = e := by
  -- `S.g ≫ e` factors through the right almost split map `S'.g`.
  obtain ⟨β, hβ⟩ := hg.factors S.X₂ (S.g ≫ e) he
  -- The resulting map of middle terms carries `S.f` into the kernel of `S'.g`, which is `S'.f`.
  have hzero : (S.f ≫ β) ≫ S'.g = 0 := by
    rw [Category.assoc, hβ, ← Category.assoc, S.zero, zero_comp]
  obtain ⟨α, hα⟩ := hS'.lift' (S.f ≫ β) hzero
  exact ⟨⟨α, β, e, hα, hβ⟩, rfl⟩

end TauCeti

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S S' : ShortComplex C}

namespace IsAlmostSplit

/-! ### Uniqueness -/

/-- **An isomorphism between the right-hand ends of two almost-split sequences is the third
component of a morphism of short complexes between them.** -/
theorem exists_hom_τ₃_eq (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit) (e : S.X₃ ≅ S'.X₃) :
    ∃ φ : S ⟶ S', φ.τ₃ = e.hom := by
  have hmono := hS'.shortExact.mono_f
  exact hS'.isRightAlmostSplit_g.exists_hom_τ₃_eq_of_not_isSplitEpi hS'.shortExact.exact e.hom
    (hS.isRightAlmostSplit_g.comp_iso e).not_isSplitEpi

/-- **A morphism of almost-split sequences that is invertible at the right-hand end is
invertible**, the sharp form of uniqueness. -/
theorem isIso_of_isIso_τ₃ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    (φ : S ⟶ S') [IsIso φ.τ₃] : IsIso φ := by
  have := hS.isLeftAlmostSplit_f.isLocalRing_end
  -- A reverse comparison makes the composite invertible at the first sequence's left end.
  obtain ⟨ψ, hψ⟩ := hS'.exists_hom_τ₃_eq hS (asIso φ.τ₃).symm
  have hmono := hS.shortExact.mono_f
  have hcomp : IsIso ((φ ≫ ψ).τ₁) :=
    hS.shortExact.exact.isIso_τ₁_of_τ₃_eq_id hS.isLeftAlmostSplit_f.not_isSplitMono
      (φ ≫ ψ) (by simp [hψ])
  rw [comp_τ₁] at hcomp
  have : IsSplitMono φ.τ₁ := TauCeti.isSplitMono_of_isSplitMono_comp φ.τ₁ ψ.τ₁
  -- The second sequence's lifting property upgrades the split comparison to an isomorphism.
  have : IsIso φ.τ₁ := hS'.isLeftAlmostSplit_f.isIso_of_isSplitMono_of_comm
    hS.isLeftAlmostSplit_f.not_isSplitMono φ.τ₁ φ.τ₂ φ.comm₁₂.symm
  have : IsIso φ.τ₂ := isIso₂_of_shortExact_of_isIso₁₃ φ hS.shortExact hS'.shortExact
  exact isIso_of_isIso φ

/-- **Uniqueness of the almost-split sequence at a given right-hand end, in its sharp form**: an
isomorphism between the right-hand ends of two almost-split sequences is realized by an
isomorphism of the sequences themselves.  The sequence ending at an object is therefore determined
up to isomorphism *under* that object, not merely up to abstract isomorphism. -/
theorem exists_iso_τ₃_eq (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    (e : S.X₃ ≅ S'.X₃) : ∃ f : S ≅ S', f.hom.τ₃ = e.hom := by
  obtain ⟨φ, hφ⟩ := hS.exists_hom_τ₃_eq hS' e
  have : IsIso φ.τ₃ := hφ ▸ inferInstanceAs (IsIso e.hom)
  have := hS.isIso_of_isIso_τ₃ hS' φ
  exact ⟨asIso φ, hφ⟩

/-- **Uniqueness of the almost-split sequence at a given right-hand end**: two almost-split
sequences whose right-hand ends are isomorphic are isomorphic as short complexes. -/
theorem nonempty_iso (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    (e : S.X₃ ≅ S'.X₃) : Nonempty (S ≅ S') :=
  (hS.exists_iso_τ₃_eq hS' e).elim fun f _ => ⟨f⟩

/-- **The left-hand ends of two almost-split sequences with isomorphic right-hand ends are
isomorphic**: the object `τ M` of the Auslander-Reiten theorem is determined by `M` up to
isomorphism. -/
theorem nonempty_iso_X₁ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    (e : S.X₃ ≅ S'.X₃) : Nonempty (S.X₁ ≅ S'.X₁) :=
  (hS.nonempty_iso hS' e).map fun f => π₁.mapIso f

/-- **The middle terms of two almost-split sequences with isomorphic right-hand ends are
isomorphic**: the middle term of the Auslander-Reiten sequence ending at `M`, which carries the
irreducible morphisms into `M`, is determined by `M` up to isomorphism. -/
theorem nonempty_iso_X₂ (hS : S.IsAlmostSplit) (hS' : S'.IsAlmostSplit)
    (e : S.X₃ ≅ S'.X₃) : Nonempty (S.X₂ ≅ S'.X₂) :=
  (hS.nonempty_iso hS' e).map fun f => π₂.mapIso f

end IsAlmostSplit

end CategoryTheory.ShortComplex
