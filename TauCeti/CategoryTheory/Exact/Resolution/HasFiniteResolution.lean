/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Resolution.Basic
public import Mathlib.CategoryTheory.ObjectProperty.HasFiniteResolution.Projective

/-!
# Finite resolutions in an exact category and Mathlib's `hasFiniteResolution`

Mathlib records finite resolutions as an object property:
`CategoryTheory.ObjectProperty.hasFiniteResolutionOfLength P n` is the inductive predicate saying
that `X` satisfies `P` (for `n = 0`), or is the cokernel of a short exact sequence
`0 ⟶ K ⟶ E ⟶ X ⟶ 0` with `P E` and `K` resolved in length `n - 1`; and
`CategoryTheory.ObjectProperty.hasFiniteResolution P` allows any finite length.

`TauCeti.ExactStructure.FiniteResolution E P X` is the same recursion carried out with the
conflations of an exact structure `E`, kept as data. This file compares the two presentations.

* For an arbitrary exact structure on a category with homology, every conflation is short exact,
  so a finite `P`-resolution of length `n` gives Mathlib's `P`-resolution of length `n`.
* For the canonical exact structure `TauCeti.ExactStructure.abelian C` of an abelian category the
  conflations are exactly the short exact sequences, so the two notions coincide, length by
  length: `TauCeti.ExactStructure.admitsFiniteResolution` is
  `CategoryTheory.ObjectProperty.hasFiniteResolution`.

For other exact structures, such as the split exact structure, only the inequality is asserted:
the conflations are then a restricted class of short exact sequences.

Combined with Mathlib's
`CategoryTheory.ObjectProperty.hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE`, finite
resolutions by projectives in the canonical exact structure of an abelian category with enough
projectives are exactly the bounds on projective dimension.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.hasFiniteResolutionOfLength`: a finite resolution of
  length `n` gives Mathlib's resolution of length `n`, for any exact structure.
* `TauCeti.ExactStructure.admitsFiniteResolution_le_hasFiniteResolution`: the corresponding
  inequality of object properties.
* `TauCeti.ExactStructure.exists_finiteResolution_length_eq_iff`: in the canonical exact structure
  of an abelian category, a finite resolution of length exactly `n` exists if and only if
  Mathlib's resolution of length `n` does.
* `TauCeti.ExactStructure.exists_finiteResolution_length_le_iff`: the same with length at most
  `n`, when `P` contains zero objects.
* `TauCeti.ExactStructure.abelian_admitsFiniteResolution`: equality of the two object properties.
* `TauCeti.ExactStructure.exists_finiteResolution_isProjective_length_eq_iff` and
  `TauCeti.ExactStructure.abelian_admitsFiniteResolution_isProjective_iff`: finite projective
  resolutions and finite projective dimension.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7,
  for finite resolutions in an exact category.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 4.1, for projective
  dimension and finite projective resolutions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ObjectProperty

universe v u

namespace ExactStructure

section General

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [CategoryWithHomology C] {E : ExactStructure C} {P : ObjectProperty C}

/-- **A finite resolution in an exact structure is a resolution in Mathlib's sense**: every
conflation of the chain is a short exact sequence, so a finite `P`-resolution of `X` of length `n`
witnesses `P.hasFiniteResolutionOfLength n X`. -/
theorem FiniteResolution.hasFiniteResolutionOfLength {X : C} (r : E.FiniteResolution P X) :
    P.hasFiniteResolutionOfLength r.length X := by
  induction r with
  | base hX => simpa using .zero _ hX
  | step hQ i p zero hp r ih =>
    simpa using .succ (ShortComplex.mk i p zero) _ (E.isKernelCokernelPair _ hp).shortExact hQ ih

variable (E P) in
/-- An object admitting a finite `P`-resolution in an exact structure has a finite `P`-resolution
in Mathlib's sense. -/
theorem admitsFiniteResolution_le_hasFiniteResolution :
    E.admitsFiniteResolution P ≤ P.hasFiniteResolution := fun _ hX ↦
  have ⟨r⟩ := (E.admitsFiniteResolution_iff P).1 hX
  hasFiniteResolutionOfLength.le_hasFiniteResolution _ r.hasFiniteResolutionOfLength

end General

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}

/-- **Finite resolutions of a given length in an abelian category** are Mathlib's resolutions of
that length: in the canonical exact structure, `X` has a finite `P`-resolution of length `n` if
and only if `P.hasFiniteResolutionOfLength n X`. -/
theorem exists_finiteResolution_length_eq_iff {X : C} {n : ℕ} :
    (∃ r : (abelian C).FiniteResolution P X, r.length = n) ↔
      P.hasFiniteResolutionOfLength n X := by
  refine ⟨fun ⟨r, hr⟩ ↦ hr ▸ r.hasFiniteResolutionOfLength, fun h ↦ ?_⟩
  induction h with
  | zero X hX => exact ⟨.base hX, by simp⟩
  | succ S n hS h₂ _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨.step h₂ S.f S.g S.zero ((abelian_conflation S).2 hS) r, by simp [hr]⟩

/-- When `P` contains the zero objects, a finite resolution can be padded to any larger length:
in the canonical exact structure of an abelian category, `X` has a finite `P`-resolution of
length at most `n` if and only if `P.hasFiniteResolutionOfLength n X`. -/
theorem exists_finiteResolution_length_le_iff [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    {X : C} {n : ℕ} :
    (∃ r : (abelian C).FiniteResolution P X, r.length ≤ n) ↔
      P.hasFiniteResolutionOfLength n X := by
  rw [← exists_finiteResolution_length_eq_iff]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r.pad (n - r.length), by simp [hr]⟩, fun ⟨r, hr⟩ ↦ ⟨r, hr.le⟩⟩

variable (P) in
/-- **Admitting a finite resolution in an abelian category is Mathlib's `hasFiniteResolution`**:
in the canonical exact structure, the object property of admitting a finite `P`-resolution is
`P.hasFiniteResolution`. -/
theorem abelian_admitsFiniteResolution :
    (abelian C).admitsFiniteResolution P = P.hasFiniteResolution := by
  refine le_antisymm (admitsFiniteResolution_le_hasFiniteResolution _ P) fun X hX ↦ ?_
  obtain ⟨n, hn⟩ := hasFiniteResolution_iff.1 hX
  obtain ⟨r, -⟩ := exists_finiteResolution_length_eq_iff.2 hn
  exact ((abelian C).admitsFiniteResolution_iff P).2 ⟨r⟩

variable [EnoughProjectives C]

/-- **Finite projective resolutions of length `n` detect projective dimension at most `n`**: in
the canonical exact structure of an abelian category with enough projectives, `X` has a finite
resolution of length `n` by projective objects if and only if its projective dimension is at
most `n`. -/
theorem exists_finiteResolution_isProjective_length_eq_iff {X : C} {n : ℕ} :
    (∃ r : (abelian C).FiniteResolution (isProjective C) X, r.length = n) ↔
      HasProjectiveDimensionLE X n := by
  rw [exists_finiteResolution_length_eq_iff,
    hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE]

/-- In an abelian category with enough projectives, an object admits a finite resolution by
projective objects if and only if it has finite projective dimension. -/
theorem abelian_admitsFiniteResolution_isProjective_iff {X : C} :
    (abelian C).admitsFiniteResolution (isProjective C) X ↔ ∃ n, HasProjectiveDimensionLE X n := by
  simp only [abelian_admitsFiniteResolution, hasFiniteResolution_iff,
    hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE]

end Abelian

end ExactStructure

end TauCeti
