/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum

/-!
# The Lazard projection set

Let `F` be a finite family of polynomials in one distinguished variable over a commutative ring
`R` with a normalized gcd, and let `B` be a basis of `F`, in Lazard's setting an irreducible basis
(`Finset.IsIrreducibleBasis`): a finite set of pairwise nonassociated irreducible polynomials of
positive degree whose products of powers recover the members of `F` up to their contents. The
Lazard projection `F.lazardProjection B` is the finite subset of `R` consisting of

* the content `f.content` of every member `f ∈ F`;
* the leading coefficient `b.leadingCoeff` and the trailing coefficient `b.trailingCoeff` of every
  member `b ∈ B`;
* the discriminant `b.discr` of every member `b ∈ B`;
* the resultant `resultant b b'` of every pair of distinct members `b, b' ∈ B`, in both orders
  (which differ only by a sign).

The trailing coefficient is Mathlib's `Polynomial.trailingCoeff`, the coefficient of the lowest
power of the distinguished variable occurring in `b`; it is the constant coefficient `b.coeff 0`
unless the distinguished variable divides `b`.

The intended coefficient ring is `R = MvPolynomial (Fin n) ℝ`. Compared with the McCallum
projection `Finset.mcCallumProjection`, only the leading and trailing coefficients of each basis
member are kept, rather than all of its coefficients
(`Finset.lazardProjection_subset_mcCallumProjection`). In exchange, the lifting theorem of
McCallum, Parusiński and Paunescu asks for invariance of Lazard valuations instead of orders of
vanishing, and allows nullification of basis members.

For an irreducible basis over a domain of characteristic zero, no element of the Lazard projection
vanishes unless the family itself contains the zero polynomial
(`Finset.IsIrreducibleBasis.zero_mem_lazardProjection_iff`). In particular the discriminant,
leading coefficient and trailing coefficient of every member of the basis are nonzero formal
polynomials in the base coordinates, as the lifting theorem requires, even though they may vanish
at points of a base cell. As for McCallum's projection, the Lazard projection depends on the choice
of irreducible basis only up to associates
(`Finset.IsIrreducibleBasis.exists_associated_mem_lazardProjection`).

## Main definitions and results

* `Finset.lazardProjection`: the Lazard projection of a family with respect to a basis.
* `Finset.mem_lazardProjection`: the explicit description of its elements.
* `Finset.lazardProjection_mono`: the projection is monotone in the family and the basis.
* `Finset.lazardProjection_subset_mcCallumProjection`: the Lazard projection is contained in the
  McCallum projection.
* `Finset.IsIrreducibleBasis.exists_associated_mem_lazardProjection`: independence of the basis
  up to associates.
* `Finset.IsIrreducibleBasis.zero_mem_lazardProjection_iff`: in characteristic zero, the Lazard
  projection of an irreducible basis contains `0` exactly when the family does.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69.
-/

public section

open Polynomial

namespace Finset

variable {R : Type*} [CommRing R] [NormalizedGCDMonoid R]

/-- The Lazard projection of the family `F` with respect to the basis `B`: the contents of the
members of `F`, together with the leading coefficients, trailing coefficients and discriminants of
the members of `B` and the resultants of pairs of distinct members of `B`. Resultants and
discriminants are taken at the actual degrees. -/
noncomputable def lazardProjection (F B : Finset R[X]) : Finset R := by
  classical
  exact F.image content ∪ B.image leadingCoeff ∪ B.image trailingCoeff ∪ B.image discr ∪
    B.offDiag.image fun bb ↦ resultant bb.1 bb.2

/-- The elements of the Lazard projection: contents of members of the family, and leading
coefficients, trailing coefficients, discriminants and pairwise resultants of members of the
basis. -/
theorem mem_lazardProjection {F B : Finset R[X]} {a : R} :
    a ∈ F.lazardProjection B ↔
      (∃ f ∈ F, f.content = a) ∨ (∃ b ∈ B, b.leadingCoeff = a) ∨
      (∃ b ∈ B, b.trailingCoeff = a) ∨ (∃ b ∈ B, b.discr = a) ∨
      ∃ b ∈ B, ∃ b' ∈ B, b ≠ b' ∧ resultant b b' = a := by
  classical
  simp only [lazardProjection, mem_union, mem_image, mem_offDiag, Prod.exists, or_assoc]
  grind

variable {F F' B B' : Finset R[X]} {f b b' : R[X]}

/-- The content of every member of the family lies in the Lazard projection. -/
theorem content_mem_lazardProjection (hf : f ∈ F) : f.content ∈ F.lazardProjection B :=
  mem_lazardProjection.2 <| .inl ⟨f, hf, rfl⟩

/-- The leading coefficient of every member of the basis lies in the Lazard projection. -/
theorem leadingCoeff_mem_lazardProjection (hb : b ∈ B) : b.leadingCoeff ∈ F.lazardProjection B :=
  mem_lazardProjection.2 <| .inr <| .inl ⟨b, hb, rfl⟩

/-- The trailing coefficient of every member of the basis lies in the Lazard projection. -/
theorem trailingCoeff_mem_lazardProjection (hb : b ∈ B) :
    b.trailingCoeff ∈ F.lazardProjection B :=
  mem_lazardProjection.2 <| .inr <| .inr <| .inl ⟨b, hb, rfl⟩

/-- The discriminant of every member of the basis lies in the Lazard projection. -/
theorem discr_mem_lazardProjection (hb : b ∈ B) : b.discr ∈ F.lazardProjection B :=
  mem_lazardProjection.2 <| .inr <| .inr <| .inr <| .inl ⟨b, hb, rfl⟩

/-- The resultant of two distinct members of the basis lies in the Lazard projection. -/
theorem resultant_mem_lazardProjection (hb : b ∈ B) (hb' : b' ∈ B) (hne : b ≠ b') :
    resultant b b' ∈ F.lazardProjection B :=
  mem_lazardProjection.2 <| .inr <| .inr <| .inr <| .inr ⟨b, hb, b', hb', hne, rfl⟩

/-- With the empty basis, the Lazard projection consists of the contents of the family. -/
@[simp]
theorem lazardProjection_empty_right [DecidableEq R] :
    F.lazardProjection ∅ = F.image content := by
  ext a
  simp [mem_lazardProjection, eq_comm]

/-- Enlarging the family or the basis enlarges the Lazard projection. -/
@[gcongr]
theorem lazardProjection_mono (hF : F ⊆ F') (hB : B ⊆ B') :
    F.lazardProjection B ⊆ F'.lazardProjection B' := by
  intro a ha
  rw [mem_lazardProjection] at ha
  rcases ha with ⟨f, hf, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ |
    ⟨b, hb, b', hb', hne, rfl⟩
  · exact content_mem_lazardProjection (hF hf)
  · exact leadingCoeff_mem_lazardProjection (hB hb)
  · exact trailingCoeff_mem_lazardProjection (hB hb)
  · exact discr_mem_lazardProjection (hB hb)
  · exact resultant_mem_lazardProjection (hB hb) (hB hb') hne

/-- The Lazard projection is contained in the McCallum projection: leading and trailing
coefficients are coefficients up to the degree. -/
theorem lazardProjection_subset_mcCallumProjection :
    F.lazardProjection B ⊆ F.mcCallumProjection B := by
  intro a ha
  rcases mem_lazardProjection.1 ha with ⟨f, hf, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ |
    ⟨b, hb, rfl⟩ | ⟨b, hb, b', hb', hne, rfl⟩
  · exact content_mem_mcCallumProjection hf
  · exact coeff_mem_mcCallumProjection hb le_rfl
  · exact coeff_mem_mcCallumProjection hb (natTrailingDegree_le_natDegree b)
  · exact discr_mem_mcCallumProjection hb
  · exact resultant_mem_mcCallumProjection hb hb' hne

namespace IsIrreducibleBasis

variable [IsDomain R] [UniqueFactorizationMonoid R]

/-! ### Independence of the basis -/

/-- **Independence of the basis.** For two irreducible bases `B` and `B'` of the same family,
every element of the Lazard projection with respect to `B'` is associated to an element of the
Lazard projection with respect to `B`. -/
theorem exists_associated_mem_lazardProjection (hB : F.IsIrreducibleBasis B)
    (hB' : F.IsIrreducibleBasis B') {a : R} (ha : a ∈ F.lazardProjection B') :
    ∃ a' ∈ F.lazardProjection B, Associated a a' := by
  rcases mem_lazardProjection.1 ha with ⟨f, hf, rfl⟩ | ⟨b', hb', rfl⟩ | ⟨b', hb', rfl⟩ |
    ⟨b', hb', rfl⟩ | ⟨b₁', hb₁', b₂', hb₂', hne, rfl⟩
  · exact ⟨_, content_mem_lazardProjection hf, .refl _⟩
  · obtain ⟨b, hb, r, hr, rfl⟩ := hB'.exists_eq_C_mul hB hb'
    refine ⟨_, leadingCoeff_mem_lazardProjection hb, ?_⟩
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact associated_unit_mul_left _ _ hr
  · obtain ⟨b, hb, r, hr, rfl⟩ := hB'.exists_eq_C_mul hB hb'
    refine ⟨_, trailingCoeff_mem_lazardProjection hb, ?_⟩
    rw [trailingCoeff_mul, trailingCoeff_eq_coeff_zero (by simpa using hr.ne_zero), coeff_C_zero]
    exact associated_unit_mul_left _ _ hr
  · obtain ⟨b, hb, h⟩ := hB'.exists_associated_discr hB hb'
    exact ⟨_, discr_mem_lazardProjection hb, h⟩
  · obtain ⟨b₁, hb₁, b₂, hb₂, hne', h⟩ := hB'.exists_associated_resultant hB hb₁' hb₂' hne
    exact ⟨_, resultant_mem_lazardProjection hb₁ hb₂ hne', h⟩

/-! ### Nonvanishing -/

/-- **Nonvanishing of the Lazard projection.** In characteristic zero, the Lazard projection of
an irreducible basis contains `0` exactly when the family contains the zero polynomial. Thus for
a family of nonzero polynomials, the contents of its members and the leading coefficients,
trailing coefficients, discriminants and pairwise resultants of the basis are all nonzero. -/
@[simp]
theorem zero_mem_lazardProjection_iff [CharZero R] (hB : F.IsIrreducibleBasis B) :
    0 ∈ F.lazardProjection B ↔ 0 ∈ F := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using content_mem_lazardProjection (B := B) h⟩
  rcases mem_lazardProjection.1 h with ⟨f, hf, hf0⟩ | ⟨b, hb, hb0⟩ | ⟨b, hb, hb0⟩ |
    ⟨b, hb, hb0⟩ | ⟨b, hb, b', hb', hne, h0⟩
  · rwa [← content_eq_zero_iff.1 hf0]
  · exact absurd (leadingCoeff_eq_zero.1 hb0) (hB.irreducible b hb).ne_zero
  · exact absurd (trailingCoeff_eq_zero.1 hb0) (hB.irreducible b hb).ne_zero
  · exact absurd hb0 (hB.discr_ne_zero hb)
  · exact absurd h0 (hB.resultant_ne_zero hb hb' hne)

end IsIrreducibleBasis

end Finset
