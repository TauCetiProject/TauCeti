/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit

/-!
# The twelve roots of `G₂`, six long and six short

Mathlib's `RootPairing.EmbeddedG2` singles out in a crystallographic reduced pairing a pair of
roots `α` (short) and `β` (long) with `⟨β, α^∨⟩ = -3`, and lists the twelve roots they generate:
`±β`, `±α`, `±(α + β)`, `±(2α + β)`, `±(3α + β)` and `±(3α + 2β)`. When the pairing is irreducible
these are *all* of its roots (`RootPairing.EmbeddedG2.card_index_eq_twelve`). This file sorts them
by length.

The length of a root here is its squared length `‖αᵢ‖²` measured by a root-positive form, Mathlib's
`RootPairing.RootPositiveForm.rootLength`. Every statement below is quantified over that form and
only ever *compares* two of its lengths, so nothing depends on which form is taken. Two inputs do
all the work. The first is that a reflection preserves lengths, so each of the ten roots away from
the chosen pair, being obtained from `α` or from `β` by reflections, has the length of the one it
came from: that is `RootPairing.RootPositiveForm.rootLength_reflectionPerm`, the `reflectionPerm`
case of the Weyl-invariance of length proved in
`TauCeti/LinearAlgebra/RootSystem/Weyl/Orbit.lean`. The second is the ratio `‖β‖² = 3‖α‖²`, which
is Mathlib's `RootPairing.EmbeddedG2.long_eq_three_mul_short` transported from the values of the
form to the `S`-valued length.

Together these split the twelve roots into six of length `‖α‖²` and six of length `3‖α‖²`, which
is the `6`-and-`6` count the `G₂` worked example asks for. The two sets are counted without
checking the fifteen pairs of distinctness relations among either six: each of the two is visibly
of at most six elements, their union is everything, and there are twelve roots in all, so neither
can have fewer than six.

## Main results

* `RootPairing.EmbeddedG2.rootLength_long_eq_three_mul_rootLength_short`: **the long root of an
  embedded `G₂` is longer than the short one by the factor `3`**, and
  `RootPairing.EmbeddedG2.rootLength_short_ne_rootLength_long` is the consequence that the two
  lengths differ.
* `RootPairing.EmbeddedG2.rootLength_shortAddLong` and its three companions: each of the four
  roots `α + β`, `2α + β`, `3α + β` and `3α + 2β` has the length of `α` or of `β`, namely of the
  root it is the reflection of.
* `RootPairing.EmbeddedG2.rootLength_eq_rootLength_short_or_long`: **every root of an irreducible
  embedded `G₂` has the length either of `α` or of `β`**: there are exactly two lengths.
* `RootPairing.EmbeddedG2.setOf_rootLength_eq_rootLength_short` and
  `RootPairing.EmbeddedG2.setOf_rootLength_eq_rootLength_long`: the two length classes named
  explicitly, `{±α, ±(α + β), ±(2α + β)}` and `{±β, ±(3α + β), ±(3α + 2β)}`.
* `RootPairing.EmbeddedG2.ncard_setOf_rootLength_eq_rootLength_short` and
  `RootPairing.EmbeddedG2.ncard_setOf_rootLength_eq_rootLength_long`: **`G₂` has six short roots
  and six long ones.**
* `TauCeti.ncard_posRoots_of_isG2`: **a `G₂` root system has six positive roots**, for any base.

## References

This file proves the root-length and positive-root clauses of the `G₂` worked example of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` ("the long/short root lengths differ by
a factor of `3` (`RootPairing.rootLength`), and `(posRoots b).ncard = 6`", for the root system of
"12 roots, 6 long and 6 short"); its Cartan-matrix and Weyl-group clauses are
`TauCeti.hasCartanType_G2_iff_isG2` and
`TauCeti.nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_G2`. See Bourbaki, *Lie Groups
and Lie Algebras, Chapters 4-6*, plate IX, and Humphreys, *Introduction to Lie Algebras and
Representation Theory*, GTM 9, §9, where the rank-two root systems are drawn and the twelve roots
of `G₂` appear in two orbits of six.
-/

public section

open Set

namespace RootPairing.EmbeddedG2

universe u v w x y

variable {ι : Type u} {R : Type v} {S : Type w} {M : Type x} {N : Type y}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [CommRing S] [LinearOrder S] [Algebra S R] [FaithfulSMul S R] [Module S M]
  [IsScalarTower S R M] {P : RootPairing ι R M N} [P.IsValuedIn S] [P.EmbeddedG2]
  (B : P.RootPositiveForm S)

/-! ### The lengths of the twelve roots

The four roots `α + β`, `2α + β`, `3α + β` and `3α + 2β` are defined in Mathlib by reflecting `α`
or `β`, so their lengths are read off by `rootLength_reflectionPerm` alone; none of the `G₂`
hypotheses beyond the embedded pair enters. The negatives `-αᵢ` are covered by Mathlib's
`RootPairing.RootPositiveForm.rootLength_reflectionPerm_self`. -/

/-- The root `α + β` is short: it is the reflection of `α` in `β`. -/
@[simp]
theorem rootLength_shortAddLong : B.rootLength (shortAddLong P) = B.rootLength (short P) := by
  rw [shortAddLong, B.rootLength_reflectionPerm]

/-- The root `2α + β` is short: it is the reflection in `α` of the reflection of `α` in `β`. -/
@[simp]
theorem rootLength_twoShortAddLong : B.rootLength (twoShortAddLong P) = B.rootLength (short P) := by
  rw [twoShortAddLong, B.rootLength_reflectionPerm, B.rootLength_reflectionPerm]

/-- The root `3α + β` is long: it is the reflection of `β` in `α`. -/
@[simp]
theorem rootLength_threeShortAddLong :
    B.rootLength (threeShortAddLong P) = B.rootLength (long P) := by
  rw [threeShortAddLong, B.rootLength_reflectionPerm]

/-- The root `3α + 2β` is long: it is the reflection in `β` of the reflection of `β` in `α`. -/
@[simp]
theorem rootLength_threeShortAddTwoLong :
    B.rootLength (threeShortAddTwoLong P) = B.rootLength (long P) := by
  rw [threeShortAddTwoLong, B.rootLength_reflectionPerm, B.rootLength_reflectionPerm]

variable [Finite ι] [CharZero R] [IsDomain R]

/-- **The long root of an embedded `G₂` is three times as long as the short one.** This is
Mathlib's `RootPairing.EmbeddedG2.long_eq_three_mul_short`, which states the same ratio for the
values of an invariant form, read through the `S`-valued length; the factor `3` there is the ratio
`⟨β, α^∨⟩ / ⟨α, β^∨⟩ = (-3) / (-1)` of the transposed pair of pairings of the embedded pair.

The ratio is what makes the two lengths of `G₂` distinguishable
(`RootPairing.EmbeddedG2.rootLength_short_ne_rootLength_long`), and with it the factor `3` by which
the triple edge of the `G₂` diagram is named. -/
theorem rootLength_long_eq_three_mul_rootLength_short :
    B.rootLength (long P) = 3 * B.rootLength (short P) := by
  apply FaithfulSMul.algebraMap_injective S R
  rw [map_mul, map_ofNat, B.algebraMap_rootLength, B.algebraMap_rootLength]
  exact long_eq_three_mul_short B.toInvariantForm

/-- **The short and the long root of an embedded `G₂` have different lengths.** Their lengths differ
by the factor `3`, and a root has positive length, so the two cannot agree. This is what lets the
twelve roots be sorted by length at all. -/
theorem rootLength_short_ne_rootLength_long [IsStrictOrderedRing S] :
    B.rootLength (short P) ≠ B.rootLength (long P) := by
  intro hc
  have hpos := B.rootLength_pos (short P)
  rw [rootLength_long_eq_three_mul_rootLength_short B] at hc
  have h2 : (2 : S) * B.rootLength (short P) = 0 := by linear_combination -hc
  exact absurd h2 (mul_pos (by norm_num) hpos).ne'

/-! ### Sorting the roots of an irreducible `G₂` by length

Irreducibility is what makes the twelve roots of the embedded `G₂` exhaustive
(`RootPairing.EmbeddedG2.setOfPred_index_eq_univ`), and so turns the length computations above into
a classification. -/

variable [P.IsIrreducible]

/-- **An irreducible embedded `G₂` has exactly two root lengths**, that of its short root `α` and
that of its long root `β`. Its twelve roots are `±α`, `±β` and the four reflections of `α` and `β`
together with their negatives, and reflecting preserves length.

`RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq` says in general that every root has
the length of a simple root of a given base, which is weaker than wanted here: it is stated against
a base, and identifying the two simple roots of a base of a `G₂` pairing with the embedded pair
`α, β` is the work of `TauCeti.hasCartanType_G2_of_isG2`, whereas the twelve-root list settles it
directly. -/
theorem rootLength_eq_rootLength_short_or_long (i : ι) :
    B.rootLength i = B.rootLength (short P) ∨ B.rootLength i = B.rootLength (long P) := by
  let _i := P.indexNeg
  have hmem := mem_univ (α := ι) i
  rw [← setOfPred_index_eq_univ (P := P)] at hmem
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [indexNeg_neg]

/-- **The six short roots of `G₂`**, namely `±α`, `±(α + β)` and `±(2α + β)`. -/
theorem setOf_rootLength_eq_rootLength_short [IsStrictOrderedRing S] :
    letI _i := P.indexNeg
    {i | B.rootLength i = B.rootLength (short P)} =
      ({short P, -short P, shortAddLong P, -shortAddLong P, twoShortAddLong P,
        -twoShortAddLong P} : Set ι) := by
  let _i := P.indexNeg
  have hne := rootLength_short_ne_rootLength_long B
  ext i
  simp only [mem_insert_iff, mem_singleton_iff, Set.mem_ofPred_eq]
  refine ⟨fun hi ↦ ?_, ?_⟩
  · have hmem := mem_univ (α := ι) i
    rw [← setOfPred_index_eq_univ (P := P)] at hmem
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [indexNeg_neg]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [indexNeg_neg]

/-- **The six long roots of `G₂`**, namely `±β`, `±(3α + β)` and `±(3α + 2β)`. -/
theorem setOf_rootLength_eq_rootLength_long [IsStrictOrderedRing S] :
    letI _i := P.indexNeg
    {i | B.rootLength i = B.rootLength (long P)} =
      ({long P, -long P, threeShortAddLong P, -threeShortAddLong P, threeShortAddTwoLong P,
        -threeShortAddTwoLong P} : Set ι) := by
  let _i := P.indexNeg
  have hne := rootLength_short_ne_rootLength_long B
  ext i
  simp only [mem_insert_iff, mem_singleton_iff, Set.mem_ofPred_eq]
  refine ⟨fun hi ↦ ?_, ?_⟩
  · have hmem := mem_univ (α := ι) i
    rw [← setOfPred_index_eq_univ (P := P)] at hmem
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [indexNeg_neg]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [indexNeg_neg]

/-- **`G₂` has six short roots and six long ones.** The two counts are proved together because
each follows from the same two bounds. Neither class has more than six roots, being a set of six
names (`RootPairing.EmbeddedG2.setOf_rootLength_eq_rootLength_short` and its long counterpart);
between them the two cover all twelve roots; and twelve is the total, so neither can be smaller
than six. In particular no distinctness relation among either six names has to be checked. -/
private theorem ncard_setOf_rootLength_short_and_long [IsStrictOrderedRing S] :
    {i | B.rootLength i = B.rootLength (short P)}.ncard = 6 ∧
      {i | B.rootLength i = B.rootLength (long P)}.ncard = 6 := by
  have key : ∀ a b c d e f : ι, ({a, b, c, d, e, f} : Set ι).ncard ≤ 6 := fun a b c d e f ↦ by
    have h1 := Set.ncard_insert_le a ({b, c, d, e, f} : Set ι)
    have h2 := Set.ncard_insert_le b ({c, d, e, f} : Set ι)
    have h3 := Set.ncard_insert_le c ({d, e, f} : Set ι)
    have h4 := Set.ncard_insert_le d ({e, f} : Set ι)
    have h5 := Set.ncard_insert_le e ({f} : Set ι)
    have h6 : ({f} : Set ι).ncard = 1 := Set.ncard_singleton f
    omega
  have hshort : {i | B.rootLength i = B.rootLength (short P)}.ncard ≤ 6 := by
    rw [setOf_rootLength_eq_rootLength_short B]
    exact key _ _ _ _ _ _
  have hlong : {i | B.rootLength i = B.rootLength (long P)}.ncard ≤ 6 := by
    rw [setOf_rootLength_eq_rootLength_long B]
    exact key _ _ _ _ _ _
  have hunion : {i | B.rootLength i = B.rootLength (short P)} ∪
      {i | B.rootLength i = B.rootLength (long P)} = (univ : Set ι) := by
    ext i
    simpa using rootLength_eq_rootLength_short_or_long B i
  have hle := Set.ncard_union_le {i | B.rootLength i = B.rootLength (short P)}
    {i | B.rootLength i = B.rootLength (long P)}
  rw [hunion, Set.ncard_univ, card_index_eq_twelve P] at hle
  omega

/-- **`G₂` has six short roots**, namely `±α`, `±(α + β)` and `±(2α + β)`. With
`RootPairing.EmbeddedG2.ncard_setOf_rootLength_eq_rootLength_long` this is the `6`-and-`6` split of
the twelve roots of `G₂` by length. -/
theorem ncard_setOf_rootLength_eq_rootLength_short [IsStrictOrderedRing S] :
    {i | B.rootLength i = B.rootLength (short P)}.ncard = 6 :=
  (ncard_setOf_rootLength_short_and_long B).1

/-- **`G₂` has six long roots**, namely `±β`, `±(3α + β)` and `±(3α + 2β)`: the companion of
`RootPairing.EmbeddedG2.ncard_setOf_rootLength_eq_rootLength_short`. -/
theorem ncard_setOf_rootLength_eq_rootLength_long [IsStrictOrderedRing S] :
    {i | B.rootLength i = B.rootLength (long P)}.ncard = 6 :=
  (ncard_setOf_rootLength_short_and_long B).2

end RootPairing.EmbeddedG2

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R] [P.IsG2]

/-- **A `G₂` root system has six positive roots**, for every base: a `G₂` pairing has twelve roots
in all (`RootPairing.EmbeddedG2.card_index_eq_twelve`), and a base splits the roots evenly into the
positive and the negative ones (`TauCeti.two_mul_ncard_posRoots`). How those six split by length is
not determined here; `RootPairing.EmbeddedG2.ncard_setOf_rootLength_eq_rootLength_short` counts the
short roots of both signs together. -/
theorem ncard_posRoots_of_isG2 (b : P.Base) : (posRoots P b).ncard = 6 := by
  have _i : P.EmbeddedG2 := RootPairing.IsG2.toEmbeddedG2 P
  have h := two_mul_ncard_posRoots P b
  rw [RootPairing.EmbeddedG2.card_index_eq_twelve P] at h
  omega

end TauCeti
