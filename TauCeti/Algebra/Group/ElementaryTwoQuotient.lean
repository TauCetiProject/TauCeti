/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index

/-!
# The maximal elementary-2 quotient `G / G²` of a commutative group

For a commutative group `G`, the quotient by its subgroup of squares, `G / G²`, has every element
of order dividing `2`, so it is a vector space over `𝔽₂ = ZMod 2`. When `G` is finite its dimension
is the **2-rank** of `G`. This file develops that construction at the level of an arbitrary
commutative group; the genus-theory specialization to a class group lives in
`TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient`, and the square-class group `Kˣ ⧸ (Kˣ)²` of
`TauCeti.FieldTheory.SquareClassGroup` is the same construction for `G = Kˣ`.

⚠ This quotient is the **maximal elementary-2 quotient** of `G`, *not* its 2-torsion subgroup
`{g | g² = 1}`. The two are different objects — a quotient and a subgroup — but for a finite group
they have the same cardinality, because the squaring endomorphism `g ↦ g²` has `G²` as its range and
the 2-torsion as its kernel, and a finite group has the same cardinality as the product of the range
and kernel of any endomorphism. We keep the two distinct in names and statements and record the
cardinality identity as `card_elementaryTwoQuotient_eq_card_sq_eq_one`.

Mathlib's `ModN G n` is the analogous additive quotient `G ⧸ nG` built from `range (lsmul ℤ G n)`;
we keep the multiplicative `Subgroup.square` framing here because the cardinality identity is
cleanest through the squaring homomorphism `powMonoidHom 2` and `Subgroup.index_range`.

## Main definitions and results

* `TauCeti.elementaryTwoQuotient`: the quotient `G ⧸ G²`, a `ZMod 2`-module.
* `TauCeti.elementaryTwoQuotientMk` and `TauCeti.elementaryTwoQuotientMk_eq_zero_iff`: the class of
  an element, trivial iff the element is a square.
* `TauCeti.card_elementaryTwoQuotient_eq_card_sq_eq_one`: `|G/G²| = |{g | g² = 1}|`.
* `TauCeti.twoRank` and `TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank`: the 2-rank, with
  `|G/G²| = 2 ^ twoRank`.
-/

namespace TauCeti

variable (G : Type*) [CommGroup G]

/-- **The maximal elementary-2 quotient `G / G²`** of a commutative group, written additively on
`Additive G`. -/
abbrev elementaryTwoQuotient : Type _ :=
  Additive G ⧸ (Subgroup.square G).toAddSubgroup

/-- The elementary-2 quotient is a `ZMod 2`-module: every element has order dividing two, since the
double of any element is (additively) the class of a square. -/
noncomputable instance : Module (ZMod 2) (elementaryTwoQuotient G) :=
  QuotientAddGroup.zmodModule fun x => by
    rw [Additive.mem_toAddSubgroup, Subgroup.mem_square, toMul_nsmul]
    exact ⟨Additive.toMul x, pow_two _⟩

instance [Finite G] : Finite (elementaryTwoQuotient G) :=
  Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)

variable {G}

/-- The class of an element of `G` in the maximal elementary-2 quotient `G / G²`. -/
def elementaryTwoQuotientMk (g : G) : elementaryTwoQuotient G :=
  QuotientAddGroup.mk (Additive.ofMul g)

/-- An element has trivial class in `G / G²` iff it is a square. -/
@[simp] theorem elementaryTwoQuotientMk_eq_zero_iff (g : G) :
    elementaryTwoQuotientMk g = 0 ↔ IsSquare g := by
  rw [elementaryTwoQuotientMk, QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup,
    Subgroup.mem_square]
  simp

variable (G)

/-- **The maximal elementary-2 quotient and the 2-torsion subgroup have the same cardinality.**
`|G/G²| = |{g | g² = 1}|`. The squaring endomorphism `g ↦ g²` has range `G²` and kernel the
2-torsion; in a finite group the index of the range equals the cardinality of the kernel. -/
theorem card_elementaryTwoQuotient_eq_card_sq_eq_one [Finite G] :
    Nat.card (elementaryTwoQuotient G) = Nat.card {g : G // g ^ 2 = 1} := by
  have hsq : Subgroup.square G = (powMonoidHom 2 : G →* G).range := by
    ext g
    simp [Subgroup.mem_square, MonoidHom.mem_range, isSquare_iff_exists_sq, eq_comm]
  rw [← AddSubgroup.index_eq_card, Subgroup.index_toAddSubgroup, hsq, Subgroup.index_range]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])

/-- **The 2-rank of a finite commutative group**: the `ZMod 2`-dimension of the maximal
elementary-2 quotient `G / G²`. -/
noncomputable def twoRank [Finite G] : ℕ := Module.finrank (ZMod 2) (elementaryTwoQuotient G)

/-- The maximal elementary-2 quotient has cardinality `2 ^ twoRank`: it is a finite `𝔽₂`-vector
space of dimension the 2-rank. -/
theorem card_elementaryTwoQuotient_eq_two_pow_twoRank [Finite G] :
    Nat.card (elementaryTwoQuotient G) = 2 ^ twoRank G := by
  rw [twoRank, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end TauCeti
