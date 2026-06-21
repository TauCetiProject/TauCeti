/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.ClassGroup.Basic
import TauCeti.Algebra.Group.ElementaryTwoQuotient

/-!
# The maximal elementary-2 quotient `Cl(R)/Cl(R)²` of a class group

For a domain `R` (for the genus-theory application, the ring of integers `𝓞 K` of a number field,
whose class group is finite), the **class group** `ClassGroup R` is an abelian group, and genus
theory studies its `2`-part through the quotient by its subgroup of squares,
`Cl(R) / Cl(R)²`. Every element of this quotient has order dividing `2`, so it is a vector space
over `𝔽₂ = ZMod 2`; its dimension is the **2-rank** of the class group, the quantity the genus-field
theorems compute.

⚠ This quotient is the **maximal elementary-2 quotient** of the class group, *not* the 2-torsion
subgroup `Cl(R)[2] = {C | C² = 1}`. The two are different objects — a quotient and a subgroup — but
for a finite abelian group they have the same cardinality (see
`card_elementaryTwoQuotient_eq_card_twoTorsion`); we keep them distinct in names and statements.

The construction itself is the general `TauCeti.elementaryTwoQuotient` of a commutative group,
specialized here to `G = ClassGroup R` under the genus-theory names Layer 2 of the multiquadratic
roadmap targets (`TauCetiRoadmap/Multiquadratic/README.md`). The same general construction is the
square-class group `Kˣ ⧸ (Kˣ)²` of `TauCeti.FieldTheory.SquareClassGroup` for `G = Kˣ`.

## Main definitions and results

* `TauCeti.ClassGroup.elementaryTwoQuotient`: the quotient `Cl(R) ⧸ Cl(R)²`, a `ZMod 2`-module.
* `TauCeti.ClassGroup.elementaryTwoQuotientMk` and `elementaryTwoQuotientMk_eq_zero_iff`: the class
  of an ideal class, trivial iff that class is a square; `elementaryTwoQuotientMk_mul`,
  `elementaryTwoQuotientMk_one`, and `elementaryTwoQuotientMk_prod` record its additivity.
* `TauCeti.ClassGroup.card_elementaryTwoQuotient_eq_card_twoTorsion`: `|Cl(R)/Cl(R)²| = |Cl(R)[2]|`,
  the quotient and the 2-torsion subgroup have equal cardinality.
* `TauCeti.ClassGroup.twoRank` and `card_elementaryTwoQuotient_eq_two_pow_twoRank`: the 2-rank, with
  `|Cl(R)/Cl(R)²| = 2 ^ twoRank`.
-/

namespace TauCeti.ClassGroup

variable (R : Type*) [CommRing R] [IsDomain R]

/-- **The maximal elementary-2 quotient `Cl(R)/Cl(R)²` of the class group**, the general
`TauCeti.elementaryTwoQuotient` specialized to `ClassGroup R`. -/
abbrev elementaryTwoQuotient : Type _ := TauCeti.elementaryTwoQuotient (ClassGroup R)

/-- The class of an ideal class in the maximal elementary-2 quotient `Cl(R)/Cl(R)²`. -/
noncomputable def elementaryTwoQuotientMk (C : ClassGroup R) : elementaryTwoQuotient R :=
  TauCeti.elementaryTwoQuotientMk C

/-- An ideal class has trivial class in `Cl(R)/Cl(R)²` iff it is a square. -/
@[simp] theorem elementaryTwoQuotientMk_eq_zero_iff (C : ClassGroup R) :
    elementaryTwoQuotientMk R C = 0 ↔ IsSquare C :=
  TauCeti.elementaryTwoQuotientMk_eq_zero_iff C

/-- The class map to `Cl(R)/Cl(R)²` sends a product of ideal classes to the sum of the classes. -/
@[simp] theorem elementaryTwoQuotientMk_mul (C D : ClassGroup R) :
    elementaryTwoQuotientMk R (C * D) = elementaryTwoQuotientMk R C + elementaryTwoQuotientMk R D :=
  TauCeti.elementaryTwoQuotientMk_mul C D

/-- The class map to `Cl(R)/Cl(R)²` sends the trivial ideal class to `0`. -/
@[simp] theorem elementaryTwoQuotientMk_one :
    elementaryTwoQuotientMk R (1 : ClassGroup R) = 0 :=
  TauCeti.elementaryTwoQuotientMk_one

/-- The class map to `Cl(R)/Cl(R)²` sends a finite product of ideal classes to the sum of the
classes. -/
theorem elementaryTwoQuotientMk_prod {ι : Type*} (S : Finset ι) (C : ι → ClassGroup R) :
    elementaryTwoQuotientMk R (∏ i ∈ S, C i) = ∑ i ∈ S, elementaryTwoQuotientMk R (C i) :=
  TauCeti.elementaryTwoQuotientMk_prod S C

/-- **The 2-rank of the class group**: the `ZMod 2`-dimension of the maximal elementary-2 quotient
`Cl(R)/Cl(R)²`. This is the quantity the genus-field theorems express as `t - 1`, with `t` the
number of ramified primes. -/
noncomputable def twoRank : ℕ := TauCeti.twoRank (ClassGroup R)

variable [Finite (ClassGroup R)]

/-- **The maximal elementary-2 quotient and the 2-torsion subgroup have the same cardinality.**
`|Cl(R)/Cl(R)²| = |Cl(R)[2]|`. -/
theorem card_elementaryTwoQuotient_eq_card_twoTorsion :
    Nat.card (elementaryTwoQuotient R) = Nat.card {C : ClassGroup R // C ^ 2 = 1} :=
  TauCeti.card_elementaryTwoQuotient_eq_card_sq_eq_one (ClassGroup R)

/-- The maximal elementary-2 quotient has cardinality `2 ^ twoRank`: it is a finite `𝔽₂`-vector
space of dimension the 2-rank. -/
theorem card_elementaryTwoQuotient_eq_two_pow_twoRank :
    Nat.card (elementaryTwoQuotient R) = 2 ^ twoRank R :=
  TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank (ClassGroup R)

end TauCeti.ClassGroup
