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

The construction itself is the general `TauCeti.ElementaryTwoQuotient` of a commutative group,
specialized here to `G = ClassGroup R` under the genus-theory names Layer 2 of the multiquadratic
roadmap targets (`TauCetiRoadmap/Multiquadratic/README.md`). The same general construction is the
square-class group `Kˣ ⧸ (Kˣ)²` of `TauCeti.FieldTheory.SquareClassGroup` for `G = Kˣ`.

## Main definitions and results

* `TauCeti.ClassGroup.ElementaryTwoQuotient`: the quotient `Cl(R) ⧸ Cl(R)²`, a `ZMod 2`-module.
* `TauCeti.ClassGroup.elementaryTwoQuotientMk` and `elementaryTwoQuotientMk_eq_zero_iff`: the class
  of an ideal class, trivial iff that class is a square; `elementaryTwoQuotientMk_mul`,
  `elementaryTwoQuotientMk_one`, and `elementaryTwoQuotientMk_prod` record its additivity, while
  `elementaryTwoQuotientMk_surjective` and `elementaryTwoQuotientMk_eq_iff` give surjectivity and
  the equality criterion.
* `TauCeti.ClassGroup.card_elementaryTwoQuotient_eq_card_twoTorsion`: `|Cl(R)/Cl(R)²| = |Cl(R)[2]|`,
  the quotient and the 2-torsion subgroup have equal cardinality.
* `TauCeti.ClassGroup.twoRank` and `card_elementaryTwoQuotient_eq_two_pow_twoRank`: the 2-rank, with
  `|Cl(R)/Cl(R)²| = 2 ^ twoRank`.
-/

namespace TauCeti.ClassGroup

variable (R : Type*) [CommRing R] [IsDomain R]

/-- **The maximal elementary-2 quotient `Cl(R)/Cl(R)²` of the class group**, the general
`TauCeti.ElementaryTwoQuotient` specialized to `ClassGroup R`. -/
abbrev ElementaryTwoQuotient : Type _ := TauCeti.ElementaryTwoQuotient (ClassGroup R)

/-- The class of an ideal class in the maximal elementary-2 quotient `Cl(R)/Cl(R)²`. -/
noncomputable def elementaryTwoQuotientMk (C : ClassGroup R) : ElementaryTwoQuotient R :=
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

/-- Every element of `Cl(R)/Cl(R)²` is the class of some ideal class. -/
theorem elementaryTwoQuotientMk_surjective :
    Function.Surjective (elementaryTwoQuotientMk R) :=
  TauCeti.elementaryTwoQuotientMk_surjective

/-- Two ideal classes have the same class in `Cl(R)/Cl(R)²` iff they differ by a square. -/
theorem elementaryTwoQuotientMk_eq_iff (C D : ClassGroup R) :
    elementaryTwoQuotientMk R C = elementaryTwoQuotientMk R D ↔ IsSquare (C / D) :=
  TauCeti.elementaryTwoQuotientMk_eq_iff C D

/-- **The 2-rank of the class group when `Cl(R)/Cl(R)²` is finite-dimensional**: the `ZMod 2`
dimension of the maximal elementary-2 quotient. In genus-theory applications the `t - 1` formula
belongs to the narrow class group; for imaginary fields the narrow and ordinary class groups
coincide. -/
noncomputable def twoRank [Module.Finite (ZMod 2) (ElementaryTwoQuotient R)] : ℕ :=
  TauCeti.twoRank (ClassGroup R)

variable [Finite (ClassGroup R)]

/-- A finite class group has finite-dimensional elementary-2 quotient. -/
instance : Module.Finite (ZMod 2) (ElementaryTwoQuotient R) := by
  infer_instance

/-- **The maximal elementary-2 quotient and the 2-torsion subgroup have the same cardinality.**
`|Cl(R)/Cl(R)²| = |Cl(R)[2]|`. -/
theorem card_elementaryTwoQuotient_eq_card_twoTorsion :
    Nat.card (ElementaryTwoQuotient R) = Nat.card {C : ClassGroup R // C ^ 2 = 1} :=
  TauCeti.card_elementaryTwoQuotient_eq_card_sq_eq_one (ClassGroup R)

/-- The maximal elementary-2 quotient has cardinality `2 ^ twoRank`: it is a finite `𝔽₂`-vector
space of dimension the 2-rank. -/
theorem card_elementaryTwoQuotient_eq_two_pow_twoRank :
    Nat.card (ElementaryTwoQuotient R) = 2 ^ twoRank R :=
  TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank (ClassGroup R)

end TauCeti.ClassGroup
