/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.NumberField.ClassNumber

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
for a finite abelian group they have the same cardinality, because the squaring endomorphism
`C ↦ C²` has `Cl(R)²` as its range and `Cl(R)[2]` as its kernel, and a finite group has the same
cardinality as the product of the range and kernel of any endomorphism. We keep the two distinct in
names and statements and record the cardinality identity as `card_elementaryTwoQuotient`.

## Main definitions and results

* `TauCeti.ClassGroup.elementaryTwoQuotient`: the quotient `Cl(R) ⧸ Cl(R)²`, a `ZMod 2`-module.
* `TauCeti.ClassGroup.card_elementaryTwoQuotient`: `|Cl(R)/Cl(R)²| = |Cl(R)[2]|`, the quotient and
  the 2-torsion subgroup have equal cardinality.
* `TauCeti.ClassGroup.twoRank` and
  `TauCeti.ClassGroup.card_elementaryTwoQuotient_eq_two_pow_twoRank`: the 2-rank, with
  `|Cl(R)/Cl(R)²| = 2 ^ twoRank`.

The `ZMod 2`-module construction mirrors the square-class group `Kˣ ⧸ (Kˣ)²` of
`TauCeti.FieldTheory.SquareClassGroup`; here it is carried out for the class group, the object
Layer 2 of the multiquadratic roadmap targets.
-/

namespace TauCeti.ClassGroup

variable (R : Type*) [CommRing R] [IsDomain R]

/-- **The maximal elementary-2 quotient `Cl(R)/Cl(R)²` of the class group**, written additively on
`Additive (ClassGroup R)`. -/
abbrev elementaryTwoQuotient : Type _ :=
  Additive (ClassGroup R) ⧸ (Subgroup.square (ClassGroup R)).toAddSubgroup

/-- The elementary-2 quotient is a `ZMod 2`-module: every element has order dividing two, since the
double of any class is (additively) the class of a square. -/
noncomputable instance : Module (ZMod 2) (elementaryTwoQuotient R) :=
  QuotientAddGroup.zmodModule fun x => by
    rw [Additive.mem_toAddSubgroup, Subgroup.mem_square, toMul_nsmul]
    exact ⟨Additive.toMul x, pow_two _⟩

instance [Finite (ClassGroup R)] : Finite (elementaryTwoQuotient R) :=
  Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)

variable [Finite (ClassGroup R)]

/-- **The maximal elementary-2 quotient and the 2-torsion subgroup have the same cardinality.**
`|Cl(R)/Cl(R)²| = |Cl(R)[2]|`. The squaring endomorphism `C ↦ C²` has range `Cl(R)²` and kernel
`Cl(R)[2]`; in a finite group the index of the range equals the cardinality of the kernel. -/
theorem card_elementaryTwoQuotient :
    Nat.card (elementaryTwoQuotient R) = Nat.card {C : ClassGroup R // C ^ 2 = 1} := by
  have hsq : Subgroup.square (ClassGroup R)
      = (powMonoidHom 2 : ClassGroup R →* ClassGroup R).range := by
    ext g
    simp [Subgroup.mem_square, MonoidHom.mem_range, isSquare_iff_exists_sq, eq_comm]
  change (Subgroup.square (ClassGroup R)).toAddSubgroup.index = _
  rw [Subgroup.index_toAddSubgroup, hsq, Subgroup.index_range]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])

/-- **The 2-rank of the class group**: the `ZMod 2`-dimension of the maximal elementary-2 quotient
`Cl(R)/Cl(R)²`. This is the quantity the genus-field theorems express as `t - 1`, with `t` the
number of ramified primes. -/
noncomputable def twoRank : ℕ := Module.finrank (ZMod 2) (elementaryTwoQuotient R)

/-- The maximal elementary-2 quotient has cardinality `2 ^ twoRank`: it is a finite `𝔽₂`-vector
space of dimension the 2-rank. -/
theorem card_elementaryTwoQuotient_eq_two_pow_twoRank :
    Nat.card (elementaryTwoQuotient R) = 2 ^ twoRank R := by
  rw [twoRank, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end TauCeti.ClassGroup
