/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient

/-!
# The elementary-2 quotient of a number-field class group

For a number field `K`, the genus-theory layer of the multiquadratic roadmap uses the
maximal elementary-2 quotient of the class group of its ring of integers,
`Cl(𝓞 K) / Cl(𝓞 K)²`. The generic construction and its class-group specialization live in
`TauCeti.Algebra.Group.ElementaryTwoQuotient` and
`TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient`; this file records the number-field
specialization where Mathlib's class-number theorem supplies finiteness automatically.

The quotient here is the maximal elementary-2 quotient, not the 2-torsion subgroup. For the
finite class group of a number field, the two have the same cardinality, and the quotient
cardinality divides the class number.

## Main definitions and results

* `TauCeti.NumberField.ClassGroupElementaryTwoQuotient`: the quotient
  `Cl(𝓞 K) / Cl(𝓞 K)²`.
* `TauCeti.NumberField.classGroupElementaryTwoQuotientMk`: the class map.
* `TauCeti.NumberField.classGroupTwoRank`: the `ZMod 2` dimension of this quotient.
* `TauCeti.NumberField.card_classGroupElementaryTwoQuotient_eq_two_pow_classGroupTwoRank`:
  the quotient has cardinality `2 ^ classGroupTwoRank K`.
* `TauCeti.NumberField.card_classGroupElementaryTwoQuotient_eq_card_twoTorsion`: the quotient
  and the 2-torsion subgroup of `Cl(𝓞 K)` have equal cardinality.
* `TauCeti.NumberField.card_classGroupElementaryTwoQuotient_dvd_classNumber`: the elementary-2
  quotient cardinality divides the class number.
* `TauCeti.NumberField.two_pow_classGroupTwoRank_dvd_classNumber`: the same divisibility in
  rank form.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

variable (K : Type*) [Field K]

/-- The maximal elementary-2 quotient `Cl(𝓞 K) / Cl(𝓞 K)²` of the class group of the ring of
integers of a number field. -/
abbrev ClassGroupElementaryTwoQuotient : Type _ :=
  TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K)

/-- The class of an ideal class in the elementary-2 quotient `Cl(𝓞 K) / Cl(𝓞 K)²`. -/
noncomputable def classGroupElementaryTwoQuotientMk
    (C : ClassGroup (𝓞 K)) : ClassGroupElementaryTwoQuotient K :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk (𝓞 K) C

/-- An ideal class has trivial image in `Cl(𝓞 K) / Cl(𝓞 K)²` iff it is a square. -/
@[simp] theorem classGroupElementaryTwoQuotientMk_eq_zero_iff (C : ClassGroup (𝓞 K)) :
    classGroupElementaryTwoQuotientMk K C = 0 ↔ IsSquare C :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_eq_zero_iff (𝓞 K) C

/-- The class map to `Cl(𝓞 K) / Cl(𝓞 K)²` sends products to sums. -/
@[simp] theorem classGroupElementaryTwoQuotientMk_mul (C D : ClassGroup (𝓞 K)) :
    classGroupElementaryTwoQuotientMk K (C * D) =
      classGroupElementaryTwoQuotientMk K C + classGroupElementaryTwoQuotientMk K D :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_mul (𝓞 K) C D

/-- The class map to `Cl(𝓞 K) / Cl(𝓞 K)²` sends the trivial class to zero. -/
@[simp] theorem classGroupElementaryTwoQuotientMk_one :
    classGroupElementaryTwoQuotientMk K (1 : ClassGroup (𝓞 K)) = 0 :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_one (𝓞 K)

/-- The class map to `Cl(𝓞 K) / Cl(𝓞 K)²` sends inverses to negatives. -/
@[simp] theorem classGroupElementaryTwoQuotientMk_inv (C : ClassGroup (𝓞 K)) :
    classGroupElementaryTwoQuotientMk K C⁻¹ = -classGroupElementaryTwoQuotientMk K C :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_inv (𝓞 K) C

/-- The class map to `Cl(𝓞 K) / Cl(𝓞 K)²` sends quotients to differences. -/
@[simp] theorem classGroupElementaryTwoQuotientMk_div (C D : ClassGroup (𝓞 K)) :
    classGroupElementaryTwoQuotientMk K (C / D) =
      classGroupElementaryTwoQuotientMk K C - classGroupElementaryTwoQuotientMk K D :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_div (𝓞 K) C D

/-- The class map to `Cl(𝓞 K) / Cl(𝓞 K)²` sends powers to scalar multiples. -/
@[simp] theorem classGroupElementaryTwoQuotientMk_pow (C : ClassGroup (𝓞 K)) (n : ℕ) :
    classGroupElementaryTwoQuotientMk K (C ^ n) =
      n • classGroupElementaryTwoQuotientMk K C :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_pow (𝓞 K) C n

/-- Every element of `Cl(𝓞 K) / Cl(𝓞 K)²` is the class of an ideal class. -/
theorem classGroupElementaryTwoQuotientMk_surjective :
    Function.Surjective (classGroupElementaryTwoQuotientMk K) :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_surjective (𝓞 K)

/-- Two ideal classes have the same image in `Cl(𝓞 K) / Cl(𝓞 K)²` iff their quotient is a
square. -/
theorem classGroupElementaryTwoQuotientMk_eq_iff (C D : ClassGroup (𝓞 K)) :
    classGroupElementaryTwoQuotientMk K C = classGroupElementaryTwoQuotientMk K D ↔
      IsSquare (C / D) :=
  TauCeti.ClassGroup.elementaryTwoQuotientMk_eq_iff (𝓞 K) C D

/-- The class-group `2`-rank of a number field: the `ZMod 2` dimension of
`Cl(𝓞 K) / Cl(𝓞 K)²`. -/
noncomputable def classGroupTwoRank : ℕ :=
  TauCeti.ClassGroup.twoRank (𝓞 K)

/-- The class-group `2`-rank is the dimension of `Cl(𝓞 K) / Cl(𝓞 K)²`. -/
@[simp] theorem classGroupTwoRank_def :
    classGroupTwoRank K =
      Module.finrank (ZMod 2) (ClassGroupElementaryTwoQuotient K) :=
  TauCeti.ClassGroup.twoRank_def (𝓞 K)

/-- The elementary-2 quotient of a number-field class group is finite-dimensional over `ZMod 2`. -/
instance [NumberField K] : Module.Finite (ZMod 2) (ClassGroupElementaryTwoQuotient K) := by
  dsimp [ClassGroupElementaryTwoQuotient]
  infer_instance

/-- The elementary-2 quotient of the class group has cardinality `2 ^ classGroupTwoRank K`. -/
theorem card_classGroupElementaryTwoQuotient_eq_two_pow_classGroupTwoRank [NumberField K] :
    Nat.card (ClassGroupElementaryTwoQuotient K) = 2 ^ classGroupTwoRank K :=
  TauCeti.ClassGroup.card_elementaryTwoQuotient_eq_two_pow_twoRank (𝓞 K)

/-- The elementary-2 quotient and the 2-torsion subgroup of the number-field class group have
the same cardinality. -/
theorem card_classGroupElementaryTwoQuotient_eq_card_twoTorsion [NumberField K] :
    Nat.card (ClassGroupElementaryTwoQuotient K) =
      Nat.card {C : ClassGroup (𝓞 K) // C ^ 2 = 1} :=
  TauCeti.ClassGroup.card_elementaryTwoQuotient_eq_card_twoTorsion (𝓞 K)

/-- The cardinality of `Cl(𝓞 K) / Cl(𝓞 K)²` divides the class number. -/
theorem card_classGroupElementaryTwoQuotient_dvd_classNumber [NumberField K] :
    Nat.card (ClassGroupElementaryTwoQuotient K) ∣ NumberField.classNumber K := by
  rw [ClassGroupElementaryTwoQuotient, TauCeti.ClassGroup.ElementaryTwoQuotient,
    TauCeti.card_elementaryTwoQuotient_eq_index_square, NumberField.classNumber]
  rw [← Nat.card_eq_fintype_card]
  exact Subgroup.index_dvd_card (Subgroup.square (ClassGroup (𝓞 K)))

/-- The elementary-2 quotient of a number-field class group has cardinality at most the class
number. -/
theorem card_classGroupElementaryTwoQuotient_le_classNumber [NumberField K] :
    Nat.card (ClassGroupElementaryTwoQuotient K) ≤ NumberField.classNumber K :=
  Nat.le_of_dvd (NumberField.classNumber_pos K) <|
    card_classGroupElementaryTwoQuotient_dvd_classNumber K

/-- The rank form of `card_classGroupElementaryTwoQuotient_dvd_classNumber`:
`2 ^ classGroupTwoRank K` divides the class number. -/
theorem two_pow_classGroupTwoRank_dvd_classNumber [NumberField K] :
    2 ^ classGroupTwoRank K ∣ NumberField.classNumber K := by
  rw [← card_classGroupElementaryTwoQuotient_eq_two_pow_classGroupTwoRank]
  exact card_classGroupElementaryTwoQuotient_dvd_classNumber K

/-- The rank form of `card_classGroupElementaryTwoQuotient_le_classNumber`:
`2 ^ classGroupTwoRank K` is bounded by the class number. -/
theorem two_pow_classGroupTwoRank_le_classNumber [NumberField K] :
    2 ^ classGroupTwoRank K ≤ NumberField.classNumber K := by
  rw [← card_classGroupElementaryTwoQuotient_eq_two_pow_classGroupTwoRank]
  exact card_classGroupElementaryTwoQuotient_le_classNumber K

end TauCeti.NumberField
