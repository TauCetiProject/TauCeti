/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FreeModule.ModN
import TauCeti.Algebra.Group.PowMonoidHom

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

This file uses Mathlib's additive quotient `ModN (Additive G) 2` and adds multiplicative-square
names around it. The cardinality identity is still expressed through the squaring homomorphism
`powMonoidHom 2` and `Subgroup.index_range`.

## Main definitions and results

* `TauCeti.ElementaryTwoQuotient`: the quotient `G ⧸ G²`, a `ZMod 2`-module.
* `TauCeti.elementaryTwoQuotientMkAdd`, `TauCeti.elementaryTwoQuotientMk`, and
  `TauCeti.elementaryTwoQuotientMk_eq_zero_iff`: the quotient map and the class of an element,
  trivial iff the element is a square; `elementaryTwoQuotientMk_mul`,
  `elementaryTwoQuotientMk_one`, and `elementaryTwoQuotientMk_prod` record its additivity.
* `TauCeti.elementaryTwoQuotientMk_surjective` and `TauCeti.elementaryTwoQuotientMk_eq_iff`: the
  class map is surjective, and two elements have the same class iff they differ by a square.
* `TauCeti.elementaryTwoQuotientLiftEquiv` and `TauCeti.elementaryTwoQuotientLinearLiftEquiv`: the
  universal property for maps out of `G/G²`, inherited from `ModN.liftEquiv`.
* `TauCeti.range_lsmul_two_toAddSubgroup_eq_square_toAddSubgroup` and
  `TauCeti.card_elementaryTwoQuotient_eq_index_square`: named identifications used to compute
  the quotient cardinality.
* `TauCeti.card_elementaryTwoQuotient_eq_card_sq_eq_one`: `|G/G²| = |{g | g² = 1}|`.
* `TauCeti.twoRank` and `TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank`: the 2-rank, with
  `|G/G²| = 2 ^ twoRank`.
-/

namespace TauCeti

variable (G : Type*) [CommGroup G]

/-- **The maximal elementary-2 quotient `G / G²`** of a commutative group, written additively on
`Additive G`. -/
abbrev ElementaryTwoQuotient : Type _ :=
  ModN (Additive G) 2

instance [Finite G] : Finite (ElementaryTwoQuotient G) :=
  Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)

variable {G}

/-- The quotient homomorphism `Additive G →+ G/G²`, exposed in the `ModN` additive form. -/
def elementaryTwoQuotientMkAdd : Additive G →+ ElementaryTwoQuotient G :=
  ModN.mkQ 2

/-- The class of an element of `G` in the maximal elementary-2 quotient `G / G²`. -/
def elementaryTwoQuotientMk (g : G) : ElementaryTwoQuotient G :=
  elementaryTwoQuotientMkAdd (Additive.ofMul g)

/-- An element has trivial class in `G / G²` iff it is a square. -/
@[simp] theorem elementaryTwoQuotientMk_eq_zero_iff (g : G) :
    elementaryTwoQuotientMk g = 0 ↔ IsSquare g := by
  -- `elementaryTwoQuotientMk g = ModN.mkQ 2 (ofMul g)` is the quotient map of `ofMul g`, so it
  -- vanishes iff `ofMul g` lies in the doubling subgroup `range (lsmul ℤ _ 2)`.
  rw [elementaryTwoQuotientMk, elementaryTwoQuotientMkAdd, ModN.mkQ]
  simp only [AddMonoidHom.coe_coe, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Additive.toMul a, ?_⟩
    have hmul := congr_arg Additive.toMul ha
    simpa [toMul_zsmul, zpow_two, pow_two] using hmul.symm
  · rintro ⟨a, ha⟩
    refine ⟨Additive.ofMul a, ?_⟩
    apply Additive.toMul.injective
    simpa [toMul_zsmul, zpow_two, pow_two] using ha.symm

/-- The universal property of `G/G²` for additive homomorphisms: maps out of the quotient are
additive homomorphisms from `Additive G` whose values are killed by `2`. -/
protected def elementaryTwoQuotientLiftEquiv [AddMonoid M] :
    (ElementaryTwoQuotient G →+ M) ≃
      {φ : Additive G →+ M // ∀ g, 2 • φ g = 0} :=
  ModN.liftEquiv

/-- The universal property of `G/G²` for `ZMod 2`-linear maps: linear maps out of the quotient are
additive homomorphisms from `Additive G` whose values are killed by `2`. -/
protected def elementaryTwoQuotientLinearLiftEquiv [AddCommGroup H] [Module (ZMod 2) H] :
    (ElementaryTwoQuotient G →ₗ[ZMod 2] H) ≃
      {φ : Additive G →+ H // ∀ g, 2 • φ g = 0} :=
  ModN.liftEquiv'

/-- The class map to `G / G²` sends a product to the sum of the classes. -/
@[simp] theorem elementaryTwoQuotientMk_mul (g h : G) :
    elementaryTwoQuotientMk (g * h) = elementaryTwoQuotientMk g + elementaryTwoQuotientMk h := by
  simp only [elementaryTwoQuotientMk, ofMul_mul, AddMonoidHom.map_add]

/-- The class map to `G / G²` sends `1` to `0`. -/
@[simp] theorem elementaryTwoQuotientMk_one : elementaryTwoQuotientMk (1 : G) = 0 := by
  simp only [elementaryTwoQuotientMk, ofMul_one, AddMonoidHom.map_zero]

/-- The class map to `G / G²` sends a finite product to the sum of the classes. -/
theorem elementaryTwoQuotientMk_prod {ι : Type*} (S : Finset ι) (g : ι → G) :
    elementaryTwoQuotientMk (∏ i ∈ S, g i) = ∑ i ∈ S, elementaryTwoQuotientMk (g i) := by
  simp only [elementaryTwoQuotientMk, ofMul_prod]
  rw [map_sum]

/-- Every element of `G / G²` is the class of some element of `G`. -/
theorem elementaryTwoQuotientMk_surjective :
    Function.Surjective (elementaryTwoQuotientMk : G → ElementaryTwoQuotient G) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Additive.toMul a, rfl⟩

/-- Two elements have the same class in `G / G²` iff they differ by a square. -/
theorem elementaryTwoQuotientMk_eq_iff (g h : G) :
    elementaryTwoQuotientMk g = elementaryTwoQuotientMk h ↔ IsSquare (g / h) := by
  have hdiv : elementaryTwoQuotientMk (g / h)
      = elementaryTwoQuotientMk g - elementaryTwoQuotientMk h := by
    simp only [elementaryTwoQuotientMk, ofMul_div, map_sub]
  rw [← elementaryTwoQuotientMk_eq_zero_iff, hdiv, sub_eq_zero]

variable (G)

/-- The doubling subgroup of `Additive G` is the additive form of the subgroup of squares of `G`. -/
theorem range_lsmul_two_toAddSubgroup_eq_square_toAddSubgroup :
    (LinearMap.range (LinearMap.lsmul ℤ (Additive G) ↑(2 : ℕ))).toAddSubgroup =
      (Subgroup.square G).toAddSubgroup := by
  ext g
  rw [Submodule.mem_toAddSubgroup, Additive.mem_toAddSubgroup, LinearMap.mem_range,
    Subgroup.mem_square]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Additive.toMul a, by simp [toMul_zsmul, zpow_two]⟩
  · rintro ⟨a, ha⟩
    refine ⟨Additive.ofMul a, ?_⟩
    apply Additive.toMul.injective
    simpa [toMul_zsmul, zpow_two, pow_two] using ha.symm

/-- The cardinality of `G/G²` is the index of the subgroup of squares. -/
theorem card_elementaryTwoQuotient_eq_index_square [Finite G] :
    Nat.card (ElementaryTwoQuotient G) = (Subgroup.square G).index := by
  rw [show Nat.card (ElementaryTwoQuotient G)
        = (LinearMap.range (LinearMap.lsmul ℤ (Additive G) ↑(2 : ℕ))).toAddSubgroup.index from
        (AddSubgroup.index_eq_card
          (LinearMap.range (LinearMap.lsmul ℤ (Additive G) ↑(2 : ℕ))).toAddSubgroup).symm,
    range_lsmul_two_toAddSubgroup_eq_square_toAddSubgroup, Subgroup.index_toAddSubgroup]

/-- **The maximal elementary-2 quotient and the 2-torsion subgroup have the same cardinality.**
`|G/G²| = |{g | g² = 1}|`. The squaring endomorphism `g ↦ g²` has range `G²` and kernel the
2-torsion; in a finite group the index of the range equals the cardinality of the kernel. -/
theorem card_elementaryTwoQuotient_eq_card_sq_eq_one [Finite G] :
    Nat.card (ElementaryTwoQuotient G) = Nat.card {g : G // g ^ 2 = 1} := by
  rw [card_elementaryTwoQuotient_eq_index_square, square_eq_powMonoidHom_two_range,
    Subgroup.index_range]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])

/-- **The 2-rank of a commutative group with finite-dimensional elementary-2 quotient**: the
`ZMod 2`-dimension of the maximal elementary-2 quotient `G / G²`. -/
noncomputable def twoRank [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)] : ℕ :=
  Module.finrank (ZMod 2) (ElementaryTwoQuotient G)

/-- The maximal elementary-2 quotient has cardinality `2 ^ twoRank`: it is a finite `𝔽₂`-vector
space of dimension the 2-rank. -/
theorem card_elementaryTwoQuotient_eq_two_pow_twoRank [Finite G] :
    Nat.card (ElementaryTwoQuotient G) = 2 ^ twoRank G := by
  rw [twoRank, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end TauCeti
