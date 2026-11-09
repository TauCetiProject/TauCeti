/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra

/-!
# Strict units for `A∞` algebras

This file records strict units for the uncurved `A∞` algebras of
`TauCeti.Algebra.Homology.AInfinity.Algebra`.  A strict unit is a degree-zero cycle whose binary
operation is a two-sided unit and whose other operations vanish whenever one input is the unit.
The higher-operation condition is stated on arbitrary input families, so it can be used directly
with the unsuspended operations without exposing the bar coderivation.

The uniqueness theorem and the elimination lemmas are the basic interface used by the later
strictly unital morphism and augmentation constructions.  On the suspended Taylor map, a word
containing the unit is killed unless it has two letters, and the unit acts on two-letter words
by `[e, y] ↦ y` and `[y, e] ↦ (-1)^|y| y`, the sign being the degree-one Koszul twist.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- A **strict unit** for an uncurved `A∞` algebra in the Keller convention.

The unit has degree zero, is closed under `m₁`, and is a two-sided unit for `m₂`.  Every operation
of arity other than two vanishes as soon as one of its inputs is the unit.  In particular, the
condition includes arity zero, although that case is vacuous because the input family is empty;
curvature is already excluded by `AInfinityAlgebra.m_zero`. -/
structure StrictUnit (𝒜 : AInfinityAlgebra R A) (e : A) : Prop where
  /-- The unit is homogeneous of degree zero. -/
  degree_zero : e ∈ 𝒜.grading.piece 0
  /-- The unit is a left unit for `m₂`. -/
  binary_left : ∀ x, 𝒜.m 2 ![e, x] = x
  /-- The unit is a right unit for `m₂`. -/
  binary_right : ∀ x, 𝒜.m 2 ![x, e] = x
  /-- Higher operations vanish on every tuple containing the unit. -/
  higher : ∀ (n : ℕ), n ≠ 2 → ∀ x : Fin n → A,
    (∃ i, x i = e) → 𝒜.m n x = 0

attribute [simp] StrictUnit.binary_left StrictUnit.binary_right

namespace StrictUnit

variable {𝒜 : AInfinityAlgebra R A} {e e' : A}

/-! ### The characteristic unit equations -/

/-- A strict unit is closed under the unary `A∞` operation. -/
@[simp]
theorem unary_eq_zero (h : 𝒜.StrictUnit e) : 𝒜.m 1 ![e] = 0 := by
  simpa using h.higher 1 (by decide) ![e] ⟨0, rfl⟩

/-- A strict unit is a cycle for the differential. -/
theorem differential_eq_zero (h : 𝒜.StrictUnit e) : 𝒜.differential e = 0 := by
  rw [differential_apply]
  exact h.unary_eq_zero

/-- The higher operations vanish when a specified input is the strict unit. -/
theorem m_eq_zero_of_eq_unit (h : 𝒜.StrictUnit e) {n : ℕ} (hn : n ≠ 2)
    (x : Fin n → A) {i : Fin n} (hi : x i = e) : 𝒜.m n x = 0 := by
  exact h.higher n hn x ⟨i, hi⟩

/-- A strict unit has degree `-1` in the suspended grading. -/
theorem mem_shift_one_piece (h : 𝒜.StrictUnit e) : e ∈ (𝒜.grading.shift 1).piece (-1) := by
  rw [InternalGrading.shift_piece, neg_add_cancel]
  exact h.degree_zero

/-! ### The suspended Taylor map on words containing the unit -/

/-- The suspended Taylor map vanishes on a word of length other than two containing the strict
unit. -/
theorem taylor_of_tprod_eq_zero (h : 𝒜.StrictUnit e) (n : {n : ℕ // 0 < n}) (hn : n.1 ≠ 2)
    (x : Fin n.1 → A) (hx : ∃ i, x i = e) :
    𝒜.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
  obtain ⟨i, hi⟩ := hx
  rw [taylor_of_tprod]
  exact h.higher n.1 hn _ ⟨i, by rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero h.degree_zero]⟩

/-- On the two-letter word `[e, y]` the suspended Taylor map returns `y`. -/
@[simp]
theorem taylor_of_two_unit_left (h : 𝒜.StrictUnit e) (y : A) :
    𝒜.taylor (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![e, y])) = y := by
  rw [taylor_of_two, 𝒜.grading.koszulTwist_apply_of_mem_zero h.degree_zero, h.binary_left]

/-- On the two-letter word `[y, e]` the suspended Taylor map returns the degree-one Koszul twist
of `y`, that is `(-1)^|y| y` for `y` of degree `|y|`. -/
@[simp]
theorem taylor_of_two_unit_right (h : 𝒜.StrictUnit e) (y : A) :
    𝒜.taylor (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![y, e])) =
      𝒜.grading.koszulTwist 1 y := by
  rw [taylor_of_two, h.binary_right]

/-! ### Uniqueness -/

/-- A strict unit of an `A∞` algebra is unique. -/
theorem eq (h : 𝒜.StrictUnit e) (h' : 𝒜.StrictUnit e') : e = e' := by
  calc
    e = 𝒜.m 2 ![e', e] := (h'.binary_left e).symm
    _ = e' := h.binary_right e'

end StrictUnit

end AInfinityAlgebra

end TauCeti
