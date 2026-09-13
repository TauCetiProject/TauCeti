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
strictly unital morphism and augmentation constructions.

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
  /-- The unit is a cycle for `m₁`. -/
  unary_eq_zero : 𝒜.m 1 ![e] = 0
  /-- The unit is a left unit for `m₂`. -/
  binary_left : ∀ x, 𝒜.m 2 ![e, x] = x
  /-- The unit is a right unit for `m₂`. -/
  binary_right : ∀ x, 𝒜.m 2 ![x, e] = x
  /-- Higher operations vanish on every tuple containing the unit. -/
  higher : ∀ (n : ℕ), n ≠ 2 → ∀ x : Fin n → A,
    (∃ i, x i = e) → 𝒜.m n x = 0

namespace StrictUnit

variable {𝒜 : AInfinityAlgebra R A} {e e' : A}

/-! ### The characteristic unit equations -/

/-- A strict unit is closed under the unary `A∞` operation. -/
@[simp]
theorem m_one_unit (h : 𝒜.StrictUnit e) : 𝒜.m 1 ![e] = 0 :=
  h.unary_eq_zero

/-- A strict unit is a left unit for the binary `A∞` operation. -/
@[simp]
theorem m_two_unit_left (h : 𝒜.StrictUnit e) (x : A) : 𝒜.m 2 ![e, x] = x :=
  h.binary_left x

/-- A strict unit is a right unit for the binary `A∞` operation. -/
@[simp]
theorem m_two_unit_right (h : 𝒜.StrictUnit e) (x : A) : 𝒜.m 2 ![x, e] = x :=
  h.binary_right x

/-- The higher operations vanish when a specified input is the strict unit. -/
theorem m_eq_zero_of_mem_unit (h : 𝒜.StrictUnit e) {n : ℕ} (hn : n ≠ 2)
    (x : Fin n → A) {i : Fin n} (hi : x i = e) : 𝒜.m n x = 0 := by
  exact h.higher n hn x ⟨i, hi⟩

/-- The higher operations vanish on a tuple containing the strict unit. -/
@[simp]
theorem m_eq_zero_of_exists_eq_unit (h : 𝒜.StrictUnit e) {n : ℕ} (hn : n ≠ 2)
    (x : Fin n → A) (hx : ∃ i, x i = e) : 𝒜.m n x = 0 :=
  h.higher n hn x hx

/-! ### Uniqueness -/

/-- A strict unit of an `A∞` algebra is unique. -/
theorem eq (h : 𝒜.StrictUnit e) (h' : 𝒜.StrictUnit e') : e = e' := by
  calc
    e = 𝒜.m 2 ![e', e] := (h'.binary_left e).symm
    _ = e' := h.binary_right e'

end StrictUnit

end AInfinityAlgebra

end TauCeti
