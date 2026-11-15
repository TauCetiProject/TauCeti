/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Basic

/-!
# Strict units for A-infinity categories

A strict unit in an `A∞` category is a degree-zero endomorphism `e X` of every object.  It is a
two-sided identity for the binary composition, and every operation of arity other than two
vanishes when one of its inputs is one of the identities.

The higher-operation condition is stated on the total morphism module used to store
`TauCeti.AInfinityCategory`.  This form accepts arbitrary, not necessarily homogeneous, inputs
and gives elimination lemmas without equality transports between hom modules.  The binary unit
laws remain stated directly on individual hom modules.

## Main definitions

* `TauCeti.AInfinityCategory.StrictUnit`: a chosen family of strict identities.
* `TauCeti.AInfinityCategory.StrictlyUnital`: the existence of a strict identity family.

## Main results

* `TauCeti.AInfinityCategory.StrictUnit.homDifferential_eq_zero`: strict identities are closed.
* `TauCeti.AInfinityCategory.StrictUnit.eq`: a strict identity family is unique.

The definition and interface adapt `TauCeti.AInfinityAlgebra.StrictUnit` from
`TauCeti/Algebra/Homology/AInfinity/Algebra/Unit.lean` to the many-object setting.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- A family of **strict units** for an uncurved `A∞` category.

For every object `X`, the endomorphism `e X` has degree zero.  These endomorphisms are the
left and right identities for `m₂`, and every operation of arity other than two vanishes on a
tuple containing an included identity. -/
structure StrictUnit (𝒞 : AInfinityCategory R C)
    (e : ∀ X : C, homModule (R := R) X X) : Prop where
  /-- Every identity has degree zero. -/
  degree_zero (X : C) : e X ∈ (grading (R := R) X X).piece 0
  /-- The identity at the target is a left identity for binary composition. -/
  binary_left (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.comp X Y Y (e Y) f = f
  /-- The identity at the source is a right identity for binary composition. -/
  binary_right (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.comp X X Y f (e X) = f
  /-- Every nonbinary operation vanishes on a tuple containing an included identity. -/
  higher (n : ℕ) (hn : n ≠ 2) (x : Fin n → TotalHom R C) :
    (∃ i X, x i = homInclusion X X (e X)) → 𝒞.m n x = 0

attribute [simp] StrictUnit.binary_left StrictUnit.binary_right

/-- An `A∞` category is strictly unital when it admits a family of strict identities. -/
@[expose]
def StrictlyUnital (𝒞 : AInfinityCategory R C) : Prop :=
  ∃ e : ∀ X : C, homModule (R := R) X X, 𝒞.StrictUnit e

namespace StrictUnit

variable {𝒞 : AInfinityCategory R C}
  {e e' : ∀ X : C, homModule (R := R) X X}

/-! ### Characteristic equations -/

/-- A nonbinary operation vanishes when a specified input is an included strict identity. -/
theorem m_eq_zero_of_eq_unit (h : 𝒞.StrictUnit e) {n : ℕ} (hn : n ≠ 2)
    (x : Fin n → TotalHom R C) {i : Fin n} {X : C}
    (hi : x i = homInclusion X X (e X)) :
    𝒞.m n x = 0 :=
  h.higher n hn x ⟨i, X, hi⟩

/-- A nonbinary operation on a composable path vanishes when a specified input is a strict
identity.  The hypothesis compares the two morphisms after inclusion in the total morphism
module, avoiding an equality transport when the adjacent objects are propositionally equal. -/
theorem pathOperation_eq_zero_of_eq_unit (h : 𝒞.StrictUnit e) {n : ℕ} (hn : n ≠ 2)
    (X : Fin (n + 1) → C) (d : Fin n → ℤ)
    (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i))
    {i : Fin n} {U : C}
    (hi : homInclusion (X i.rev.castSucc) (X i.rev.succ) (x i).1 =
      homInclusion U U (e U)) :
    𝒞.pathOperation X d x = 0 := by
  apply Subtype.ext
  apply homInclusion_injective (X 0) (X (Fin.last n))
  rw [𝒞.homInclusion_pathOperation]
  simpa only [Submodule.coe_zero, map_zero] using h.m_eq_zero_of_eq_unit hn _ hi

/-- An included strict identity is closed under the unary operation. -/
@[simp]
theorem unary_eq_zero (h : 𝒞.StrictUnit e) (X : C) :
    𝒞.m 1 ![homInclusion X X (e X)] = 0 := by
  exact h.m_eq_zero_of_eq_unit (n := 1) (i := 0) (X := X) (by decide) _ (by simp)

/-- A strict identity is a cycle for the differential on its endomorphism module. -/
@[simp]
theorem homDifferential_eq_zero (h : 𝒞.StrictUnit e) (X : C) :
    𝒞.homDifferential X X (e X) = 0 := by
  apply homInclusion_injective X X
  rw [𝒞.homInclusion_homDifferential, AInfinityAlgebra.differential_apply, h.unary_eq_zero,
    map_zero]

/-! ### Uniqueness -/

/-- A family of strict identities in an `A∞` category is unique. -/
theorem eq (h : 𝒞.StrictUnit e) (h' : 𝒞.StrictUnit e') : e = e' := by
  funext X
  calc
    e X = 𝒞.comp X X X (e' X) (e X) := (h'.binary_left X X (e X)).symm
    _ = e' X := h.binary_right X X (e' X)

end StrictUnit

end AInfinityCategory

end TauCeti
