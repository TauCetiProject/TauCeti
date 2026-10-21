/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Perfect
import TauCeti.RingTheory.Polynomial.GaussLemma
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Squarefree bases of finite families of polynomials

Let `D` be a GCD domain and `F` a finite family of polynomials in one distinguished variable
over `D`. A *squarefree basis* of `F`, in McCallum's sense, is a finite set `B` of primitive,
squarefree polynomials of positive degree which are pairwise relatively prime, such that every
member of `F` is a constant times a product of powers of members of `B`. The constant is the
content of the member up to a unit, since products of primitive polynomials are primitive.

Every irreducible basis (`Finset.IsIrreducibleBasis`) is a squarefree basis, but the members
of a squarefree basis need not be irreducible: over `ℤ`, `{X ^ 2 - 1}` is a squarefree basis
of itself, and the nonconstant factors `sᵢ` of a factorization `f = c * ∏ i, sᵢ ^ i` of a
single polynomial `f` into primitive, squarefree, pairwise relatively prime `sᵢ` form a
squarefree basis of `{f}`. McCallum's family lifting theorem only uses
the properties recorded here.

Over the fraction field the product of a squarefree basis stays squarefree, by Gauss's lemma;
in characteristic zero the discriminant of the product of any subfamily is therefore nonzero.

## Main definitions and results

* `Finset.IsSquarefreeBasis F B`: `B` is a squarefree basis of the finite family `F`.
* `Finset.IsSquarefreeBasis.exists_eq_C_content_mul_unit_mul_prod`: every member of the family
  is its content times a unit times a product of powers of the basis.
* `Finset.IsSquarefreeBasis.squarefree_prod`, `Finset.IsSquarefreeBasis.squarefree_prod_map`:
  the product of the basis is squarefree, also over the fraction field.
* `Finset.IsSquarefreeBasis.discr_prod_ne_zero`: in characteristic zero, the product of any
  subfamily of the basis has nonzero discriminant.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*, in
  *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998), 242–268.
-/

public section

open Polynomial

namespace Finset

section Defs

variable {D : Type*} [CommRing D]

/-- `B` is a squarefree basis of the finite family `F` of polynomials over `D`: its members
are primitive, squarefree, of positive degree and pairwise relatively prime, and every member
of `F` is a constant times a product of powers of members of `B`. -/
structure IsSquarefreeBasis (F B : Finset D[X]) : Prop where
  /-- Every member of the basis is primitive. -/
  isPrimitive : ∀ b ∈ B, b.IsPrimitive
  /-- Every member of the basis has positive degree. -/
  natDegree_pos : ∀ b ∈ B, 0 < b.natDegree
  /-- Every member of the basis is squarefree. -/
  squarefree : ∀ b ∈ B, Squarefree b
  /-- Distinct members of the basis are relatively prime. -/
  isRelPrime : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → IsRelPrime b b'
  /-- Every member of the family is a constant times a product of powers of the basis. -/
  exists_eq_C_mul_prod : ∀ f ∈ F, ∃ (c : D) (e : D[X] → ℕ), f = C c * ∏ b ∈ B, b ^ e b

end Defs

namespace IsSquarefreeBasis

variable {D : Type*} [CommRing D] {F B : Finset D[X]}

/-- Every product of powers of the members of a squarefree basis is primitive, so the
constant in `exists_eq_C_mul_prod` is the content of the member up to a unit. -/
theorem isPrimitive_prod [IsGCDMonoid D] (hB : F.IsSquarefreeBasis B) (e : D[X] → ℕ) :
    (∏ b ∈ B, b ^ e b).IsPrimitive := by
  let := Classical.arbitrary (NormalizedGCDMonoid D)
  refine Finset.prod_induction _ IsPrimitive (fun _ _ ↦ IsPrimitive.mul) isPrimitive_one
    fun b hb ↦ ?_
  induction e b with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul (hB.isPrimitive b hb)

/-- Every member of the family is its content, times a unit, times a product of powers of the
members of a squarefree basis. -/
theorem exists_eq_C_content_mul_unit_mul_prod [NormalizedGCDMonoid D]
    (hB : F.IsSquarefreeBasis B) {f : D[X]} (hf : f ∈ F) :
    ∃ (u : Dˣ) (e : D[X] → ℕ), f = C (f.content * u) * ∏ b ∈ B, b ^ e b := by
  obtain ⟨c, e, rfl⟩ := hB.exists_eq_C_mul_prod f hf
  have hc := associated_content_C_mul c (∏ b ∈ B, b ^ e b)
  rw [(hB.isPrimitive_prod e).content_eq_one, mul_one] at hc
  obtain ⟨u, hu⟩ := hc.symm
  exact ⟨u⁻¹, e, by rw [← hu, Units.mul_inv_cancel_right]⟩

variable [IsDomain D] [IsGCDMonoid D]

/-- The product of the members of a squarefree basis is squarefree. -/
theorem squarefree_prod (hB : F.IsSquarefreeBasis B) : Squarefree (∏ b ∈ B, b) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun b hb b' hb' hne ↦ hB.isRelPrime b hb b' hb' hne) hB.squarefree

/-- The product of the members of a squarefree basis is squarefree over the fraction field. -/
theorem squarefree_prod_map (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (hB : F.IsSquarefreeBasis B) : Squarefree (∏ b ∈ B, b.map (algebraMap D K)) := by
  rw [← Polynomial.map_prod]
  exact hB.squarefree_prod.map_fraction_map

/-- In characteristic zero, the product of any subfamily of a squarefree basis has
nonzero discriminant. This includes the empty subfamily, whose product is `1`. -/
theorem discr_prod_ne_zero [CharZero D] (hB : F.IsSquarefreeBasis B)
    {A : Finset D[X]} (hA : A ⊆ B) : (∏ b ∈ A, b).discr ≠ 0 := by
  let K := FractionRing D
  have hinj := IsFractionRing.injective D K
  have : CharZero K := charZero_of_injective_algebraMap hinj
  have hsep : (∏ b ∈ A, b.map (algebraMap D K)).Separable :=
    PerfectField.separable_iff_squarefree.2 <|
      (hB.squarefree_prod_map K).squarefree_of_dvd
        (Finset.prod_dvd_prod_of_subset A B _ hA)
  have h := (Polynomial.discr_ne_zero_iff hsep.ne_zero).2 hsep
  rw [← Polynomial.map_prod, Polynomial.discr_map_of_natDegree_eq _
    (Polynomial.natDegree_map_eq_of_injective hinj _), map_ne_zero_iff _ hinj] at h
  exact h

end IsSquarefreeBasis

end Finset
