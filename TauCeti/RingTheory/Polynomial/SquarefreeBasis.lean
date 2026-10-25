/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.RingTheory.Polynomial.GaussLemma
import TauCeti.RingTheory.Polynomial.Resultant.Basic
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

Over the fraction field the product of a squarefree basis stays squarefree and its members stay
pairwise coprime, by Gauss's lemma. Hence the resultants of distinct members are nonzero, and in
characteristic zero the discriminant of the product of any subfamily is nonzero.

## Main definitions and results

* `Finset.IsSquarefreeBasis F B`: `B` is a squarefree basis of the finite family `F`.
* `Finset.IsSquarefreeBasis.exists_eq_C_content_mul_unit_mul_prod`: every member of the family
  is its content times a unit times a product of powers of the basis.
* `Finset.IsSquarefreeBasis.squarefree_prod`, `Finset.IsSquarefreeBasis.squarefree_prod_map`:
  the product of the basis is squarefree, also over the fraction field.
* `Finset.IsSquarefreeBasis.isCoprime_map`, `Finset.IsSquarefreeBasis.resultant_ne_zero`:
  distinct members of the basis are coprime over the fraction field, so their resultant is
  nonzero.
* `Finset.IsSquarefreeBasis.discr_prod_ne_zero`, `Finset.IsSquarefreeBasis.discr_ne_zero`: in
  characteristic zero, the product of any subfamily of the basis, in particular each member, has
  nonzero discriminant.
* `Finset.IsSquarefreeBasis.isRoot_map_iff`: after a specialization `φ : D →+* A` into a
  domain under which a member `f` of the family does not vanish, the roots of the specialized
  `f` are exactly the roots of the specialized basis members dividing `f`.

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

variable {D : Type*} [CommRing D] {F B : Finset D[X]} {b b' : D[X]}

/-- Roots of a specialized member of the family are the roots of the specialized members of
the basis dividing it, provided the specialization of the member does not vanish. -/
theorem isRoot_map_iff (hB : F.IsSquarefreeBasis B) {f : D[X]} (hf : f ∈ F) {A : Type*}
    [CommRing A] [IsDomain A] (φ : D →+* A) (hφ : f.map φ ≠ 0) (t : A) :
    (f.map φ).IsRoot t ↔ ∃ b ∈ B, b ∣ f ∧ (b.map φ).IsRoot t := by
  refine ⟨fun ht ↦ ?_, fun ⟨b, _, hbf, hbt⟩ ↦ hbt.dvd (Polynomial.map_dvd φ hbf)⟩
  obtain ⟨c, e, rfl⟩ := hB.exists_eq_C_mul_prod f hf
  have hc : φ c ≠ 0 := by rintro hc; simp [Polynomial.map_mul, hc] at hφ
  simp only [Polynomial.map_mul, map_C, Polynomial.map_prod, Polynomial.map_pow, IsRoot,
    eval_mul, eval_C, eval_prod, eval_pow, mul_eq_zero, hc, false_or,
    Finset.prod_eq_zero_iff, pow_eq_zero_iff', ne_eq] at ht
  obtain ⟨b, hb, hbt, he⟩ := ht
  exact ⟨b, hb, ((dvd_pow_self b he).trans
    (dvd_prod_of_mem (fun b ↦ b ^ e b) hb)).mul_left _, hbt⟩

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
    {A : Finset D[X]} (hA : A ⊆ B) : (∏ b ∈ A, b).discr ≠ 0 :=
  (hB.squarefree_prod.squarefree_of_dvd (Finset.prod_dvd_prod_of_subset A B _ hA)).discr_ne_zero

/-- In characteristic zero, the discriminant of a member of a squarefree basis is nonzero. -/
theorem discr_ne_zero [CharZero D] (hB : F.IsSquarefreeBasis B) (hb : b ∈ B) : b.discr ≠ 0 :=
  (hB.squarefree b hb).discr_ne_zero

/-- Distinct members of a squarefree basis are coprime over the fraction field. -/
theorem isCoprime_map (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (hB : F.IsSquarefreeBasis B) (hb : b ∈ B) (hb' : b' ∈ B) (hne : b ≠ b') :
    IsCoprime (b.map (algebraMap D K)) (b'.map (algebraMap D K)) :=
  (hB.isRelPrime b hb b' hb' hne).map_fraction_map.isCoprime

/-- The resultant of two distinct members of a squarefree basis is nonzero. -/
theorem resultant_ne_zero (hB : F.IsSquarefreeBasis B) (hb : b ∈ B) (hb' : b' ∈ B)
    (hne : b ≠ b') : resultant b b' ≠ 0 := by
  have hinj := IsFractionRing.injective D (FractionRing D)
  have h := Polynomial.resultant_ne_zero _ _ (hB.isCoprime_map (FractionRing D) hb hb' hne)
  rwa [resultant_map_of_natDegree_eq _ (natDegree_map_eq_of_injective hinj _)
    (natDegree_map_eq_of_injective hinj _), map_ne_zero_iff _ hinj] at h

end IsSquarefreeBasis

end Finset
