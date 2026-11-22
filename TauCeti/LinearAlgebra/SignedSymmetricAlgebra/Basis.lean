/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Decomposition
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Signed monomial bases

Bases of the even and odd summands of an internally integer-graded module give a basis of its
signed symmetric algebra when `2` is invertible. Its indices are pairs `(d, s)`: a finitely
supported natural exponent vector for the even generators and a finite subset of the odd
indices. Odd factors are ordered using the chosen linear order on their indices.

`TauCeti.SignedSym.monomialBasis` transports Mathlib's symmetric and exterior monomial bases
through `TauCeti.SignedSym.symTensorExteriorEquiv`. Thus its `repr` gives unique finite signed
monomial expansions, with reconstruction by `Module.Basis.linearCombination_repr`. Neither
generator index type needs to be finite. Multiplication adds even exponents; intersecting odd
supports give zero, and disjoint odd supports give the sign of the sorting permutation.
The basis is homogeneous for word length and parity, without requiring that the chosen parity
bases be homogeneous for integer degree.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the free
  supercommutative algebra.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.SignedSym

variable {R V I J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Invertible (2 : R)] [LinearOrder J]
  (G : InternalGrading R V ℤ)
  (b₀ : Basis I R (parityGrading G.piece 0))
  (b₁ : Basis J R (parityGrading G.piece 1))

/-- The signed monomial basis, indexed by even exponent vectors and finite odd supports.
The odd support is multiplied in increasing order. -/
noncomputable def monomialBasis : Basis ((I →₀ ℕ) × Finset J) R (SignedSym G) :=
  (b₀.symmetricAlgebra.tensorProduct b₁.ExteriorAlgebra).map
    (symTensorExteriorEquiv G).symm.toLinearEquiv

/-- Signed monomial coordinates are the tensor-product coordinates under the comparison. -/
theorem monomialBasis_repr (a : SignedSym G) :
    (monomialBasis G b₀ b₁).repr a =
      (b₀.symmetricAlgebra.tensorProduct b₁.ExteriorAlgebra).repr (toSymTensorExterior G a) := by
  rw [← symTensorExteriorEquiv_apply]
  simp [monomialBasis]

/-- The coefficient of a signed monomial in a factored product is the product of the
corresponding even and odd coefficients. -/
@[simp]
theorem monomialBasis_repr_fromSymmetricEven_mul_fromExteriorOdd
    (x : SymmetricAlgebra R (parityGrading G.piece 0))
    (y : ExteriorAlgebra R (parityGrading G.piece 1)) (p : (I →₀ ℕ) × Finset J) :
    (monomialBasis G b₀ b₁).repr (fromSymmetricEven G x * fromExteriorOdd G y) p =
      b₀.symmetricAlgebra.repr x p.1 * b₁.ExteriorAlgebra.repr y p.2 := by
  rcases p with ⟨d, s⟩
  rw [monomialBasis_repr, map_mul, toSymTensorExterior_fromSymmetricEven,
    toSymTensorExterior_fromExteriorOdd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- A signed monomial is an even symmetric monomial followed by an ordered odd exterior
monomial. -/
theorem monomialBasis_apply (d : I →₀ ℕ) (s : Finset J) :
    monomialBasis G b₀ b₁ (d, s) =
      fromSymmetricEven G (b₀.symmetricAlgebra d) *
        fromExteriorOdd G (b₁.ExteriorAlgebra s) := by
  simp [monomialBasis, Basis.tensorProduct_apply, fromSymTensorExterior_tmul]

/-- In a signed monomial, the odd generators occur exactly once each, in increasing order. -/
theorem monomialBasis_eq_mul_prod (d : I →₀ ℕ) (s : Finset J) :
    monomialBasis G b₀ b₁ (d, s) = fromSymmetricEven G (b₀.symmetricAlgebra d) *
      ((s.sort (· ≤ ·)).map fun j => generator G (b₁ j : V)).prod := by
  rw [monomialBasis_apply, b₁.exteriorAlgebra_eq_prod_map_sort, map_list_prod, List.map_map]
  simp only [Function.comp_def, fromExteriorOdd_ι, List.map_map]

/-- With empty odd support, a signed monomial is the image of the corresponding
symmetric monomial. -/
theorem monomialBasis_empty (d : I →₀ ℕ) :
    monomialBasis G b₀ b₁ (d, ∅) = fromSymmetricEven G (b₀.symmetricAlgebra d) := by
  simp [monomialBasis_eq_mul_prod]

/-- With zero even exponents, a signed monomial is the image of the corresponding
exterior monomial. -/
theorem monomialBasis_zero (s : Finset J) :
    monomialBasis G b₀ b₁ (0, s) = fromExteriorOdd G (b₁.ExteriorAlgebra s) := by
  simp [monomialBasis_apply, b₀.symmetricAlgebra_zero]

/-- The empty signed monomial is the unit. -/
@[simp]
theorem monomialBasis_zero_empty : monomialBasis G b₀ b₁ (0, ∅) = 1 := by
  simp [monomialBasis_empty, b₀.symmetricAlgebra_zero]

/-- A single even exponent represents a power of the corresponding even generator. -/
@[simp]
theorem monomialBasis_single_empty (i : I) (n : ℕ) :
    monomialBasis G b₀ b₁ (Finsupp.single i n, ∅) = generator G (b₀ i : V) ^ n := by
  simp [monomialBasis_empty, b₀.symmetricAlgebra_single]

/-- A singleton odd support represents the corresponding odd generator. -/
@[simp]
theorem monomialBasis_zero_singleton (j : J) :
    monomialBasis G b₀ b₁ (0, {j}) = generator G (b₁ j : V) := by
  simp [monomialBasis_zero, b₁.exteriorAlgebra_eq_prod_map_sort]

/-- The unit has only the empty monomial coordinate, with coefficient one. -/
@[simp]
theorem monomialBasis_repr_one :
    (monomialBasis G b₀ b₁).repr 1 = Finsupp.single (0, ∅) 1 := by
  rw [← monomialBasis_zero_empty G b₀ b₁, Basis.repr_self]

/-- A power of an even basis generator has just its single-index monomial coordinate. -/
@[simp]
theorem monomialBasis_repr_generator_even_pow (i : I) (n : ℕ) :
    (monomialBasis G b₀ b₁).repr (generator G (b₀ i : V) ^ n) =
      Finsupp.single (Finsupp.single i n, ∅) 1 := by
  rw [← monomialBasis_single_empty G b₀ b₁, Basis.repr_self]

/-- An even basis generator has coefficient one at its single-index monomial. -/
@[simp]
theorem monomialBasis_repr_generator_even (i : I) :
    (monomialBasis G b₀ b₁).repr (generator G (b₀ i : V)) =
      Finsupp.single (Finsupp.single i 1, ∅) 1 := by
  simpa only [pow_one] using monomialBasis_repr_generator_even_pow G b₀ b₁ i 1

/-- An odd basis generator has coefficient one at its singleton-support monomial. -/
@[simp]
theorem monomialBasis_repr_generator_odd (j : J) :
    (monomialBasis G b₀ b₁).repr (generator G (b₁ j : V)) = Finsupp.single (0, {j}) 1 := by
  rw [← monomialBasis_zero_singleton G b₀ b₁, Basis.repr_self]

/-- The polynomial-exterior comparison sends the signed monomial basis to the tensor
product of the two native monomial bases. -/
@[simp]
theorem toSymTensorExterior_monomialBasis (p : (I →₀ ℕ) × Finset J) :
    toSymTensorExterior G (monomialBasis G b₀ b₁ p) =
      b₀.symmetricAlgebra p.1 ⊗ₜ[R] b₁.ExteriorAlgebra p.2 := by
  rw [← symTensorExteriorEquiv_apply]
  simp [monomialBasis, Basis.tensorProduct_apply']

/-- A signed monomial has word length equal to the sum of its even exponents and the size
of its odd support. -/
theorem monomialBasis_mem_lengthPiece (d : I →₀ ℕ) (s : Finset J) :
    monomialBasis G b₀ b₁ (d, s) ∈ lengthPiece G (d.degree + s.card) := by
  rw [monomialBasis_apply]
  apply SetLike.mul_mem_graded
  · exact fromSymmetricEven_mem_lengthPiece G (b₀.symmetricAlgebra_mem_homogeneousSubmodule d)
  · exact fromExteriorOdd_mem_lengthPiece G (b₁.exteriorAlgebra_mem_exteriorPower s)

/-- A signed monomial has the parity of the size of its odd support. -/
theorem monomialBasis_mem_parityGrading (d : I →₀ ℕ) (s : Finset J) :
    monomialBasis G b₀ b₁ (d, s) ∈
      parityGrading (signedSymPiece G) (s.card : ZMod 2) := by
  rw [monomialBasis_apply]
  have hodd : fromExteriorOdd G (b₁.ExteriorAlgebra s) ∈
      parityGrading (signedSymPiece G) (s.card : ZMod 2) := by
    apply fromExteriorOdd_mem_parityGrading G
    rw [← Int.cast_natCast (R := ZMod 2)]
    apply mem_parityGrading_of_mem (n := (s.card : ℤ))
    rw [TauCeti.ExteriorAlgebra.integerGrading_natCast]
    exact b₁.exteriorAlgebra_mem_exteriorPower s
  simpa only [zero_add] using SetLike.mul_mem_graded
    (fromSymmetricEven_mem_parityGrading_zero G (b₀.symmetricAlgebra d)) hodd

/-- Augmentation selects the empty signed monomial. -/
@[simp]
theorem augmentation_monomialBasis (p : (I →₀ ℕ) × Finset J) [Decidable (p = (0, ∅))] :
    augmentation G (monomialBasis G b₀ b₁ p) = if p = (0, ∅) then 1 else 0 := by
  by_cases h : p = (0, ∅)
  · subst p
    simp
  · rcases p with ⟨d, s⟩
    rw [ite_eq_right h]
    apply augmentation_eq_zero_of_mem_lengthPiece G (n := d.degree + s.card) ?_
      (monomialBasis_mem_lengthPiece G b₀ b₁ d s)
    simpa only [ne_eq, Prod.mk.injEq, Nat.add_eq_zero_iff, Finsupp.degree_eq_zero_iff,
      Finset.card_eq_zero] using h

/-- The coefficient of the empty signed monomial is the augmentation. -/
@[simp]
theorem monomialBasis_repr_zero_empty (a : SignedSym G) :
    (monomialBasis G b₀ b₁).repr a (0, ∅) = augmentation G a := by
  classical
  have heq : (Finsupp.lapply (0, ∅)).comp (monomialBasis G b₀ b₁).repr.toLinearMap =
      (augmentation G).toLinearMap := (monomialBasis G b₀ b₁).ext fun p ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      AlgHom.toLinearMap_apply, augmentation_monomialBasis, Basis.repr_self, Finsupp.single_apply]
  exact LinearMap.congr_fun heq a

/-- The product of two signed monomials is zero if an odd generator occurs in both. -/
theorem monomialBasis_mul_of_not_disjoint (d e : I →₀ ℕ) (s t : Finset J)
    (h : ¬Disjoint s t) :
    monomialBasis G b₀ b₁ (d, s) * monomialBasis G b₀ b₁ (e, t) = 0 := by
  apply (symTensorExteriorEquiv G).injective
  simp only [map_mul, symTensorExteriorEquiv_apply, toSymTensorExterior_monomialBasis, map_zero,
    Algebra.TensorProduct.tmul_mul_tmul]
  have hodd := ExteriorAlgebra.basis_mul_of_not_disjoint b₁
    (⟨s, rfl⟩ : Set.powersetCard J s.card) (⟨t, rfl⟩ : Set.powersetCard J t.card) h
  simp only [hodd, TensorProduct.tmul_zero]

/-- With disjoint odd supports, multiplication adds even exponents and combines the odd
supports with the sign of their sorting permutation. -/
theorem monomialBasis_mul_of_disjoint (d e : I →₀ ℕ) (s t : Finset J)
    (h : Disjoint s t) :
    monomialBasis G b₀ b₁ (d, s) * monomialBasis G b₀ b₁ (e, t) =
      (Set.powersetCard.permOfDisjoint
        (s := (⟨s, rfl⟩ : Set.powersetCard J s.card))
        (t := (⟨t, rfl⟩ : Set.powersetCard J t.card)) h).sign •
      monomialBasis G b₀ b₁ (d + e, s ∪ t) := by
  apply (symTensorExteriorEquiv G).injective
  simp only [map_mul, map_zsmul_unit, symTensorExteriorEquiv_apply,
    toSymTensorExterior_monomialBasis, Algebra.TensorProduct.tmul_mul_tmul]
  have hodd := ExteriorAlgebra.basis_mul_of_disjoint b₁
    (⟨s, rfl⟩ : Set.powersetCard J s.card) (⟨t, rfl⟩ : Set.powersetCard J t.card) h
  rw [hodd, ← b₀.symmetricAlgebra_add, Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, TensorProduct.tmul_smul]

end TauCeti.SignedSym
