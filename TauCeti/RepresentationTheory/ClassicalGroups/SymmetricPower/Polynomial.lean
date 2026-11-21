/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Basic
public import TauCeti.RingTheory.MvPolynomial.BinaryMonomial

/-!
# Symmetric powers of the standard representation as homogeneous polynomials

Multiplying out a pure symmetric tensor identifies the symmetric power `Symᵈ(Rⁿ)` with the forms
of degree `d` in `n` variables (`SymmetricPower.equivHomogeneous` followed by
`TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial`). This file proves that this
dictionary intertwines the symmetric power `TauCeti.symPowerRep` of the standard representation
with the substitution of standard vectors `TauCeti.polynomialRep`
(`TauCeti.symPowerRepEquivPolynomialRep`). In two variables it sends the pure symmetric tensor
with `d - i` copies of the first standard vector and `i` copies of the second to the binary
monomial `TauCeti.polynomialMonomial k d i`.

## Main definitions

* `TauCeti.symPowerRepEquivPolynomialRep`: the symmetric power of the standard representation
  of `GL n k` is equivalent to the forms of degree `d` in `n` variables.

## Main results

* `TauCeti.coe_symPowerRepEquivPolynomialRep_tprod`: the dictionary multiplies out a pure
  symmetric tensor.
* `TauCeti.coe_symPowerRepEquivPolynomialRep_symPowerRep`: the dictionary intertwines the
  symmetric power of the standard representation with substitution.
* `TauCeti.coe_symPowerRepEquivPolynomialRep_tprod_ite`: the dictionary sends the pure tensor
  with `d - i` copies of the first and `i` copies of the second standard vector of `k²` to the
  binary monomial.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, p. 63: the
  representations of `SL₂` on homogeneous polynomials in two variables.
-/

public section

open MvPolynomial Matrix
open scoped TensorProduct

namespace TauCeti

section SymmetricPower

variable (k : Type) [CommRing k] (n d : ℕ)

/-- The dictionary between symmetric tensors and forms multiplies out a pure tensor. -/
private theorem coe_symmetricPowerHomogeneous_tprod (m : Fin d → Fin n → k) :
    ((SymmetricPower.equivHomogeneous d).trans
        (SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial k (Fin n → k)
          (Pi.basisFun k (Fin n)) d) (⨂ₛ[k] i, m i) : MvPolynomial (Fin n) k) =
      ∏ i, ∑ j, C (m i j) * X j := by
  simp only [LinearEquiv.trans_apply,
    SymmetricAlgebra.coe_homogeneousSubmoduleEquivMvPolynomial_apply,
    SymmetricPower.coe_equivHomogeneous_apply, SymmetricPower.toSymmetricAlgebra_tprod, map_prod,
    _root_.SymmetricAlgebra.equivMvPolynomial_ι, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, smul_eq_C_mul]

/-- **The symmetric power of the standard representation is the representation on forms**:
multiplying out symmetric tensors identifies `Symᵈ(kⁿ)` with the forms of degree `d` in `n`
variables, intertwining the symmetric power of the standard representation of `GL n k` with the
substitution of standard vectors. -/
noncomputable def symPowerRepEquivPolynomialRep :
    (symPowerRep k n d).Equiv (polynomialRep (Fin n) k d) :=
  .mk ((SymmetricPower.equivHomogeneous d).trans
      (SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial k (Fin n → k)
        (Pi.basisFun k (Fin n)) d)) fun g ↦ by
    refine SymmetricPower.ext fun m ↦ Subtype.ext ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Representation.symmetricPower_apply_tprod, stdRep_apply_apply, coe_polynomialRep_apply,
      coe_symmetricPowerHomogeneous_tprod, map_prod, polynomialAction_sum_C_mul_X]

/-- The underlying linear equivalence of `TauCeti.symPowerRepEquivPolynomialRep` is the dictionary
`SymmetricPower.equivHomogeneous` followed by
`TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial`. -/
@[simp]
theorem symPowerRepEquivPolynomialRep_toLinearEquiv :
    (symPowerRepEquivPolynomialRep k n d).toLinearEquiv =
      (SymmetricPower.equivHomogeneous d).trans
        (SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial k (Fin n → k)
          (Pi.basisFun k (Fin n)) d) :=
  (rfl)

/-- The equivalence `TauCeti.symPowerRepEquivPolynomialRep` multiplies out a pure symmetric
tensor of vectors `mᵢ`, as a product of the linear forms with coefficient vectors `mᵢ`. -/
@[simp]
theorem coe_symPowerRepEquivPolynomialRep_tprod (m : Fin d → Fin n → k) :
    (symPowerRepEquivPolynomialRep k n d (⨂ₛ[k] i, m i) : MvPolynomial (Fin n) k) =
      ∏ i, ∑ j, C (m i j) * X j :=
  coe_symmetricPowerHomogeneous_tprod k n d m

/-- The equivalence `TauCeti.symPowerRepEquivPolynomialRep` sends a pure symmetric tensor of
standard basis vectors to the product of the corresponding variables. -/
theorem coe_symPowerRepEquivPolynomialRep_tprod_single (f : Fin d → Fin n) :
    (symPowerRepEquivPolynomialRep k n d (⨂ₛ[k] i, Pi.single (f i) 1) :
        MvPolynomial (Fin n) k) =
      ∏ i, X (f i) := by
  rw [coe_symPowerRepEquivPolynomialRep_tprod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single (f i) (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

variable {n} in
/-- In degree `0` the inverse of `TauCeti.symPowerRepEquivPolynomialRep` sends the constant
polynomial `1` to the unit tensor. -/
theorem symPowerRepEquivPolynomialRep_symm_one :
    (symPowerRepEquivPolynomialRep k n 0).symm ⟨1, isHomogeneous_one (Fin n) k⟩ =
      ⨂ₛ[k] i : Fin 0, Fin.elim0 i := by
  apply EquivLike.injective (symPowerRepEquivPolynomialRep k n 0)
  rw [Representation.Equiv.apply_symm_apply]
  ext : 1
  simp [coe_symPowerRepEquivPolynomialRep_tprod]

/-- The equivalence `TauCeti.symPowerRepEquivPolynomialRep` intertwines the symmetric power of the
standard representation with the substitution of standard vectors. -/
theorem coe_symPowerRepEquivPolynomialRep_symPowerRep (g : GL (Fin n) k)
    (x : Sym[k]^d(Fin n → k)) :
    (symPowerRepEquivPolynomialRep k n d (symPowerRep k n d g x) : MvPolynomial (Fin n) k) =
      polynomialAction (g : Matrix (Fin n) (Fin n) k) (symPowerRepEquivPolynomialRep k n d x) := by
  rw [← coe_polynomialRep_apply]
  exact congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _
    (symPowerRepEquivPolynomialRep k n d).toIntertwiningMap g x)

end SymmetricPower

section Dictionary

variable {k : Type} [CommRing k] {d i : ℕ}

/-- **The dictionary on binary monomials**: the equivalence `TauCeti.symPowerRepEquivPolynomialRep`
sends the pure symmetric tensor with `d - i` copies of the first standard vector of `k²` followed
by `i` copies of the second to the binary monomial `e_i^d = x ^ (d - i) * y ^ i`. -/
theorem coe_symPowerRepEquivPolynomialRep_tprod_ite (h : i ≤ d) :
    (symPowerRepEquivPolynomialRep k 2 d
        (⨂ₛ[k] l : Fin d, Pi.single (if (l : ℕ) < d - i then 0 else 1) 1) :
        MvPolynomial (Fin 2) k) =
      polynomialMonomial k d i := by
  rw [coe_symPowerRepEquivPolynomialRep_tprod_single, polynomialMonomial_of_le h]
  simp only [apply_ite X, Finset.prod_ite, Finset.prod_const]
  congr 2
  · rw [Fin.card_filter_val_lt, min_eq_right (Nat.sub_le d i)]
  · have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin d))) (fun l : Fin d ↦ (l : ℕ) < d - i)
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.sub_le d i), Finset.card_univ,
      Fintype.card_fin] at hcard
    omega

/-- The inverse of `TauCeti.symPowerRepEquivPolynomialRep` sends the binary monomial
`e_i^d = x ^ (d - i) * y ^ i` to the pure symmetric tensor with `d - i` copies of the first
standard vector of `k²` followed by `i` copies of the second. -/
theorem symPowerRepEquivPolynomialRep_symm_polynomialMonomial (h : i ≤ d) :
    (symPowerRepEquivPolynomialRep k 2 d).symm
        ⟨polynomialMonomial k d i, polynomialMonomial_mem_homogeneousSubmodule k d i⟩ =
      ⨂ₛ[k] l : Fin d, (Pi.single (if (l : ℕ) < d - i then 0 else 1) 1 : Fin 2 → k) := by
  apply EquivLike.injective (symPowerRepEquivPolynomialRep k 2 d)
  rw [Representation.Equiv.apply_symm_apply]
  exact Subtype.ext (coe_symPowerRepEquivPolynomialRep_tprod_ite h).symm

end Dictionary

end TauCeti
