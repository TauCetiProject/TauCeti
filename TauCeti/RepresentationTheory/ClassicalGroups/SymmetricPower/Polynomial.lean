/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Symmetric powers of the standard representation as homogeneous polynomials

A square matrix `g` acts on polynomials in the standard basis vectors `X i` of `Rˢ` by the same
rule as on vectors: `X j ↦ ∑ᵢ gᵢⱼ X i`, the image of the `j`-th standard vector. In two variables,
with `x = X 0` and `y = X 1`, the matrix `!![a, b; c, d]` substitutes `x ↦ a x + c y` and
`y ↦ b x + d y`. This is `TauCeti.polynomialAction g`. Unlike the pullback of polynomial
functions `MvPolynomial.linearSubst`, of which it is the transpose, it is a left action:
`polynomialAction (g * h) = polynomialAction g ∘ polynomialAction h`. Restricted to the forms of
degree `d` it is the representation `TauCeti.polynomialRep` of the general linear group.

Multiplying out a pure symmetric tensor identifies the symmetric power `Symᵈ(Rⁿ)` with the forms
of degree `d` in `n` variables (`TauCeti.SymmetricPower.equivHomogeneous` followed by
`TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial`). This file proves that this
dictionary intertwines the symmetric power `TauCeti.symPowerRep` of the standard representation
with `TauCeti.polynomialRep` (`TauCeti.symPowerRepEquivPolynomialRep`).

## Main definitions

* `TauCeti.polynomialAction`: the substitution of standard vectors by a square matrix.
* `TauCeti.polynomialRep`: its restriction to forms of degree `d`, as a representation of
  `GL σ R`.
* `TauCeti.symPowerRepEquivPolynomialRep`: the symmetric power of the standard representation
  of `GL n k` is equivalent to the forms of degree `d` in `n` variables.

## Main results

* `TauCeti.polynomialAction_mul`: the substitution is a left action.
* `TauCeti.polynomialAction_sum_C_mul_X`: on linear forms it is matrix-vector multiplication of
  the coefficient vector.
* `TauCeti.coe_symPowerRepEquivPolynomialRep_tprod`: the dictionary multiplies out a pure
  symmetric tensor.
* `TauCeti.coe_symPowerRepEquivPolynomialRep_symPowerRep`: the dictionary intertwines the
  symmetric power of the standard representation with substitution.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, p. 63: the
  representations of `SL₂` on homogeneous polynomials in two variables.
-/

public section

open MvPolynomial Matrix
open scoped TensorProduct

namespace TauCeti

section Action

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- The substitution of standard vectors by a square matrix `g`: the variable `X j`, the `j`-th
standard vector, goes to its image `∑ᵢ gᵢⱼ X i` under `g`. In two variables the matrix
`!![a, b; c, d]` substitutes `X 0 ↦ a X 0 + c X 1` and `X 1 ↦ b X 0 + d X 1`. -/
noncomputable def polynomialAction (g : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  linearSubst gᵀ

/-- The substitution of standard vectors is the change of variables along the transpose. -/
theorem polynomialAction_eq_linearSubst_transpose (g : Matrix σ σ R) :
    polynomialAction g = linearSubst gᵀ :=
  (rfl)

@[simp]
theorem polynomialAction_X (g : Matrix σ σ R) (j : σ) :
    polynomialAction g (X j) = ∑ i, C (g i j) * X i := by
  simp [polynomialAction_eq_linearSubst_transpose]

@[simp]
theorem polynomialAction_one [DecidableEq σ] :
    polynomialAction (1 : Matrix σ σ R) = AlgHom.id R _ := by
  simp [polynomialAction_eq_linearSubst_transpose]

/-- The substitution of standard vectors is a left action of the matrix monoid. -/
theorem polynomialAction_mul (g h : Matrix σ σ R) :
    polynomialAction (g * h) = (polynomialAction g).comp (polynomialAction h) := by
  rw [polynomialAction_eq_linearSubst_transpose, transpose_mul, linearSubst_mul]
  rfl

theorem polynomialAction_mul_apply (g h : Matrix σ σ R) (p : MvPolynomial σ R) :
    polynomialAction (g * h) p = polynomialAction g (polynomialAction h p) := by
  rw [polynomialAction_mul, AlgHom.comp_apply]

/-- On linear forms the substitution of standard vectors is matrix-vector multiplication of the
coefficient vector: the linear form with coefficients `v` goes to the one with coefficients
`g *ᵥ v`. -/
theorem polynomialAction_sum_C_mul_X (g : Matrix σ σ R) (v : σ → R) :
    polynomialAction g (∑ j, C (v j) * X j) = ∑ i, C ((g *ᵥ v) i) * X i := by
  simp only [map_sum, map_mul, polynomialAction_X, algHom_C, algebraMap_eq, Finset.mul_sum,
    mulVec, dotProduct, map_sum C, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- A diagonal matrix rescales each variable by its diagonal entry. -/
theorem polynomialAction_diagonal [DecidableEq σ] (t : σ → R) :
    polynomialAction (diagonal t) = rescale t := by
  rw [polynomialAction_eq_linearSubst_transpose, diagonal_transpose, linearSubst_diagonal]

/-- The substitution of standard vectors preserves homogeneity. -/
theorem _root_.MvPolynomial.IsHomogeneous.polynomialAction {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (g : Matrix σ σ R) :
    (TauCeti.polynomialAction g p).IsHomogeneous n :=
  hp.linearSubst gᵀ

variable (σ R) in
/-- The substitution of standard vectors restricted to the forms of degree `d`, as a
representation of the general linear group. -/
noncomputable def polynomialRep [DecidableEq σ] (d : ℕ) :
    Representation R (GL σ R) (homogeneousSubmodule σ R d) :=
  (linearSubstRep σ R d).comp ((transposeRingEquiv σ R).toMonoidHom.comp (Units.coeHom _))

@[simp]
theorem coe_polynomialRep_apply [DecidableEq σ] {d : ℕ} (g : GL σ R)
    (p : homogeneousSubmodule σ R d) :
    (polynomialRep σ R d g p : MvPolynomial σ R) = polynomialAction (g : Matrix σ σ R) p := by
  simp [polynomialRep, polynomialAction_eq_linearSubst_transpose]

end Action

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
`TauCeti.SymmetricPower.equivHomogeneous` followed by
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

end TauCeti
