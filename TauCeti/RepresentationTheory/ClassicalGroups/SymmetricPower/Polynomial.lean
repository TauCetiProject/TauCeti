/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
public import TauCeti.RepresentationTheory.SU2.SymmetricPower
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
with `TauCeti.polynomialRep` (`TauCeti.symPowerRepEquivPolynomialRep`), and hence also the
symmetric powers `TauCeti.SU2.symPower` of the standard representation of `SU(2)` with the
substitution action of `SU(2)`.

In two variables the monomials `x ^ (d - i) * y ^ i` for `0 ≤ i ≤ d` form a basis of the forms
of degree `d`; `TauCeti.polynomialMonomial R d i` denotes them, extended by zero for `i > d`.
A diagonal matrix `diag(t₀, t₁)` scales it by `t₀ ^ (d - i) * t₁ ^ i`, so it has weight
`(d - i, i)`, and the dictionary sends the pure symmetric tensor with `d - i` copies of the first
standard vector and `i` copies of the second to it. With the substitution action and the
dictionary, they give the polynomial model of the symmetric powers of `ℂ²` under `GL₂(ℂ)` and
`SU(2)`, in which explicit computations with these representations are coordinate calculations
with binary forms.

## Main definitions

* `TauCeti.polynomialAction`: the substitution of standard vectors by a square matrix.
* `TauCeti.polynomialRep`: its restriction to forms of degree `d`, as a representation of
  `GL σ R`.
* `TauCeti.symPowerRepEquivPolynomialRep`: the symmetric power of the standard representation
  of `GL n k` is equivalent to the forms of degree `d` in `n` variables.
* `TauCeti.polynomialMonomial`: the binary monomial `x ^ (d - i) * y ^ i`, zero for `i > d`.

## Main results

* `TauCeti.polynomialAction_mul`: the substitution is a left action.
* `TauCeti.polynomialAction_sum_C_mul_X`: on linear forms it is matrix-vector multiplication of
  the coefficient vector.
* `TauCeti.coe_symPowerRepEquivPolynomialRep_tprod`: the dictionary multiplies out a pure
  symmetric tensor.
* `TauCeti.coe_symPowerRepEquivPolynomialRep_symPower`: the dictionary intertwines the symmetric
  powers of the standard representation of `SU(2)` with substitution.
* `TauCeti.coeff_polynomialMonomial_self`, `TauCeti.coeff_polynomialMonomial_of_ne`: the binary
  monomial has coefficient `1` at the exponent `(d - i, i)` and `0` elsewhere.
* `TauCeti.polynomialAction_diagonal_polynomialMonomial`: the binary monomial has weight
  `(d - i, i)`.
* `TauCeti.coe_symPowerRepEquivPolynomialRep_tprod_ite`: the dictionary sends the pure tensor
  with `d - i` copies of the first and `i` copies of the second standard vector to the monomial.

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
theorem polynomialAction_eq_linearSubst (g : Matrix σ σ R) :
    polynomialAction g = linearSubst gᵀ :=
  (rfl)

@[simp]
theorem polynomialAction_X (g : Matrix σ σ R) (j : σ) :
    polynomialAction g (X j) = ∑ i, C (g i j) * X i := by
  simp [polynomialAction_eq_linearSubst]

@[simp]
theorem polynomialAction_one [DecidableEq σ] :
    polynomialAction (1 : Matrix σ σ R) = AlgHom.id R _ := by
  simp [polynomialAction_eq_linearSubst]

/-- The substitution of standard vectors is a left action of the matrix monoid. -/
theorem polynomialAction_mul (g h : Matrix σ σ R) :
    polynomialAction (g * h) = (polynomialAction g).comp (polynomialAction h) := by
  rw [polynomialAction_eq_linearSubst, transpose_mul, linearSubst_mul]
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
  rw [polynomialAction_eq_linearSubst, diagonal_transpose, linearSubst_diagonal]

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
  simp [polynomialRep, polynomialAction_eq_linearSubst]

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

/-- The equivalence `TauCeti.symPowerRepEquivPolynomialRep` intertwines the symmetric power of the
standard representation with the substitution of standard vectors. -/
theorem coe_symPowerRepEquivPolynomialRep_symPowerRep (g : GL (Fin n) k)
    (x : Sym[k]^d(Fin n → k)) :
    (symPowerRepEquivPolynomialRep k n d (symPowerRep k n d g x) : MvPolynomial (Fin n) k) =
      polynomialAction (g : Matrix (Fin n) (Fin n) k) (symPowerRepEquivPolynomialRep k n d x) := by
  rw [← coe_polynomialRep_apply]
  exact congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _
    (symPowerRepEquivPolynomialRep k n d).toIntertwiningMap g x)

/-- The equivalence `TauCeti.symPowerRepEquivPolynomialRep` intertwines the symmetric powers
`TauCeti.SU2.symPower` of the standard representation of `SU(2)` with the substitution of
standard vectors. -/
theorem coe_symPowerRepEquivPolynomialRep_symPower (g : SU2) (x : Sym[ℂ]^d(Fin 2 → ℂ)) :
    (symPowerRepEquivPolynomialRep ℂ 2 d (SU2.symPower d g x) : MvPolynomial (Fin 2) ℂ) =
      polynomialAction (g : Matrix (Fin 2) (Fin 2) ℂ) (symPowerRepEquivPolynomialRep ℂ 2 d x) := by
  rw [SU2.symPower_apply, coe_symPowerRepEquivPolynomialRep_symPowerRep, SU2.coe_toGL]

end SymmetricPower

section Monomial

variable (R : Type*) [CommSemiring R] (d i : ℕ)

/-- The binary monomial `e_i^d = x ^ (d - i) * y ^ i` of degree `d`, where `x = X 0` and
`y = X 1`, for `i ≤ d`; it is zero for `i > d`. -/
noncomputable def polynomialMonomial : MvPolynomial (Fin 2) R :=
  if i ≤ d then X 0 ^ (d - i) * X 1 ^ i else 0

variable {d i}

theorem polynomialMonomial_of_le (h : i ≤ d) :
    polynomialMonomial R d i = X 0 ^ (d - i) * X 1 ^ i := by
  simp [polynomialMonomial, h]

theorem polynomialMonomial_of_lt (h : d < i) : polynomialMonomial R d i = 0 := by
  simp [polynomialMonomial, h.not_ge]

/-- The binary monomial `e_i^d` is the monomial with exponent `(d - i, i)` and coefficient `1`. -/
theorem polynomialMonomial_eq_monomial (h : i ≤ d) :
    polynomialMonomial R d i =
      monomial (Finsupp.single 0 (d - i) + Finsupp.single 1 i) 1 := by
  rw [polynomialMonomial_of_le R h, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial,
    one_mul]

variable (d) in
@[simp]
theorem polynomialMonomial_zero_right : polynomialMonomial R d 0 = X 0 ^ d := by
  simp [polynomialMonomial]

variable (d) in
@[simp]
theorem polynomialMonomial_self : polynomialMonomial R d d = X 1 ^ d := by
  simp [polynomialMonomial]

variable (d i) in
/-- The binary monomial `e_i^d` is homogeneous of degree `d`, also when it vanishes. -/
theorem isHomogeneous_polynomialMonomial : (polynomialMonomial R d i).IsHomogeneous d := by
  by_cases h : i ≤ d
  · rw [polynomialMonomial_of_le R h]
    simpa only [Nat.sub_add_cancel h] using (isHomogeneous_X_pow 0 (d - i)).mul
      (isHomogeneous_X_pow 1 i)
  · rw [polynomialMonomial_of_lt R (not_le.mp h)]
    exact isHomogeneous_zero _ _ _

variable (d i) in
theorem polynomialMonomial_mem_homogeneousSubmodule :
    polynomialMonomial R d i ∈ homogeneousSubmodule (Fin 2) R d :=
  isHomogeneous_polynomialMonomial R d i

/-- The binary monomial `e_i^d` has coefficient `1` at the exponent `(d - i, i)`. -/
theorem coeff_polynomialMonomial_self (h : i ≤ d) :
    (polynomialMonomial R d i).coeff (Finsupp.single 0 (d - i) + Finsupp.single 1 i) = 1 := by
  simp [polynomialMonomial_eq_monomial R h]

/-- The binary monomial `e_i^d` has coefficient `0` away from the exponent `(d - i, i)`. -/
theorem coeff_polynomialMonomial_of_ne {s : Fin 2 →₀ ℕ}
    (hs : s ≠ Finsupp.single 0 (d - i) + Finsupp.single 1 i) :
    (polynomialMonomial R d i).coeff s = 0 := by
  by_cases h : i ≤ d
  · rw [polynomialMonomial_eq_monomial R h, coeff_monomial, ite_eq_right_iff]
    exact fun h' ↦ absurd h'.symm hs
  · simp [polynomialMonomial_of_lt R (not_le.mp h)]

variable (d i) in
/-- **The weight of `e_i^d` is `(d - i, i)`**: the diagonal matrix `diag(t₀, t₁)` scales the
binary monomial `e_i^d` by `t₀ ^ (d - i) * t₁ ^ i`. -/
theorem polynomialAction_diagonal_polynomialMonomial (t : Fin 2 → R) :
    polynomialAction (diagonal t) (polynomialMonomial R d i) =
      (t 0 ^ (d - i) * t 1 ^ i) • polynomialMonomial R d i := by
  by_cases h : i ≤ d
  · rw [polynomialMonomial_of_le R h, polynomialAction_diagonal, map_mul, map_pow, map_pow,
      rescale_X, rescale_X, smul_eq_C_mul, mul_pow, mul_pow, map_mul, map_pow, map_pow]
    ring
  · rw [polynomialMonomial_of_lt R (not_le.mp h), map_zero, smul_zero]

end Monomial

/-- **The dictionary on binary monomials**: the equivalence `TauCeti.symPowerRepEquivPolynomialRep`
sends the pure symmetric tensor with `d - i` copies of the first standard vector of `k²` followed
by `i` copies of the second to the binary monomial `e_i^d = x ^ (d - i) * y ^ i`. -/
theorem coe_symPowerRepEquivPolynomialRep_tprod_ite (k : Type) [CommRing k] {d i : ℕ}
    (h : i ≤ d) :
    (symPowerRepEquivPolynomialRep k 2 d
        (⨂ₛ[k] l : Fin d, Pi.single (if (l : ℕ) < d - i then 0 else 1) 1) :
        MvPolynomial (Fin 2) k) =
      polynomialMonomial k d i := by
  rw [coe_symPowerRepEquivPolynomialRep_tprod_single, polynomialMonomial_of_le k h]
  simp only [apply_ite X, Finset.prod_ite, Finset.prod_const]
  congr 2
  · rw [Fin.card_filter_val_lt, min_eq_right (Nat.sub_le d i)]
  · have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin d))) (fun l : Fin d ↦ (l : ℕ) < d - i)
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.sub_le d i), Finset.card_univ,
      Fintype.card_fin] at hcard
    omega

end TauCeti
