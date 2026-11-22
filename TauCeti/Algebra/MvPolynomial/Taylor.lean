/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Taylor shift of multivariate polynomials

`MvPolynomial.taylor a` is the `R`-algebra endomorphism `p ↦ p(X + a)` substituting `Xᵢ + aᵢ`
for each variable `Xᵢ`. Its constant coefficient is `eval a p` and its linear coefficients are the
partial derivatives `(∂p/∂Xᵢ)(a)` (`MvPolynomial.constantCoeff_taylor`,
`MvPolynomial.coeff_single_one_taylor`). Over a commutative ring it is an `R`-algebra
automorphism `MvPolynomial.taylorEquiv a` with inverse `MvPolynomial.taylor (-a)` and preserves
total and partial degrees.

## Main definitions

* `MvPolynomial.taylor`: the Taylor shift `p ↦ p(X + a)`.
* `MvPolynomial.taylorEquiv`: the Taylor shift as an `R`-algebra automorphism over a commutative
  ring.

## Main results

* `MvPolynomial.constantCoeff_taylor`: the constant coefficient of `taylor a p` is `eval a p`.
* `MvPolynomial.coeff_single_one_taylor`: the coefficient of `Xᵢ` in `taylor a p` is
  `eval a (pderiv i p)`.
* `MvPolynomial.pderiv_taylor`: partial differentiation commutes with `taylor a`.
* `MvPolynomial.totalDegree_taylor_le`, `MvPolynomial.degreeOf_taylor_le`: `taylor a` does not
  increase total or partial degree (with equality over a commutative ring).
-/

public section

namespace MvPolynomial

open Finsupp

variable {σ τ R : Type*}

section Taylor

variable [CommSemiring R]

/-- The Taylor shift of a multivariate polynomial at `a`: the substitution `p ↦ p(X + a)` of
`Xᵢ + aᵢ` for each variable `Xᵢ`. The coefficients of `taylor a p` are the Taylor coefficients
of `p` at `a`. -/
noncomputable def taylor (a : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ X i + C (a i)

theorem taylor_apply (a : σ → R) (p : MvPolynomial σ R) :
    taylor a p = aeval (fun i ↦ X i + C (a i)) p :=
  (rfl)

@[simp]
theorem taylor_X (a : σ → R) (i : σ) : taylor a (X i) = X i + C (a i) :=
  aeval_X _ _

theorem taylor_C (a : σ → R) (r : R) : taylor a (C r) = C r :=
  aeval_C _ _

/-- Taylor shifts commute with coefficient maps, with the center mapped along the same
homomorphism. -/
@[simp]
theorem map_taylor {S : Type*} [CommSemiring S] (p : MvPolynomial σ R) (a : σ → R)
    (f : R →+* S) :
    map f (taylor a p) = taylor (fun i ↦ f (a i)) (map f p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- Taylor coefficients depend polynomially on the center. Evaluate the formal center in
`taylor X (map C p)` at `a` to recover each coefficient of `taylor a p`. -/
@[simp]
theorem eval_coeff_taylor_map_C (p : MvPolynomial σ R) (a : σ → R) (v : σ →₀ ℕ) :
    eval a ((taylor (X : σ → MvPolynomial σ R) (map C p)).coeff v) =
      (taylor a p).coeff v := by
  rw [← coeff_map, map_taylor, map_map]
  have h : (eval a).comp (C : R →+* MvPolynomial σ R) = RingHom.id R := by
    ext r
    simp
  simp [h, map_id]

@[simp]
theorem eval_taylor (a x : σ → R) (p : MvPolynomial σ R) :
    eval x (taylor a p) = eval (x + a) p := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- The constant Taylor coefficient of `p` at `a` is the value of `p` at `a`. -/
@[simp]
theorem constantCoeff_taylor (a : σ → R) (p : MvPolynomial σ R) :
    constantCoeff (taylor a p) = eval a p := by
  rw [← eval_zero, eval_taylor, zero_add]

@[simp]
theorem taylor_zero (p : MvPolynomial σ R) : taylor 0 p = p := by
  induction p using MvPolynomial.induction_on <;> simp_all

theorem taylor_taylor (a b : σ → R) (p : MvPolynomial σ R) :
    taylor a (taylor b p) = taylor (a + b) p := by
  induction p using MvPolynomial.induction_on <;> simp_all [add_assoc]

/-- Renaming the variables commutes with Taylor shifts, with the center pulled back along the
renaming. -/
theorem taylor_rename (f : σ → τ) (b : τ → R) (p : MvPolynomial σ R) :
    taylor b (rename f p) = rename f (taylor (b ∘ f) p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- The Taylor shift does not increase the total degree. -/
theorem totalDegree_taylor_le (a : σ → R) (p : MvPolynomial σ R) :
    (taylor a p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd ↦ ?_)
  rw [taylor_apply, aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans (le_trans ?_ (le_totalDegree hd))
  refine Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans ?_
  refine (Nat.mul_le_mul_left _ ((totalDegree_add _ _).trans (max_le ?_ ?_))).trans_eq
    (mul_one _)
  · exact (totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp

/-- Partial differentiation commutes with the Taylor shift. -/
@[simp]
theorem pderiv_taylor (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    pderiv i (taylor a p) = taylor a (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    obtain rfl | hj := eq_or_ne j i
    · simp [hp]
    · simp [hp, pderiv_X_of_ne hj]

/-- The linear Taylor coefficients of `p` at `a` are the values of its partial derivatives:
`[Yᵢ] p(a + Y) = (∂p/∂Xᵢ)(a)`. -/
@[simp]
theorem coeff_single_one_taylor (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    (taylor a p).coeff (Finsupp.single i 1) = eval a (pderiv i p) := by
  classical
  rw [← constantCoeff_taylor, ← pderiv_taylor, constantCoeff_eq, coeff_pderiv]
  simp

/-- The Taylor shift does not increase the degree in any variable. -/
theorem degreeOf_taylor_le (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    (taylor a p).degreeOf i ≤ p.degreeOf i := by
  classical
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim (taylor a p) 0]
  conv_lhs => rw [p.as_sum, map_sum]
  refine (degreeOf_sum_le i _ _).trans (Finset.sup_le fun m hm ↦ ?_)
  rw [taylor_apply, aeval_monomial, algebraMap_eq]
  refine (degreeOf_C_mul_le _ i _).trans ((degreeOf_prod_le i _ _).trans ?_)
  calc ∑ j ∈ m.support, ((X j + C (a j)) ^ m j).degreeOf i
      ≤ ∑ j ∈ m.support, if i = j then m j else 0 := by
        refine Finset.sum_le_sum fun j _ ↦ (degreeOf_pow_le i _ _).trans ?_
        have : (X j + C (a j) : MvPolynomial σ R).degreeOf i ≤ if i = j then 1 else 0 :=
          (degreeOf_add_le i _ _).trans (by simp [degreeOf_X, degreeOf_C])
        split_ifs at this ⊢ <;> simpa using Nat.mul_le_mul_left (m j) this
    _ ≤ m i := by rw [Finset.sum_ite_eq]; split_ifs <;> simp
    _ ≤ p.degreeOf i := monomial_le_degreeOf i hm

end Taylor

section TaylorRing

variable [CommRing R]

@[simp]
theorem taylor_neg_taylor (a : σ → R) (p : MvPolynomial σ R) : taylor (-a) (taylor a p) = p := by
  rw [taylor_taylor, neg_add_cancel, taylor_zero]

/-- The Taylor shift `p ↦ p(X + a)` as an `R`-algebra automorphism of `MvPolynomial σ R`, with
inverse `taylor (-a)`. -/
noncomputable def taylorEquiv (a : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (taylor a) (taylor (-a))
    (AlgHom.ext fun p ↦ by rw [AlgHom.comp_apply, taylor_taylor, add_neg_cancel, taylor_zero,
      AlgHom.id_apply])
    (AlgHom.ext fun p ↦ by rw [AlgHom.comp_apply, taylor_neg_taylor, AlgHom.id_apply])

@[simp]
theorem taylorEquiv_apply (a : σ → R) (p : MvPolynomial σ R) :
    taylorEquiv a p = taylor a p := by
  simp [taylorEquiv]

@[simp]
theorem toAlgHom_taylorEquiv (a : σ → R) :
    (taylorEquiv a : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) = taylor a :=
  AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

@[simp]
theorem taylorEquiv_symm (a : σ → R) :
    (taylorEquiv a).symm = taylorEquiv (-a) := by
  ext p
  simp [taylorEquiv, AlgEquiv.ofAlgHom_symm]

/-- The Taylor shift preserves the total degree. -/
@[simp]
theorem totalDegree_taylor (a : σ → R) (p : MvPolynomial σ R) :
    (taylor a p).totalDegree = p.totalDegree :=
  (totalDegree_taylor_le a p).antisymm <| by simpa using totalDegree_taylor_le (-a) (taylor a p)

theorem taylor_injective (a : σ → R) : Function.Injective (taylor a) :=
  Function.LeftInverse.injective (taylor_neg_taylor a)

/-- The Taylor shift preserves the degree in each variable. -/
@[simp]
theorem degreeOf_taylor (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    (taylor a p).degreeOf i = p.degreeOf i :=
  (degreeOf_taylor_le a i p).antisymm <| by
    simpa using degreeOf_taylor_le (-a) i (taylor a p)

/-- **The Taylor shift of a substitution.** Writing `a i = g i (b)` for the image point, the Taylor
shift of `p(g)` at `b` is obtained by substituting `g i (X + b) - a i`, polynomials without
constant term, into the Taylor shift of `p` at `a`: in Taylor coordinates the substitution fixes
the origin. -/
theorem taylor_aeval (g : σ → MvPolynomial τ R) (b : τ → R) (p : MvPolynomial σ R) :
    taylor b (aeval g p) =
      aeval (fun i ↦ taylor b (g i) - C (eval b (g i))) (taylor (fun i ↦ eval b (g i)) p) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  ext i : 1
  simp [taylor]

end TaylorRing

end MvPolynomial
