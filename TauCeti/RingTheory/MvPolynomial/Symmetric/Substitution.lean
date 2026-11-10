/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Substitution in symmetric multivariate polynomials

Substituting into a symmetric multivariate polynomial a family of polynomials that is permuted
along with the variables, for instance the same univariate polynomial in every variable,
preserves symmetry. For finitely many variables over a commutative ring, Mathlib's fundamental
theorem of symmetric polynomials (`MvPolynomial.esymmAlgHom_surjective`) then expresses the
substituted polynomial in the elementary symmetric polynomials.

In the other direction, substituting the elementary symmetric polynomials for the variables
gives the ring endomorphism `TauCeti.esymmSubst` of `MvPolynomial (Fin n) R`. It agrees with
Mathlib's `MvPolynomial.esymmAlgHom`, so over a commutative ring it is injective: an expression of
a symmetric polynomial in the elementary symmetric polynomials is unique.

## Main declarations

* `MvPolynomial.IsSymmetric.bind₁`: substituting an equivariant family of polynomials preserves
  symmetry.
* `MvPolynomial.IsSymmetric.bind₁_aeval_X`: uniform univariate substitution preserves
  symmetry.
* `TauCeti.esymmSubst`: the substitution of the elementary symmetric polynomials
  `e_1, …, e_n` for the variables `X_0, …, X_(n-1)`.
* `TauCeti.esymmSubst_injective`: over a commutative ring, elementary-symmetric substitution is
  injective, by the fundamental theorem of symmetric polynomials.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R}

/-- Substituting into a symmetric polynomial a family of polynomials `f` that is equivariant
under permutations of the variables, `rename e (f i) = f (e i)`, yields a symmetric
polynomial. -/
protected theorem IsSymmetric.bind₁ (hp : p.IsSymmetric) {f : σ → MvPolynomial σ R}
    (hf : ∀ (e : Equiv.Perm σ) (i : σ), rename e (f i) = f (e i)) :
    (bind₁ f p).IsSymmetric := fun e => by
  conv_rhs => rw [← hp e, bind₁_rename, Function.comp_def]
  simp_rw [rename_bind₁, hf]

/-- Substituting the same univariate polynomial into every variable of a symmetric multivariate
polynomial preserves symmetry. -/
theorem IsSymmetric.bind₁_aeval_X (hp : p.IsSymmetric) (q : Polynomial R) :
    (bind₁ (fun i => Polynomial.aeval (X i) q) p).IsSymmetric :=
  hp.bind₁ fun e i => by rw [← Polynomial.aeval_algHom_apply, rename_X]

end MvPolynomial

namespace TauCeti

section esymmSubst

variable {R : Type*}

/-- The substitution sending variable `i` to the elementary symmetric polynomial `e_(i+1)`. -/
noncomputable def esymmSubst [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R :=
  (MvPolynomial.aeval fun i : Fin n => MvPolynomial.esymm (Fin n) R ((i : ℕ) + 1)).toRingHom

/-- Elementary-symmetric substitution sends `X i` to `e_(i+1)`. -/
@[simp]
theorem esymmSubst_X [CommSemiring R] (n : ℕ) (i : Fin n) :
    esymmSubst n (MvPolynomial.X i) = MvPolynomial.esymm (Fin n) R ((i : ℕ) + 1) := by
  simp [esymmSubst]

/-- Elementary-symmetric substitution agrees with Mathlib's fundamental-theorem map. -/
theorem esymmSubst_apply [CommSemiring R] (n : ℕ) (p : MvPolynomial (Fin n) R) :
    esymmSubst n p = (MvPolynomial.esymmAlgHom (Fin n) R n p).1 :=
  (MvPolynomial.esymmAlgHom_apply p).symm

/-- Substitution by the elementary symmetric polynomials is injective. -/
lemma esymmSubst_injective [CommRing R] (n : ℕ) :
    Function.Injective (esymmSubst (R := R) n) := fun p q hpq =>
  (MvPolynomial.esymmAlgHom_fin_bijective R n).1 <| Subtype.ext <| by
    simpa only [← esymmSubst_apply] using hpq

end esymmSubst

end TauCeti
