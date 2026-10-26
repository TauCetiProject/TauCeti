/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor
public import TauCeti.RingTheory.MvPolynomial.Lazard.Valuation

/-!
# The Kronecker substitution

For a weight `e : σ → ℕ`, the *Kronecker substitution* `Xₛ ↦ T ^ eₛ` turns a multivariate
polynomial into a polynomial in one variable `T`, sending the monomial `c X^μ` to
`c T ^ (weight e μ)` (`MvPolynomial.aeval_X_pow_left_monomial`). It is injective on the
polynomials supported in any set of exponent vectors on which `weight e` is injective, and every
finite set of exponent vectors admits such a weight.
Consequently a finite family of multivariate polynomials can be carried to a family of univariate
polynomials while preserving linear independence. This reduces statements about several
variables, such as the generalized Wronskian criterion, to the one-variable case.

Translating `T` to `T + a` turns the substitution into `Xₛ ↦ (T + a) ^ eₛ - a ^ eₛ` applied to
the Taylor expansion of `f` at `(a ^ eₛ)ₛ`. This gives a chain rule: Hasse derivatives of the
image of `f`, evaluated at `a`, are linear combinations of the Hasse derivatives of `f`
evaluated at `(a ^ eₛ)ₛ`.

## Main results

* `Finsupp.exists_injOn_weight`: every finite set of exponent vectors is separated by
  `weight e` for some `e : σ → ℕ`.
* `MvPolynomial.coeff_aeval_X_pow_weight`: if `weight e` is injective on a set containing the
  support of `f` and `μ`, the coefficient of `T ^ (weight e μ)` is that of `X^μ` in `f`.
* `MvPolynomial.injOn_aeval_X_pow`, `MvPolynomial.linearIndependent_aeval_X_pow`: the
  substitution is injective on such polynomials and preserves linear independence of families
  supported there.
* `MvPolynomial.taylor_aeval_X_pow`: the substitution intertwines the Taylor expansions at `a`
  and at `(a ^ eₛ)ₛ`.
* `MvPolynomial.eval_hasseDeriv_aeval_X_pow`: the chain rule for the substitution; the `k`-th
  Hasse derivative of the image only involves Hasse derivatives `∂^ν f` with `|ν| ≤ k`
  (`MvPolynomial.coeff_aeval_X_add_C_pow_sub_C_eq_zero`).

## Implementation notes

The variables may form an arbitrary type. A separating weight is a Lazard evaluator
(`TauCeti.exists_isLazardEvaluator`, `TauCeti.IsLazardEvaluator.weight_injOn`) for a linear
order on the variables chosen locally from a well-ordering; the statement does not depend on
that order.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  Exercise 3.5, which uses the weights `eⱼ = Bʲ` for `B` larger than all partial degrees.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Proposition 6.3.10.
* The injectivity of the substitution on separated supports and its use for linear independence
  are adapted from Ralf Stephan's `DiophantineApproximation/GeneralizedWronskian.lean`
  in [`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems), commit
  `5cff93ceb4b69b2048473301411763febe96bb3f` (Apache 2.0).
-/

public section

noncomputable section

namespace Finsupp

variable {σ : Type*}

/-- Every finite set of exponent vectors is separated by a single weight: some `e : σ → ℕ`
makes `weight e` injective on it. No order on the variables is needed. -/
theorem exists_injOn_weight (T : Finset (σ →₀ ℕ)) :
    ∃ e : σ → ℕ, Set.InjOn (weight e) (T : Set (σ →₀ ℕ)) := by
  let _ : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨e, he⟩ := TauCeti.exists_isLazardEvaluator T.finite_toSet
  exact ⟨e, he.weight_injOn⟩

end Finsupp

namespace MvPolynomial

open Finsupp

variable {R σ : Type*}

section CommSemiring

variable [CommSemiring R]

/-- If `weight e` is injective on a set `T` containing the support of `f` and the exponent `μ`,
then after the Kronecker substitution `Xₛ ↦ T ^ eₛ` the coefficient of `T ^ (weight e μ)` is the
coefficient of `X^μ` in `f`. -/
theorem coeff_aeval_X_pow_weight {e : σ → ℕ} {T : Set (σ →₀ ℕ)} (he : Set.InjOn (weight e) T)
    {f : MvPolynomial σ R} (hf : ↑f.support ⊆ T) {μ : σ →₀ ℕ} (hμ : μ ∈ T) :
    (aeval (fun s ↦ (Polynomial.X : Polynomial R) ^ e s) f).coeff (weight e μ) = f.coeff μ := by
  classical
  conv_lhs => rw [f.as_sum]
  simp only [map_sum, aeval_X_pow_left_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single μ (fun ν hν hne ↦ ite_eq_right_iff.mpr fun h ↦
    absurd (he (hf hν) hμ h) hne) fun h ↦ by simp [notMem_support_iff.mp h]]
  simp

/-- The Kronecker substitution `Xₛ ↦ T ^ eₛ` is injective on the polynomials supported in a set
of exponent vectors on which `weight e` is injective. -/
theorem injOn_aeval_X_pow {e : σ → ℕ} {T : Set (σ →₀ ℕ)} (he : Set.InjOn (weight e) T) :
    Set.InjOn (aeval fun s ↦ (Polynomial.X : Polynomial R) ^ e s)
      (restrictSupport R T : Set (MvPolynomial σ R)) := by
  intro f hf g hg h
  rw [SetLike.mem_coe, mem_restrictSupport_iff] at hf hg
  ext μ
  by_cases hμ : μ ∈ T
  · rw [← coeff_aeval_X_pow_weight he hf hμ, ← coeff_aeval_X_pow_weight he hg hμ, h]
  · rw [notMem_support_iff.mp fun h ↦ hμ (hf h), notMem_support_iff.mp fun h ↦ hμ (hg h)]

/-- The Kronecker substitution `Xₛ ↦ T ^ eₛ` preserves linear independence of a family of
polynomials supported in a set of exponent vectors on which `weight e` is injective. -/
theorem linearIndependent_aeval_X_pow {ι : Type*} {e : σ → ℕ} {T : Set (σ →₀ ℕ)}
    (he : Set.InjOn (weight e) T) {φ : ι → MvPolynomial σ R} (hφT : ∀ i, ↑(φ i).support ⊆ T)
    (hφ : LinearIndependent R φ) :
    LinearIndependent R fun i ↦ aeval (fun s ↦ (Polynomial.X : Polynomial R) ^ e s) (φ i) := by
  refine hφ.map_injOn (aeval fun s ↦ (Polynomial.X : Polynomial R) ^ e s).toLinearMap
    ((injOn_aeval_X_pow he).mono ?_)
  rw [SetLike.coe_subset_coe, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (mem_restrictSupport_iff (R := R)).mpr (hφT i)

end CommSemiring

section CommRing

variable [CommRing R]

/-- Translating `T` to `T + a` after the Kronecker substitution `Xₛ ↦ T ^ eₛ` is the same as
translating `X` to `X + (a ^ eₛ)ₛ` and then substituting `Xₛ ↦ (T + a) ^ eₛ - a ^ eₛ`. -/
theorem taylor_aeval_X_pow (e : σ → ℕ) (a : R) (f : MvPolynomial σ R) :
    Polynomial.taylor a (aeval (fun s ↦ (Polynomial.X : Polynomial R) ^ e s) f) =
      aeval (fun s ↦ (Polynomial.X + Polynomial.C a) ^ e s - Polynomial.C (a ^ e s))
        (taylor (fun s ↦ a ^ e s) f) := by
  have h : (Polynomial.taylorAlgHom a).comp (aeval fun s ↦ (Polynomial.X : Polynomial R) ^ e s) =
      (aeval fun s ↦ (Polynomial.X + Polynomial.C a) ^ e s - Polynomial.C (a ^ e s)).comp
        (taylor fun s ↦ a ^ e s) :=
    algHom_ext fun s ↦ by simp [taylor_X]
  simpa using DFunLike.congr_fun h f

/-- The translated Kronecker substitution `Xₛ ↦ (T + a) ^ eₛ - a ^ eₛ` sends `X^ν` to a multiple
of `T ^ |ν|`, so the coefficients of `T ^ k` with `k < |ν|` vanish. -/
theorem coeff_aeval_X_add_C_pow_sub_C_eq_zero (e : σ → ℕ) (a : R) (ν : σ →₀ ℕ) {k : ℕ}
    (hk : k < ν.degree) :
    (aeval (fun s ↦ (Polynomial.X + Polynomial.C a) ^ e s - Polynomial.C (a ^ e s))
      (monomial ν (1 : R))).coeff k = 0 := by
  refine Polynomial.X_pow_dvd_iff.mp ?_ k hk
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod, degree_apply, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun s _ ↦ pow_dvd_pow_of_dvd ?_ _
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- **The chain rule for the Kronecker substitution.** The `k`-th Hasse derivative of the image of
`f` under `Xₛ ↦ T ^ eₛ`, evaluated at `a`, is a linear combination of the Hasse derivatives
`∂^ν f` evaluated at `(a ^ eₛ)ₛ`, with coefficients independent of `f`. -/
theorem eval_hasseDeriv_aeval_X_pow (e : σ → ℕ) (a : R) (f : MvPolynomial σ R) (k : ℕ)
    {T : Finset (σ →₀ ℕ)} (hT : (taylor (fun s ↦ a ^ e s) f).support ⊆ T) :
    (Polynomial.hasseDeriv k (aeval (fun s ↦ (Polynomial.X : Polynomial R) ^ e s) f)).eval a =
      ∑ ν ∈ T, (aeval (fun s ↦ (Polynomial.X + Polynomial.C a) ^ e s - Polynomial.C (a ^ e s))
        (monomial ν (1 : R))).coeff k * eval (fun s ↦ a ^ e s) (hasseDeriv ν f) := by
  rw [← Polynomial.taylor_coeff, taylor_aeval_X_pow,
    (taylor (fun s ↦ a ^ e s) f).as_sum, Finset.sum_subset hT fun ν _ hν ↦ by
      rw [notMem_support_iff.mp hν, monomial_zero], map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  rw [coeff_taylor]
  conv_lhs => rw [← mul_one (eval _ (hasseDeriv ν f)), ← smul_eq_mul, ← smul_monomial]
  rw [map_smul, Polynomial.coeff_smul, smul_eq_mul, mul_comm]

end CommRing

end MvPolynomial
