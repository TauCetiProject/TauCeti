/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
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

## Main results

* `Finsupp.exists_injOn_weight`: every finite set of exponent vectors is separated by
  `weight e` for some `e : σ → ℕ`.
* `MvPolynomial.coeff_aeval_X_pow_weight`: if `weight e` is injective on a set containing the
  support of `f` and `μ`, the coefficient of `T ^ (weight e μ)` is that of `X^μ` in `f`.
* `MvPolynomial.disjoint_restrictSupport_ker_aeval_X_pow`,
  `MvPolynomial.linearIndependent_aeval_X_pow`: the substitution is injective on such
  polynomials and preserves linear independence of families supported there.

## Implementation notes

The weight is found without ordering or enumerating the variables, which may form an arbitrary
type; for linearly ordered variables, the Lazard evaluators of
`TauCeti.exists_isLazardEvaluator` are such weights (`TauCeti.IsLazardEvaluator.weight_injOn`).
The product over all pairs `μ ≠ ν` of the linear forms `∑ₛ (μₛ - νₛ) Xₛ` is a nonzero polynomial
over `ℤ`, so it does not vanish at some point with natural coordinates
(`MvPolynomial.funext_set`); any such point is a separating weight.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  Exercise 3.5, which uses the weights `eⱼ = Bʲ` for `B` larger than all partial degrees.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Proposition 6.3.10.
-/

public section

noncomputable section

namespace Finsupp

variable {σ : Type*}

/-- Every finite set of exponent vectors is separated by a single weight: some `e : σ → ℕ`
makes `weight e` injective on it. No order on the variables is needed. -/
theorem exists_injOn_weight (T : Finset (σ →₀ ℕ)) :
    ∃ e : σ → ℕ, Set.InjOn (weight e) (T : Set (σ →₀ ℕ)) := by
  classical
  -- The linear form `∑ₛ μₛ Xₛ` over `ℤ`; its value at `x` is `weight x μ`.
  let ℓ : (σ →₀ ℕ) → MvPolynomial σ ℤ := fun μ ↦ weight MvPolynomial.X μ
  have hℓ (x : σ → ℤ) (μ : σ →₀ ℕ) : MvPolynomial.eval x (ℓ μ) = weight x μ := by
    simp [ℓ, weight_apply, Finsupp.sum, map_sum]
  have hℓinj : Function.Injective ℓ := fun μ ν h ↦ Finsupp.ext fun s ↦ by
    have := congrArg (MvPolynomial.eval (Pi.single s 1)) h
    simpa [hℓ, weight_single_index] using this
  have hQ : ∏ p ∈ T.offDiag, (ℓ p.1 - ℓ p.2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp ↦
      sub_ne_zero.mpr (hℓinj.ne (Finset.mem_offDiag.mp hp).2.2)
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ fun _ : σ ↦ Set.range (Nat.cast : ℕ → ℤ),
      MvPolynomial.eval x (∏ p ∈ T.offDiag, (ℓ p.1 - ℓ p.2)) ≠ 0 := by
    by_contra! h
    exact hQ (MvPolynomial.funext_set _ (fun _ ↦ Set.infinite_range_of_injective
      Nat.cast_injective) fun x hx ↦ by rw [h x hx, map_zero])
  choose e he using fun s ↦ hx s (Set.mem_univ s)
  have hx' : x = fun s ↦ (e s : ℤ) := funext fun s ↦ (he s).symm
  refine ⟨e, fun μ hμ ν hν h ↦ by_contra fun hne ↦ hQx ?_⟩
  rw [map_prod]
  refine Finset.prod_eq_zero (i := (μ, ν)) (Finset.mem_offDiag.mpr ⟨hμ, hν, hne⟩) ?_
  rw [map_sub, hℓ, hℓ, sub_eq_zero, hx']
  simpa [weight_apply, Finsupp.sum] using congrArg (Nat.cast : ℕ → ℤ) h

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
theorem disjoint_restrictSupport_ker_aeval_X_pow {e : σ → ℕ} {T : Set (σ →₀ ℕ)}
    (he : Set.InjOn (weight e) T) :
    Disjoint (restrictSupport R T)
      (LinearMap.ker (aeval fun s ↦ (Polynomial.X : Polynomial R) ^ e s).toLinearMap) := by
  rw [Submodule.disjoint_def]
  intro f hf hker
  rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hker
  by_contra hf0
  obtain ⟨μ, hμ⟩ := support_nonempty.mpr hf0
  have hfT : ↑f.support ⊆ T := (mem_restrictSupport_iff (R := R)).mp hf
  exact mem_support_iff.mp hμ (by
    rw [← coeff_aeval_X_pow_weight he hfT (hfT hμ), hker, Polynomial.coeff_zero])

end CommSemiring

section CommRing

variable [CommRing R]

/-- The Kronecker substitution `Xₛ ↦ T ^ eₛ` preserves linear independence of a family of
polynomials supported in a set of exponent vectors on which `weight e` is injective. -/
theorem linearIndependent_aeval_X_pow {ι : Type*} {e : σ → ℕ} {T : Set (σ →₀ ℕ)}
    (he : Set.InjOn (weight e) T) {φ : ι → MvPolynomial σ R} (hφT : ∀ i, ↑(φ i).support ⊆ T)
    (hφ : LinearIndependent R φ) :
    LinearIndependent R fun i ↦ aeval (fun s ↦ (Polynomial.X : Polynomial R) ^ e s) (φ i) := by
  refine hφ.map (f := (aeval fun s ↦ (Polynomial.X : Polynomial R) ^ e s).toLinearMap) ?_
  refine (disjoint_restrictSupport_ker_aeval_X_pow he).mono_left ?_
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (mem_restrictSupport_iff (R := R)).mpr (hφT i)

end CommRing

end MvPolynomial
