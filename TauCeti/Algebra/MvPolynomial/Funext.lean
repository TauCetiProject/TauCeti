/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Polynomial nonvanishing and polynomial maps with vector coefficients

Over an infinite integral domain `R`, a nonzero multivariate polynomial takes a nonzero value at
some assignment of the variables (`MvPolynomial.exists_eval_ne_zero`), the contrapositive of
Mathlib's `MvPolynomial.funext`. More generally, two polynomials over an integral domain `R` that
agree on the image of an injective map from an infinite type are equal
(`MvPolynomial.funext_of_injective`, `MvPolynomial.funext_algebraMap`).

A polynomial map `z ↦ ∑ α ∈ s, (∏ i, z i ^ α i) • c α` from `ι → K` to a `K`-vector space `V`,
over an infinite field `K`, determines its coefficients: if it vanishes everywhere, every
`c α` with `α ∈ s` is zero. This is Mathlib's `MvPolynomial.funext` with coefficients in a vector
space rather than in `K`, deduced from it by composing with the linear functionals on `V`. It is
the algebraic half of the identity theorem for power series in several variables.
-/

public section

namespace MvPolynomial

/-- Over an infinite integral domain, a nonzero multivariate polynomial takes a nonzero value at
some assignment of the variables. -/
theorem exists_eval_ne_zero {σ R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {p : MvPolynomial σ R} (hp : p ≠ 0) : ∃ x : σ → R, eval x p ≠ 0 := by
  contrapose! hp
  exact funext fun x ↦ by simp [hp x]

/-- Two multivariate polynomials over an integral domain are equal if they agree at all points with
coordinates in the image of an injective map from an infinite type. -/
theorem funext_of_injective {σ S R : Type*} [Infinite S] [CommRing R] [IsDomain R]
    {f : S → R} (hf : Function.Injective f) {p q : MvPolynomial σ R}
    (h : ∀ x : σ → S, eval (f ∘ x) p = eval (f ∘ x) q) : p = q := by
  refine funext_set (fun _ ↦ Set.range f) (fun _ ↦ Set.infinite_range_of_injective hf) fun y hy ↦ ?_
  choose x hx using fun i ↦ hy i (Set.mem_univ i)
  have hxy : y = f ∘ x := by ext i; exact (hx i).symm
  rw [hxy]
  exact h x

/-- Two multivariate polynomials over an integral domain `R` that is a faithful algebra over an
infinite commutative semiring `S` (for instance any nontrivial algebra over an infinite field such
as `ℝ`) are equal if they agree at all `S`-points. -/
theorem funext_algebraMap {σ S R : Type*} [CommSemiring S] [Infinite S] [CommRing R] [IsDomain R]
    [Algebra S R] [FaithfulSMul S R] {p q : MvPolynomial σ R}
    (h : ∀ x : σ → S, eval (algebraMap S R ∘ x) p = eval (algebraMap S R ∘ x) q) : p = q :=
  funext_of_injective (FaithfulSMul.algebraMap_injective S R) h

end MvPolynomial

namespace TauCeti

open Finset

variable {K ι V : Type*} [Field K] [Infinite K] [Fintype ι] [AddCommGroup V] [Module K V]

/-- Over an infinite field, a polynomial map `z ↦ ∑ α ∈ s, (∏ i, z i ^ α i) • c α` with
coefficients in a vector space vanishes identically only if all its coefficients `c α`,
`α ∈ s`, vanish. -/
theorem eq_zero_of_forall_sum_prod_pow_smul_eq_zero {s : Finset (ι → ℕ)} {c : (ι → ℕ) → V}
    (h : ∀ z : ι → K, ∑ α ∈ s, (∏ i, z i ^ α i) • c α = 0) {α : ι → ℕ} (hα : α ∈ s) :
    c α = 0 := by
  classical
  refine (Module.forall_dual_apply_eq_zero_iff K (c α)).1 fun φ ↦ ?_
  -- Under the functional `φ`, the polynomial map is the evaluation of a scalar polynomial `P`.
  let e : (ι →₀ ℕ) ≃ (ι → ℕ) := Finsupp.equivFunOnFinite
  let P : MvPolynomial ι K := ∑ β ∈ s, MvPolynomial.monomial (e.symm β) (φ (c β))
  have hP : P = 0 := MvPolynomial.funext fun z ↦ by
    simpa [P, e, MvPolynomial.eval_monomial, Finsupp.prod_fintype, mul_comm] using
      congr(φ $(h z))
  simpa [P, e, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hα] using
    congrArg (fun Q : MvPolynomial ι K ↦ Q.coeff (e.symm α)) hP

end TauCeti
