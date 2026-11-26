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
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Combinatorics.Nullstellensatz

/-!
# Polynomial nonvanishing and polynomial maps with vector coefficients

Over an infinite integral domain `R`, a nonzero multivariate polynomial takes a nonzero value at
some assignment of the variables (`MvPolynomial.exists_eval_ne_zero`), the contrapositive of
Mathlib's `MvPolynomial.funext`. Over any integral domain with more elements than the total degree
of the polynomial, in finitely many variables, the same holds
(`MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`).

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

/-- Over an integral domain with more elements than the total degree of a nonzero polynomial `P`
in finitely many variables, `P` takes a nonzero value: a monomial of top degree, by the
combinatorial Nullstellensatz. -/
theorem exists_eval_ne_zero_of_totalDegree_lt_card {k σ : Type*} [Finite σ] [CommRing k]
    [IsDomain k] {P : MvPolynomial σ k} (hP : P ≠ 0)
    (hdeg : (P.totalDegree : Cardinal) < Cardinal.mk k) : ∃ a : σ → k, eval a P ≠ 0 := by
  classical
  obtain ⟨t, ht, hmax⟩ := P.support.exists_max_image (fun s ↦ s.degree) (support_nonempty.2 hP)
  have htot : P.totalDegree = t.degree := by
    refine le_antisymm (Finset.sup_le fun s hs ↦ ?_) ?_
    · exact hmax s hs
    · exact le_totalDegree ht
  have hS (i : σ) : ∃ S : Finset k, t i + 1 = S.card := by
    refine Cardinal.exists_finset_eq_card ?_
    push_cast
    refine Cardinal.natCast_add_one_le_iff.2 (lt_of_le_of_lt ?_ hdeg)
    exact_mod_cast htot ▸ Finsupp.le_degree i t
  choose S hS using hS
  obtain ⟨a, -, ha⟩ := combinatorial_nullstellensatz_exists_eval_ne_zero P t (mem_support_iff.1 ht)
    htot S fun i ↦ by rw [← hS i]; exact Nat.lt_succ_self _
  exact ⟨a, ha⟩

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
