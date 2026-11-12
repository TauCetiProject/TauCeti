/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Polynomial maps with vector coefficients

A polynomial map `z ↦ ∑ α ∈ s, (∏ i, z i ^ α i) • c α` from `ι → K` to a `K`-vector space `V`,
over an infinite field `K`, determines its coefficients: if it vanishes everywhere, every
`c α` with `α ∈ s` is zero. This is Mathlib's `MvPolynomial.funext` with coefficients in a vector
space rather than in `K`, deduced from it by composing with the linear functionals on `V`. It is
the algebraic half of the identity theorem for power series in several variables.
-/

public section

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
