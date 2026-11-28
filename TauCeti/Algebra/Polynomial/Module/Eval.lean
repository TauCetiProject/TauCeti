/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Polynomial.Module.Basic
import TauCeti.LinearAlgebra.PolynomialFamily

/-!
# Evaluation of module-valued polynomials

Evaluation is a finite power sum with vector coefficients. Over an infinite domain,
evaluation at all scalars separates module-valued polynomials with torsion-free coefficients.
-/

public section

namespace PolynomialModule

/-- Evaluation can sum over any initial segment containing the coefficient support. -/
theorem eval_eq_sum_range {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : PolynomialModule R M) (x : R) {d : ℕ} (hd : p.coeff.support ⊆ Finset.range d) :
    eval x p = ∑ i ∈ Finset.range d, x ^ i • p.coeff i := by
  rw [eval_apply, Finsupp.sum_of_support_subset _ hd _ (fun _ _ ↦ smul_zero _)]

/-- Two polynomials with torsion-free module coefficients are equal if their values agree
at every point of the infinite scalar domain. -/
theorem eq_of_forall_eval_eq {R M : Type*} [CommRing R] [IsDomain R] [Infinite R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] {p q : PolynomialModule R M}
    (h : ∀ x : R, eval x p = eval x q) : p = q := by
  let d := (p.coeff.support ∪ q.coeff.support).sup id + 1
  have hsub : p.coeff.support ∪ q.coeff.support ⊆ Finset.range d := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hp := Finset.subset_union_left.trans hsub
  have hq := Finset.subset_union_right.trans hsub
  refine coeff_injective (Finsupp.ext fun i ↦ ?_)
  by_cases hi : i < d
  · exact TauCeti.eq_of_forall_sum_range_pow_smul_eq (fun x ↦ by
      simpa only [p.eval_eq_sum_range x hp, q.eval_eq_sum_range x hq] using h x) hi
  · rw [Finsupp.notMem_support_iff.mp (fun hm ↦ hi (Finset.mem_range.mp (hp hm))),
      Finsupp.notMem_support_iff.mp (fun hm ↦ hi (Finset.mem_range.mp (hq hm)))]

end PolynomialModule
