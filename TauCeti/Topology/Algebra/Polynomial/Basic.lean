/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Continuity of polynomial families

For a family of polynomials `f x` over a topological semiring, indexed by a parameter `x`, the
coefficients of a product are finite sums of products of coefficients of the factors. Hence if
every coefficient of each factor is continuous at a point, so is every coefficient of the product.
This is used to treat the product of a finite family of polynomials with continuous coefficients
as a single polynomial family.

If the degrees of the family are bounded and its coefficients are continuous, then the evaluation
`(x, t) ↦ (f x).eval t` is jointly continuous, since it is a finite sum of products of
coefficients with powers of `t`.

## Main results

* `Polynomial.continuousAt_coeff_mul`: coefficients of a product of two families.
* `Polynomial.continuousAt_coeff_prod`: coefficients of a finite product of families.
* `Polynomial.continuous_eval_of_continuous_coeff`: joint continuity of the evaluation of a family
  of bounded degree.
-/

public section

open Filter Topology

namespace Polynomial

variable {X R ι : Type*} [TopologicalSpace X] [CommSemiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] {x₀ : X}

/-- If every coefficient of two polynomial families is continuous at `x₀`, then so is every
coefficient of their product. -/
theorem continuousAt_coeff_mul {f g : X → R[X]}
    (hf : ∀ i, ContinuousAt (fun x => (f x).coeff i) x₀)
    (hg : ∀ i, ContinuousAt (fun x => (g x).coeff i) x₀) (i : ℕ) :
    ContinuousAt (fun x => (f x * g x).coeff i) x₀ := by
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun p _ => (hf p.1).mul (hg p.2)

/-- If every coefficient of each member of a finite family of polynomial families is continuous at
`x₀`, then so is every coefficient of their product. -/
theorem continuousAt_coeff_prod {f : ι → X → R[X]} (s : Finset ι)
    (hf : ∀ k ∈ s, ∀ i, ContinuousAt (fun x => (f k x).coeff i) x₀) (i : ℕ) :
    ContinuousAt (fun x => (∏ k ∈ s, f k x).coeff i) x₀ := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty =>
    simp only [Finset.prod_empty]
    exact continuousAt_const
  | insert k s hk ih =>
    simp only [Finset.prod_insert hk]
    exact continuousAt_coeff_mul (hf k (Finset.mem_insert_self k s))
      (ih fun l hl => hf l (Finset.mem_insert_of_mem hl)) i

/-- If a family of polynomials has degree at most `d` and its coefficients of index at most `d` are
continuous, then its evaluation is jointly continuous in the parameter and the point. -/
theorem continuous_eval_of_continuous_coeff {f : X → R[X]} {d : ℕ}
    (hf : ∀ i ≤ d, Continuous fun x => (f x).coeff i) (hd : ∀ x, (f x).natDegree ≤ d) :
    Continuous fun z : X × R => (f z.1).eval z.2 := by
  simp_rw [fun z : X × R => eval_eq_sum_range' (Nat.lt_succ_of_le (hd z.1)) z.2]
  exact continuous_finsetSum _ fun i hi =>
    ((hf i (Finset.mem_range_succ_iff.1 hi)).comp continuous_fst).mul (continuous_snd.pow i)

end Polynomial
