/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Submodules of multivariate polynomial rings

Basic membership criterion for submodules of `MvPolynomial ι R` in terms of monomials.

## Main results

* `MvPolynomial.mem_submodule_of_forall_monomial_mem`: a submodule of `MvPolynomial ι R` containing
  every monomial `monomial α 1` in the support of `p` contains `p`.
-/

public section

namespace MvPolynomial

/-- A submodule of `MvPolynomial ι R` containing every monomial occurring in `p` contains `p`. -/
theorem mem_submodule_of_forall_monomial_mem {R ι : Type*} [CommSemiring R]
    {N : Submodule R (MvPolynomial ι R)} {p : MvPolynomial ι R}
    (h : ∀ α ∈ p.support, monomial α (1 : R) ∈ N) : p ∈ N := by
  rw [p.as_sum]
  exact N.sum_mem fun α hα ↦ by simpa [smul_monomial] using N.smul_mem _ (h α hα)

end MvPolynomial
