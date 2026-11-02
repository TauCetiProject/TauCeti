/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading

/-!
# The degree filtration of a symmetric algebra and its grading

The degree filtration of `SymmetricAlgebra R M` is the word filtration
`TauCeti.Algebra.wordFiltration` of the generator map: its `k`-th step is spanned by the products of
at most `k` generators. Since every such product is homogeneous of degree at most `k`, an element of
the `k`-th step has no homogeneous component of degree above `k`
(`TauCeti.SymmetricAlgebra.coe_decompose_eq_zero_of_mem_wordFiltration`). In particular a nonzero
homogeneous element of degree `n` does not have degree below `n`
(`TauCeti.SymmetricAlgebra.disjoint_homogeneousSubmodule_wordFiltrationPrevious`), which is how
leading terms are read off in degree inductions on the symmetric algebra.

## Main results

* `TauCeti.SymmetricAlgebra.coe_decompose_eq_zero_of_mem_wordFiltration`: an element of degree at
  most `k` has zero homogeneous component in every degree above `k`.
* `TauCeti.SymmetricAlgebra.disjoint_homogeneousSubmodule_wordFiltrationPrevious`: the homogeneous
  elements of degree `n` meet the elements of degree below `n` only in zero.
-/

public section

namespace TauCeti.SymmetricAlgebra

open TauCeti.Algebra

universe u v

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- **An element of degree at most `k` has no homogeneous component above `k`**: if `x` lies in the
`k`-th step of the degree filtration of the symmetric algebra and `k < n`, then the degree-`n`
homogeneous component of `x` is zero. -/
theorem coe_decompose_eq_zero_of_mem_wordFiltration {k n : ℕ} (hkn : k < n)
    {x : _root_.SymmetricAlgebra R M} (hx : x ∈ wordFiltration (_root_.SymmetricAlgebra.ι R M) k) :
    (DirectSum.decompose (homogeneousSubmodule R M) x n : _root_.SymmetricAlgebra R M) = 0 := by
  rw [wordFiltration_eq_iSup_pow] at hx
  induction hx using Submodule.iSup_induction' with
  | mem i y hy =>
      exact DirectSum.decompose_of_mem_ne _ hy (i.2.trans_lt hkn).ne
  | zero => simp
  | add y z _ _ hy hz => simp [DirectSum.decompose_add, hy, hz]

/-- **A homogeneous element of degree `n` has degree below `n` only if it is zero**: the degree-`n`
homogeneous submodule of the symmetric algebra is disjoint from the step of the degree filtration
preceding degree `n`. -/
theorem disjoint_homogeneousSubmodule_wordFiltrationPrevious (n : ℕ) :
    Disjoint (homogeneousSubmodule R M n)
      (wordFiltrationPrevious (_root_.SymmetricAlgebra.ι R M) n) := by
  refine Submodule.disjoint_def.mpr fun x hxn hx ↦ ?_
  cases n with
  | zero => rwa [wordFiltrationPrevious_zero, Submodule.mem_bot] at hx
  | succ k =>
      rw [wordFiltrationPrevious_succ] at hx
      rw [← DirectSum.decompose_of_mem_same _ hxn]
      exact coe_decompose_eq_zero_of_mem_wordFiltration (Nat.lt_succ_self k) hx

end TauCeti.SymmetricAlgebra
