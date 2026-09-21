/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Vanishing off the index set of a function antidiagonal

`Finset.piAntidiag s n` is the finset of functions with support contained in `s` whose values sum
to `n` over `s`.  Such a function therefore vanishes at every point outside `s`.

## Main results

* `Finset.eq_zero_of_notMem_of_mem_piAntidiag`: a member of `Finset.piAntidiag s n` vanishes off
  `s`.
-/

public section

namespace Finset

variable {ι μ : Type*} [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]
  {s : Finset ι} {n : μ} {f : ι → μ} {i : ι}

/-- A function in `Finset.piAntidiag s n` has support contained in `s`, so it takes the value `0`
at every point outside `s`. -/
theorem eq_zero_of_notMem_of_mem_piAntidiag (hi : i ∉ s) (hf : f ∈ piAntidiag s n) : f i = 0 :=
  not_not.1 fun h ↦ hi ((mem_piAntidiag.1 hf).2 i h)

end Finset
