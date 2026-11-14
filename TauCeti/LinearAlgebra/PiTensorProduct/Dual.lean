/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
# Pure tensors of nonzero vectors

Over a nontrivial commutative semiring without zero divisors, such as an integral domain, a pure
tensor `⨂ₜ i, v i` of nonzero vectors of finitely many projective modules, for instance of vector
spaces over a field, is nonzero. Each `v i` is detected by a linear form
`f i` with `f i (v i) ≠ 0`, and the product form `PiTensorProduct.dualDistrib (⨂ₜ i, f i)` takes
the value `∏ i, f i (v i) ≠ 0` on the pure tensor.

Over a ring with zero divisors this fails: over `ℤ/4`, the tensor square of `ℤ/4` is `ℤ/4`, and
`2 ⊗ 2 = 4 = 0` although `2 ≠ 0`.

## Main results

* `PiTensorProduct.tprod_ne_zero`: a pure tensor of nonzero vectors of finitely many projective
  modules over a nontrivial commutative semiring without zero divisors is nonzero.
* `PiTensorProduct.tprod_eq_zero_iff`: such a pure tensor vanishes exactly when one of its factors
  does.
-/

public section

namespace PiTensorProduct

open Module

variable {ι R : Type*} [Finite ι] [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Projective R (M i)]

/-- **A pure tensor of nonzero vectors is nonzero**, for a finite family of projective modules over
a nontrivial commutative semiring without zero divisors, such as an integral domain. -/
theorem tprod_ne_zero {v : ∀ i, M i} (hv : ∀ i, v i ≠ 0) : tprod R v ≠ 0 := by
  have := Fintype.ofFinite ι
  choose f hf using fun i ↦ Projective.exists_dual_ne_zero R (hv i)
  intro h
  have := congrArg (dualDistrib (tprod R f)) h
  rw [dualDistrib_apply, map_zero] at this
  exact Finset.prod_ne_zero_iff.2 (fun i _ ↦ hf i) this

/-- Over a nontrivial commutative semiring without zero divisors, such as an integral domain, a pure
tensor of vectors of finitely many projective modules is zero exactly when one of the vectors is
zero. -/
@[simp]
theorem tprod_eq_zero_iff {v : ∀ i, M i} : tprod R v = 0 ↔ ∃ i, v i = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ (tprod R).map_coord_zero i hi⟩
  by_contra hv
  exact tprod_ne_zero (fun i hi ↦ hv ⟨i, hi⟩) h

end PiTensorProduct
