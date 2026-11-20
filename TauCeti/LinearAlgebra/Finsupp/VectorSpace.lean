/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The basis of a direct sum

Mathlib's `DFinsupp.basis` collects bases `b i` of modules `M i` into a basis of `Π₀ i, M i`,
indexed by `Σ i, η i`. This file records its vectors and coordinates, as Mathlib's
`Finsupp.coe_basis` and `Finsupp.basis_repr` do for `Finsupp.basis`.

## Main results

* `DFinsupp.basis_apply`: the basis vector of index `⟨i, x⟩` is `DFinsupp.single i (b i x)`.
* `DFinsupp.basis_repr`: the coordinate of index `⟨i, x⟩` is the `x`-th coordinate of the `i`-th
  component in the basis `b i`.
-/

public section

namespace DFinsupp

variable {ι R : Type*} {M : ι → Type*} [Semiring R] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] {η : ι → Type*}

/-- **The coordinates in the basis of a direct sum are the coordinates of the components.** -/
@[simp]
theorem basis_repr (b : ∀ i, Module.Basis (η i) R (M i)) (g : Π₀ i, M i) (ix : Σ i, η i) :
    (DFinsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl

/-- **The vectors of the basis of a direct sum are the basis vectors of the components.** -/
@[simp]
theorem basis_apply [DecidableEq ι] (b : ∀ i, Module.Basis (η i) R (M i)) (ix : Σ i, η i) :
    DFinsupp.basis b ix = DFinsupp.single ix.1 (b ix.1 ix.2) := by
  obtain ⟨i, x⟩ := ix
  refine Module.Basis.apply_eq_iff.mpr (Finsupp.ext fun ⟨j, y⟩ => ?_)
  rw [basis_repr]
  by_cases h : i = j
  · subst h
    simp [Finsupp.single_apply_left sigma_mk_injective]
  · simp [h]

end DFinsupp
