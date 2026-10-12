/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Linear currying for direct sums

The linear equivalence `DirectSum.sigmaLcurryEquiv` groups a direct sum indexed by a dependent
pair into an iterated direct sum. This file supplies its coordinate formula and its forward and
inverse formulas on generators, so regrouping summands can be calculated without unfolding the
equivalence.

These formulas use Mathlib's `DirectSum.sigmaLcurry_apply` and `DirectSum.sigmaCurry_of`.
-/

public section

open scoped DirectSum

namespace DirectSum

variable {R ι : Type*} [Semiring R] {α : ι → Type*} {δ : ∀ i, α i → Type*}
  [DecidableEq ι] [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)]

/-- The coefficient of a curried direct sum at `i, j` is its original coefficient at `⟨i, j⟩`. -/
@[simp]
theorem sigmaLcurryEquiv_apply (x : ⨁ z : Σ i, α i, δ z.1 z.2) (i : ι) (j : α i) :
    sigmaLcurryEquiv R (δ := δ) x i j = x ⟨i, j⟩ := by
  -- Mathlib defines the equivalence through `DFinsupp.sigmaCurryLEquiv`; its forward function
  -- is `DFinsupp.sigmaCurry`, the same function as the linear map `DirectSum.sigmaLcurry`.
  exact sigmaLcurry_apply R x i j

/-- Linear currying sends the generator at `⟨i, j⟩` to the iterated generator at `i, j`. -/
@[simp]
theorem sigmaLcurryEquiv_lof [∀ i, DecidableEq (α i)] (i : ι) (j : α i) (x : δ i j) :
    sigmaLcurryEquiv R (δ := δ)
        (lof R (Σ i, α i) (fun z ↦ δ z.1 z.2) ⟨i, j⟩ x) =
      lof R ι (fun i ↦ ⨁ j, δ i j) i (lof R (α i) (δ i) j x) := by
  ext k l
  rw [sigmaLcurryEquiv_apply]
  simpa only [sigmaCurry_apply, lof_eq_of] using
    congrArg (fun y : ⨁ i, ⨁ j, δ i j ↦ y k l) (sigmaCurry_of (δ := δ) ⟨i, j⟩ x)

/-- Inverse linear currying sends an iterated generator at `i, j` to the generator at `⟨i, j⟩`. -/
@[simp]
theorem sigmaLcurryEquiv_symm_lof_lof [∀ i, DecidableEq (α i)]
    (i : ι) (j : α i) (x : δ i j) :
    (sigmaLcurryEquiv R (δ := δ)).symm
        (lof R ι (fun i ↦ ⨁ j, δ i j) i (lof R (α i) (δ i) j x)) =
      lof R (Σ i, α i) (fun z ↦ δ z.1 z.2) ⟨i, j⟩ x := by
  rw [LinearEquiv.symm_apply_eq]
  exact (sigmaLcurryEquiv_lof i j x).symm

end DirectSum
