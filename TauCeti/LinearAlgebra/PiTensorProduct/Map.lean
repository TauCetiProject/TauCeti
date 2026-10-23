/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Sums of tensor maps differing in one factor

Mathlib's `PiTensorProduct.map_update_add` says that `PiTensorProduct.map` is additive in each
factor. This file records the form of that statement used when two tensor maps are compared
directly: if two families of linear maps agree away from one index `k`, then the sum of their
tensor maps is the tensor map of the family whose `k`-th factor is the sum of the two `k`-th
factors.

## Main results

* `TauCeti.PiTensorProduct.map_add_map_eq_map_update`: the sum of two tensor maps whose factors
  agree away from one index.
-/

public section

universe uι uR us ut

namespace TauCeti.PiTensorProduct

variable {ι : Type uι} {R : Type uR} {s : ι → Type us} {t : ι → Type ut} [DecidableEq ι]
  [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)] [∀ i, AddCommMonoid (t i)]
  [∀ i, Module R (t i)]

/-- Two tensor maps whose factors agree away from one index `k` add up to the tensor map with the
sum of their factors at `k`. -/
theorem map_add_map_eq_map_update (f g : ∀ i, s i →ₗ[R] t i) (k : ι)
    (h : ∀ i, i ≠ k → f i = g i) :
    PiTensorProduct.map f + PiTensorProduct.map g =
      PiTensorProduct.map (Function.update f k (f k + g k)) := by
  have hg : g = Function.update f k (g k) := by
    funext i
    by_cases hi : i = k
    · subst hi
      simp
    · simp [Function.update_of_ne hi, h i hi]
  rw [PiTensorProduct.map_update_add, Function.update_eq_self, ← hg]

end TauCeti.PiTensorProduct
