/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Basic

/-!
# Pivot maps of triangular families

If `f (π i) (z j) = 0` for `i < j` while `f (π j) (z j) ≠ 0`, then the pivot map `π` is injective
(`Function.Injective.of_triangular`). This is the distinctness of the pivot rows in a triangular
family, as produced by Gaussian elimination.
-/

public section

/-- The pivot rows of a triangular family are distinct: if `f (π i) (z j) = 0` for `i < j` while
`f (π j) (z j) ≠ 0`, then `π` is injective. -/
theorem Function.Injective.of_triangular {ι κ M N : Type*} [LinearOrder ι] [Zero N]
    {f : κ → M → N} {z : ι → M} {π : ι → κ} (h₀ : ∀ i j, i < j → f (π i) (z j) = 0)
    (hp : ∀ j, f (π j) (z j) ≠ 0) : Function.Injective π := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hp j (hij ▸ h₀ i j h)
  · exact hp i (hij.symm ▸ h₀ j i h)
