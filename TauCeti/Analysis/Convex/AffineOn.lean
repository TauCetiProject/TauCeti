/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function

/-!
# Functions that are both convex and concave

On a convex set `s`, a function is both convex and concave exactly when it preserves the convex
combinations of points of `s`: `f (a • x + b • y) = a • f x + b • f y` for `x, y ∈ s` and
`a, b ≥ 0` with `a + b = 1`. This recognizes the two properties from the affine combination
identity, for instance for a Lagrangian that is affine in each variable separately, whose
convexity and concavity feed Sion's minimax theorem.
-/

public section

variable {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
  [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β] {s : Set E} {f : E → β}

/-- On a convex set, a function is both convex and concave if and only if it preserves the
convex combinations of points of the set. The identity is only required for the combinations
used by `ConvexOn` and `ConcaveOn`, so it may fail off `s` and for coefficients outside
`[0, 1]`. -/
theorem Convex.convexOn_and_concaveOn_iff (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f ∧ ConcaveOn 𝕜 s f ↔
      ∀ x ∈ s, ∀ y ∈ s, ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a • x + b • y) = a • f x + b • f y :=
  ⟨fun h _ hx _ hy _ _ ha hb hab ↦ (h.1.2 hx hy ha hb hab).antisymm (h.2.2 hx hy ha hb hab),
    fun h ↦ ⟨⟨hs, fun x hx y hy a b ha hb hab ↦ (h x hx y hy a b ha hb hab).le⟩,
      ⟨hs, fun x hx y hy a b ha hb hab ↦ (h x hx y hy a b ha hb hab).ge⟩⟩⟩
