/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sion

/-!
# Helpers for real-valued applications of Sion's minimax theorem

Mathlib's infimum-supremum form of Sion's theorem uses a complete linear order as its codomain.
Real-valued affine functions are therefore commonly coerced to `EReal`. This file records that
convexity and concavity of the real function give the corresponding quasiconvexity and
quasiconcavity after coercion, together with a small criterion recognizing both properties from
the affine combination identity.

These lemmas let finite-dimensional minimax arguments keep their elementary algebra over `ℝ`
while using `EReal` only for the outer extrema.

## References

* M. Sion, *On general minimax theorems*, Pacific J. Math. 8 (1958), 171--176.
* `Mathlib.Topology.Sion`, formalized by Antoine Chambert-Loir and Anatole Dedecker.
-/

public section

open Set

namespace TauCeti

/-- A real-valued convex function is quasiconvex after coercion to `EReal`. -/
theorem _root_.ConvexOn.quasiconvexOn_ereal_coe {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} {g : E → ℝ} (hg : ConvexOn ℝ s g) :
    QuasiconvexOn ℝ s fun x ↦ ((g x : ℝ) : EReal) := by
  intro r
  induction r with
  | bot =>
    have hs : {x ∈ s | ((g x : ℝ) : EReal) ≤ ⊥} = ∅ := by ext x; simp [le_bot_iff]
    rw [hs]
    exact convex_empty
  | coe a =>
    have hs : {x ∈ s | ((g x : ℝ) : EReal) ≤ (a : EReal)} = {x ∈ s | g x ≤ a} := by
      ext x
      simp
    rw [hs]
    exact hg.convex_le a
  | top =>
    have hs : {x ∈ s | ((g x : ℝ) : EReal) ≤ ⊤} = s := by ext x; simp
    rw [hs]
    exact hg.1

/-- A real-valued concave function is quasiconcave after coercion to `EReal`. -/
theorem _root_.ConcaveOn.quasiconcaveOn_ereal_coe {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} {g : E → ℝ} (hg : ConcaveOn ℝ s g) :
    QuasiconcaveOn ℝ s fun x ↦ ((g x : ℝ) : EReal) := by
  intro r
  induction r with
  | bot =>
    have hs : {x ∈ s | (⊥ : EReal) ≤ ((g x : ℝ) : EReal)} = s := by ext x; simp
    rw [hs]
    exact hg.1
  | coe a =>
    have hs : {x ∈ s | (a : EReal) ≤ ((g x : ℝ) : EReal)} = {x ∈ s | a ≤ g x} := by
      ext x
      simp
    rw [hs]
    exact hg.convex_ge a
  | top =>
    have hs : {x ∈ s | (⊤ : EReal) ≤ ((g x : ℝ) : EReal)} = ∅ := by ext x; simp [top_le_iff]
    rw [hs]
    exact convex_empty

/-- A function preserving the convex combinations of points of a convex set is both convex and
concave there. Only the combinations used by `ConvexOn` and `ConcaveOn` are required, so the
identity may fail off `s` and for coefficients outside `[0, 1]`. -/
theorem _root_.Convex.convexOn_and_concaveOn_of_affine {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} (hs : Convex ℝ s) {g : E → ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      g (a • x + b • y) = a * g x + b * g y) :
    ConvexOn ℝ s g ∧ ConcaveOn ℝ s g :=
  ⟨⟨hs, fun x hx y hy a b ha hb hab ↦ by rw [h x hx y hy a b ha hb hab]; simp⟩,
    ⟨hs, fun x hx y hy a b ha hb hab ↦ by rw [h x hx y hy a b ha hb hab]; simp⟩⟩

end TauCeti
