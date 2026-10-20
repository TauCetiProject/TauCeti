/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic

/-!
# Fibers of convex subsets of products

For a convex set `s ⊆ V × W`, each fiber `Prod.mk v ⁻¹' s` is convex, and a convex combination
of two fibers, formed by pointwise Minkowski operations, lies in the fiber over the
corresponding convex combination of base points. The second inclusion is the set-level input
for Brunn's concavity principle, which compares fiber volumes by the Brunn–Minkowski inequality.
-/

public section

open Set
open scoped Pointwise

variable {𝕜 V W : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid V] [Module 𝕜 V] [AddCommMonoid W] [Module 𝕜 W] {s : Set (V × W)}

/-- The fibers of a convex subset of a product are convex. -/
theorem Convex.preimage_prodMk (hs : Convex 𝕜 s) (v : V) : Convex 𝕜 (Prod.mk v ⁻¹' s) := by
  intro y hy z hz a b ha hb hab
  simpa only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk, Convex.combo_self hab] using
    hs hy hz ha hb hab

/-- A convex combination of two fibers of a convex set lies in the fiber over the convex
combination of the base points. -/
theorem Convex.smul_preimage_prodMk_add_smul_preimage_prodMk_subset (hs : Convex 𝕜 s) (p q : V)
    {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • (Prod.mk p ⁻¹' s) + b • (Prod.mk q ⁻¹' s) ⊆ Prod.mk (a • p + b • q) ⁻¹' s := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
  simpa only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk] using hs hy hz ha hb hab
