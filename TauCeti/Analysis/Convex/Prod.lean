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

A strip `|u.1| < a` of a product `𝕜 × W` is convex (`TauCeti.convex_setOf_abs_fst_lt`). Convexity
transfers between subsets of `V × 𝕜` that correspond under a nonzero rescaling of the height
coordinate (`TauCeti.convex_of_height_scale`).
-/

public section

open Set
open scoped Pointwise

variable {𝕜 V W : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid V] [AddCommMonoid W] [SMul 𝕜 W] {s : Set (V × W)}

/-- The fibers of a convex subset of a product are convex. -/
theorem Convex.preimage_prodMk [Module 𝕜 V] (hs : Convex 𝕜 s) (v : V) :
    Convex 𝕜 (Prod.mk v ⁻¹' s) := by
  intro y hy z hz a b ha hb hab
  simpa only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk, Convex.combo_self hab] using
    hs hy hz ha hb hab

/-- A convex combination of two fibers of a convex set lies in the fiber over the convex
combination of the base points. -/
theorem Convex.smul_preimage_prodMk_add_smul_preimage_prodMk_subset [SMul 𝕜 V] (hs : Convex 𝕜 s)
    (p q : V) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • (Prod.mk p ⁻¹' s) + b • (Prod.mk q ⁻¹' s) ⊆ Prod.mk (a • p + b • q) ⁻¹' s := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
  simpa only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk] using hs hy hz ha hb hab

namespace TauCeti

/-- A strip `|u.1| < a` of a product `𝕜 × W` is convex. -/
theorem convex_setOf_abs_fst_lt {𝕜 W : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid W] [SMul 𝕜 W] (a : 𝕜) : Convex 𝕜 {u : 𝕜 × W | |u.1| < a} := by
  have : {u : 𝕜 × W | |u.1| < a} = Ioo (-a) a ×ˢ univ := by
    ext v; simp [abs_lt]
  exact this ▸ (convex_Ioo (-a) a).prod convex_univ

/-- Rescaling the height coordinate by a nonzero scalar `r` transfers convexity from a subset of
`V × 𝕜` to any subset that corresponds to it under that rescaling. -/
theorem convex_of_height_scale {𝕜 V : Type*} [Semifield 𝕜] [PartialOrder 𝕜] [AddCommMonoid V]
    [SMul 𝕜 V] {s t : Set (V × 𝕜)} {r : 𝕜} (hr : r ≠ 0) (hst : ∀ x τ, (x, τ) ∈ s ↔ (x, r * τ) ∈ t)
    (h : Convex 𝕜 s) : Convex 𝕜 t := by
  intro p hp q hq a b ha hb hab
  -- Undoing the rescaling of the height coordinate pulls points of `t` back to `s`.
  have hback (u : V × 𝕜) (hu : u ∈ t) : (u.1, r⁻¹ * u.2) ∈ s :=
    (hst _ _).2 (by simpa [mul_inv_cancel_left₀ hr] using hu)
  convert (hst _ _).1 (h (hback p hp) (hback q hq) ha hb hab) using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp

end TauCeti
