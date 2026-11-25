/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Products and translates of von Neumann bounded sets

A product `s ×ˢ t` of von Neumann bounded subsets of two topological spaces with a `𝕜`-action is
von Neumann bounded in the product space. This is used to check the boundedness condition in
Mathlib's `Bundle.RiemannianMetric` for the product of two Riemannian metrics.

The translate `(p + ·) ⁻¹' s` of a von Neumann bounded set is von Neumann bounded
(`Bornology.IsVonNBounded.preimage_add`). This is used to transport Mathlib's gauge, which is
centred at `0`, to an arbitrary centre.
-/

public section

open Set

namespace Bornology

variable {𝕜 E F : Type*} [SeminormedRing 𝕜]
  [Zero E] [SMul 𝕜 E] [TopologicalSpace E] [Zero F] [SMul 𝕜 F] [TopologicalSpace F]

/-- A product of von Neumann bounded sets is von Neumann bounded. -/
protected theorem IsVonNBounded.prod {s : Set E} {t : Set F} (hs : IsVonNBounded 𝕜 s)
    (ht : IsVonNBounded 𝕜 t) : IsVonNBounded 𝕜 (s ×ˢ t) := by
  intro W hW
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
  filter_upwards [(hs hU).eventually, (ht hV).eventually] with a ha hb
  grw [← hUV, smul_set_prod, ha, hb]

/-- The translate of a von Neumann bounded set is von Neumann bounded. -/
protected theorem IsVonNBounded.preimage_add {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hb : IsVonNBounded 𝕜 s) (p : E) : IsVonNBounded 𝕜 ((p + ·) ⁻¹' s) := by
  simpa [← image_vadd, image_add_left] using hb.vadd (-p)

end Bornology
