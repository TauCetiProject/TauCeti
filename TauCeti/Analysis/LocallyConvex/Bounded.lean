/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Von Neumann boundedness helpers

A product `s ×ˢ t` of von Neumann bounded subsets of two topological spaces with a `𝕜`-action is
von Neumann bounded in the product space (`Bornology.IsVonNBounded.prod`, used to check the
boundedness condition in Mathlib's `Bundle.RiemannianMetric` for the product of two Riemannian
metrics).

The translate `(p + ·) ⁻¹' s` of a von Neumann bounded set is von Neumann bounded
(`Bornology.IsVonNBounded.preimage_add`). This is used to transport Mathlib's gauge, which is
centred at `0`, to an arbitrary centre.

Moreover, the norms of a continuous semilinear map into a seminormed space are bounded above on
any von Neumann bounded set (`Bornology.IsVonNBounded.bddAbove_range_norm_apply`).
-/

public section

open Set

namespace Bornology

section Prod

variable {𝕜 E F : Type*} [SeminormedRing 𝕜]
  [Zero E] [SMul 𝕜 E] [TopologicalSpace E] [Zero F] [SMul 𝕜 F] [TopologicalSpace F]

/-- A product of von Neumann bounded sets is von Neumann bounded. -/
protected theorem IsVonNBounded.prod {s : Set E} {t : Set F} (hs : IsVonNBounded 𝕜 s)
    (ht : IsVonNBounded 𝕜 t) : IsVonNBounded 𝕜 (s ×ˢ t) := by
  intro W hW
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
  filter_upwards [(hs hU).eventually, (ht hV).eventually] with a ha hb
  grw [← hUV, smul_set_prod, ha, hb]

end Prod

/-- The translate of a von Neumann bounded set is von Neumann bounded. -/
protected theorem IsVonNBounded.preimage_add {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hb : IsVonNBounded 𝕜 s) (p : E) : IsVonNBounded 𝕜 ((p + ·) ⁻¹' s) := by
  simpa [← image_vadd, image_add_left] using hb.vadd (-p)

section Normed

variable {𝕜₁ 𝕜₂ E F : Type*} [NormedDivisionRing 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} [RingHomSurjective σ] [RingHomIsometric σ]
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- The norms of a continuous semilinear map into a seminormed space are bounded above on any
von Neumann bounded set. -/
protected theorem IsVonNBounded.bddAbove_range_norm_apply {s : Set E} (hs : IsVonNBounded 𝕜₁ s)
    (f : E →SL[σ] F) :
    BddAbove (Set.range fun x : s ↦ ‖f x‖) := by
  obtain ⟨r, hr⟩ := (NormedSpace.image_isVonNBounded_iff 𝕜₂).1 (hs.image f)
  exact ⟨r, Set.forall_mem_range.2 fun x ↦ hr x x.property⟩

end Normed

end Bornology
