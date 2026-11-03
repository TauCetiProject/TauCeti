/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Tangent cones of products

Mathlib shows that the tangent cone of a product `s ×ˢ t` contains the tangent cones of the two
factors, embedded along the coordinate axes (`subset_tangentConeAt_prod_left`,
`subset_tangentConeAt_prod_right`). This file bounds it from above by the product of the tangent
cones of the factors, and shows that for convex sets the positive tangent cone of the product is
exactly the product of the positive tangent cones. The ranges of real models with corners are
convex, so this computes the positive tangent cones of product models, from which the depth of a
point of a product of manifolds with corners is read.

## Main results

* `TauCeti.tangentConeAt_prod_subset`: the tangent cone of a product lies in the product of the
  tangent cones.
* `Convex.posTangentConeAt_prod`: for convex sets the positive tangent cone of the product is the
  product of the positive tangent cones.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- The tangent cone of a product of sets is contained in the product of the tangent cones of the
factors. -/
theorem tangentConeAt_prod_subset {R E F : Type*} [AddCommGroup E] [SMul R E]
    [TopologicalSpace E] [AddCommGroup F] [SMul R F] [TopologicalSpace F] {s : Set E} {t : Set F}
    {x : E} {y : F} :
    tangentConeAt R (s ×ˢ t) (x, y) ⊆ tangentConeAt R s x ×ˢ tangentConeAt R t y := by
  intro v hv
  obtain ⟨α, l, hl, c, d, hd₀, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  refine ⟨mem_tangentConeAt_of_seq l c (fun n ↦ (d n).1) ?_ (hds.mono fun n hn ↦ hn.1) ?_,
    mem_tangentConeAt_of_seq l c (fun n ↦ (d n).2) ?_ (hds.mono fun n hn ↦ hn.2) ?_⟩
  · simpa [Function.comp_def] using (continuous_fst.tendsto _).comp hd₀
  · simpa [Function.comp_def] using (continuous_fst.tendsto _).comp hcd
  · simpa [Function.comp_def] using (continuous_snd.tendsto _).comp hd₀
  · simpa [Function.comp_def] using (continuous_snd.tendsto _).comp hcd

end TauCeti

/-- For convex sets containing the base points, the positive tangent cone of the product is the
product of the positive tangent cones. -/
@[simp]
theorem Convex.posTangentConeAt_prod {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {t : Set F} (hs : Convex ℝ s)
    (ht : Convex ℝ t) {x : E} {y : F} (hx : x ∈ s) (hy : y ∈ t) :
    posTangentConeAt (s ×ˢ t) (x, y) = posTangentConeAt s x ×ˢ posTangentConeAt t y := by
  refine TauCeti.tangentConeAt_prod_subset.antisymm ?_
  rintro ⟨v, w⟩ ⟨hv, hw⟩
  obtain ⟨α, l₁, hl₁, c₁, d₁, hd₁, hds₁, hcd₁⟩ := exists_fun_of_mem_tangentConeAt hv
  obtain ⟨β, l₂, hl₂, c₂, d₂, hd₂, hds₂, hcd₂⟩ := exists_fun_of_mem_tangentConeAt hw
  -- Both families are rescaled to the larger of the two scalars. The rescaling ratios lie in
  -- `[0, 1]`, so by convexity the rescaled vectors still point from `x` and `y` into `s` and `t`.
  let C : α × β → NNReal := fun p ↦ max (c₁ p.1) (c₂ p.2)
  have hle₁ (p : α × β) : c₁ p.1 / C p ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) zero_le
  have hle₂ (p : α × β) : c₂ p.2 / C p ≤ 1 := div_le_one_of_le₀ (le_max_right _ _) zero_le
  refine mem_tangentConeAt_of_seq (l₁ ×ˢ l₂) C
    (fun p ↦ ((c₁ p.1 / C p) • d₁ p.1, (c₂ p.2 / C p) • d₂ p.2)) ?_ ?_ ?_
  · have hb (r : α × β → NNReal) (hr : ∀ p, r p ≤ 1) :
        IsBoundedUnder (· ≤ ·) (l₁ ×ˢ l₂) (norm ∘ fun p ↦ (r p : ℝ)) :=
      isBoundedUnder_of ⟨1, fun p ↦ by simpa using hr p⟩
    rw [← Prod.mk_zero_zero]
    simp only [NNReal.smul_def]
    exact ((hb _ hle₁).smul_tendsto_zero (hd₁.comp tendsto_fst)).prodMk_nhds
      ((hb _ hle₂).smul_tendsto_zero (hd₂.comp tendsto_snd))
  · filter_upwards [tendsto_fst.eventually hds₁, tendsto_snd.eventually hds₂] with p hp₁ hp₂
    exact ⟨by simpa [NNReal.smul_def] using hs.add_smul_mem hx hp₁ ⟨NNReal.coe_nonneg _, hle₁ p⟩,
      by simpa [NNReal.smul_def] using ht.add_smul_mem hy hp₂ ⟨NNReal.coe_nonneg _, hle₂ p⟩⟩
  · have hC (p : α × β) : C p • ((c₁ p.1 / C p) • d₁ p.1, (c₂ p.2 / C p) • d₂ p.2) =
        (c₁ p.1 • d₁ p.1, c₂ p.2 • d₂ p.2) := by
      rw [Prod.smul_mk, smul_smul, smul_smul,
        mul_div_cancel_of_imp' fun h ↦ le_antisymm ((le_max_left _ _).trans_eq h) zero_le,
        mul_div_cancel_of_imp' fun h ↦ le_antisymm ((le_max_right _ _).trans_eq h) zero_le]
    simp only [hC]
    exact (hcd₁.comp tendsto_fst).prodMk_nhds (hcd₂.comp tendsto_snd)
