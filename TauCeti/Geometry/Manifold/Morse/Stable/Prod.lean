/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality

/-!
# Products of Morse–Smale pseudo-gradients

Let `X` and `Y` be pseudo-gradients adapted to Morse functions `f` on `M` and `g` on `N`, both
satisfying the Morse–Smale condition. This file shows that the product pseudo-gradient
`(x, y) ↦ (X x, Y y)`, adapted to the separated sum `f ∘ Prod.fst + g ∘ Prod.snd`
(`TauCeti.IsAdaptedPseudoGradient.prod`), satisfies the Morse–Smale condition too
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`).

The unstable and stable manifolds of the product are products
(`TauCeti.IsAdaptedPseudoGradient.unstableSet_prod`,
`TauCeti.IsAdaptedPseudoGradient.stableSet_prod`), and the tangent space of a product of sets
contains the product of their tangent spaces. At a common point `z`, the tangent spaces of
`W^u(a) ∩ W^s(b)` therefore contain the products of those of the factors, which span `E` and `E'`
by transversality in each factor, so together they span `E × E'`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 2 (the Morse complex of a product).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance 10] prodNormedChartedSpace
attribute [local instance] isManifold_prodNormedChartedSpace

variable {E E' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N]

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {Y : (y : N) → TangentSpace 𝓘(ℝ, E') y} {hX : IsAdaptedPseudoGradient f X}
  {hY : IsAdaptedPseudoGradient g Y}

/-- **Products of Morse–Smale pseudo-gradients are Morse–Smale.** If the pseudo-gradients `X` and
`Y`, adapted to the Morse functions `f` and `g`, satisfy the Morse–Smale condition, so does the
product pseudo-gradient, adapted to the separated sum `f ∘ Prod.fst + g ∘ Prod.snd`. -/
theorem IsMorseSmale.prod (h₁ : hX.IsMorseSmale) (h₂ : hY.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hg : IsMorse 𝓘(ℝ, E') g) : (hX.prod hY hf hg).IsMorseSmale := by
  refine IsMorseSmale.of_forall fun a b z _ _ hz ↦ ?_
  rw [unstableSet_prod hX hY hf hg, stableSet_prod hX hY hf hg] at hz ⊢
  obtain ⟨⟨hu₁, hu₂⟩, hs₁, hs₂⟩ := hz
  rw [eq_top_iff, ← Submodule.prod_top, ← h₁.span_mtangentConeAt_sup_eq_top ⟨hu₁, hs₁⟩,
    ← h₂.span_mtangentConeAt_sup_eq_top ⟨hu₂, hs₂⟩, ← Submodule.prod_sup_prod]
  exact sup_le_sup (span_mtangentConeAt_prod_le_prodNormed hu₁ hu₂)
    (span_mtangentConeAt_prod_le_prodNormed hs₁ hs₂)

end IsAdaptedPseudoGradient

end TauCeti
