/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Prod
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
import TauCeti.Geometry.Manifold.TangentCone.Prod

/-!
# Pseudo-gradients on a product manifold

Let `X` be a pseudo-gradient field adapted to a Morse function `f` on `M`, and `Y` one adapted to
a Morse function `g` on `N`. Then the product field `(X, Y)` is a pseudo-gradient field adapted to
the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N`. When `M` and `N` are compact Hausdorff,
so that these fields have global flows, the flow of `(X, Y)` is the product of the two flows, its
stable and unstable manifolds are the products of those of `X` and `Y`, and it satisfies the
Morse–Smale condition when `X` and `Y` do. These are the product Morse data with which the Morse
complex of `M × N` is compared to the tensor product of the Morse complexes of `M` and `N`
(Hutchings, §3, Exercise 2).

Near a critical point `(x, y)` the product field is linear in the product of Morse charts at `x`
and at `y`, whose coordinates and weights are those of the two factors placed side by side
(`TauCeti.MorseChart.prod`, `TauCeti.MorseChart.coord_mfderiv_prod`). Away from the critical
points `f ∘ Prod.fst + g ∘ Prod.snd` strictly decreases along `(X, Y)`, because neither summand
increases and one of them strictly decreases.

The adapted pseudo-gradients of `TauCeti.IsAdaptedPseudoGradient` live on manifolds modelled on a
normed space `F` with the model `𝓘(ℝ, F)`. Mathlib's product charts on `M × N` take values in the
type synonym `ModelProd E E'`, with the product model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`. This file reads the
same charts on the normed space `E × E'` (`TauCeti.chartedSpaceProd` and
`TauCeti.isManifold_chartedSpaceProd`, local instances), and transports Mathlib's product results
along `modelWithCornersSelf_prod`.

## Main declarations

* `TauCeti.MorseChart.coord_mfderiv_prod`: the product of fields linear in Morse charts is linear
  in the product Morse chart.
* `TauCeti.IsAdaptedPseudoGradient.prod`: the product field is a pseudo-gradient adapted to the
  separated sum.
* `TauCeti.IsAdaptedPseudoGradient.flow_prod` and `TauCeti.IsAdaptedPseudoGradient.flow_prod_apply`:
  on compact Hausdorff manifolds, its flow is the product of the flows (`Flow.prod`).
* `TauCeti.IsAdaptedPseudoGradient.stableSet_prod` and
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_prod`: its stable and unstable manifolds are the
  products of the stable and unstable manifolds of the factors.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`: on compact Hausdorff manifolds, the product
  of Morse–Smale pseudo-gradients is Morse–Smale.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (pseudo-gradient fields) and Chapter 4.
* M. Hutchings, *Lecture notes on Morse homology*, 2002, §3, Exercise 2 (the Morse complex of a
  product).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
  [ChartedSpace E' N]

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

/-! ### Product fields in product Morse charts -/

namespace MorseChart

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] {f : M → ℝ} {g : N → ℝ} {x : M}
  {y : N}

variable (φ : MorseChart E f x) (ψ : MorseChart E' g y)

/-- **The product of linear fields is linear in the product of Morse charts.** If, at `p.1`, `X`
is the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and `Y` is the linear field in the
Morse chart `ψ` at `p.2`, then the product field `(X, Y)` is the linear field in the product chart
at `p`. -/
theorem coord_mfderiv_prod {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
    {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z} {p : M × N} (hp : p ∈ (φ.prod ψ).toChart.source)
    (hφ : φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart p.1 (X p.1)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart p.1) i))
    (hψ : ψ.coord (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart p.2 (Y p.2)) =
      fun i ↦ -(ψ.weight i * ψ.coord (ψ.toChart p.2) i)) :
    (φ.prod ψ).coord (mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ, E × E') (φ.prod ψ).toChart p
      (Manifold.prodVectorField X Y p)) =
      fun i ↦ -((φ.prod ψ).weight i * (φ.prod ψ).coord ((φ.prod ψ).toChart p) i) := by
  have := φ.finiteDimensional
  have := ψ.finiteDimensional
  rw [prod_toChart] at hp ⊢
  obtain ⟨hp₁, hp₂⟩ := hp
  have hD : mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ, E × E') (φ.toChart.prod ψ.toChart) p
      (Manifold.prodVectorField X Y p) =
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart p.1 (X p.1),
        mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart p.2 (Y p.2)) : E × E') := by
    -- Mathlib's `mfderiv_prodMap` is stated for the product model and product charts; the
    -- product model is `𝓘(ℝ, E × E')` and the product charts on `E × E'` are its own chart.
    have h := mfderiv_prodMap (φ.mdifferentiableAt_toChart hp₁) (ψ.mdifferentiableAt_toChart hp₂)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    rw [← Manifold.prodVectorField_fst X Y p, ← Manifold.prodVectorField_snd X Y p]
    exact congr($h (Manifold.prodVectorField X Y p))
  ext i
  rw [hD, prod_coord_apply, prod_weight_apply, prod_coord_apply]
  rcases prodIndexEquiv E E' i with j | j
  · exact congrFun hφ j
  · exact congrFun hψ j

end MorseChart

/-! ### Products of adapted pseudo-gradients -/

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] {f : M → ℝ} {g : N → ℝ}
  {X : (z : M) → TangentSpace 𝓘(ℝ, E) z} {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}

/-- **The product of adapted pseudo-gradients.** If `X` is a pseudo-gradient adapted to `f` on `M`
and `Y` one adapted to `g` on `N`, then the product field `(X, Y)` is a pseudo-gradient adapted to
the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N`. -/
theorem prod (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y) :
    IsAdaptedPseudoGradient (f ∘ Prod.fst + g ∘ Prod.snd) (Manifold.prodVectorField X Y) where
  contMDiff := Manifold.contMDiff_prodVectorField_chartedSpaceProd hX.contMDiff hY.contMDiff
  mvfderiv_apply_lt_zero p hp := by
    have hfp := hX.mdifferentiable p.1
    have hgp := hY.mdifferentiable p.2
    rw [Ne, mfderiv_comp_fst_add_comp_snd_eq_zero_iff_chartedSpaceProd hfp hgp, not_and_or] at hp
    rw [modelWithCornersSelf_prod, mvfderiv_comp_fst_add_comp_snd_apply hfp hgp,
      Manifold.prodVectorField_fst, Manifold.prodVectorField_snd]
    rcases hp with hp | hp
    · exact add_neg_of_neg_of_nonpos (hX.mvfderiv_apply_lt_zero _ hp) (hY.mvfderiv_apply_nonpos _)
    · exact add_neg_of_nonpos_of_neg (hX.mvfderiv_apply_nonpos _) (hY.mvfderiv_apply_lt_zero _ hp)
  exists_morseChart p hp := by
    obtain ⟨p₁, p₂⟩ := p
    obtain ⟨h₁, h₂⟩ := (mfderiv_comp_fst_add_comp_snd_eq_zero_iff_chartedSpaceProd
      (hX.mdifferentiable p₁) (hY.mdifferentiable p₂)).1 hp
    obtain ⟨φ, hφ⟩ := hX.exists_morseChart p₁ h₁
    obtain ⟨ψ, hψ⟩ := hY.exists_morseChart p₂ h₂
    refine ⟨φ.prod ψ, fun q hq ↦ φ.coord_mfderiv_prod ψ hq ?_ ?_⟩
    · rw [MorseChart.prod_toChart] at hq
      exact hφ q.1 hq.1
    · rw [MorseChart.prod_toChart] at hq
      exact hψ q.2 hq.2

/-! ### The flow, stable and unstable manifolds of a product -/

section Flow

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M]
  [CompactSpace N] [T2Space N] (hX : IsAdaptedPseudoGradient f X)
  (hY : IsAdaptedPseudoGradient g Y)

/-- **The flow of a product of pseudo-gradients is the product of the flows.** This is not a `simp`
lemma: `TauCeti.IsAdaptedPseudoGradient.flow_prod_apply`, `stableSet_prod` and `unstableSet_prod`
are the `simp` forms of its consequences. -/
theorem flow_prod : (hX.prod hY).flow = hX.flow.prod hY.flow := by
  refine Flow.ext fun t p ↦ ?_
  have hγ : IsMIntegralCurve (fun s ↦ (hX.flow s p.1, hY.flow s p.2))
      (Manifold.prodVectorField X Y) := by
    have h := (hX.isMIntegralCurve_flow p.1).prodMk (hY.isMIntegralCurve_flow p.2)
    rwa [← modelWithCornersSelf_prod] at h
  have h := globalFlow_eq_of_isMIntegralCurve ((hX.prod hY).contMDiff.of_le (by simp))
    (hX.prod hY).isCompleteVectorField hγ t
  simp only [Flow.map_zero_apply] at h
  rw [Flow.prod_apply, ← h, (hX.prod hY).flow_apply]
  exact (globalFlow_apply ..).symm

/-- The flow of a product of pseudo-gradients acts on each component by the flow of the
corresponding factor. -/
@[simp]
theorem flow_prod_apply (t : ℝ) (p : M × N) :
    (hX.prod hY).flow t p = (hX.flow t p.1, hY.flow t p.2) := by
  rw [hX.flow_prod hY, Flow.prod_apply]

/-- **The stable manifolds of a product of pseudo-gradients are the products of the stable
manifolds.** -/
@[simp]
theorem stableSet_prod (a : M × N) :
    (hX.prod hY).flow.stableSet a = hX.flow.stableSet a.1 ×ˢ hY.flow.stableSet a.2 := by
  rw [hX.flow_prod hY, Flow.stableSet_prod]

/-- **The unstable manifolds of a product of pseudo-gradients are the products of the unstable
manifolds.** -/
@[simp]
theorem unstableSet_prod (a : M × N) :
    (hX.prod hY).flow.unstableSet a = hX.flow.unstableSet a.1 ×ˢ hY.flow.unstableSet a.2 := by
  rw [hX.flow_prod hY, Flow.unstableSet_prod]

omit hX hY in
/-- **The product of Morse–Smale pseudo-gradients is Morse–Smale.** On compact Hausdorff
manifolds, if the unstable and stable manifolds of `X` meet transversally, and so do those of `Y`,
then so do those of the product field `(X, Y)`, since its unstable and stable manifolds are the
products of those of `X` and `Y`. -/
theorem IsMorseSmale.prod {hX : IsAdaptedPseudoGradient f X} {hY : IsAdaptedPseudoGradient g Y}
    (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale) : (hX.prod hY).IsMorseSmale := by
  refine IsMorseSmale.of_forall ?_
  rintro a b ⟨p₁, p₂⟩ - - hp
  rw [hX.unstableSet_prod hY, hX.stableSet_prod hY] at hp ⊢
  obtain ⟨⟨hu₁, hu₂⟩, hs₁, hs₂⟩ := hp
  rw [eq_top_iff, ← Submodule.prod_top, ← hXs.span_mtangentConeAt_sup_eq_top ⟨hu₁, hs₁⟩,
    ← hYs.span_mtangentConeAt_sup_eq_top ⟨hu₂, hs₂⟩, ← Submodule.prod_sup_prod,
    modelWithCornersSelf_prod]
  exact sup_le_sup (prod_span_mtangentConeAt_le (subset_closure hu₁) (subset_closure hu₂))
    (prod_span_mtangentConeAt_le (subset_closure hs₁) (subset_closure hs₂))

end Flow

end IsAdaptedPseudoGradient

end TauCeti
