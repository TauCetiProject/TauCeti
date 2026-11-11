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
import TauCeti.Geometry.Manifold.TangentCone.Prod

/-!
# Pseudo-gradients on a product manifold

Let `X` be a pseudo-gradient field adapted to a Morse function `f` on `M`, and `Y` one adapted to
a Morse function `g` on `N`. Then the product field `(X, Y)` is a pseudo-gradient field adapted to
the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N`. Its flow is the product of the two
flows, so its stable and unstable manifolds are the products of those of `X` and `Y`, and it
satisfies the Morse–Smale condition when `X` and `Y` do. On compact manifolds these are the product
Morse data with which the Morse complex of `M × N` is compared to the tensor product of the Morse
complexes of `M` and `N` (Hutchings, §3, Exercise 2).

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
* `TauCeti.IsAdaptedPseudoGradient.flow_prod_apply`: its flow is the product of the flows.
* `TauCeti.IsAdaptedPseudoGradient.stableSet_prod` and
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_prod`: its stable and unstable manifolds are the
  products of the stable and unstable manifolds of the factors.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`: the product of Morse–Smale pseudo-gradients
  is Morse–Smale.

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

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E') ∞ N] {f : M → ℝ} {g : N → ℝ} {x : M} {y : N}

variable (φ : MorseChart E f x) (ψ : MorseChart E' g y)
  (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
  (hy : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y)

/-- **The product of linear fields is linear in the product of Morse charts.** If `X` is the
linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ` and `Y` is the linear field in the Morse chart
`ψ`, then the product field `(X, Y)` is the linear field in the product chart. -/
theorem coord_mfderiv_prod {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
    {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}
    (hφ : ∀ z ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z (X z)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart z) i))
    (hψ : ∀ z ∈ ψ.toChart.source, ψ.coord (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart z (Y z)) =
      fun i ↦ -(ψ.weight i * ψ.coord (ψ.toChart z) i))
    {p : M × N} (hp : p ∈ (φ.prod ψ hx hy).toChart.source) :
    (φ.prod ψ hx hy).coord (mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ, E × E') (φ.prod ψ hx hy).toChart p
      (Manifold.prodVectorField X Y p)) =
      fun i ↦
        -((φ.prod ψ hx hy).weight i * (φ.prod ψ hx hy).coord ((φ.prod ψ hx hy).toChart p) i) := by
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
  · exact congrFun (hφ p.1 hp₁) j
  · exact congrFun (hψ p.2 hp₂) j

end MorseChart

/-! ### Products of adapted pseudo-gradients -/

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E') ∞ N] {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}

/-- **The product of adapted pseudo-gradients.** If `X` is a pseudo-gradient adapted to the Morse
function `f` on `M` and `Y` one adapted to the Morse function `g` on `N`, then the product field
`(X, Y)` is a pseudo-gradient adapted to the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on
`M × N`. -/
theorem prod (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)
    (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g) :
    IsAdaptedPseudoGradient (f ∘ Prod.fst + g ∘ Prod.snd) (Manifold.prodVectorField X Y) where
  contMDiff := Manifold.contMDiff_prodVectorField_chartedSpaceProd hX.contMDiff hY.contMDiff
  mvfderiv_apply_lt_zero p hp := by
    have hfp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f p.1 := hf.contMDiff.mdifferentiable (by simp) _
    have hgp : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ) g p.2 := hg.contMDiff.mdifferentiable (by simp) _
    rw [Ne, mfderiv_comp_fst_add_comp_snd_eq_zero_iff hfp hgp, not_and_or] at hp
    rw [modelWithCornersSelf_prod, mvfderiv_add ((hfp.comp p mdifferentiableAt_fst))
      (hgp.comp p mdifferentiableAt_snd), add_apply, mvfderiv_comp_fst_apply,
      mvfderiv_comp_snd_apply, Manifold.prodVectorField_fst, Manifold.prodVectorField_snd]
    rcases hp with hp | hp
    · exact add_neg_of_neg_of_nonpos (hX.mvfderiv_apply_lt_zero _ hp) (hY.mvfderiv_apply_nonpos _)
    · exact add_neg_of_nonpos_of_neg (hX.mvfderiv_apply_nonpos _) (hY.mvfderiv_apply_lt_zero _ hp)
  exists_morseChart p hp := by
    obtain ⟨p₁, p₂⟩ := p
    obtain ⟨h₁, h₂⟩ := (mfderiv_comp_fst_add_comp_snd_eq_zero_iff
      (hf.contMDiff.mdifferentiable (by simp) p₁) (hg.contMDiff.mdifferentiable (by simp) p₂)).1 hp
    obtain ⟨φ, hφ⟩ := hX.exists_morseChart p₁ h₁
    obtain ⟨ψ, hψ⟩ := hY.exists_morseChart p₂ h₂
    refine ⟨φ.prod ψ (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero h₁)
      (hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero h₂),
      fun q hq ↦ ?_⟩
    exact MorseChart.coord_mfderiv_prod _ _ _ _ hφ hψ hq

/-! ### The flow, stable and unstable manifolds of a product -/

section Flow

variable [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y) (hf : IsMorse 𝓘(ℝ, E) f)
  (hg : IsMorse 𝓘(ℝ, E') g)

/-- **The flow of a product of pseudo-gradients is the product of the flows.** -/
@[simp]
theorem flow_prod_apply (t : ℝ) (p : M × N) :
    (hX.prod hY hf hg).flow t p = (hX.flow t p.1, hY.flow t p.2) := by
  have hγ : IsMIntegralCurve (fun s ↦ (hX.flow s p.1, hY.flow s p.2))
      (Manifold.prodVectorField X Y) := by
    intro s
    have h := (hX.isMIntegralCurve_flow p.1 s).prodMk (hY.isMIntegralCurve_flow p.2 s)
    rw [← modelWithCornersSelf_prod] at h
    refine h.congr_mfderiv ?_
    -- `Manifold.prodVectorField` is not exposed, so its value is read off componentwise.
    exact ContinuousLinearMap.ext fun c ↦ Prod.ext
      (congrArg ((show ℝ from c) • ·)
        (Manifold.prodVectorField_fst X Y (hX.flow s p.1, hY.flow s p.2)).symm)
      (congrArg ((show ℝ from c) • ·)
        (Manifold.prodVectorField_snd X Y (hX.flow s p.1, hY.flow s p.2)).symm)
  have h := globalFlow_eq_of_isMIntegralCurve ((hX.prod hY hf hg).contMDiff.of_le (by simp))
    (hX.prod hY hf hg).isCompleteVectorField hγ t
  simp only [Flow.map_zero_apply] at h
  rw [← h, (hX.prod hY hf hg).flow_apply]
  exact (globalFlow_apply ..).symm

/-- **The stable manifolds of a product of pseudo-gradients are the products of the stable
manifolds.** -/
@[simp]
theorem stableSet_prod (a : M × N) :
    (hX.prod hY hf hg).flow.stableSet a = hX.flow.stableSet a.1 ×ˢ hY.flow.stableSet a.2 := by
  obtain ⟨a₁, a₂⟩ := a
  ext p
  simp only [Flow.mem_stableSet, mem_prod, hX.flow_prod_apply hY hf hg, nhds_prod_eq]
  exact tendsto_prod_iff'

/-- **The unstable manifolds of a product of pseudo-gradients are the products of the unstable
manifolds.** -/
@[simp]
theorem unstableSet_prod (a : M × N) :
    (hX.prod hY hf hg).flow.unstableSet a = hX.flow.unstableSet a.1 ×ˢ hY.flow.unstableSet a.2 := by
  obtain ⟨a₁, a₂⟩ := a
  ext p
  simp only [Flow.mem_unstableSet, mem_prod, hX.flow_prod_apply hY hf hg, nhds_prod_eq]
  exact tendsto_prod_iff'

/-- **The product of Morse–Smale pseudo-gradients is Morse–Smale.** If the unstable and stable
manifolds of `X` meet transversally, and so do those of `Y`, then so do those of the product field
`(X, Y)`, since its unstable and stable manifolds are the products of those of `X` and `Y`. -/
theorem IsMorseSmale.prod (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale) :
    (hX.prod hY hf hg).IsMorseSmale := by
  refine IsMorseSmale.of_forall ?_
  rintro a b ⟨p₁, p₂⟩ ha hb hp
  have hfd := hf.contMDiff.mdifferentiable (by simp)
  have hgd := hg.contMDiff.mdifferentiable (by simp)
  rw [mfderiv_comp_fst_add_comp_snd_eq_zero_iff (hfd _) (hgd _)] at ha hb
  rw [hX.unstableSet_prod hY hf hg, hX.stableSet_prod hY hf hg] at hp ⊢
  obtain ⟨⟨hu₁, hu₂⟩, hs₁, hs₂⟩ := hp
  rw [eq_top_iff, ← Submodule.prod_top,
    ← hXs.span_mtangentConeAt_sup_eq_top ha.1 hb.1 ⟨hu₁, hs₁⟩,
    ← hYs.span_mtangentConeAt_sup_eq_top ha.2 hb.2 ⟨hu₂, hs₂⟩, ← Submodule.prod_sup_prod,
    modelWithCornersSelf_prod]
  exact sup_le_sup (prod_span_mtangentConeAt_le hu₁ hu₂) (prod_span_mtangentConeAt_le hs₁ hs₂)

end Flow

end IsAdaptedPseudoGradient

end TauCeti
