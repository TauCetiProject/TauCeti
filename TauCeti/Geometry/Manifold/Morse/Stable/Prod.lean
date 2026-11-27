/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod
public import TauCeti.Geometry.Manifold.Morse.Stable.Frame

/-!
# Normal coordinates and unstable frames on a product manifold

Let `X` be a pseudo-gradient adapted to `f` on a compact manifold `M`, and `Y` one adapted to `g`
on a compact manifold `N`, so that the product field `(X, Y)` is adapted to the separated sum
`f ∘ Prod.fst + g ∘ Prod.snd` on `M × N` (`TauCeti.IsAdaptedPseudoGradient.prod`). Let `φ` be a
Morse chart of `f` at `x` in which `X` is linear and `ψ` one of `g` at `y` in which `Y` is linear,
so that `(X, Y)` is linear in the product chart `φ.prod ψ` at `(x, y)`
(`TauCeti.MorseChart.coord_mfderiv_prod`).

The coordinates of negative weight of `φ.prod ψ` are those of `φ` followed by those of `ψ`
(`TauCeti.MorseChart.prodNegativeEquiv`). This file shows that the normal coordinates of the
stable manifold and the frame of the unstable manifold of `(x, y)`, which orient the Morse complex
of `M × N`, are the products of those of the factors:

* at a point `(y₁, y₂)` of `W^s(x) × W^s(y)`, the normal coordinates of `φ.prod ψ` send `(u, v)`
  to the pair of normal coordinates of `u` and `v`
  (`TauCeti.IsAdaptedPseudoGradient.prodNegativeEquiv_stableNormal_prod`);
* at a point `(y₁, y₂)` of `W^u(x) × W^u(y)`, the unstable frame of `φ.prod ψ` sends the pair
  `(a, b)` of coordinates of negative weight to the pair of frames
  (`TauCeti.IsAdaptedPseudoGradient.unstableFrame_prod_prodNegativeEquiv_symm`).

Both follow from the formulas of `TauCeti.Geometry.Manifold.Morse.Stable.Frame` at an admissible
time common to the two factors, since the flow of `(X, Y)` is the product of the flows
(`TauCeti.IsAdaptedPseudoGradient.flow_prod_apply`) and the linear flow of `φ.prod ψ` is the
product of the linear flows. At the centre of a Morse chart, the normal coordinates invert the
unstable frame (`TauCeti.IsAdaptedPseudoGradient.stableNormal_unstableFrame_self`): there the two
maps are read off the chart itself.

As in `TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod`, the charts of `M × N` are read on the
normed space `E × E'` (`TauCeti.chartedSpaceProd` and `TauCeti.isManifold_chartedSpaceProd`, local
instances).

## Main declarations

* `TauCeti.MorseChart.prodNegativeEquiv`: the coordinates of negative weight of a product of Morse
  charts are the pairs of coordinates of negative weight of the factors.
* `TauCeti.IsAdaptedPseudoGradient.prodNegativeEquiv_stableNormal_prod`: the normal coordinates of
  a product.
* `TauCeti.IsAdaptedPseudoGradient.unstableFrame_prod_prodNegativeEquiv_symm`: the unstable frame
  of a product.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds) and §3,
  Exercise 2 (the Morse complex of a product).
-/

public section

open Filter Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
  [ChartedSpace E' N]

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

/-! ### Coordinates of negative weight of a product of Morse charts -/

namespace MorseChart

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] {f : M → ℝ} {g : N → ℝ} {x : M}
  {y : N} (φ : MorseChart E f x) (ψ : MorseChart E' g y) [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E']

/-- The coordinates of negative weight of a product of Morse charts are those of the first chart
followed by those of the second. -/
noncomputable def prodNegativeWeightEquiv :
    {i // (φ.prod ψ).weight i < 0} ≃ {j // φ.weight j < 0} ⊕ {j // ψ.weight j < 0} :=
  (Equiv.subtypeEquiv (prodIndexEquiv E E') fun i ↦ by rw [prod_weight_apply]).trans
    (Equiv.subtypeSum (p := fun k ↦ Sum.elim φ.weight ψ.weight k < 0))

/-- A coordinate of negative weight of a product of Morse charts is the corresponding coordinate
of `E` or of `E'`. -/
@[simp]
theorem sumMap_val_prodNegativeWeightEquiv (i : {i // (φ.prod ψ).weight i < 0}) :
    Sum.map Subtype.val Subtype.val (φ.prodNegativeWeightEquiv ψ i) = prodIndexEquiv E E' i := by
  rcases h : prodIndexEquiv E E' i with j | j <;>
    simp [prodNegativeWeightEquiv, Equiv.subtypeSum, h]

/-- **The coordinates of negative weight of a product of Morse charts** are the pairs of
coordinates of negative weight of the two charts. -/
noncomputable def prodNegativeEquiv :
    ({i // (φ.prod ψ).weight i < 0} → ℝ) ≃ₗ[ℝ]
      ({j // φ.weight j < 0} → ℝ) × ({j // ψ.weight j < 0} → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (φ.prodNegativeWeightEquiv ψ).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ)

/-- The coordinates of negative weight of `(a, b)` read in the product chart. -/
theorem prodNegativeEquiv_symm_apply (a : {j // φ.weight j < 0} → ℝ)
    (b : {j // ψ.weight j < 0} → ℝ) (i : {i // (φ.prod ψ).weight i < 0}) :
    (φ.prodNegativeEquiv ψ).symm (a, b) i = Sum.elim a b (φ.prodNegativeWeightEquiv ψ i) := by
  simp only [prodNegativeEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Equiv.symm_symm]
  rcases φ.prodNegativeWeightEquiv ψ i with j | j
  · rw [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, Sum.elim_inl]
  · rw [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, Sum.elim_inr]

/-- The coordinates of negative weight of `v` in the product chart, split between the two charts. -/
theorem prodNegativeEquiv_apply (v : {i // (φ.prod ψ).weight i < 0} → ℝ) :
    φ.prodNegativeEquiv ψ v =
      (fun j ↦ v ((φ.prodNegativeWeightEquiv ψ).symm (Sum.inl j)),
        fun j ↦ v ((φ.prodNegativeWeightEquiv ψ).symm (Sum.inr j))) := by
  refine (φ.prodNegativeEquiv ψ).symm.injective ?_
  funext i
  rw [LinearEquiv.symm_apply_apply, prodNegativeEquiv_symm_apply]
  rcases h : φ.prodNegativeWeightEquiv ψ i with j | j
  · rw [Sum.elim_inl, ← h, Equiv.symm_apply_apply]
  · rw [Sum.elim_inr, ← h, Equiv.symm_apply_apply]

/-- The coordinates of negative weight of a vector of `E × E'` in a product of Morse charts are
those of its two components. -/
@[simp]
theorem prodNegativeEquiv_negativeCoord (v : E × E') :
    φ.prodNegativeEquiv ψ ((φ.prod ψ).negativeCoord v) =
      (φ.negativeCoord v.1, ψ.negativeCoord v.2) := by
  refine (φ.prodNegativeEquiv ψ).symm.injective ?_
  rw [LinearEquiv.symm_apply_apply]
  funext i
  rw [prodNegativeEquiv_symm_apply, MorseBottChart.negativeCoord_apply, prod_coord_apply]
  have h := φ.sumMap_val_prodNegativeWeightEquiv ψ i
  rcases hi : φ.prodNegativeWeightEquiv ψ i with j | j <;> rw [hi] at h <;> simp [← h]

/-- The vector of a product of Morse charts with coordinates of negative weight `(a, b)` and
vanishing coordinates of positive weight has these components in the two charts. -/
@[simp]
theorem prod_negativeExtend_prodNegativeEquiv_symm (a : {j // φ.weight j < 0} → ℝ)
    (b : {j // ψ.weight j < 0} → ℝ) :
    (φ.prod ψ).negativeExtend ((φ.prodNegativeEquiv ψ).symm (a, b)) =
      (φ.negativeExtend a, ψ.negativeExtend b) := by
  have hpos : ∀ i, ¬(φ.prod ψ).weight i < 0 →
      (φ.prod ψ).coord (φ.negativeExtend a, ψ.negativeExtend b) i = 0 := by
    intro i hi
    rw [prod_coord_apply]
    rw [prod_weight_apply] at hi
    rcases h : prodIndexEquiv E E' i with j | j <;> rw [h] at hi <;>
      simp [coord_negativeExtend_of_not_weight_neg _ _ hi]
  rw [← (φ.prod ψ).negativeExtend_negativeCoord hpos]
  congr 1
  refine (φ.prodNegativeEquiv ψ).injective ?_
  simp

/-- The linear flow of a product of Morse charts is the product of the linear flows, read in the
coordinates of the two charts. -/
theorem prod_coord_symm_linearFlow_coord (t : ℝ) (z : E × E') :
    (φ.prod ψ).coord.symm ((φ.prod ψ).linearFlow t ((φ.prod ψ).coord z)) =
      (φ.coord.symm (φ.linearFlow t (φ.coord z.1)),
        ψ.coord.symm (ψ.linearFlow t (ψ.coord z.2))) := by
  simp only [prod_coord_symm_apply, MorseBottChart.linearFlow_apply, prod_weight_apply,
    prod_coord_apply, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
  refine Prod.ext (congrArg φ.coord.symm (funext fun j ↦ ?_))
    (congrArg ψ.coord.symm (funext fun j ↦ ?_)) <;> rw [MorseBottChart.linearFlow_apply]

end MorseChart

/-! ### Normal coordinates and unstable frames of a product -/

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z} {hX : IsAdaptedPseudoGradient f X}
  {hY : IsAdaptedPseudoGradient g Y} {x : M} {y : N} {φ : MorseChart E f x}
  {ψ : MorseChart E' g y} {y₁ : M} {y₂ : N} {T : ℝ}

/-- A time of linear forward flow of `y₁` in `φ` and of `y₂` in `ψ` is a time of linear forward
flow of `(y₁, y₂)` in the product chart. -/
theorem prod_mem_linearForwardTimes (h₁ : T ∈ hX.linearForwardTimes φ y₁)
    (h₂ : T ∈ hY.linearForwardTimes ψ y₂) :
    T ∈ (hX.prod hY).linearForwardTimes (φ.prod ψ) (y₁, y₂) := by
  refine ((hX.prod hY).mem_linearForwardTimes _).2 ⟨?_, fun t ht ↦ ?_⟩
  · rw [flow_prod_apply hX hY, MorseChart.prod_toChart]
    exact ⟨((hX.mem_linearForwardTimes φ).1 h₁).1, ((hY.mem_linearForwardTimes ψ).1 h₂).1⟩
  · rw [flow_prod_apply hX hY, MorseChart.prod_toChart, OpenPartialHomeomorph.prod_apply,
      ← MorseChart.prod_toChart, MorseChart.prod_coord_symm_linearFlow_coord,
      MorseChart.prod_toChart, OpenPartialHomeomorph.prod_target]
    exact ⟨((hX.mem_linearForwardTimes φ).1 h₁).2 t ht, ((hY.mem_linearForwardTimes ψ).1 h₂).2 t ht⟩

/-- A time of linear backward flow of `y₁` in `φ` and of `y₂` in `ψ` is a time of linear backward
flow of `(y₁, y₂)` in the product chart. -/
theorem prod_mem_linearBackwardTimes (h₁ : T ∈ hX.linearBackwardTimes φ y₁)
    (h₂ : T ∈ hY.linearBackwardTimes ψ y₂) :
    T ∈ (hX.prod hY).linearBackwardTimes (φ.prod ψ) (y₁, y₂) := by
  refine ((hX.prod hY).mem_linearBackwardTimes _).2 ⟨?_, fun t ht ↦ ?_⟩
  · rw [flow_prod_apply hX hY, MorseChart.prod_toChart]
    exact ⟨((hX.mem_linearBackwardTimes φ).1 h₁).1, ((hY.mem_linearBackwardTimes ψ).1 h₂).1⟩
  · rw [flow_prod_apply hX hY, MorseChart.prod_toChart, OpenPartialHomeomorph.prod_apply,
      ← MorseChart.prod_toChart, MorseChart.prod_coord_symm_linearFlow_coord,
      MorseChart.prod_toChart, OpenPartialHomeomorph.prod_target]
    exact ⟨((hX.mem_linearBackwardTimes φ).1 h₁).2 t ht,
      ((hY.mem_linearBackwardTimes ψ).1 h₂).2 t ht⟩

/-- The derivative of the product chart composed with the time-`T` map of the product flow acts
componentwise. -/
theorem mfderiv_prod_toChart_comp_flow (h₁ : hX.flow T y₁ ∈ φ.toChart.source)
    (h₂ : hY.flow T y₂ ∈ ψ.toChart.source) (w : E × E') :
    mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ, E × E') ((φ.prod ψ).toChart ∘ (hX.prod hY).flow T) (y₁, y₂) w =
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y₁ w.1,
        mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (ψ.toChart ∘ hY.flow T) y₂ w.2) : E × E') := by
  have hd₁ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y₁ :=
    (φ.mdifferentiableAt_toChart h₁).comp _
      ((hX.contMDiff_flow_apply T).mdifferentiable (by simp) y₁)
  have hd₂ : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E') (ψ.toChart ∘ hY.flow T) y₂ :=
    (ψ.mdifferentiableAt_toChart h₂).comp _
      ((hY.contMDiff_flow_apply T).mdifferentiable (by simp) y₂)
  have hfun : (φ.prod ψ).toChart ∘ (hX.prod hY).flow T =
      Prod.map (φ.toChart ∘ hX.flow T) (ψ.toChart ∘ hY.flow T) := by
    funext ⟨z₁, z₂⟩
    simp only [comp_apply, flow_prod_apply hX hY, MorseChart.prod_toChart,
      OpenPartialHomeomorph.prod_apply, Prod.map_apply]
  -- Mathlib's `mfderiv_prodMap` is stated for the product model and product charts; the product
  -- model is `𝓘(ℝ, E × E')` and the product charts on `E × E'` are its own chart.
  have h := mfderiv_prodMap (p := (y₁, y₂)) hd₁ hd₂
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  rw [hfun]
  exact congr($h w)

variable (hφ : ∀ z ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z (X z)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart z) i))
  (hψ : ∀ z ∈ ψ.toChart.source, ψ.coord (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart z (Y z)) =
    fun i ↦ -(ψ.weight i * ψ.coord (ψ.toChart z) i))
include hφ hψ

/-- **The normal coordinates of a product.** At a point `(y₁, y₂)` of `W^s(x) × W^s(y)`, the
normal coordinates of the stable manifold of `(x, y)` in the product chart send `w` to the pair of
normal coordinates of its components, in the coordinates of negative weight of the two charts. -/
theorem prodNegativeEquiv_stableNormal_prod (h₁ : y₁ ∈ hX.flow.stableSet x)
    (h₂ : y₂ ∈ hY.flow.stableSet y) (w : E × E') :
    φ.prodNegativeEquiv ψ ((hX.prod hY).stableNormal (φ.prod ψ) (y₁, y₂) w) =
      (hX.stableNormal φ y₁ w.1, hY.stableNormal ψ y₂ w.2) := by
  obtain ⟨T, hT₁, hT₂⟩ := ((hX.eventually_mem_linearForwardTimes hφ h₁).and
    (hY.eventually_mem_linearForwardTimes hψ h₂)).exists
  -- The product field has its tangent spaces for the model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`, so `rw`
  -- cannot rewrite inside terms involving the product flow; `congrArg` transports the formulas.
  have hN := (hX.prod hY).stableNormal_apply (φ.forall_coord_mfderiv_prod ψ hφ hψ)
    (prod_mem_linearForwardTimes hT₁ hT₂) w
  have hD := mfderiv_prod_toChart_comp_flow (hX := hX) (hY := hY) (φ := φ) (ψ := ψ)
    ((hX.mem_linearForwardTimes φ).1 hT₁).1 ((hY.mem_linearForwardTimes ψ).1 hT₂).1 w
  refine (congrArg (φ.prodNegativeEquiv ψ) (hN.trans
    (congrArg (fun v ↦ Real.exp (-T) • (φ.prod ψ).negativeCoord v) hD))).trans ?_
  rw [map_smul, MorseChart.prodNegativeEquiv_negativeCoord]
  -- The components are vectors of the tangent spaces of `M` and `N`, which are `E` and `E'`.
  exact Prod.ext (hX.stableNormal_apply hφ hT₁ w.1).symm (hY.stableNormal_apply hψ hT₂ w.2).symm

/-- **The unstable frame of a product.** At a point `(y₁, y₂)` of `W^u(x) × W^u(y)`, the unstable
frame of `(x, y)` in the product chart sends the pair `(a, b)` of coordinates of negative weight of
the two charts to the pair of unstable frames. -/
theorem unstableFrame_prod_prodNegativeEquiv_symm (hf : IsMorse 𝓘(ℝ, E) f)
    (hg : IsMorse 𝓘(ℝ, E') g) (h₁ : y₁ ∈ hX.flow.unstableSet x) (h₂ : y₂ ∈ hY.flow.unstableSet y)
    (a : {j // φ.weight j < 0} → ℝ) (b : {j // ψ.weight j < 0} → ℝ) :
    (hX.prod hY).unstableFrame (φ.prod ψ) (y₁, y₂) ((φ.prodNegativeEquiv ψ).symm (a, b)) =
      ((hX.unstableFrame φ y₁ a, hY.unstableFrame ψ y₂ b) : E × E') := by
  obtain ⟨T, hT₁, hT₂⟩ := ((hX.eventually_mem_linearBackwardTimes hφ hf h₁).and
    (hY.eventually_mem_linearBackwardTimes hψ hg h₂)).exists
  have hT := prod_mem_linearBackwardTimes hT₁ hT₂
  have hs₁ := ((hX.mem_linearBackwardTimes φ).1 hT₁).1
  have hs₂ := ((hY.mem_linearBackwardTimes ψ).1 hT₂).1
  refine (isInvertible_mfderiv_toChart_comp_flow
    (((hX.prod hY).mem_linearBackwardTimes _).1 hT).1).injective ?_
  -- As for the normal coordinates, the two sides are compared through `congrArg` and `Eq.trans`
  -- rather than `rw`, which cannot rewrite inside terms involving the product flow.
  have hF := (hX.prod hY).mfderiv_unstableFrame (φ.forall_coord_mfderiv_prod ψ hφ hψ) hT
    ((φ.prodNegativeEquiv ψ).symm (a, b))
  have hD := mfderiv_prod_toChart_comp_flow (hX := hX) (hY := hY) (φ := φ) (ψ := ψ) hs₁ hs₂
    ((hX.unstableFrame φ y₁ a, hY.unstableFrame ψ y₂ b) : E × E')
  refine hF.trans (Eq.trans ?_ hD.symm)
  rw [MorseChart.prod_negativeExtend_prodNegativeEquiv_symm, Prod.smul_mk,
    hX.mfderiv_unstableFrame hφ hT₁, hY.mfderiv_unstableFrame hψ hT₂]

end IsAdaptedPseudoGradient

end TauCeti
