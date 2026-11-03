/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# `L^p` isometric equivalences from an almost-everywhere inverse pair

Mathlib turns a measure-preserving map `f : α → β` into a linear isometry
`MeasureTheory.Lp.compMeasurePreservingₗᵢ : Lp E p μb →ₗᵢ[𝕜] Lp E p μ`, but stops there: there is
no constructor producing a `LinearIsometryEquiv`. Transporting structure between `L²` spaces —
a Hilbert basis, an orthonormal family, a spectral decomposition — needs the equivalence, since
`HilbertBasis.mapₗᵢ` and its relatives consume `≃ₗᵢ` rather than `→ₗᵢ`.

A change of variables rarely supplies a `MeasurableEquiv`. The maps that arise in practice are
inverse to each other only *almost everywhere*: `Real.cos ∘ Real.arccos` is the identity only on
`[-1, 1]`, and `Real.arccos ∘ Real.cos` only on `[0, π]`. This file therefore takes a convenient
sufficient hypothesis — a pair of measure-preserving maps that compose to the identity almost
everywhere in one direction — and builds the isometric equivalence from it. One direction is
enough: both precompositions are linear isometries, hence injective, and an injective map with a
one-sided inverse has that inverse on both sides.

## Main declarations

* `MeasureTheory.Lp.compMeasurePreservingₗᵢ_apply` is the application lemma for Mathlib's
  linear isometry. Mathlib's `@[simps!]` generates only `compMeasurePreservingₗᵢ_apply_coe`,
  which unfolds one level too far to rewrite with.
* `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv` upgrades that linear isometry to a
  `LinearIsometryEquiv` given a one-sided almost-everywhere inverse partner.
* `MeasureTheory.Lp.coeFn_compMeasurePreservingₗᵢEquiv` and
  `MeasureTheory.Lp.coeFn_compMeasurePreservingₗᵢEquiv_symm` identify the equivalence and its
  inverse with precomposition by `f` and by `g` respectively.
* `MeasureTheory.Lp.leftInverse_compMeasurePreserving`: precomposition by `g` is a left inverse
  of precomposition by `f` when `f ∘ g` is almost everywhere the identity.
* `MeasureTheory.Lp.compMeasurePreserving_toLp` identifies precomposition on the `Lp` class of a
  continuous function with ordinary composition of continuous maps.
-/

public section

open scoped ENNReal

namespace MeasureTheory
namespace Lp

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E] {f : α → β} {g : β → α}

/-- If `f` and `g` are measure-preserving and `f ∘ g` is the identity almost everywhere, then
precomposition by `g` is a left inverse of precomposition by `f` on `Lp`. -/
theorem leftInverse_compMeasurePreserving (hf : MeasurePreserving f μ μb)
    (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) :
    Function.LeftInverse (compMeasurePreserving (E := E) (p := p) g hg)
      (compMeasurePreserving f hf) := fun x ↦ by
  rw [← compMeasurePreserving_comp_apply x hf hg]
  refine Subtype.ext ?_
  rw [compMeasurePreserving_val, AEEqFun.compMeasurePreserving_congr _ _ measurable_id hfg,
    AEEqFun.compMeasurePreserving_id]

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]

/-- The application lemma for `MeasureTheory.Lp.compMeasurePreservingₗᵢ`.

Mathlib marks that definition `@[simps!]`, which generates `compMeasurePreservingₗᵢ_apply_coe`
— an equation about the underlying `AEEqFun`, one unfolding past the point where a rewrite is
usable. This states the map itself. -/
@[simp]
theorem compMeasurePreservingₗᵢ_apply (hf : MeasurePreserving f μ μb) (x : Lp E p μb) :
    compMeasurePreservingₗᵢ 𝕜 f hf x = compMeasurePreserving f hf x :=
  rfl

/-- **The `L^p` isometric equivalence induced by an almost-everywhere inverse pair of
measure-preserving maps.**

`f` and `g` are each measure-preserving and `f ∘ g` is the identity almost everywhere;
precomposition by `f` is then an isometric isomorphism `Lp E p μb ≃ₗᵢ[𝕜] Lp E p μ`, with inverse
precomposition by `g`.

The symmetric hypothesis `g ∘ f =ᵐ[μ] id` is not required: precomposition by `g` is injective,
so a one-sided inverse of it is already two-sided.

The almost-everywhere hypothesis is what makes this usable for a change of variables: `Real.cos`
and `Real.arccos` satisfy it without forming a `MeasurableEquiv`. -/
noncomputable def compMeasurePreservingₗᵢEquiv (hf : MeasurePreserving f μ μb)
    (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) : Lp E p μb ≃ₗᵢ[𝕜] Lp E p μ :=
  have h := leftInverse_compMeasurePreserving (E := E) (p := p) hf hg hfg
  LinearIsometryEquiv.ofLinearIsometry (compMeasurePreservingₗᵢ 𝕜 f hf)
    (compMeasurePreservingₗ 𝕜 g hg)
    (LinearMap.ext (h.rightInverse_of_injective (isometry_compMeasurePreserving hg).injective))
    (LinearMap.ext h)

@[simp]
theorem compMeasurePreservingₗᵢEquiv_apply (hf : MeasurePreserving f μ μb)
    (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x = compMeasurePreserving f hf x := by
  rw [compMeasurePreservingₗᵢEquiv, LinearIsometryEquiv.coe_ofLinearIsometry,
    compMeasurePreservingₗᵢ_apply]

@[simp]
theorem compMeasurePreservingₗᵢEquiv_symm_apply (hf : MeasurePreserving f μ μb)
    (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μ) :
    (compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg).symm x = compMeasurePreserving g hg x := by
  rw [compMeasurePreservingₗᵢEquiv, LinearIsometryEquiv.coe_ofLinearIsometry_symm]
  rfl

/-- The equivalence is almost everywhere precomposition by `f`. -/
theorem coeFn_compMeasurePreservingₗᵢEquiv (hf : MeasurePreserving f μ μb)
    (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    ⇑(compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x) =ᵐ[μ] ⇑x ∘ f := by
  rw [compMeasurePreservingₗᵢEquiv_apply]
  exact coeFn_compMeasurePreserving x hf

/-- The inverse equivalence is almost everywhere precomposition by `g`. -/
theorem coeFn_compMeasurePreservingₗᵢEquiv_symm (hf : MeasurePreserving f μ μb)
    (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μ) :
    ⇑((compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg).symm x) =ᵐ[μb] ⇑x ∘ g := by
  rw [compMeasurePreservingₗᵢEquiv_symm_apply]
  exact coeFn_compMeasurePreserving x hg

section ContinuousMap

variable [TopologicalSpace α] [CompactSpace α] [BorelSpace α] [TopologicalSpace β]
  [CompactSpace β] [BorelSpace β] [SecondCountableTopologyEither α E]
  [SecondCountableTopologyEither β E] [IsFiniteMeasure μ] [IsFiniteMeasure μb]

/-- Precomposition of the `Lp` class of a continuous function by a measure-preserving continuous
map is the `Lp` class of the composite continuous function. -/
@[simp]
theorem compMeasurePreserving_toLp (F : C(β, E)) (φ : C(α, β)) (hφ : MeasurePreserving φ μ μb) :
    compMeasurePreserving φ hφ (ContinuousMap.toLp p μb 𝕜 F) =
      ContinuousMap.toLp p μ 𝕜 (F.comp φ) := by
  refine Lp.ext ((coeFn_compMeasurePreserving _ hφ).trans ?_)
  exact (hφ.quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μb F)).trans
      (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μ (F.comp φ)).symm

end ContinuousMap

end Lp
end MeasureTheory
