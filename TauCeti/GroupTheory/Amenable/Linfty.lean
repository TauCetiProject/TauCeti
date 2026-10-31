/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Function.Lp.Restriction
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Invariant means on `L∞` restrict to invariant means on `UCB`

Let `μ` be a left-invariant measure on the Borel sets of a topological group `G`, for instance
a left Haar measure. Taking almost-everywhere classes, `f ↦ [f]`, is a positive linear map
`TauCeti.UCB G → Lp ℝ ∞ μ` which sends `1` to `1` and intertwines the left translations
`L_g f = f (g⁻¹ * ·)` on both sides (`BoundedContinuousFunction.toLpTop`,
`MeasureTheory.Lp.leftTranslation_toLpTop`). When `μ` is positive on nonempty open sets, as Haar
measures are, it is moreover isometric (`BoundedContinuousFunction.norm_toLpTop`).

Consequently a positive linear functional `M` on `L∞(G, μ)` with `M 1 = 1` restricts to a mean
`f ↦ M [f]` on `UCB G` (`TauCeti.Mean.ofLpTop`), and this mean is left invariant when `M` is.
So a topological group is amenable as soon as `L∞` of some left-invariant measure carries a
left-invariant mean; this is one implication of the characterization of amenable locally compact
groups by invariant means on Haar `L∞`.

For a compact group, integration against the normalized Haar measure `TauCeti.haarProb G` is
such a mean on `L∞`, by left invariance of Haar measure. Hence every compact topological group
is amenable, for its given topology.

## Main definitions

* `TauCeti.Mean.ofLpTop M hM`: the restriction `f ↦ M [f]` of a normalized positive functional
  on `L∞` to a mean on `UCB G`.

## Main results

* `TauCeti.Mean.isLeftInvariant_ofLpTop`: the restriction of a left-invariant functional is a
  left-invariant mean.
* `TauCeti.Amenable.of_lpTop`: a topological group with a left-invariant normalized positive
  functional on `L∞` of a left-invariant measure is amenable.
* `TauCeti.Amenable.of_compactSpace`: every compact topological group is amenable.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, in particular
  Theorem G.3.1 for the comparison of means on `UCB` and on `L∞`.
-/

public section

noncomputable section

open MeasureTheory BoundedContinuousFunction
open scoped ENNReal BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G}

namespace Mean

/-- The restriction `f ↦ M [f]` of a positive linear functional `M` on `L∞(G, μ)` with
`M 1 = 1` to a mean on `UCB G`, where `[f]` is the almost-everywhere class of `f`. -/
def ofLpTop (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (hM : M linftyOne = 1) : Mean G :=
  mk₀ (M.toLinearMap ∘ₗ (toLpTop μ ℝ).toLinearMap ∘ₗ (ucb G).val.toLinearMap)
    (fun f hf => M.map_nonneg (by simpa using toLpTop_mono μ (f := 0) hf))
    (by simpa using hM)

/-- The restricted mean evaluates `M` on the class of `f` in `L∞`. -/
@[simp]
theorem ofLpTop_apply (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (hM : M linftyOne = 1) (f : UCB G) :
    ofLpTop M hM f = M (toLpTop μ ℝ (f : G →ᵇ ℝ)) :=
  mk₀_apply ..

/-- If a normalized positive functional on `L∞(G, μ)` is invariant under left translation, so is
its restriction to `UCB G`. -/
theorem isLeftInvariant_ofLpTop [μ.IsMulLeftInvariant] {M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ}
    (hM : M linftyOne = 1) (h : ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) :
    (Mean.ofLpTop M hM).IsLeftInvariant := by
  refine isLeftInvariant_iff.2 fun g f => ?_
  rw [ofLpTop_apply, ofLpTop_apply, UCB.coe_leftTranslation, ← Lp.leftTranslation_toLpTop, h]

end Mean

/-- A topological group is amenable if, for some left-invariant measure `μ` on its Borel sets,
`L∞(G, μ)` carries a positive linear functional `M` with `M 1 = 1` which is invariant under left
translation. -/
theorem Amenable.of_lpTop [μ.IsMulLeftInvariant] (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (hM : M linftyOne = 1)
    (h : ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) : Amenable G :=
  (amenable_iff G).2 ⟨Mean.ofLpTop M hM, Mean.isLeftInvariant_ofLpTop hM h⟩

end TauCeti

namespace TauCeti

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Every compact topological group is amenable: integration against normalized Haar measure is
a left-invariant mean on its `L∞`, and restricts to a left-invariant mean on `UCB G`. -/
instance (priority := 100) Amenable.of_compactSpace : Amenable G := by
  borelize G
  -- Integration against normalized Haar measure, as a positive functional on `L∞`.
  let I := Set.setIntegralLp (𝕜 := ℝ) (F := ℝ) (p := ∞) (μ := haarProb G) Set.univ
    (measure_lt_top _ _)
  have hI (φ : Lp ℝ ∞ (haarProb G)) : I φ = ∫ x, φ x ∂haarProb G := by
    rw [Set.setIntegralLp_apply, setIntegral_univ]
  let M : Lp ℝ ∞ (haarProb G) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ I.toLinearMap
    fun φ hφ => (hI φ).trans_ge (integral_nonneg_of_ae ((Lp.coeFn_nonneg φ).2 hφ))
  have hM : M linftyOne = 1 := (hI _).trans ((integral_congr_ae coeFn_linftyOne).trans (by simp))
  refine Amenable.of_lpTop M hM fun g φ => ?_
  -- `M φ` is by definition `I φ`; `PositiveLinearMap.mk₀` has no evaluation lemma.
  exact (hI _).trans ((Lp.integral_leftTranslation g φ).trans (hI φ).symm)

end TauCeti
