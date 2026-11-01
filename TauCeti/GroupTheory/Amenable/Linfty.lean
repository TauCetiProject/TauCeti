/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.MeasureTheory.Function.Lp.AddContent
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Function.Lp.Restriction
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Invariant means on `L∞`, finitely additive probabilities, and `UCB`

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

Positive functionals on `L∞(G, μ)` correspond to nonnegative finitely additive set functions on
the measurable sets which vanish on `μ`-null sets, by `M ↦ (s ↦ M [1_s])`
(`MeasureTheory.AddContent.linftyIntegral`). Since left translation maps `[1_s]` to `[1_(g • s)]`,
a functional is left invariant exactly when its set function is. Hence `L∞(G, μ)` carries a
left-invariant mean exactly when the measurable sets carry a left-invariant finitely additive
probability vanishing on `μ`-null sets, and such a probability also makes `G` amenable.

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
* `PositiveLinearMap.forall_apply_leftTranslation_eq_iff`: a positive functional on `L∞` is left
  invariant exactly when its set function `s ↦ M [1_s]` is.
* `TauCeti.exists_linftyMean_iff_exists_invariantContent`: `L∞(G, μ)` carries a left-invariant
  mean exactly when the measurable sets carry a left-invariant finitely additive probability
  vanishing on `μ`-null sets.
* `TauCeti.Amenable.of_invariantContent`: such a probability makes a topological group amenable.
* `TauCeti.Amenable.of_compactSpace`: every compact topological group is amenable.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, in particular
  Theorem G.3.1 for the comparison of means on `UCB` and on `L∞`.
-/

public section

noncomputable section

open MeasureTheory BoundedContinuousFunction
open scoped ENNReal BoundedContinuousFunction Pointwise

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

namespace PositiveLinearMap

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [μ.IsMulLeftInvariant]

/-- A positive functional on `L∞(μ)` is invariant under left translation exactly when its set
function `s ↦ M [1_s]` is invariant under left multiplication of measurable sets. -/
theorem forall_apply_leftTranslation_eq_iff (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) :
    (∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∀ (g : G) s, MeasurableSet s →
        M.toLinearMap.linftyContent (g • s) = M.toLinearMap.linftyContent s := by
  refine ⟨fun h g s hs => ?_, fun h g => ?_⟩
  · rw [LinearMap.linftyContent_apply _ hs, LinearMap.linftyContent_apply _ (hs.const_smul g),
      ← Lp.leftTranslation_linftyIndicator]
    exact h g _
  · -- `φ ↦ M (L_g φ)` is a positive functional with the same set function as `M`.
    let Mg : Lp ℝ ∞ μ →ₚ[ℝ] ℝ :=
      { toLinearMap := M.toLinearMap ∘ₗ (Lp.leftTranslation μ ∞ ℝ g).toLinearMap
        monotone' := fun _ _ hφ => M.monotone' (Lp.leftTranslation_mono g hφ) }
    have hMg : Mg = M := ext_linftyIndicator fun s hs => by
      have := h g s hs
      rw [LinearMap.linftyContent_apply _ hs, LinearMap.linftyContent_apply _ (hs.const_smul g),
        ← Lp.leftTranslation_linftyIndicator] at this
      -- `Mg ψ` is `M (L_g ψ)` by construction.
      exact this
    exact fun φ => DFunLike.congr_fun hMg φ

end PositiveLinearMap

namespace TauCeti

open MeasureTheory

section Content

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [μ.IsMulLeftInvariant]

/-- `L∞` of a left-invariant measure `μ` carries a left-invariant positive functional `M` with
`M 1 = 1` exactly when the measurable sets carry a left-invariant finitely additive probability
`ν` which vanishes on `μ`-null sets. The correspondence is `ν s = M [1_s]`. -/
theorem exists_linftyMean_iff_exists_invariantContent :
    (∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M linftyOne = 1 ∧
        ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∃ ν : AddContent ℝ≥0∞ {s : Set G | MeasurableSet s}, ν Set.univ = 1 ∧
        (∀ s, MeasurableSet s → μ s = 0 → ν s = 0) ∧
        ∀ (g : G) s, MeasurableSet s → ν (g • s) = ν s := by
  constructor
  · rintro ⟨M, hM1, hM⟩
    refine ⟨M.toLinearMap.linftyContent.ofReal fun _ => M.linftyContent_nonneg, ?_, ?_, ?_⟩
    · simpa using congrArg ENNReal.ofReal hM1
    · intro s hs hμs
      simp [LinearMap.linftyContent_of_measure_eq_zero _ hs hμs]
    · intro g s hs
      simp [(M.forall_apply_leftTranslation_eq_iff.1 hM) g s hs]
  · rintro ⟨ν, hν1, hνμ, hνg⟩
    have hfin : ∀ s ∈ {s : Set G | MeasurableSet s}, ν s ≠ ∞ := fun s hs =>
      ne_top_of_le_ne_top (hν1 ▸ ENNReal.one_ne_top) (addContent_mono
        isSetRing_setOf_measurableSet.isSetSemiring hs MeasurableSet.univ (Set.subset_univ s))
    let M := AddContent.linftyIntegral (ν := ν.toReal hfin) (μ := μ)
      (fun s _ => AddContent.toReal_nonneg ν hfin s) fun s hs hμs => by simp [hνμ s hs hμs]
    refine ⟨M, by simp [M, hν1], M.forall_apply_leftTranslation_eq_iff.2 fun g s hs => ?_⟩
    rw [LinearMap.linftyContent_linftyIntegral _ _ hs,
      LinearMap.linftyContent_linftyIntegral _ _ (hs.const_smul g), AddContent.toReal_apply,
      AddContent.toReal_apply, hνg g s hs]

end Content

/-- A topological group is amenable if, for some left-invariant measure `μ` on its Borel sets,
the measurable sets carry a left-invariant finitely additive probability vanishing on `μ`-null
sets. -/
theorem Amenable.of_invariantContent {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [μ.IsMulLeftInvariant] (ν : AddContent ℝ≥0∞ {s : Set G | MeasurableSet s})
    (hν1 : ν Set.univ = 1) (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)
    (hνg : ∀ (g : G) s, MeasurableSet s → ν (g • s) = ν s) : Amenable G :=
  have ⟨M, hM1, hM⟩ := exists_linftyMean_iff_exists_invariantContent.2 ⟨ν, hν1, hνμ, hνg⟩
  Amenable.of_lpTop (μ := μ) M hM1 hM

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
