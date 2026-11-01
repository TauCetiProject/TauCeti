/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Finite
public import TauCeti.MeasureTheory.Function.Lp.AbsolutelyContinuous
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

Whether `L∞(G, μ)` carries such an invariant functional depends only on the null sets of `μ`:
the classes of essentially bounded functions for measures with the same null sets correspond,
compatibly with order, the constant one and left translation. In particular it is unchanged by
multiplying `μ` by a nonzero constant, and on a locally compact group it does not depend on the
choice of regular Haar measure.

For a Borel probability measure `μ`, integration `φ ↦ ∫ x, φ x ∂μ` is a normalized positive
functional on `L∞(G, μ)` (`MeasureTheory.Lp.integralPositiveLinearMap`), left invariant
when `μ` is. Its restriction to `UCB G` is the mean `f ↦ ∫ x, f x ∂μ` (`TauCeti.Mean.integral`).
For a compact group, the normalized Haar measure `TauCeti.haarProb G` is such a measure. Hence
every compact topological group is amenable, for its given topology. On a finite group, with any
group topology, the Haar mean is the normalized counting mean `f ↦ (∑ x, f x) / |G|`, since that
is the only left-invariant mean (`TauCeti.Mean.IsLeftInvariant.eq_uniform`).

## Main definitions

* `TauCeti.Mean.ofLpTop M hM`: the restriction `f ↦ M [f]` of a normalized positive functional
  on `L∞` to a mean on `UCB G`.
* `TauCeti.Mean.integral μ`: integration against a Borel probability measure, as a mean on
  `UCB G`.

## Main results

* `TauCeti.Mean.isLeftInvariant_ofLpTop`: the restriction of a left-invariant functional is a
  left-invariant mean.
* `TauCeti.Amenable.of_lpTop`: a topological group with a left-invariant normalized positive
  functional on `L∞` of a left-invariant measure is amenable.
* `TauCeti.Mean.isLeftInvariant_integral`: integration against a left-invariant probability
  measure is a left-invariant mean.
* `TauCeti.exists_lpTop_invariant_of_absolutelyContinuous`: such a functional for `μ` gives one
  for every left-invariant `ν` with `μ ≪ ν`.
* `TauCeti.exists_lpTop_invariant_smul_iff`, `TauCeti.exists_lpTop_invariant_iff_of_regular`:
  existence is unchanged by scaling `μ`, and is the same for all regular Haar measures.
* `TauCeti.Amenable.of_compactSpace`: every compact topological group is amenable.
* `TauCeti.Mean.integral_haarProb`: on a finite group, integration against normalized Haar
  measure is the uniform mean.

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

variable (μ) in
/-- Integration against a Borel probability measure `μ`, `f ↦ ∫ x, f x ∂μ`, as a mean on `UCB G`.
It is the restriction to `UCB G` of integration against `μ` on `L∞(G, μ)`. -/
def integral [IsProbabilityMeasure μ] : Mean G :=
  ofLpTop (Lp.integralPositiveLinearMap μ ∞) (by simp)

/-- The integration mean integrates a function in `UCB G` against `μ`. -/
@[simp]
theorem integral_apply [IsProbabilityMeasure μ] (f : UCB G) :
    integral μ f = ∫ x, (f : G →ᵇ ℝ) x ∂μ := by
  rw [integral, ofLpTop_apply, Lp.integralPositiveLinearMap_apply]
  exact integral_congr_ae (coeFn_toLpTop μ (𝕜 := ℝ) (f : G →ᵇ ℝ))

/-- Integration against a Dirac mass is evaluation at its point. -/
@[simp]
theorem integral_dirac (x : G) : integral (Measure.dirac x) = eval G x :=
  ext fun f => by
    rw [integral_apply, eval_apply, integral_dirac' _ _ (f : G →ᵇ ℝ).continuous.stronglyMeasurable]

/-- Integration against a left-invariant probability measure is a left-invariant mean. -/
theorem isLeftInvariant_integral [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    (integral μ).IsLeftInvariant :=
  isLeftInvariant_ofLpTop _ fun g φ => by simp

end Mean

/-- A topological group is amenable if, for some left-invariant measure `μ` on its Borel sets,
`L∞(G, μ)` carries a positive linear functional `M` with `M 1 = 1` which is invariant under left
translation. -/
theorem Amenable.of_lpTop [μ.IsMulLeftInvariant] (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (hM : M linftyOne = 1)
    (h : ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) : Amenable G :=
  (amenable_iff G).2 ⟨Mean.ofLpTop M hM, Mean.isLeftInvariant_ofLpTop hM h⟩

end TauCeti

namespace TauCeti

/-! ### Independence of the measure within its class -/

section AbsolutelyContinuous

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ ν : Measure G}
  [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]

/-- Let `μ ≪ ν` be left-invariant measures on a group. If `L∞(G, μ)` carries a left-invariant
positive linear functional `M` with `M 1 = 1`, then so does `L∞(G, ν)`: send a `ν`-class to its
`μ`-class and apply `M`. -/
theorem exists_lpTop_invariant_of_absolutelyContinuous (h : μ ≪ ν)
    (hμ : ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M linftyOne = 1 ∧
      ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) :
    ∃ M : Lp ℝ ∞ ν →ₚ[ℝ] ℝ, M linftyOne = 1 ∧ ∀ g φ, M (Lp.leftTranslation ν ∞ ℝ g φ) = M φ := by
  obtain ⟨M, hM₁, hM⟩ := hμ
  let T : Lp ℝ ∞ ν →L[ℝ] Lp ℝ ∞ μ := Lp.linftyOfAbsolutelyContinuous ℝ h
  let M' : Lp ℝ ∞ ν →ₚ[ℝ] ℝ :=
    { M.toLinearMap ∘ₗ (T : Lp ℝ ∞ ν →ₗ[ℝ] Lp ℝ ∞ μ) with
      monotone' := fun _ _ hφψ => M.monotone' (Lp.linftyOfAbsolutelyContinuous_mono h hφψ) }
  -- `M'` is built as a structure, so its evaluation is `M ∘ T` by definition.
  have hM' (φ : Lp ℝ ∞ ν) : M' φ = M (T φ) := rfl
  refine ⟨M', ?_, fun g φ => ?_⟩
  · rw [hM', Lp.linftyOfAbsolutelyContinuous_linftyOne, hM₁]
  · rw [hM', hM', ← Lp.leftTranslation_linftyOfAbsolutelyContinuous, hM]

/-- For left-invariant measures `μ` and `ν` on a group with the same null sets, `L∞(G, μ)` carries
a left-invariant positive linear functional taking the value `1` at `1` if and only if
`L∞(G, ν)` does. -/
theorem exists_lpTop_invariant_congr (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M linftyOne = 1 ∧ ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∃ M : Lp ℝ ∞ ν →ₚ[ℝ] ℝ, M linftyOne = 1 ∧
        ∀ g φ, M (Lp.leftTranslation ν ∞ ℝ g φ) = M φ :=
  ⟨exists_lpTop_invariant_of_absolutelyContinuous hμν,
    exists_lpTop_invariant_of_absolutelyContinuous hνμ⟩

/-- The existence of a left-invariant positive linear functional on `L∞(G, μ)` taking the value
`1` at `1` is unchanged when `μ` is multiplied by a nonzero constant. -/
theorem exists_lpTop_invariant_smul_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∃ M : Lp ℝ ∞ (c • μ) →ₚ[ℝ] ℝ, M linftyOne = 1 ∧
      ∀ g φ, M (Lp.leftTranslation (c • μ) ∞ ℝ g φ) = M φ) ↔
      ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M linftyOne = 1 ∧
        ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ :=
  exists_lpTop_invariant_congr Measure.smul_absolutelyContinuous
    (Measure.absolutelyContinuous_smul hc)

end AbsolutelyContinuous

/-- On a locally compact group, the existence of a left-invariant positive linear functional on
Haar `L∞` taking the value `1` at `1` does not depend on the choice of regular Haar measure. -/
theorem exists_lpTop_invariant_iff_of_regular {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] [μ.Regular] [ν.Regular] :
    (∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M linftyOne = 1 ∧ ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∃ M : Lp ℝ ∞ ν →ₚ[ℝ] ℝ, M linftyOne = 1 ∧
        ∀ g φ, M (Lp.leftTranslation ν ∞ ℝ g φ) = M φ := by
  refine exists_lpTop_invariant_congr ?_ ?_
  · rw [Measure.isMulLeftInvariant_eq_smul_of_regular μ ν]
    exact Measure.smul_absolutelyContinuous
  · rw [Measure.isMulLeftInvariant_eq_smul_of_regular ν μ]
    exact Measure.smul_absolutelyContinuous

end TauCeti

namespace TauCeti

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every compact topological group is amenable: integration against normalized Haar measure is
a left-invariant mean on `UCB G`. -/
instance (priority := 100) Amenable.of_compactSpace [CompactSpace G] : Amenable G := by
  borelize G
  exact (amenable_iff G).2 ⟨Mean.integral (haarProb G), Mean.isLeftInvariant_integral⟩

variable [MeasurableSpace G] [BorelSpace G]

/-- On a finite group, with any group topology, integration against normalized Haar measure is
the normalized counting mean `f ↦ (∑ x, f x) / |G|`. -/
theorem Mean.integral_haarProb [Finite G] : integral (haarProb G) = uniform G :=
  isLeftInvariant_integral.eq_uniform

end TauCeti
