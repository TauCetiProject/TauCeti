/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Finite
public import TauCeti.MeasureTheory.Function.Lp.AbsolutelyContinuous
public import TauCeti.MeasureTheory.Function.Lp.AddContent
public import TauCeti.MeasureTheory.Function.Lp.Restriction
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Invariant means on `L∞` and invariant means on `UCB`

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
groups by invariant means on Haar `L∞`. Such functionals correspond to finitely additive
probabilities on the Borel sets vanishing on `μ`-null sets
(`TauCeti/MeasureTheory/Function/Lp/AddContent.lean`), so a left-invariant such probability also
makes `G` amenable.

On a discrete group, conversely, every mean on `UCB G` arises in this way, from exactly one
functional (`TauCeti.Mean.lpTopEquiv`), whenever `μ` charges every point (`μ.IsOpenPosMeasure`):
then every essentially bounded function is bounded, so taking classes identifies `UCB G`, which
is all bounded functions, with `L∞(G, μ)` (`BoundedContinuousFunction.toLpTopLinearIsometryEquiv`).
The correspondence preserves left invariance. Hence a discrete group is amenable exactly when
`L∞` of a Haar measure, or of any left-invariant measure charging every point, carries a
left-invariant mean (`TauCeti.amenable_iff_exists_lpTop_invariant`). This is the
characterization of amenable locally compact groups by invariant means on Haar `L∞`, in the
discrete case.

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
* `TauCeti.Mean.lpTopEquiv μ`: on a discrete group, the bijection between means on `UCB G` and
  normalized positive functionals on `L∞(G, μ)`, inverse to `TauCeti.Mean.ofLpTop`.
* `TauCeti.Mean.integral μ`: integration against a Borel probability measure, as a mean on
  `UCB G`.

## Main results

* `TauCeti.Mean.isLeftInvariant_ofLpTop`: the restriction of a left-invariant functional is a
  left-invariant mean.
* `TauCeti.Amenable.of_lpTop`: a topological group with a left-invariant normalized positive
  functional on `L∞` of a left-invariant measure is amenable.
* `TauCeti.Amenable.of_addContent`: a topological group with a left-invariant finitely additive
  probability on its Borel sets vanishing on the null sets of a left-invariant measure is amenable.
* `TauCeti.Mean.isLeftInvariant_iff_lpTopEquiv`: on a discrete group, a mean is left invariant
  exactly when the corresponding functional on `L∞` is.
* `TauCeti.amenable_iff_exists_lpTop_invariant`: a discrete group is amenable exactly when `L∞`
  of a left-invariant measure charging every point carries a left-invariant mean.
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
open scoped ENNReal BoundedContinuousFunction Pointwise

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G}

namespace Mean

/-- The restriction `f ↦ M [f]` of a positive linear functional `M` on `L∞(G, μ)` with
`M 1 = 1` to a mean on `UCB G`, where `[f]` is the almost-everywhere class of `f`. -/
def ofLpTop (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (hM : M 1 = 1) : Mean G :=
  mk₀ (M.toLinearMap ∘ₗ (toLpTop μ ℝ).toLinearMap ∘ₗ (ucb G).val.toLinearMap)
    (fun f hf => M.map_nonneg (by simpa using toLpTop_mono μ (f := 0) hf))
    (by simpa using hM)

/-- The restricted mean evaluates `M` on the class of `f` in `L∞`. -/
@[simp]
theorem ofLpTop_apply (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (hM : M 1 = 1) (f : UCB G) :
    ofLpTop M hM f = M (toLpTop μ ℝ (f : G →ᵇ ℝ)) :=
  mk₀_apply ..

/-- If a normalized positive functional on `L∞(G, μ)` is invariant under left translation, so is
its restriction to `UCB G`. -/
theorem isLeftInvariant_ofLpTop [μ.IsMulLeftInvariant] {M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ}
    (hM : M 1 = 1) (h : ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) :
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
theorem Amenable.of_lpTop [μ.IsMulLeftInvariant] (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (hM : M 1 = 1)
    (h : ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) : Amenable G :=
  (amenable_iff G).2 ⟨Mean.ofLpTop M hM, Mean.isLeftInvariant_ofLpTop hM h⟩

/-- A topological group is amenable if, for some left-invariant measure `μ` on its Borel sets,
there is a left-invariant finitely additive probability `ν` on the Borel sets that vanishes on
`μ`-null sets. Integration against `ν` is then a left-invariant mean on `L∞(G, μ)`. -/
theorem Amenable.of_addContent [μ.IsMulLeftInvariant]
    (ν : AddContent ℝ {s : Set G | MeasurableSet s}) (hν₀ : ∀ s, MeasurableSet s → 0 ≤ ν s)
    (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) (hν₁ : ν Set.univ = 1)
    (hν : ∀ (g : G) s, MeasurableSet s → ν (g • s) = ν s) : Amenable G := by
  refine Amenable.of_lpTop (PositiveLinearMap.ofAddContentLpTop ν hν₀ hνμ) (by simpa using hν₁)
    ((PositiveLinearMap.forall_apply_leftTranslation_eq_iff _).2 fun g s hs => ?_)
  rw [PositiveLinearMap.toAddContentLpTop_ofAddContentLpTop_apply _ _ hs,
    PositiveLinearMap.toAddContentLpTop_ofAddContentLpTop_apply _ _ (hs.const_smul g), hν g s hs]

section Discrete

variable [DiscreteTopology G] [μ.IsOpenPosMeasure]

namespace Mean

variable (μ) in
/-- On a discrete group, means on `UCB G` correspond to positive linear functionals `M` on
`L∞(G, μ)` with `M 1 = 1`, for any measure `μ` charging every point. A mean `m` corresponds to
`[f] ↦ m f`, and the inverse is the restriction `TauCeti.Mean.ofLpTop`. -/
def lpTopEquiv : Mean G ≃ {M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ // M 1 = 1} where
  toFun m := ⟨{
      toLinearMap := m.toPositiveLinearMap.toLinearMap ∘ₗ ((UCB.discreteLinearIsometryEquiv G).trans
        (toLpTopLinearIsometryEquiv μ ℝ)).symm.toLinearEquiv.toLinearMap
      monotone' := fun _ _ h => OrderHomClass.mono m (by simpa using h) },
    (congrArg m (by simp)).trans m.map_one⟩
  invFun M := ofLpTop M.1 M.2
  left_inv m := ext fun f => (ofLpTop_apply _ _ f).trans
    (congrArg m (by simpa using (UCB.discreteAlgEquiv G).symm_apply_apply f))
  right_inv M := Subtype.ext (PositiveLinearMap.ext fun φ =>
    (ofLpTop_apply M.1 M.2 _).trans (congrArg M.1 (by simp)))

/-- The functional corresponding to a mean `m` evaluates `m` on the bounded function
representing a class in `L∞`. -/
theorem lpTopEquiv_apply (m : Mean G) (φ : Lp ℝ ∞ μ) :
    (lpTopEquiv μ m).1 φ =
      m ((UCB.discreteAlgEquiv G).symm ((toLpTopLinearIsometryEquiv μ ℝ).symm φ)) :=
  congrArg m (by simp)

/-- The functional corresponding to a mean `m` takes the value `m f` at the class of `f`. -/
@[simp]
theorem lpTopEquiv_apply_toLpTop (m : Mean G) (f : G →ᵇ ℝ) :
    (lpTopEquiv μ m).1 (toLpTop μ ℝ f) = m ((UCB.discreteAlgEquiv G).symm f) := by
  rw [lpTopEquiv_apply, toLpTopLinearIsometryEquiv_symm_toLpTop]

/-- The mean corresponding to a normalized positive functional on `L∞` is its restriction. -/
@[simp]
theorem lpTopEquiv_symm_apply (M : {M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ // M 1 = 1}) :
    (lpTopEquiv μ).symm M = ofLpTop M.1 M.2 :=
  (rfl)

/-- The correspondence between means on a discrete group and normalized positive functionals on
`L∞(G, μ)` preserves and reflects left invariance. -/
theorem isLeftInvariant_iff_lpTopEquiv [μ.IsMulLeftInvariant] {m : Mean G} :
    m.IsLeftInvariant ↔
      ∀ g φ, (lpTopEquiv μ m).1 (Lp.leftTranslation μ ∞ ℝ g φ) = (lpTopEquiv μ m).1 φ := by
  refine ⟨fun hm g φ => ?_, fun h => ?_⟩
  · obtain ⟨f, rfl⟩ := toLpTop_surjective μ (𝕜 := ℝ) φ
    rw [Lp.leftTranslation_toLpTop, lpTopEquiv_apply_toLpTop, lpTopEquiv_apply_toLpTop,
      UCB.discreteAlgEquiv_symm_compContinuous_mulLeft, hm.apply_leftTranslation]
  · rw [← (lpTopEquiv μ).symm_apply_apply m, lpTopEquiv_symm_apply]
    exact isLeftInvariant_ofLpTop _ h

end Mean

variable (μ) in
/-- A discrete group is amenable exactly when, for a left-invariant measure `μ` charging every
point (for instance a Haar measure), `L∞(G, μ)` carries a left-invariant positive linear
functional `M` with `M 1 = 1`. -/
theorem amenable_iff_exists_lpTop_invariant [μ.IsMulLeftInvariant] :
    Amenable G ↔ ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M 1 = 1 ∧
      ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ := by
  refine ⟨fun h => ?_, fun ⟨M, hM, h⟩ => Amenable.of_lpTop M hM h⟩
  obtain ⟨m, hm⟩ := (amenable_iff G).1 h
  exact ⟨(Mean.lpTopEquiv μ m).1, (Mean.lpTopEquiv μ m).2,
    Mean.isLeftInvariant_iff_lpTopEquiv.1 hm⟩

end Discrete

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
    (hμ : ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M 1 = 1 ∧
      ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) :
    ∃ M : Lp ℝ ∞ ν →ₚ[ℝ] ℝ, M 1 = 1 ∧ ∀ g φ, M (Lp.leftTranslation ν ∞ ℝ g φ) = M φ := by
  obtain ⟨M, hM₁, hM⟩ := hμ
  let T : Lp ℝ ∞ ν →L[ℝ] Lp ℝ ∞ μ := Lp.linftyOfAbsolutelyContinuous ℝ h
  let M' : Lp ℝ ∞ ν →ₚ[ℝ] ℝ :=
    { M.toLinearMap ∘ₗ (T : Lp ℝ ∞ ν →ₗ[ℝ] Lp ℝ ∞ μ) with
      monotone' := fun _ _ hφψ => M.monotone' (Lp.linftyOfAbsolutelyContinuous_mono h hφψ) }
  -- `M'` is built as a structure, so its evaluation is `M ∘ T` by definition.
  have hM' (φ : Lp ℝ ∞ ν) : M' φ = M (T φ) := rfl
  refine ⟨M', ?_, fun g φ => ?_⟩
  · rw [hM', Lp.linftyOfAbsolutelyContinuous_one, hM₁]
  · rw [hM', hM', ← Lp.leftTranslation_linftyOfAbsolutelyContinuous, hM]

/-- For left-invariant measures `μ` and `ν` on a group with the same null sets, `L∞(G, μ)` carries
a left-invariant positive linear functional taking the value `1` at `1` if and only if
`L∞(G, ν)` does. -/
theorem exists_lpTop_invariant_congr (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M 1 = 1 ∧ ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∃ M : Lp ℝ ∞ ν →ₚ[ℝ] ℝ, M 1 = 1 ∧
        ∀ g φ, M (Lp.leftTranslation ν ∞ ℝ g φ) = M φ :=
  ⟨exists_lpTop_invariant_of_absolutelyContinuous hμν,
    exists_lpTop_invariant_of_absolutelyContinuous hνμ⟩

/-- The existence of a left-invariant positive linear functional on `L∞(G, μ)` taking the value
`1` at `1` is unchanged when `μ` is multiplied by a nonzero constant. -/
theorem exists_lpTop_invariant_smul_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∃ M : Lp ℝ ∞ (c • μ) →ₚ[ℝ] ℝ, M 1 = 1 ∧
      ∀ g φ, M (Lp.leftTranslation (c • μ) ∞ ℝ g φ) = M φ) ↔
      ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M 1 = 1 ∧
        ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ :=
  exists_lpTop_invariant_congr Measure.smul_absolutelyContinuous
    (Measure.absolutelyContinuous_smul hc)

end AbsolutelyContinuous

/-- On a locally compact group, the existence of a left-invariant positive linear functional on
Haar `L∞` taking the value `1` at `1` does not depend on the choice of regular Haar measure. -/
theorem exists_lpTop_invariant_iff_of_regular {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] [μ.Regular] [ν.Regular] :
    (∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M 1 = 1 ∧ ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∃ M : Lp ℝ ∞ ν →ₚ[ℝ] ℝ, M 1 = 1 ∧
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
