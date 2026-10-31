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
groups by invariant means on Haar `L∞`.

On a discrete group, conversely, every mean on `UCB G` arises in this way, from exactly one
functional (`TauCeti.Mean.lpTopEquiv`), whenever `μ` charges every point (`μ.IsOpenPosMeasure`):
then every essentially bounded function is bounded, so taking classes identifies `UCB G`, which
is all bounded functions, with `L∞(G, μ)` (`BoundedContinuousFunction.toLpTopLinearIsometryEquiv`).
The correspondence preserves left invariance. Hence a discrete group is amenable exactly when
`L∞` of a Haar measure, or of any left-invariant measure charging every point, carries a
left-invariant mean (`TauCeti.amenable_iff_exists_lpTop`). This is the characterization of
amenable locally compact groups by invariant means on Haar `L∞`, in the discrete case.

For a compact group, integration against the normalized Haar measure `TauCeti.haarProb G` is
such a mean on `L∞`, by left invariance of Haar measure. Hence every compact topological group
is amenable, for its given topology.

## Main definitions

* `TauCeti.Mean.ofLpTop M hM`: the restriction `f ↦ M [f]` of a normalized positive functional
  on `L∞` to a mean on `UCB G`.
* `TauCeti.Mean.lpTopEquiv μ`: on a discrete group, the bijection between means on `UCB G` and
  normalized positive functionals on `L∞(G, μ)`, inverse to `TauCeti.Mean.ofLpTop`.

## Main results

* `TauCeti.Mean.isLeftInvariant_ofLpTop`: the restriction of a left-invariant functional is a
  left-invariant mean.
* `TauCeti.Amenable.of_lpTop`: a topological group with a left-invariant normalized positive
  functional on `L∞` of a left-invariant measure is amenable.
* `TauCeti.Mean.isLeftInvariant_iff_lpTopEquiv`: on a discrete group, a mean is left invariant
  exactly when the corresponding functional on `L∞` is.
* `TauCeti.amenable_iff_exists_lpTop`: a discrete group is amenable exactly when `L∞` of a
  left-invariant measure charging every point carries a left-invariant mean.
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

section Discrete

variable [DiscreteTopology G] [μ.IsOpenPosMeasure]

namespace Mean

variable (μ) in
/-- The functional `[f] ↦ m f` on `L∞(G, μ)` induced by a mean `m` on a discrete group. -/
private def lpTopFunctional (m : Mean G) : Lp ℝ ∞ μ →ₚ[ℝ] ℝ where
  toLinearMap := m.toPositiveLinearMap.toLinearMap ∘ₗ
    (UCB.discreteAlgEquiv G).symm.toLinearMap ∘ₗ
    (toLpTopLinearIsometryEquiv μ ℝ).symm.toLinearEquiv.toLinearMap
  monotone' _ _ h := OrderHomClass.mono m
    (UCB.discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff.2
      ((toLpTopLinearIsometryEquiv_symm_le_symm_iff μ).2 h))

private theorem lpTopFunctional_apply (m : Mean G) (φ : Lp ℝ ∞ μ) :
    lpTopFunctional μ m φ =
      m ((UCB.discreteAlgEquiv G).symm ((toLpTopLinearIsometryEquiv μ ℝ).symm φ)) :=
  rfl

variable (μ) in
/-- On a discrete group, means on `UCB G` correspond to positive linear functionals `M` on
`L∞(G, μ)` with `M 1 = 1`, for any measure `μ` charging every point. A mean `m` corresponds to
`[f] ↦ m f`, and the inverse is the restriction `TauCeti.Mean.ofLpTop`. -/
def lpTopEquiv : Mean G ≃ {M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ // M linftyOne = 1} where
  toFun m := ⟨lpTopFunctional μ m, by
    have h₁ : (toLpTopLinearIsometryEquiv μ ℝ).symm linftyOne = 1 := by
      rw [LinearIsometryEquiv.symm_apply_eq, coe_toLpTopLinearIsometryEquiv, toLpTop_one]
    simp [lpTopFunctional_apply, h₁]⟩
  invFun M := ofLpTop M.1 M.2
  left_inv m := ext fun f => by
    rw [ofLpTop_apply, lpTopFunctional_apply, toLpTopLinearIsometryEquiv_symm_toLpTop,
      ← UCB.discreteAlgEquiv_apply, AlgEquiv.symm_apply_apply]
  right_inv M := Subtype.ext (PositiveLinearMap.ext fun φ => by simp [lpTopFunctional_apply])

/-- The functional corresponding to a mean `m` evaluates `m` on the bounded function
representing a class in `L∞`. -/
theorem lpTopEquiv_apply (m : Mean G) (φ : Lp ℝ ∞ μ) :
    (lpTopEquiv μ m).1 φ =
      m ((UCB.discreteAlgEquiv G).symm ((toLpTopLinearIsometryEquiv μ ℝ).symm φ)) :=
  lpTopFunctional_apply m φ

/-- The functional corresponding to a mean `m` takes the value `m f` at the class of `f`. -/
@[simp]
theorem lpTopEquiv_apply_toLpTop (m : Mean G) (f : G →ᵇ ℝ) :
    (lpTopEquiv μ m).1 (toLpTop μ ℝ f) = m ((UCB.discreteAlgEquiv G).symm f) := by
  rw [lpTopEquiv_apply, toLpTopLinearIsometryEquiv_symm_toLpTop]

/-- The mean corresponding to a normalized positive functional on `L∞` is its restriction. -/
@[simp]
theorem lpTopEquiv_symm_apply (M : {M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ // M linftyOne = 1}) :
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
theorem amenable_iff_exists_lpTop [μ.IsMulLeftInvariant] :
    Amenable G ↔ ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M linftyOne = 1 ∧
      ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ := by
  refine ⟨fun h => ?_, fun ⟨M, hM, h⟩ => Amenable.of_lpTop M hM h⟩
  obtain ⟨m, hm⟩ := (amenable_iff G).1 h
  exact ⟨(Mean.lpTopEquiv μ m).1, (Mean.lpTopEquiv μ m).2,
    Mean.isLeftInvariant_iff_lpTopEquiv.1 hm⟩

end Discrete

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
