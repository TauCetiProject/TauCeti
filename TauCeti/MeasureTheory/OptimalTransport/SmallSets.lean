/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SingularSet
public import TauCeti.MeasureTheory.Measure.Haar.Hausdorff

/-!
# Measures vanishing on small sets

In quadratic optimal transport and Wasserstein barycenter theory on a finite-dimensional real space
`E` of dimension `n`, singular sets of convex potentials have Hausdorff dimension at most `n - 1`.
Following Agueh and Carlier, a subset of `E` is called *small* if its Hausdorff codimension is at
least `1`, encoded dimension-uniformly as `dimH A + 1 ≤ Module.finrank ℝ E` so that in dimension
`n = 0` no set (not even `∅`, which has `dimH ∅ = 0`) is small and every measure vanishes on small
sets, while in dimension `n ≥ 1` the condition agrees with `dimH A ≤ n - 1`.

## Main definitions and results

* `MeasureTheory.Measure.VanishesOnSmallSets`: a measure `μ` on `E` assigns mass `0` to every
  measurable set `A` satisfying `dimH A + 1 ≤ Module.finrank ℝ E`.
* `MeasureTheory.Measure.vanishesOnSmallSets_iff_dimH_le`: for nontrivial finite-dimensional `E`,
  `μ.VanishesOnSmallSets` is equivalent to vanishing on measurable sets of Hausdorff dimension at
  most `finrank ℝ E - 1`.
* `MeasureTheory.Measure.vanishesOnSmallSets_of_absolutelyContinuous_hausdorffMeasure`: any Borel
  measure absolutely continuous with respect to `μH[d]` for `finrank ℝ E < d + 1` vanishes on small
  sets; in particular, `vanishesOnSmallSets_addHaar` and
  `VanishesOnSmallSets.of_absolutelyContinuous` cover additive Haar measure and all measures
  absolutely continuous with respect to it.
* `MeasureTheory.Measure.VanishesOnSmallSets.measure_setOf_inner_eq_orthogonalProjectionOnto` and
  `MeasureTheory.Measure.VanishesOnSmallSets.ae_eventually_ne_top_and_differentiableAt_toReal`:
  measures vanishing on small sets assign zero mass to Lipschitz hyperplane graphs and witness
  almost-everywhere differentiability of proper convex potentials on their effective domains.

## References

* Martial Agueh and Guillaume Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal.
  **43** (2011), no. 2, 904–924, Definition 3.2.
* Robert J. McCann, *Existence and uniqueness of monotone measure-preserving maps*, Duke Math. J.
  **80** (1995), no. 2, 309–323.
-/

public section

open Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace MeasureTheory.Measure

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  {μ ν : Measure E}

/-- A measure `μ` on a real normed space `E` *vanishes on small sets* (in the sense of Agueh and
Carlier) if `μ A = 0` for every measurable set `A` with `dimH A + 1 ≤ Module.finrank ℝ E`. For
`finrank ℝ E ≥ 1` this means `dimH A ≤ finrank ℝ E - 1`; for `finrank ℝ E = 0` the inequality
`dimH A + 1 ≤ 0` is vacuous, so every measure vanishes on small sets. -/
def VanishesOnSmallSets (μ : Measure E) : Prop :=
  ∀ ⦃A : Set E⦄, MeasurableSet A → dimH A + 1 ≤ Module.finrank ℝ E → μ A = 0

/-- Defining characterization of `Measure.VanishesOnSmallSets`. -/
theorem vanishesOnSmallSets_def : μ.VanishesOnSmallSets ↔
    ∀ ⦃A : Set E⦄, MeasurableSet A → dimH A + 1 ≤ Module.finrank ℝ E → μ A = 0 := (Iff.rfl)

/-- A measure vanishing on small sets assigns mass zero to any measurable set with
`dimH A + 1 ≤ Module.finrank ℝ E`. -/
theorem VanishesOnSmallSets.measure_eq_zero (hμ : μ.VanishesOnSmallSets) {A : Set E}
    (hA : MeasurableSet A) (hdim : dimH A + 1 ≤ Module.finrank ℝ E) : μ A = 0 :=
  hμ hA hdim

/-- In a nontrivial finite-dimensional real normed space `E`, `μ.VanishesOnSmallSets` is equivalent
to `μ A = 0` for every measurable set `A` with `dimH A ≤ finrank ℝ E - 1`. -/
theorem vanishesOnSmallSets_iff_dimH_le [FiniteDimensional ℝ E] [Nontrivial E] :
    μ.VanishesOnSmallSets ↔
      ∀ ⦃A : Set E⦄, MeasurableSet A →
        dimH A ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0 := by
  have heq : ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) + 1 = Module.finrank ℝ E := by
    exact_mod_cast Nat.sub_add_cancel Module.finrank_pos
  refine forall₂_congr fun A _ => imp_congr_left ?_
  rw [← heq, ENNReal.add_le_add_iff_right ENNReal.one_ne_top]

@[simp]
theorem vanishesOnSmallSets_zero : (0 : Measure E).VanishesOnSmallSets :=
  fun _ _ _ => rfl

/-- When `Module.finrank ℝ E = 0` (for example on a zero-dimensional or infinite-dimensional space),
no set satisfies `dimH A + 1 ≤ 0`, so every measure vanishes on small sets. -/
theorem vanishesOnSmallSets_of_finrank_eq_zero (h : Module.finrank ℝ E = 0) (μ : Measure E) :
    μ.VanishesOnSmallSets := by
  intro A _ hdim
  rw [h, Nat.cast_zero] at hdim
  exact absurd (nonpos_iff_eq_zero.mp (le_add_self.trans hdim)) one_ne_zero

/-- On a subsingleton space `E`, every measure vanishes on small sets. -/
theorem vanishesOnSmallSets_of_subsingleton [Subsingleton E] (μ : Measure E) :
    μ.VanishesOnSmallSets :=
  vanishesOnSmallSets_of_finrank_eq_zero Module.finrank_zero_of_subsingleton μ

/-- `VanishesOnSmallSets` is inherited under absolute continuity. -/
theorem VanishesOnSmallSets.mono_ac (hμ : μ.VanishesOnSmallSets) (hνμ : ν ≪ μ) :
    ν.VanishesOnSmallSets :=
  fun _ hA hdim => hνμ (hμ hA hdim)

/-- `VanishesOnSmallSets` is downward-closed in the measure order. -/
theorem VanishesOnSmallSets.mono (hμ : μ.VanishesOnSmallSets) (hνμ : ν ≤ μ) :
    ν.VanishesOnSmallSets :=
  hμ.mono_ac (absolutelyContinuous_of_le hνμ)

theorem VanishesOnSmallSets.add (hμ : μ.VanishesOnSmallSets) (hν : ν.VanishesOnSmallSets) :
    (μ + ν).VanishesOnSmallSets := by
  intro A hA hdim
  simp [hμ hA hdim, hν hA hdim]

@[simp]
theorem vanishesOnSmallSets_add_iff :
    (μ + ν).VanishesOnSmallSets ↔ μ.VanishesOnSmallSets ∧ ν.VanishesOnSmallSets :=
  ⟨fun h => ⟨h.mono (Measure.le_add_right le_rfl), h.mono (Measure.le_add_left le_rfl)⟩,
    fun ⟨hμ, hν⟩ => hμ.add hν⟩

theorem VanishesOnSmallSets.smul (hμ : μ.VanishesOnSmallSets) (c : ℝ≥0∞) :
    (c • μ).VanishesOnSmallSets := by
  intro A hA hdim
  simp [hμ hA hdim]

theorem VanishesOnSmallSets.finsetSum {ι : Type*} {s : Finset ι} {μ : ι → Measure E}
    (hμ : ∀ i ∈ s, (μ i).VanishesOnSmallSets) :
    (∑ i ∈ s, μ i).VanishesOnSmallSets := by
  intro A hA hdim
  rw [FunLike.coe_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi => hμ i hi hA hdim

@[simp]
theorem vanishesOnSmallSets_sum_iff {ι : Type*} {μ : ι → Measure E} :
    (Measure.sum μ).VanishesOnSmallSets ↔ ∀ i, (μ i).VanishesOnSmallSets := by
  refine ⟨fun h i => h.mono (le_sum μ i), fun h A hA hdim => ?_⟩
  rw [Measure.sum_apply _ hA, tsum_eq_zero_iff]
  exact fun i => h i hA hdim

theorem VanishesOnSmallSets.restrict (hμ : μ.VanishesOnSmallSets) (s : Set E) :
    (μ.restrict s).VanishesOnSmallSets :=
  hμ.mono restrict_le_self

/-- Continuous linear equivalences preserve `VanishesOnSmallSets` under pushforward. -/
@[simp]
theorem vanishesOnSmallSets_map_continuousLinearEquiv_iff [BorelSpace E] [BorelSpace F]
    (e : E ≃L[ℝ] F) :
    (μ.map e).VanishesOnSmallSets ↔ μ.VanishesOnSmallSets := by
  have hfin : Module.finrank ℝ E = Module.finrank ℝ F := e.toLinearEquiv.finrank_eq
  constructor
  · intro h A hA hdim
    have hAe : MeasurableSet (e.symm ⁻¹' A) := hA.preimage e.symm.continuous.measurable
    have hdime : dimH (e.symm ⁻¹' A) + 1 ≤ Module.finrank ℝ F := by
      rwa [e.symm.dimH_preimage, ← hfin]
    have hmap := h hAe hdime
    rw [Measure.map_apply e.continuous.measurable hAe] at hmap
    convert hmap using 2
    ext x
    simp
  · intro h B hB hdim
    rw [Measure.map_apply e.continuous.measurable hB]
    refine h (hB.preimage e.continuous.measurable) ?_
    rwa [e.dimH_preimage, hfin]

/-- Any Borel measure absolutely continuous with respect to `d`-dimensional Hausdorff measure with
`finrank ℝ E < d + 1` (for example surface measure on a hypersurface of dimension `> n - 1`, or
`n`-dimensional Hausdorff measure itself) vanishes on small sets. -/
theorem vanishesOnSmallSets_of_absolutelyContinuous_hausdorffMeasure [BorelSpace E] {d : ℝ≥0}
    (hd : (Module.finrank ℝ E : ℝ≥0∞) < (d : ℝ≥0∞) + 1) (hμ : μ ≪ μH[d]) :
    μ.VanishesOnSmallSets := by
  intro A _ hdim
  exact measure_zero_of_dimH_lt hμ
    ((ENNReal.add_lt_add_iff_right ENNReal.one_ne_top).mp (hdim.trans_lt hd))

/-- Every additive Haar measure on a Borel real normed space vanishes on small sets. -/
theorem vanishesOnSmallSets_addHaar [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ.VanishesOnSmallSets := by
  intro A _ hdim
  have hne : dimH A ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (le_self_add.trans hdim)
  exact addHaar_eq_zero_of_dimH_lt_finrank μ ((ENNReal.lt_add_right hne one_ne_zero).trans_le hdim)

/-- Any Borel measure absolutely continuous with respect to an additive Haar measure vanishes on
small sets. -/
theorem VanishesOnSmallSets.of_absolutelyContinuous [BorelSpace E] {ρ : Measure E}
    [ρ.IsAddHaarMeasure] (hμ : μ ≪ ρ) : μ.VanishesOnSmallSets :=
  (vanishesOnSmallSets_addHaar ρ).mono_ac hμ

/-- In a nontrivial finite-dimensional space with measurable singletons, any measure vanishing on
small sets has null singletons. -/
theorem VanishesOnSmallSets.nullSingletonClass [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSingletonClass E] (hμ : μ.VanishesOnSmallSets) : NullSingletonClass μ :=
  ⟨fun x => hμ (measurableSet_singleton x) <| by
    rw [dimH_singleton, zero_add]
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)⟩

/-- In a nontrivial finite-dimensional space with measurable singletons, no Dirac measure vanishes
on small sets. -/
theorem not_vanishesOnSmallSets_dirac [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSingletonClass E] (x : E) : ¬ (Measure.dirac x).VanishesOnSmallSets := by
  intro h
  have := h.nullSingletonClass.measure_singleton x
  simp at this

/-- **Almost-everywhere differentiability of convex potentials under `VanishesOnSmallSets`.** On a
finite-dimensional Borel real normed space `E`, if `μ.VanishesOnSmallSets` and `f : E → EReal` has
convex epigraph, then at `μ`-almost every point of `{x | f x ≠ ⊤}`, `f` is finite on a neighborhood
and `(f ·).toReal` is differentiable. -/
theorem VanishesOnSmallSets.ae_eventually_ne_top_and_differentiableAt_toReal
    [FiniteDimensional ℝ E] [BorelSpace E] (hμ : μ.VanishesOnSmallSets) {f : E → EReal}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x :=
  TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal_of_null_dimH_add_one_le hf hμ

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- A Borel measure vanishing on small sets assigns mass zero to every Lipschitz hyperplane graph
orthogonal to a nonzero vector. -/
theorem VanishesOnSmallSets.measure_setOf_inner_eq_orthogonalProjectionOnto
    (hμ : μ.VanishesOnSmallSets) {v : E} (hv : v ≠ 0) {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : LipschitzWith K g) :
    μ {x : E | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} = 0 :=
  hμ (TauCeti.isClosed_setOf_inner_eq_orthogonalProjectionOnto hg.continuous).measurableSet
    (hg.dimH_setOf_inner_eq_orthogonalProjectionOnto_add_one_le hv)

end InnerProductSpace

end MeasureTheory.Measure
