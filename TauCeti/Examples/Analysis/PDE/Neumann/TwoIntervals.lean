/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Neumann.Kernel
public import TauCeti.Analysis.Sobolev.W1p.ConnectedComponents
import TauCeti.Topology.ConnectedComponents

/-!
# The Neumann kernel on two disjoint intervals

On `Ω = (0, 1) ∪ (2, 3)`, viewed in `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, the Neumann problem
`−u'' = f` with `Γ = ∅` has a kernel of dimension `2`: `Ω` has two connected components, and the
functions `u ∈ H¹(Ω)` with `∫_Ω u' v' = 0` for every `v ∈ H¹(Ω)` are exactly the combinations of
the indicators of the two intervals. So uniqueness up to one additive constant needs `Ω`
connected, and the Neumann eigenvalue `0` of this `Ω` has multiplicity `2`.

## Main declarations

* `TauCeti.Examples.NeumannTwoIntervals.twoIntervals`: the open set `(0, 1) ∪ (2, 3)` of `ℝ¹`.
* `TauCeti.Examples.NeumannTwoIntervals.card_connectedComponents_twoIntervals`: it has two
  connected components.
* `TauCeti.Examples.NeumannTwoIntervals.finrank_ker_gradientL_twoIntervals`: the Sobolev
  functions on it with vanishing weak gradient form a space of dimension `2`, for every `p`.
* `TauCeti.Examples.NeumannTwoIntervals.forall_energyFormH1_eq_zero_iff_twoIntervals`: the
  Neumann kernel on it consists of the combinations `a 1_{(0,1)} + b 1_{(2,3)}`.
-/

public section

noncomputable section

namespace TauCeti.Examples.NeumannTwoIntervals

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal

/-- The left interval `(0, 1)`, read in the coordinate of `ℝ¹`. -/
@[expose] def leftInterval : Set (EuclideanSpace ℝ (Fin 1)) :=
  {x | x 0 ∈ Ioo 0 1}

/-- The right interval `(2, 3)`, read in the coordinate of `ℝ¹`. -/
@[expose] def rightInterval : Set (EuclideanSpace ℝ (Fin 1)) :=
  {x | x 0 ∈ Ioo 2 3}

/-- The left interval is open. -/
theorem isOpen_leftInterval : IsOpen leftInterval :=
  isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous

/-- The right interval is open. -/
theorem isOpen_rightInterval : IsOpen rightInterval :=
  isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous

/-- The left interval is preconnected. -/
theorem isPreconnected_leftInterval : IsPreconnected leftInterval :=
  ((convex_Ioo (0 : ℝ) 1).linear_preimage
    (EuclideanSpace.projₗ (0 : Fin 1))).isPreconnected

/-- The right interval is preconnected. -/
theorem isPreconnected_rightInterval : IsPreconnected rightInterval :=
  ((convex_Ioo (2 : ℝ) 3).linear_preimage
    (EuclideanSpace.projₗ (0 : Fin 1))).isPreconnected

/-- The two intervals are disjoint. -/
theorem disjoint_leftInterval_rightInterval : Disjoint leftInterval rightInterval :=
  disjoint_left.2 fun _ h1 h2 => by
    simp only [leftInterval, rightInterval, mem_ofPred_eq, mem_Ioo] at h1 h2
    linarith [h1.2, h2.1]

/-- The open set `Ω = (0, 1) ∪ (2, 3)` of `ℝ¹`. -/
@[expose] def twoIntervals : Opens (EuclideanSpace ℝ (Fin 1)) :=
  ⟨leftInterval ∪ rightInterval, isOpen_leftInterval.union isOpen_rightInterval⟩

/-- `Ω` is the union of the two intervals. -/
theorem coe_twoIntervals :
    (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) = leftInterval ∪ rightInterval :=
  rfl

/-- The point `1/2` of the left interval. -/
private theorem single_half_mem_leftInterval :
    WithLp.toLp 2 (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ leftInterval := by
  simp only [leftInterval, mem_ofPred_eq, mem_Ioo]
  norm_num

/-- The point `5/2` of the right interval. -/
private theorem single_fiveHalves_mem_rightInterval :
    WithLp.toLp 2 (fun _ : Fin 1 => (5 / 2 : ℝ)) ∈ rightInterval := by
  simp only [rightInterval, mem_ofPred_eq, mem_Ioo]
  norm_num

/-- **`(0, 1) ∪ (2, 3)` has two connected components.** -/
theorem card_connectedComponents_twoIntervals :
    Nat.card (ConnectedComponents (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))) = 2 := by
  have hL : leftInterval ⊆ (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) := subset_union_left
  have hR : rightInterval ⊆ (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) := subset_union_right
  have ha := single_half_mem_leftInterval
  have hb := single_fiveHalves_mem_rightInterval
  refine Nat.card_eq_two_iff.2 ⟨ConnectedComponents.mk ⟨_, hL ha⟩,
    ConnectedComponents.mk ⟨_, hR hb⟩, fun h => ?_, ?_⟩
  · rw [ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn] at h
    have hsub : connectedComponentIn (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))
        (WithLp.toLp 2 (fun _ : Fin 1 => (5 / 2 : ℝ))) ⊆ rightInterval :=
      (isPreconnected_connectedComponentIn).subset_right_of_subset_union isOpen_leftInterval
        isOpen_rightInterval disjoint_leftInterval_rightInterval
        (connectedComponentIn_subset _ _)
        ⟨_, mem_connectedComponentIn (hR hb), hb⟩
    exact disjoint_leftInterval_rightInterval.notMem_of_mem_left ha (hsub h)
  · refine eq_univ_of_forall fun c => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases hz with hz | hz
    · exact Or.inl (isPreconnected_leftInterval.connectedComponents_mk_eq hL hz ha)
    · exact Or.inr (isPreconnected_rightInterval.connectedComponents_mk_eq hR hz hb)

/-- `(0, 1) ∪ (2, 3)` is bounded. -/
theorem isBounded_twoIntervals :
    Bornology.IsBounded (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) := by
  refine isBounded_iff_forall_norm_le.2 ⟨3, fun x hx => ?_⟩
  have hx' : 0 < x 0 ∧ x 0 < 3 := by
    rcases hx with hx | hx <;>
      simp only [leftInterval, rightInterval, mem_ofPred_eq, mem_Ioo] at hx <;>
      constructor <;> linarith
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq hx'.1.le]
  exact hx'.2.le

/-- `(0, 1) ∪ (2, 3)` has finite measure. -/
instance instIsFiniteMeasureRestrictTwoIntervals :
    IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
      (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))) :=
  isFiniteMeasure_restrict.2 (isBounded_twoIntervals.measure_lt_top).ne

/-- `(0, 1) ∪ (2, 3)` has finitely many connected components. -/
instance instFiniteConnectedComponentsTwoIntervals :
    Finite (ConnectedComponents (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))) :=
  Nat.finite_of_card_ne_zero (by rw [card_connectedComponents_twoIntervals]; norm_num)

/-- **The kernel of the weak gradient on `(0, 1) ∪ (2, 3)` has dimension `2`.** -/
theorem finrank_ker_gradientL_twoIntervals {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    finrank ℝ (LinearMap.ker (W1p.gradientL : W1p volume twoIntervals p →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 1)) p
          (volume.restrict (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))))).toLinearMap) = 2 := by
  rw [W1p.finrank_ker_gradientL, card_connectedComponents_twoIntervals]

/-- **The Neumann kernel on `(0, 1) ∪ (2, 3)`.** A function `u ∈ H¹(Ω)` satisfies
`∫_Ω u' v' = 0` for every `v ∈ H¹(Ω)` exactly when it is almost everywhere a combination
`a 1_{(0,1)} + b 1_{(2,3)}` of the indicators of the two intervals. -/
theorem forall_energyFormH1_eq_zero_iff_twoIntervals (u : W1p volume twoIntervals 2) :
    (∀ v : W1p volume twoIntervals 2, PDE.energyFormH1 (fun _ => 1) 0 0 u v = 0) ↔
      ∃ a b : ℝ, W1p.value u =ᵐ[volume.restrict twoIntervals]
        leftInterval.indicator (fun _ => a) + rightInterval.indicator (fun _ => b) := by
  have hL : leftInterval ⊆ (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) := subset_union_left
  have hR : rightInterval ⊆ (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) := subset_union_right
  have hdisj := disjoint_leftInterval_rightInterval
  rw [PDE.forall_energyFormH1_one_zero_zero_eq_zero_iff_exists_isLocallyConstant]
  constructor
  · rintro ⟨g, hg, hug⟩
    have hconst {s : Set (EuclideanSpace ℝ (Fin 1))} (hs : IsPreconnected s)
        (hsΩ : s ⊆ twoIntervals) {y z} (hy : y ∈ s) (hz : z ∈ s) : g y = g z := by
      have hpre : IsPreconnected (((↑) : twoIntervals → EuclideanSpace ℝ (Fin 1)) ⁻¹' s) := by
        refine Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_
        convert hs using 1
        exact image_preimage_eq_of_subset fun x hx => ⟨⟨x, hsΩ hx⟩, rfl⟩
      exact hg.apply_eq_of_isPreconnected hpre (x := ⟨y, hsΩ hy⟩) (y := ⟨z, hsΩ hz⟩) hy hz
    refine ⟨g (WithLp.toLp 2 fun _ => 1 / 2), g (WithLp.toLp 2 fun _ => 5 / 2), ?_⟩
    refine hug.trans ((ae_restrict_mem twoIntervals.isOpen.measurableSet).mono fun x hx => ?_)
    rcases hx with hx | hx
    · simp only [Pi.add_apply, indicator_of_mem hx, indicator_of_notMem
        (hdisj.notMem_of_mem_left hx), add_zero]
      exact hconst isPreconnected_leftInterval hL hx single_half_mem_leftInterval
    · simp only [Pi.add_apply, indicator_of_mem hx, indicator_of_notMem
        (hdisj.notMem_of_mem_right hx), zero_add]
      exact hconst isPreconnected_rightInterval hR hx single_fiveHalves_mem_rightInterval
  · rintro ⟨a, b, hu⟩
    refine ⟨_, (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, hu⟩
    rcases x.property with hx | hx
    · filter_upwards [(isOpen_leftInterval.preimage continuous_subtypeVal).mem_nhds hx]
        with y hy
      have hy' : (y : EuclideanSpace ℝ (Fin 1)) ∈ leftInterval := hy
      simp only [Set.domRestrict, Pi.add_apply]
      rw [indicator_of_mem hx, indicator_of_notMem (hdisj.notMem_of_mem_left hx),
        indicator_of_mem hy', indicator_of_notMem (hdisj.notMem_of_mem_left hy')]
    · filter_upwards [(isOpen_rightInterval.preimage continuous_subtypeVal).mem_nhds hx]
        with y hy
      have hy' : (y : EuclideanSpace ℝ (Fin 1)) ∈ rightInterval := hy
      simp only [Set.domRestrict, Pi.add_apply]
      rw [indicator_of_mem hx, indicator_of_notMem (hdisj.notMem_of_mem_right hx),
        indicator_of_mem hy', indicator_of_notMem (hdisj.notMem_of_mem_right hy')]

end TauCeti.Examples.NeumannTwoIntervals
