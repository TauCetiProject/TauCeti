/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Neumann.Kernel
public import TauCeti.Analysis.PDE.Spectrum.Interval
public import TauCeti.Analysis.Sobolev.W1p.ConnectedComponents
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.LocallyConstant.ConnectedComponents

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
  connected components, the component of `5/2` being `(2, 3)`
  (`TauCeti.Examples.NeumannTwoIntervals.connectedComponentIn_twoIntervals_fiveHalves`).
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

/-- The open set `Ω = (0, 1) ∪ (2, 3)` of `ℝ¹`. -/
def twoIntervals : Opens (EuclideanSpace ℝ (Fin 1)) :=
  PDE.intervalDomain 0 1 ⊔ PDE.intervalDomain 2 3

/-- `Ω` is the union of the two intervals. -/
@[simp]
theorem coe_twoIntervals :
    (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) =
      (PDE.intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))) ∪ PDE.intervalDomain 2 3 :=
  Opens.coe_sup _ _

/-- A point lies in `Ω` exactly when it lies in one of the two intervals. -/
@[simp]
theorem mem_twoIntervals {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ twoIntervals ↔ x ∈ PDE.intervalDomain 0 1 ∨ x ∈ PDE.intervalDomain 2 3 :=
  Opens.mem_sup

/-- The two intervals are disjoint. -/
theorem disjoint_intervalDomain :
    Disjoint (PDE.intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))) (PDE.intervalDomain 2 3) :=
  disjoint_left.2 fun _ h1 h2 => by
    simp only [SetLike.mem_coe, PDE.mem_intervalDomain, mem_Ioo] at h1 h2
    linarith [h1.2, h2.1]

/-- The left interval lies in `Ω`. -/
private theorem intervalDomain_zero_one_subset :
    (PDE.intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))) ⊆ twoIntervals :=
  subset_union_left

/-- The right interval lies in `Ω`. -/
theorem intervalDomain_two_three_subset :
    (PDE.intervalDomain 2 3 : Set (EuclideanSpace ℝ (Fin 1))) ⊆ twoIntervals :=
  subset_union_right

/-- The point `1/2` of the left interval. -/
private theorem half_mem_intervalDomain :
    WithLp.toLp 2 (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ PDE.intervalDomain 0 1 := by
  rw [PDE.mem_intervalDomain, mem_Ioo]
  norm_num

/-- The point `5/2` of the right interval. -/
theorem fiveHalves_mem_intervalDomain :
    WithLp.toLp 2 (fun _ : Fin 1 => (5 / 2 : ℝ)) ∈ PDE.intervalDomain 2 3 := by
  rw [PDE.mem_intervalDomain, mem_Ioo]
  norm_num

/-- On the left interval, `a 1_{(0,1)} + b 1_{(2,3)}` takes the value `a`. -/
private theorem indicator_add_indicator_of_mem_left {a b : ℝ} {x : EuclideanSpace ℝ (Fin 1)}
    (hx : x ∈ PDE.intervalDomain 0 1) :
    ((PDE.intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))).indicator (fun _ => a) +
      (PDE.intervalDomain 2 3 : Set (EuclideanSpace ℝ (Fin 1))).indicator (fun _ => b)) x = a := by
  rw [Pi.add_apply, indicator_of_mem hx, indicator_of_notMem
    (disjoint_intervalDomain.notMem_of_mem_left hx), add_zero]

/-- On the right interval, `a 1_{(0,1)} + b 1_{(2,3)}` takes the value `b`. -/
private theorem indicator_add_indicator_of_mem_right {a b : ℝ} {x : EuclideanSpace ℝ (Fin 1)}
    (hx : x ∈ PDE.intervalDomain 2 3) :
    ((PDE.intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))).indicator (fun _ => a) +
      (PDE.intervalDomain 2 3 : Set (EuclideanSpace ℝ (Fin 1))).indicator (fun _ => b)) x = b := by
  rw [Pi.add_apply, indicator_of_mem hx, indicator_of_notMem
    (disjoint_intervalDomain.notMem_of_mem_right hx), zero_add]

/-- The connected component of `5/2` in `Ω` is the right interval `(2, 3)`. -/
theorem connectedComponentIn_twoIntervals_fiveHalves :
    connectedComponentIn (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))
      (WithLp.toLp 2 fun _ => 5 / 2) = PDE.intervalDomain 2 3 := by
  rw [coe_twoIntervals, union_comm]
  exact (PDE.isPreconnected_intervalDomain 2 3).connectedComponentIn_union_eq_left
    (PDE.intervalDomain 2 3).isOpen (PDE.intervalDomain 0 1).isOpen
    disjoint_intervalDomain.symm fiveHalves_mem_intervalDomain

/-- **`(0, 1) ∪ (2, 3)` has two connected components.** -/
theorem card_connectedComponents_twoIntervals :
    Nat.card (ConnectedComponents (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))) = 2 := by
  have hL := intervalDomain_zero_one_subset
  have hR := intervalDomain_two_three_subset
  have ha := half_mem_intervalDomain
  have hb := fiveHalves_mem_intervalDomain
  refine Nat.card_eq_two_iff.2 ⟨ConnectedComponents.mk ⟨_, hL ha⟩,
    ConnectedComponents.mk ⟨_, hR hb⟩, fun h => ?_, ?_⟩
  · rw [ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn,
      connectedComponentIn_twoIntervals_fiveHalves] at h
    exact disjoint_intervalDomain.notMem_of_mem_left ha h
  · refine eq_univ_of_forall fun c => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases mem_twoIntervals.1 hz with hz | hz
    · exact Or.inl ((PDE.isPreconnected_intervalDomain 0 1).connectedComponents_mk_eq hL hz ha)
    · exact Or.inr ((PDE.isPreconnected_intervalDomain 2 3).connectedComponents_mk_eq hR hz hb)

/-- `(0, 1) ∪ (2, 3)` is bounded. -/
theorem isBounded_twoIntervals :
    Bornology.IsBounded (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) :=
  PDE.isBounded_intervalDomain.union PDE.isBounded_intervalDomain

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
        (PDE.intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))).indicator (fun _ => a) +
          (PDE.intervalDomain 2 3 : Set (EuclideanSpace ℝ (Fin 1))).indicator (fun _ => b) := by
  rw [PDE.forall_energyFormH1_one_zero_zero_eq_zero_iff_exists_isLocallyConstant]
  constructor
  · rintro ⟨g, hg, hug⟩
    refine ⟨g (WithLp.toLp 2 fun _ => 1 / 2), g (WithLp.toLp 2 fun _ => 5 / 2), ?_⟩
    refine hug.trans ((ae_restrict_mem twoIntervals.isOpen.measurableSet).mono fun x hx => ?_)
    rcases mem_twoIntervals.1 hx with hx | hx
    · rw [indicator_add_indicator_of_mem_left hx]
      exact hg.apply_eq_of_isPreconnected_of_subset (PDE.isPreconnected_intervalDomain 0 1)
        intervalDomain_zero_one_subset hx half_mem_intervalDomain
    · rw [indicator_add_indicator_of_mem_right hx]
      exact hg.apply_eq_of_isPreconnected_of_subset (PDE.isPreconnected_intervalDomain 2 3)
        intervalDomain_two_three_subset hx fiveHalves_mem_intervalDomain
  · rintro ⟨a, b, hu⟩
    refine ⟨_, (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, hu⟩
    rcases mem_twoIntervals.1 x.property with hx | hx
    · filter_upwards [((PDE.intervalDomain 0 1).isOpen.preimage continuous_subtypeVal).mem_nhds hx]
        with y hy
      simp only [Set.domRestrict_apply, indicator_add_indicator_of_mem_left hx,
        indicator_add_indicator_of_mem_left (Set.mem_preimage.1 hy)]
    · filter_upwards [((PDE.intervalDomain 2 3).isOpen.preimage continuous_subtypeVal).mem_nhds hx]
        with y hy
      simp only [Set.domRestrict_apply, indicator_add_indicator_of_mem_right hx,
        indicator_add_indicator_of_mem_right (Set.mem_preimage.1 hy)]

end TauCeti.Examples.NeumannTwoIntervals
