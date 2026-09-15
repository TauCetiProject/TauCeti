/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Extreme
public import TauCeti.MeasureTheory.Group.CountableAction

/-!
# Ergodic group actions and extreme invariant measures

For a countable group `G` acting measurably on `X`, an invariant probability measure is ergodic
if and only if it is an extreme point of the convex set of `G`-invariant probability measures.
This is the group-action form of Mathlib's `Ergodic.iff_mem_extremePoints`, which concerns a
single measure-preserving map; the two are not interchangeable, since a group action has no one
map whose ergodicity is the action's.

Two general facts about an ergodic action carry the characterisation and are useful on their
own: an almost invariant function is almost everywhere constant
(`ErgodicSMul.ae_eq_const_of_forall_comp_smul_ae_eq`), and an invariant measure absolutely
continuous with respect to an ergodic one is a multiple of it
(`ErgodicSMul.eq_smul_of_absolutelyContinuous`). The characterisation is stated first for
invariant measures of a fixed finite total mass and then for probability measures, as in Mathlib.

## Main results

* `MeasureTheory.ErgodicSMul.ae_eq_const_of_forall_comp_smul_ae_eq`
* `MeasureTheory.ErgodicSMul.eq_smul_of_absolutelyContinuous`,
  `MeasureTheory.ErgodicSMul.eq_of_absolutelyContinuous_measure_univ_eq`,
  `MeasureTheory.ErgodicSMul.eq_of_absolutelyContinuous`
* `TauCeti.MeasureTheory.invariantMeasuresOfMeasureUnivEq`,
  `TauCeti.MeasureTheory.invariantProbabilityMeasures`, with membership and convexity lemmas
* `MeasureTheory.ErgodicSMul.iff_mem_extremePoints_measure_univ_eq`,
  `MeasureTheory.ErgodicSMul.iff_mem_extremePoints`

## References

The absolute-continuity comparison and both extreme-point directions adapt
`Graphon/RelErgodicExtreme.lean` in `cameronfreer/graphon` (Apache 2.0) at commit
`18d47ebb4155d32031090ec3412eb71583a94f69`, where they are proved for the sortwise relabelling
action on relational structures; here they are stated for an arbitrary countable group action.
-/

public section

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {G X : Type*} [Group G] [MulAction G X] {m : MeasurableSpace X} {μ ν : Measure X}


/-- **An almost invariant function under an ergodic action is almost everywhere constant.** The
target may be any nonempty countably separated measurable space; the action-level analogue of
`Ergodic.ae_eq_const_of_ae_eq_comp₀`. -/
theorem ErgodicSMul.ae_eq_const_of_forall_comp_smul_ae_eq
    {β : Type*} [Nonempty β] [MeasurableSpace β] [MeasurableSpace.CountablySeparated β]
    [ErgodicSMul G X μ] {g : X → β} (hgm : NullMeasurable g μ)
    (hg : ∀ c : G, g ∘ (c • ·) =ᵐ[μ] g) : ∃ b, g =ᵐ[μ] const X b :=
  exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU => by
    have h := aeconst_of_forall_preimage_smul_ae_eq G (μ := μ) (s := g ⁻¹' U) (hgm hU)
      fun c => by rw [← preimage_comp]; exact (hg c).preimage U
    exact eventuallyEmptyOrUniv_iff.mp h

/-- **An invariant finite measure absolutely continuous with respect to an ergodic one is a
multiple of it.** The action-level analogue of `Ergodic.eq_smul_of_absolutelyContinuous`. -/
theorem ErgodicSMul.eq_smul_of_absolutelyContinuous [MeasurableConstSMul G X]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ErgodicSMul G X μ] [SMulInvariantMeasure G X ν]
    (hνμ : ν ≪ μ) : ∃ c : ℝ≥0∞, ν = c • μ := by
  have hinv : ∀ g : G, ν.rnDeriv μ ∘ (g • ·) =ᵐ[μ] ν.rnDeriv μ := fun g =>
    MeasurePreserving.rnDeriv_comp_aeEq (measurePreserving_smul g ν) (measurePreserving_smul g μ)
  obtain ⟨c, hc⟩ := ErgodicSMul.ae_eq_const_of_forall_comp_smul_ae_eq (G := G)
    (measurable_rnDeriv ν μ).nullMeasurable hinv
  refine ⟨c, ?_⟩
  ext s hs
  calc ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm <| setLIntegral_rnDeriv hνμ _
    _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae <| hc.filter_mono <| ae_mono restrict_le_self
    _ = (c • μ) s := by simp

/-- **An invariant finite measure absolutely continuous with respect to an ergodic one, of the
same total mass, equals it.** The action-level analogue of
`Ergodic.eq_of_absolutelyContinuous_measure_univ_eq`. -/
theorem ErgodicSMul.eq_of_absolutelyContinuous_measure_univ_eq [MeasurableConstSMul G X]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ErgodicSMul G X μ] [SMulInvariantMeasure G X ν]
    (hνμ : ν ≪ μ) (huniv : ν univ = μ univ) : ν = μ := by
  obtain ⟨c, rfl⟩ := ErgodicSMul.eq_smul_of_absolutelyContinuous (G := G) hνμ
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp
  · have hc : c = 1 := by
      rw [Measure.smul_apply, smul_eq_mul] at huniv
      exact (ENNReal.mul_eq_right (measure_univ_ne_zero.mpr hμ0) (measure_ne_top μ _)).mp huniv
    rw [hc, one_smul]

/-- **An invariant probability measure absolutely continuous with respect to an ergodic one equals
it.** -/
theorem ErgodicSMul.eq_of_absolutelyContinuous [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [ErgodicSMul G X μ]
    [SMulInvariantMeasure G X ν] (hνμ : ν ≪ μ) : ν = μ :=
  ErgodicSMul.eq_of_absolutelyContinuous_measure_univ_eq (G := G) hνμ (by simp)

end MeasureTheory

namespace TauCeti.MeasureTheory

variable {G X : Type*} [Group G] [MulAction G X] {m : MeasurableSpace X} {μ ν : Measure X}

/-- The `G`-invariant measures on `X` of total mass `c`, a convex set of measures. -/
def invariantMeasuresOfMeasureUnivEq (G X : Type*) [SMul G X] [MeasurableSpace X] (c : ℝ≥0∞) :
    Set (Measure X) :=
  {ν | SMulInvariantMeasure G X ν ∧ ν univ = c}

/-- Membership in the invariant measures of total mass `c`. -/
@[simp]
theorem mem_invariantMeasuresOfMeasureUnivEq_iff {c : ℝ≥0∞} :
    ν ∈ invariantMeasuresOfMeasureUnivEq G X c ↔ SMulInvariantMeasure G X ν ∧ ν univ = c :=
  Iff.rfl

/-- The convex set of `G`-invariant probability measures on `X`, the set whose extreme points
ergodicity characterises. -/
def invariantProbabilityMeasures (G X : Type*) [SMul G X] [MeasurableSpace X] : Set (Measure X) :=
  {ν | SMulInvariantMeasure G X ν ∧ IsProbabilityMeasure ν}

/-- Membership in the invariant probability measures. -/
@[simp]
theorem mem_invariantProbabilityMeasures_iff :
    ν ∈ invariantProbabilityMeasures G X ↔ SMulInvariantMeasure G X ν ∧ IsProbabilityMeasure ν :=
  Iff.rfl

/-- The invariant probability measures are the invariant measures of total mass one. -/
theorem invariantProbabilityMeasures_eq :
    invariantProbabilityMeasures G X = invariantMeasuresOfMeasureUnivEq G X 1 := by
  ext ν; simp only [mem_invariantProbabilityMeasures_iff, mem_invariantMeasuresOfMeasureUnivEq_iff,
    isProbabilityMeasure_iff]

/-- The invariant measures of a fixed total mass form a convex set. -/
theorem convex_invariantMeasuresOfMeasureUnivEq {c : ℝ≥0∞} :
    Convex ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X c) := by
  rintro ν₁ ⟨hν₁, hν₁u⟩ ν₂ ⟨hν₂, hν₂u⟩ a b _ _ hab
  refine ⟨⟨fun g s hs => ?_⟩, ?_⟩
  · simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      SMulInvariantMeasure.measure_preimage_smul g hs]
  · rw [Measure.coe_add, Pi.add_apply, Measure.smul_apply, Measure.smul_apply, hν₁u, hν₂u,
      smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]

/-- The invariant probability measures form a convex set. -/
theorem convex_invariantProbabilityMeasures : Convex ℝ≥0∞ (invariantProbabilityMeasures G X) := by
  rw [invariantProbabilityMeasures_eq]; exact convex_invariantMeasuresOfMeasureUnivEq

end TauCeti.MeasureTheory

namespace MeasureTheory

variable {G X : Type*} [Group G] [MulAction G X] {m : MeasurableSpace X} {μ ν : Measure X}

open TauCeti.MeasureTheory

/-- **An ergodic finite measure is an extreme point** of the invariant measures of its total
mass. -/
theorem ErgodicSMul.mem_extremePoints_measure_univ_eq [MeasurableConstSMul G X]
    [IsFiniteMeasure μ] [ErgodicSMul G X μ] :
    μ ∈ extremePoints ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X (μ univ)) := by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨inferInstance, rfl⟩, ?_⟩
  rintro ν₁ ⟨hν₁, hν₁u⟩ ν₂ ⟨hν₂, hν₂u⟩ ⟨a, b, ha, hb, hab, hμ⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁u]; exact measure_lt_top μ _⟩
  have hac : ν₁ ≪ μ := hμ ▸ (absolutelyContinuous_smul ha.ne').add_right _
  exact ErgodicSMul.eq_of_absolutelyContinuous_measure_univ_eq (G := G) hac hν₁u

/-- **An ergodic probability measure is an extreme point** of the invariant probability measures. -/
theorem ErgodicSMul.mem_extremePoints [MeasurableConstSMul G X] [IsProbabilityMeasure μ]
    [ErgodicSMul G X μ] : μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X) := by
  rw [invariantProbabilityMeasures_eq, ← measure_univ (μ := μ)]
  exact ErgodicSMul.mem_extremePoints_measure_univ_eq

/-- **An extreme invariant measure of finite total mass is ergodic.** -/
theorem ErgodicSMul.of_mem_extremePoints_measure_univ_eq [Countable G] [MeasurableConstSMul G X]
    {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : μ ∈ extremePoints ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X c)) : ErgodicSMul G X μ := by
  have hinv : SMulInvariantMeasure G X μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · have : μ = 0 := measure_univ_eq_zero.mp h.1.2
    subst this
    exact ⟨fun {s} _ _ => by simp [EventuallyEmptyOrUniv, EventuallyConst, ae_zero]⟩
  have : IsFiniteMeasure μ := ⟨by rw [h.1.2]; exact lt_top_iff_ne_top.mpr hc⟩
  -- an exactly invariant `t` of intermediate mass would write `μ` as a proper combination of
  -- the invariant measures `c • μ[|t]` and `c • μ[|tᶜ]` of mass `c`; countability of `G` reduces
  -- almost invariant events to exactly invariant ones
  refine TauCeti.MeasureTheory.ergodicSMul_of_forall_smul_invariant fun t htm htinv => ?_
  have hmem {u : Set X} (hum : MeasurableSet u) (huinv : ∀ g : G, (fun x => g • x) ⁻¹' u = u)
      (hu0 : μ u ≠ 0) : c • μ[|u] ∈ invariantMeasuresOfMeasureUnivEq G X c := by
    refine ⟨⟨fun g v hv => ?_⟩, ?_⟩
    · have hres : (μ.restrict u).map (g • ·) = μ.restrict u := by
        have hmp := (measurePreserving_smul g μ).restrict_preimage hum
        rw [huinv g] at hmp
        exact hmp.map_eq
      -- `μ[|u]` is `(μ u)⁻¹ • μ.restrict u` by the definition of `ProbabilityTheory.cond`
      simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
      rw [← Measure.map_apply (measurable_const_smul g) hv, hres]
    · rw [Measure.smul_apply, (cond_isProbabilityMeasure hu0).1, smul_eq_mul, mul_one]
  by_contra H
  obtain ⟨hs, hs'⟩ : μ t ≠ 0 ∧ μ tᶜ ≠ 0 := by
    simpa [eventuallyEmptyOrUniv_iff, ae_iff, and_comm] using! H
  have hcond : c • μ[|t] = μ := by
    apply h.2 (hmem htm htinv hs) (hmem htm.compl (fun g => by rw [preimage_compl, htinv g]) hs')
    refine ⟨μ t / c, μ tᶜ / c, ENNReal.div_pos hs hc, ENNReal.div_pos hs' hc, ?_, ?_⟩
    · rw [← ENNReal.add_div, measure_add_measure_compl htm, h.1.2, ENNReal.div_self hc₀ hc]
    · simp [ProbabilityTheory.cond, smul_smul, ← mul_assoc, ENNReal.div_mul_cancel,
        ENNReal.mul_inv_cancel, hs, hs', hc₀, hc, measure_ne_top,
        Measure.restrict_add_restrict_compl htm]
  have : μ tᶜ = 0 := by
    rw [← hcond, Measure.smul_apply, ProbabilityTheory.cond_apply htm, inter_compl_self,
      measure_empty, mul_zero, smul_zero]
  exact hs' this

/-- **An extreme invariant probability measure is ergodic.** -/
theorem ErgodicSMul.of_mem_extremePoints [Countable G] [MeasurableConstSMul G X]
    (h : μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X)) : ErgodicSMul G X μ :=
  ErgodicSMul.of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top <| by
    rwa [invariantProbabilityMeasures_eq] at h

/-- **Ergodicity is extremality** for a countable group action, among the invariant measures of
the same finite total mass. -/
theorem ErgodicSMul.iff_mem_extremePoints_measure_univ_eq [Countable G] [MeasurableConstSMul G X]
    [IsFiniteMeasure μ] :
    ErgodicSMul G X μ ↔ μ ∈ extremePoints ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X (μ univ)) :=
  ⟨fun _ => ErgodicSMul.mem_extremePoints_measure_univ_eq,
    ErgodicSMul.of_mem_extremePoints_measure_univ_eq (measure_ne_top μ _)⟩

/-- **Ergodicity is extremality** for a countable group action: an invariant probability measure
is ergodic if and only if it is an extreme point of the invariant probability measures. -/
theorem ErgodicSMul.iff_mem_extremePoints [Countable G] [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] :
    ErgodicSMul G X μ ↔ μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X) :=
  ⟨fun _ => ErgodicSMul.mem_extremePoints, ErgodicSMul.of_mem_extremePoints⟩

end MeasureTheory
