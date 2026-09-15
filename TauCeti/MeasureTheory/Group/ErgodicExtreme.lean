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

For a countable group `G` acting measurably on `X`, an invariant measure of finite total mass is
ergodic if and only if it is an extreme point of the `G`-invariant measures of that total mass;
in particular an invariant probability measure is ergodic if and only if it is an extreme point of
the invariant probability measures. This is the group-action form of Mathlib's
`Ergodic.iff_mem_extremePoints`, which concerns a single measure-preserving map.

Two general facts about an ergodic action carry the characterisation and are useful on their
own: an almost invariant function is almost everywhere constant
(`ErgodicSMul.ae_eq_const_of_forall_ae_eq_comp_smul₀`), and an invariant measure absolutely
continuous with respect to an ergodic one is a multiple of it
(`ErgodicSMul.eq_smul_of_absolutelyContinuous`). These, the invariant-measure sets and the
forward direction of the characterisation need only an action by a type with a scalar
multiplication; the group and its countability enter only in the reverse direction, through the
saturation of an almost invariant event in `CountableAction.lean`.

## Main results

* `TauCeti.MeasureTheory.invariantMeasuresOfMeasureUnivEq`,
  `TauCeti.MeasureTheory.invariantProbabilityMeasures`, with membership and convexity lemmas
* `MeasureTheory.SMulInvariantMeasure.restrict` — restriction to an invariant set is invariant
* `ErgodicSMul.ae_eq_const_of_forall_ae_eq_comp_smul₀`
* `ErgodicSMul.eq_smul_of_absolutelyContinuous`,
  `ErgodicSMul.eq_of_absolutelyContinuous_measure_univ_eq`, `ErgodicSMul.eq_of_absolutelyContinuous`
* `ErgodicSMul.iff_mem_extremePoints_measure_univ_eq`, `ErgodicSMul.iff_mem_extremePoints`

## References

The proofs of `eq_smul_of_absolutelyContinuous`, `eq_of_absolutelyContinuous_measure_univ_eq`,
`mem_extremePoints_measure_univ_eq` and `of_mem_extremePoints_measure_univ_eq` are adapted from
Mathlib's `Mathlib/Dynamics/Ergodic/Extreme.lean` by Yury Kudryashov, transposed from a single
measure-preserving map to an action; `ae_eq_const_of_forall_ae_eq_comp_smul₀` follows
`PreErgodic.ae_eq_const_of_ae_eq_comp` in `Mathlib/Dynamics/Ergodic/Function.lean`. The same
argument for the sortwise relabelling action on relational structures appears in
`Graphon/RelErgodicExtreme.lean` of `cameronfreer/graphon` (Apache 2.0) at commit
`18d47ebb4155d32031090ec3412eb71583a94f69`.
-/

public section

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

/-! ### Invariant measures and ergodic actions of a scalar multiplication -/

namespace TauCeti.MeasureTheory

variable {G X : Type*} [SMul G X] {m : MeasurableSpace X} {ν : Measure X}

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
  refine ⟨inferInstance, ?_⟩
  simp [Measure.add_apply, Measure.smul_apply, hν₁u, hν₂u, ← add_mul, hab]

/-- The invariant probability measures form a convex set. -/
theorem convex_invariantProbabilityMeasures : Convex ℝ≥0∞ (invariantProbabilityMeasures G X) := by
  rw [invariantProbabilityMeasures_eq]; exact convex_invariantMeasuresOfMeasureUnivEq

end TauCeti.MeasureTheory

namespace MeasureTheory

variable {G X : Type*} [SMul G X] {m : MeasurableSpace X} {μ ν : Measure X}

/-- The restriction of an invariant measure to an exactly invariant measurable set is
invariant. -/
theorem SMulInvariantMeasure.restrict [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
    {u : Set X} (hum : MeasurableSet u) (huinv : ∀ g : G, (g • ·) ⁻¹' u = u) :
    SMulInvariantMeasure G X (μ.restrict u) :=
  ⟨fun g v hv => by
    have hmp := (measurePreserving_smul g μ).restrict_preimage hum
    rw [huinv g] at hmp
    exact hmp.measure_preimage hv.nullMeasurableSet⟩

end MeasureTheory

namespace ErgodicSMul

open TauCeti.MeasureTheory

section SMul

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X}

/-- **An almost invariant function under an ergodic action is almost everywhere constant.** The
target may be any nonempty countably separated measurable space; the action-level analogue of
`Ergodic.ae_eq_const_of_ae_eq_comp₀`. -/
theorem ae_eq_const_of_forall_ae_eq_comp_smul₀ (G : Type*) [SMul G X]
    {β : Type*} [Nonempty β] [MeasurableSpace β] [MeasurableSpace.CountablySeparated β]
    [ErgodicSMul G X μ] {g : X → β} (hgm : NullMeasurable g μ)
    (hg : ∀ c : G, g ∘ (c • ·) =ᵐ[μ] g) : ∃ b, g =ᵐ[μ] const X b :=
  exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU => by
    have h := MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq G (μ := μ) (s := g ⁻¹' U)
      (hgm hU)
      fun c => by rw [← preimage_comp]; exact (hg c).preimage U
    exact eventuallyEmptyOrUniv_iff.mp h

/-- **An invariant finite measure absolutely continuous with respect to an ergodic one is a
multiple of it.** The action-level analogue of `Ergodic.eq_smul_of_absolutelyContinuous`. -/
theorem eq_smul_of_absolutelyContinuous (G : Type*) [SMul G X] [MeasurableConstSMul G X]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ErgodicSMul G X μ] [SMulInvariantMeasure G X ν]
    (hνμ : ν ≪ μ) : ∃ c : ℝ≥0∞, ν = c • μ := by
  have hinv : ∀ g : G, ν.rnDeriv μ ∘ (g • ·) =ᵐ[μ] ν.rnDeriv μ := fun g =>
    MeasurePreserving.rnDeriv_comp_aeEq (measurePreserving_smul g ν) (measurePreserving_smul g μ)
  obtain ⟨c, hc⟩ := ae_eq_const_of_forall_ae_eq_comp_smul₀ G
    (measurable_rnDeriv ν μ).nullMeasurable hinv
  refine ⟨c, ?_⟩
  ext s hs
  calc ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm <| setLIntegral_rnDeriv hνμ _
    _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae <| hc.filter_mono <| ae_mono restrict_le_self
    _ = (c • μ) s := by simp

/-- **An invariant finite measure absolutely continuous with respect to an ergodic one, of the
same total mass, equals it.** The action-level analogue of
`Ergodic.eq_of_absolutelyContinuous_measure_univ_eq`. -/
theorem eq_of_absolutelyContinuous_measure_univ_eq (G : Type*) [SMul G X]
    [MeasurableConstSMul G X] [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ErgodicSMul G X μ]
    [SMulInvariantMeasure G X ν] (hνμ : ν ≪ μ) (huniv : ν univ = μ univ) : ν = μ := by
  obtain ⟨c, rfl⟩ := eq_smul_of_absolutelyContinuous G hνμ
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp
  · have hc : c = 1 := by
      rw [Measure.smul_apply, smul_eq_mul] at huniv
      exact (ENNReal.mul_eq_right (measure_univ_ne_zero.mpr hμ0) (measure_ne_top μ _)).mp huniv
    rw [hc, one_smul]

/-- **An invariant probability measure absolutely continuous with respect to an ergodic one equals
it.** -/
theorem eq_of_absolutelyContinuous (G : Type*) [SMul G X] [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [ErgodicSMul G X μ]
    [SMulInvariantMeasure G X ν] (hνμ : ν ≪ μ) : ν = μ :=
  eq_of_absolutelyContinuous_measure_univ_eq G hνμ (by simp)

/-- **An ergodic finite measure is an extreme point** of the invariant measures of its total
mass. -/
theorem mem_extremePoints_measure_univ_eq {G : Type*} [SMul G X] [MeasurableConstSMul G X]
    [IsFiniteMeasure μ] [ErgodicSMul G X μ] :
    μ ∈ extremePoints ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X (μ univ)) := by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨inferInstance, rfl⟩, ?_⟩
  rintro ν₁ ⟨hν₁, hν₁u⟩ ν₂ ⟨hν₂, hν₂u⟩ ⟨a, b, ha, hb, hab, hμ⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁u]; exact measure_lt_top μ _⟩
  have hac : ν₁ ≪ μ := hμ ▸ (absolutelyContinuous_smul ha.ne').add_right _
  exact eq_of_absolutelyContinuous_measure_univ_eq G hac hν₁u

/-- **An ergodic probability measure is an extreme point** of the invariant probability measures. -/
theorem mem_extremePoints {G : Type*} [SMul G X] [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] [ErgodicSMul G X μ] :
    μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X) := by
  rw [invariantProbabilityMeasures_eq, ← measure_univ (μ := μ)]
  exact mem_extremePoints_measure_univ_eq

end SMul

/-! ### The reverse direction, for a countable group action -/

section Group

variable {G X : Type*} [Group G] [Countable G] [MulAction G X] {m : MeasurableSpace X}
  [MeasurableConstSMul G X] {μ : Measure X}

/-- **An extreme invariant measure of finite total mass is ergodic.** -/
theorem of_mem_extremePoints_measure_univ_eq {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : μ ∈ extremePoints ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X c)) : ErgodicSMul G X μ := by
  have hinv : SMulInvariantMeasure G X μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · have : μ = 0 := measure_univ_eq_zero.mp h.1.2
    subst this
    exact ⟨fun _ _ => EventuallyEmptyOrUniv.bot.anti ae_zero.le⟩
  have : IsFiniteMeasure μ := ⟨by rw [h.1.2]; exact lt_top_iff_ne_top.mpr hc⟩
  -- an exactly invariant `t` of intermediate mass would write `μ` as a proper combination of
  -- the invariant measures `c • μ[|t]` and `c • μ[|tᶜ]` of mass `c`; countability of `G` reduces
  -- almost invariant events to exactly invariant ones
  refine TauCeti.MeasureTheory.ergodicSMul_of_forall_smul_invariant fun t htm htinv => ?_
  have hmem {u : Set X} (hum : MeasurableSet u) (huinv : ∀ g : G, (fun x => g • x) ⁻¹' u = u)
      (hu0 : μ u ≠ 0) : c • μ[|u] ∈ invariantMeasuresOfMeasureUnivEq G X c := by
    have := SMulInvariantMeasure.restrict (G := G) (μ := μ) hum huinv
    refine ⟨?_, ?_⟩
    · -- `μ[|u]` is `(μ u)⁻¹ • μ.restrict u` by the definition of `ProbabilityTheory.cond`
      rw [ProbabilityTheory.cond]; infer_instance
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
  rw [← hcond] at hs'
  simp [ProbabilityTheory.cond_apply, htm] at hs'

/-- **An extreme invariant probability measure is ergodic.** -/
theorem of_mem_extremePoints
    (h : μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X)) : ErgodicSMul G X μ :=
  of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top <| by
    rwa [invariantProbabilityMeasures_eq] at h

/-- **Ergodicity is extremality** for a countable group action, among the invariant measures of
the same finite total mass. -/
theorem iff_mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] :
    ErgodicSMul G X μ ↔ μ ∈ extremePoints ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X (μ univ)) :=
  ⟨fun _ => mem_extremePoints_measure_univ_eq,
    of_mem_extremePoints_measure_univ_eq (measure_ne_top μ _)⟩

/-- **Ergodicity is extremality** for a countable group action: an invariant probability measure
is ergodic if and only if it is an extreme point of the invariant probability measures. -/
theorem iff_mem_extremePoints [IsProbabilityMeasure μ] :
    ErgodicSMul G X μ ↔ μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X) :=
  ⟨fun _ => mem_extremePoints, of_mem_extremePoints⟩

end Group

end ErgodicSMul
