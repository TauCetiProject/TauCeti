/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Extreme
public import TauCeti.MeasureTheory.Group.CountableAction
import Mathlib.Dynamics.Ergodic.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Ergodic group actions and extreme invariant measures

For a countable group `G` acting measurably on `X`, an invariant probability measure is ergodic
if and only if it is an extreme point of the convex set of `G`-invariant probability measures.
This is the group-action form of Mathlib's `Ergodic.iff_mem_extremePoints`, which concerns a
single measure-preserving map; the two are not interchangeable, since a group action has no one
map whose ergodicity is the action's.

The route is Mathlib's. An almost invariant function under an ergodic action is almost
everywhere constant (`ErgodicSMul.ae_eq_const_of_forall_comp_smul_ae_eq`); applied to a
Radon–Nikodym derivative, an invariant measure absolutely continuous with respect to an ergodic
one is a multiple of it (`ErgodicSMul.eq_smul_of_absolutelyContinuous`), which gives extremality.
Conversely an invariant event of intermediate mass decomposes the measure as a proper convex
combination of its two conditional measures; countability of `G` reduces almost invariant events
to exactly invariant ones.

## Main results

* `MeasureTheory.ErgodicSMul.ae_eq_const_of_forall_comp_smul_ae_eq`
* `MeasureTheory.ErgodicSMul.eq_smul_of_absolutelyContinuous`,
  `MeasureTheory.ErgodicSMul.eq_of_absolutelyContinuous`
* `MeasureTheory.invariantProbabilityMeasures`
* `MeasureTheory.ergodicSMul_iff_mem_extremePoints`

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
multiple of it**: the Radon–Nikodym derivative is invariant under every group element, hence
almost everywhere constant. The action-level analogue of
`Ergodic.eq_smul_of_absolutelyContinuous`. -/
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

/-- **An invariant probability measure absolutely continuous with respect to an ergodic one equals
it.** -/
theorem ErgodicSMul.eq_of_absolutelyContinuous [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [ErgodicSMul G X μ]
    [SMulInvariantMeasure G X ν] (hνμ : ν ≪ μ) : ν = μ := by
  obtain ⟨c, rfl⟩ := ErgodicSMul.eq_smul_of_absolutelyContinuous (G := G) hνμ
  have h : c = 1 := by
    have := (measure_univ : (c • μ) univ = 1)
    rwa [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at this
  rw [h, one_smul]

/-- The convex set of `G`-invariant probability measures on `X`, the set whose extreme points
ergodicity characterises. -/
def invariantProbabilityMeasures (G X : Type*) [SMul G X] [MeasurableSpace X] : Set (Measure X) :=
  {ν | SMulInvariantMeasure G X ν ∧ IsProbabilityMeasure ν}

/-- **An ergodic probability measure is an extreme point** of the invariant probability measures:
any measure in a proper convex decomposition is absolutely continuous, hence equal to it. -/
theorem ErgodicSMul.mem_extremePoints [MeasurableConstSMul G X] [IsProbabilityMeasure μ]
    [ErgodicSMul G X μ] : μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X) := by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro ν₁ ⟨hν₁, hν₁p⟩ ν₂ ⟨hν₂, hν₂p⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have hac : ν₁ ≪ a • ν₁ + b • ν₂ := (absolutelyContinuous_smul ha.ne').add_right _
  exact ErgodicSMul.eq_of_absolutelyContinuous (G := G) hac

/-- **An extreme invariant probability measure is ergodic.** -/
theorem ErgodicSMul.of_mem_extremePoints [Countable G] [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
    (h : μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X)) : ErgodicSMul G X μ := by
  -- as for a single map: an invariant `t` of intermediate mass would decompose `μ` as a proper
  -- combination of `μ[|t]` and `μ[|tᶜ]`, both invariant probability measures; countability of
  -- `G` reduces almost invariant events to exactly invariant ones
  refine TauCeti.MeasureTheory.ergodicSMul_of_forall_smul_invariant fun t htm htinv => ?_
  set S := invariantProbabilityMeasures G X
  have hmem {u : Set X} (hum : MeasurableSet u) (huinv : ∀ g : G, (fun x => g • x) ⁻¹' u = u)
      (hu0 : μ u ≠ 0) : μ[|u] ∈ S := by
    refine ⟨⟨fun g v hv => ?_⟩, cond_isProbabilityMeasure hu0⟩
    have hres : (μ.restrict u).map (g • ·) = μ.restrict u := by
      have hmp := (measurePreserving_smul g μ).restrict_preimage hum
      rw [huinv g] at hmp
      exact hmp.map_eq
    change ((μ u)⁻¹ • μ.restrict u) ((g • ·) ⁻¹' v) = ((μ u)⁻¹ • μ.restrict u) v
    rw [Measure.smul_apply, Measure.smul_apply,
      ← Measure.map_apply (measurable_const_smul g) hv, hres]
  by_contra H
  obtain ⟨hs, hs'⟩ : μ t ≠ 0 ∧ μ tᶜ ≠ 0 := by
    simpa [eventuallyEmptyOrUniv_iff, ae_iff, and_comm] using! H
  have hcond : μ[|t] = μ := by
    apply h.2 (hmem htm htinv hs) (hmem htm.compl (fun g => by rw [preimage_compl, htinv g]) hs')
    refine ⟨μ t, μ tᶜ, pos_iff_ne_zero.mpr hs, pos_iff_ne_zero.mpr hs', ?_, ?_⟩
    · rw [measure_add_measure_compl htm, measure_univ]
    · simp [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel, hs, hs',
        measure_ne_top, Measure.restrict_add_restrict_compl htm]
  have : μ tᶜ = 0 := by
    rw [← hcond, ProbabilityTheory.cond_apply htm, inter_compl_self, measure_empty, mul_zero]
  exact hs' this

/-- **Ergodicity is extremality** for a countable group action: an invariant probability measure
is ergodic if and only if it is an extreme point of the invariant probability measures. -/
theorem ergodicSMul_iff_mem_extremePoints [Countable G] [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ] :
    ErgodicSMul G X μ ↔ μ ∈ extremePoints ℝ≥0∞ (invariantProbabilityMeasures G X) :=
  ⟨fun _ => ErgodicSMul.mem_extremePoints, ErgodicSMul.of_mem_extremePoints⟩

end MeasureTheory
