/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Countable
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Total variation distance as the least probability of disagreement of a coupling

Let `μ` and `ν` be measures on `α`, and let `γ` be a coupling of them, a
measure on `α × α` with marginals `μ` and `ν`. Whatever the coupling, the two marginals can only
differ on the event where the two coordinates differ, so, for finite `μ`,

```text
etvDist μ ν ≤ 2 * γ {z | z.1 ≠ z.2}.
```

On a countable space with measurable singletons some coupling attains equality, so `tvDist μ ν / 2`
is the least probability of disagreement over all couplings. The optimal coupling puts the common
part `μ ⊓ ν` on the diagonal, which gives mass `min (μ {x}) (ν {x})` to `(x, x)`, and couples the
two remaining excesses arbitrarily; all of the disagreement comes from these excesses, whose mass is
`etvDist μ ν / 2`.

This characterization turns bounds on total variation into constructions of couplings and back;
in the theory of Markov chain mixing, optimal couplings of the rows of a kernel are composed into
couplings of its powers.

The factor two comes from Mathlib's normalization of `MeasureTheory.tvDist`, under which the
distance between probability measures lies in `[0, 2]`.

## Main statements

* `MeasureTheory.Measure.inf_apply_singleton`: the infimum of two measures gives a measurable
  singleton the smaller of the two masses;
* `MeasureTheory.etvDist_eq_two_mul_measure_univ_sub_inf`: on a countable space, total variation
  is twice the mass of `μ` not shared with `ν`;
* `TauCeti.IsCoupling.etvDist_le_two_mul_measure_ne` and
  `TauCeti.IsCoupling.tvDist_le_two_mul_measureReal_ne`: the **coupling inequality**, total
  variation is at most twice the probability of disagreement of any coupling;
* `TauCeti.exists_isCoupling_etvDist_eq_two_mul_measure_ne`: on a countable space, an optimal
  coupling attains the bound;
* `TauCeti.isLeast_measureReal_ne_of_isCoupling`: on a countable space, `tvDist μ ν / 2` is the
  least probability of disagreement over all couplings of `μ` and `ν`.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Proposition 4.7 and Remark 4.8.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The infimum of two measures gives a measurable singleton the smaller of its two masses. -/
@[simp]
theorem inf_apply_singleton (μ ν : Measure α) (x : α) : (μ ⊓ ν) {x} = min (μ {x}) (ν {x}) := by
  rw [inf_apply (measurableSet_singleton x)]
  refine le_antisymm (le_min (sInf_le ⟨univ, by simp⟩) (sInf_le ⟨∅, by simp⟩)) (le_sInf ?_)
  rintro _ ⟨t, rfl⟩
  by_cases hx : x ∈ t <;> simp [hx]

end MeasureTheory.Measure

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {μ ν : Measure α}

/-- **Total variation and overlap.** On a countable space with measurable singletons, for a finite
measure `μ` and a measure `ν` of the same total mass, the total variation distance is twice the mass
of `μ` that is not shared with `ν`, the shared part being the infimum `μ ⊓ ν`. -/
theorem etvDist_eq_two_mul_measure_univ_sub_inf [IsFiniteMeasure μ] (h : μ univ = ν univ) :
    etvDist μ ν = 2 * (μ univ - (μ ⊓ ν) univ) := by
  have hfin : (μ ⊓ ν) univ ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ univ) (Measure.le_iff'.1 inf_le_left univ)
  -- Pointwise, `μ {x}` splits as `min (μ {x}) (ν {x}) + (μ {x} - ν {x})`.
  have hsplit : μ univ = (μ ⊓ ν) univ + ∑' x, (μ {x} - ν {x}) := by
    rw [← μ.tsum_indicator_apply_singleton univ .univ,
      ← (μ ⊓ ν).tsum_indicator_apply_singleton univ .univ, ← tsum_add]
    simp only [indicator_univ, Measure.inf_apply_singleton]
    exact tsum_congr fun x => by rw [add_comm, tsub_add_min]
  rw [etvDist_eq_two_mul_tsum_singleton h, ENNReal.sub_eq_of_eq_add_rev hfin hsplit]

end MeasureTheory

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {γ : Measure (α × α)} {μ ν : Measure α}

namespace IsCoupling

/-- **The coupling inequality, in `ℝ≥0∞`.** The total variation distance between two finite
measures is at most twice the mass that any coupling of them gives to the event where the two
coordinates differ. -/
theorem etvDist_le_two_mul_measure_ne [IsFiniteMeasure μ] (hγ : IsCoupling γ μ ν) :
    etvDist μ ν ≤ 2 * γ {z | z.1 ≠ z.2} := by
  rw [etvDist_le_two_mul_iff hγ.measure_univ_eq]
  intro A hA
  rw [← hγ.fst_eq, ← hγ.snd_eq, Measure.fst_apply hA, Measure.snd_apply hA]
  -- Where the coordinates agree, the first one lies in `A` exactly when the second does.
  calc γ (Prod.fst ⁻¹' A)
      ≤ γ (Prod.fst ⁻¹' A ∩ {z | z.1 = z.2}) + γ (Prod.fst ⁻¹' A \ {z | z.1 = z.2}) :=
        measure_le_inter_add_sdiff γ _ _
    _ ≤ γ (Prod.snd ⁻¹' A) + γ {z | z.1 ≠ z.2} := by
        gcongr
        · rintro z ⟨hz, hzz⟩
          simpa [mem_preimage, ← (show z.1 = z.2 from hzz)] using hz
        · exact fun z hz => hz.2

/-- **The coupling inequality.** The total variation distance between two measures is at most
twice the mass that any coupling of them gives to the event where the two coordinates differ.
For infinite measures the left side is the junk value `0`. -/
theorem tvDist_le_two_mul_measureReal_ne (hγ : IsCoupling γ μ ν) :
    tvDist μ ν ≤ 2 * γ.real {z | z.1 ≠ z.2} := by
  by_cases hμ : IsFiniteMeasure μ
  · have := hγ.isFiniteMeasure
    rw [tvDist, measureReal_def, ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (by finiteness) hγ.etvDist_le_two_mul_measure_ne
  · rw [tvDist_of_not_isFiniteMeasure_left hμ]
    positivity

end IsCoupling

variable [Countable α] [MeasurableSingletonClass α]

/-- **Optimal coupling.** On a countable space with measurable singletons, a finite measure `μ`
and a measure `ν` of the same total mass have a coupling whose mass off the diagonal is exactly
half their total variation distance. -/
theorem exists_isCoupling_etvDist_eq_two_mul_measure_ne [IsFiniteMeasure μ]
    (h : μ univ = ν univ) :
    ∃ γ : Measure (α × α), IsCoupling γ μ ν ∧ etvDist μ ν = 2 * γ {z | z.1 ≠ z.2} := by
  -- Put the common part `μ ⊓ ν` on the diagonal and couple the two excesses.
  have hdiag := (μ ⊓ ν).isCoupling_diagonalCoupling
  obtain ⟨ρ, -, hγ, hρ⟩ := exists_isCoupling_add_of_le_marginals h
    (hdiag.fst_eq.trans_le inf_le_left) (hdiag.snd_eq.trans_le inf_le_right)
  refine ⟨_, hγ, le_antisymm hγ.etvDist_le_two_mul_measure_ne ?_⟩
  have hne : (μ ⊓ ν).diagonalCoupling {z : α × α | z.1 ≠ z.2} = 0 := by
    rw [Measure.diagonalCoupling_apply _ .of_discrete]
    simp
  calc 2 * ((μ ⊓ ν).diagonalCoupling + ρ) {z | z.1 ≠ z.2} ≤ 2 * ρ univ := by
        rw [_root_.add_apply, hne, zero_add]
        gcongr
        exact subset_univ _
    _ = etvDist μ ν := by
        rw [hρ, ← hdiag.measure_univ_left, etvDist_eq_two_mul_measure_univ_sub_inf h]

/-- **Total variation as the least probability of disagreement.** On a countable space with
measurable singletons, for a finite measure `μ` and a measure `ν` of the same total mass (e.g. two
probability measures), `tvDist μ ν / 2` is the least mass that a coupling of `μ` and `ν` gives to
the event where the two coordinates differ. -/
theorem isLeast_measureReal_ne_of_isCoupling [IsFiniteMeasure μ] (h : μ univ = ν univ) :
    IsLeast ((fun γ : Measure (α × α) => γ.real {z | z.1 ≠ z.2}) '' {γ | IsCoupling γ μ ν})
      (tvDist μ ν / 2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ, heq⟩ := exists_isCoupling_etvDist_eq_two_mul_measure_ne h
    refine ⟨γ, hγ, ?_⟩
    simp [tvDist, heq, measureReal_def]
  · rintro _ ⟨γ, hγ, rfl⟩
    linarith [hγ.tvDist_le_two_mul_measureReal_ne]

end TauCeti
