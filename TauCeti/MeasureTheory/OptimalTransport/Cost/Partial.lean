/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Partial transport and the relaxed primal value

A partial plan has marginals dominated by the prescribed measures. The value
`partialTransportCost c μ ν ε` permits a source-mass deficit of at most `ε`; for equal-mass
measures this is also the target-mass deficit. The relaxed value `relaxedTransportCost`
is the supremum of these values over positive deficits, so it allows arbitrarily small
amounts of mass to be discarded before minimizing. The zero deficit is deliberately excluded
from that supremum: extended Borel costs can have a gap between the ordinary and relaxed values.

For finite measures of equal mass, every partial plan can be completed by coupling its residual
marginals. If the cost is bounded by a finite constant `C`, completion costs at most `C * ε`.
Consequently relaxation does not change the value of a bounded cost, without any topology or
measurability hypothesis on the cost. Infinite values remain part of both primal interfaces.

## References

* M. Beiglböck, C. Léonard and W. Schachermayer, *A general duality theorem for the
  Monge--Kantorovich transport problem*, Studia Math. 209 (2012), 151--167.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
  {c d : X × Y → ℝ≥0∞} {ε a : ℝ≥0∞}

/-- The infimum cost of plans with dominated marginals and source-mass deficit at most `ε`.
For equal-mass measures the same bound holds for the target-mass deficit. An empty feasible
set has value `∞`. -/
def partialTransportCost (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y)
    (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : π.fst ≤ μ) (_ : π.snd ≤ ν)
    (_ : μ univ ≤ π univ + ε), ∫⁻ z, c z ∂π

/-- The defining infimum over partial plans. -/
theorem partialTransportCost_def :
    partialTransportCost c μ ν ε =
      ⨅ (π : Measure (X × Y)) (_ : π.fst ≤ μ) (_ : π.snd ≤ ν)
        (_ : μ univ ≤ π univ + ε), ∫⁻ z, c z ∂π := (rfl)

/-- A feasible partial plan bounds the partial transport cost from above. -/
theorem partialTransportCost_le_lintegral (hfst : π.fst ≤ μ) (hsnd : π.snd ≤ ν)
    (hmass : μ univ ≤ π univ + ε) :
    partialTransportCost c μ ν ε ≤ ∫⁻ z, c z ∂π :=
  iInf_le_of_le π <| iInf_le_of_le hfst <| iInf_le_of_le hsnd <| iInf_le_of_le hmass le_rfl

/-- A lower bound on every feasible partial plan bounds the partial value from below. -/
theorem le_partialTransportCost
    (h : ∀ π : Measure (X × Y), π.fst ≤ μ → π.snd ≤ ν →
      μ univ ≤ π univ + ε → a ≤ ∫⁻ z, c z ∂π) : a ≤ partialTransportCost c μ ν ε :=
  le_iInf fun π ↦ le_iInf fun hfst ↦ le_iInf fun hsnd ↦ le_iInf fun hmass ↦
    h π hfst hsnd hmass

/-- A strict upper bound on the partial value is witnessed by a partial plan. -/
theorem partialTransportCost_lt_iff :
    partialTransportCost c μ ν ε < a ↔
      ∃ π : Measure (X × Y), π.fst ≤ μ ∧ π.snd ≤ ν ∧
        μ univ ≤ π univ + ε ∧ ∫⁻ z, c z ∂π < a := by
  simp only [partialTransportCost, iInf_lt_iff, exists_prop]

/-- Increasing the permitted deficit decreases the partial value. -/
theorem partialTransportCost_antitone : Antitone (partialTransportCost c μ ν) := by
  intro ε δ hεδ
  exact le_partialTransportCost fun π hfst hsnd hmass ↦
    partialTransportCost_le_lintegral hfst hsnd (hmass.trans (by gcongr))

/-- The partial value is monotone in the cost. -/
@[gcongr]
theorem partialTransportCost_mono (hcd : c ≤ d) :
    partialTransportCost c μ ν ε ≤ partialTransportCost d μ ν ε :=
  le_partialTransportCost fun _ hfst hsnd hmass ↦
    (partialTransportCost_le_lintegral hfst hsnd hmass).trans (lintegral_mono hcd)

/-- A full coupling is feasible for every permitted deficit. -/
theorem partialTransportCost_le_transportCost :
    partialTransportCost c μ ν ε ≤ transportCost c μ ν :=
  le_transportCost fun _ hπ ↦ partialTransportCost_le_lintegral
    hπ.fst_eq.le hπ.snd_eq.le (by rw [hπ.measure_univ_left]; exact le_self_add)

/-- Discarding the entire source permits the zero plan and gives zero cost. -/
@[simp]
theorem partialTransportCost_eq_zero (hε : μ univ ≤ ε) :
    partialTransportCost c μ ν ε = 0 := by
  refine le_antisymm ?_ bot_le
  simpa using partialTransportCost_le_lintegral (c := c) (π := 0)
    (by simpa using μ.zero_le) (by simpa using ν.zero_le) (by simpa using hε)

/-- At zero deficit, dominated marginals of finite equal mass are the prescribed marginals,
so the partial and ordinary primal values agree. -/
@[simp]
theorem partialTransportCost_zero [IsFiniteMeasure μ] (hmass : μ univ = ν univ) :
    partialTransportCost c μ ν 0 = transportCost c μ ν := by
  refine le_antisymm partialTransportCost_le_transportCost ?_
  refine le_partialTransportCost fun π hfst hsnd hπmass ↦ ?_
  have : IsFiniteMeasure π.fst := isFiniteMeasure_of_le μ hfst
  have : IsFiniteMeasure ν := ⟨by rw [← hmass]; exact measure_lt_top μ univ⟩
  have : IsFiniteMeasure π.snd := isFiniteMeasure_of_le ν hsnd
  have heq : π univ = μ univ := le_antisymm
    (by simpa only [Measure.fst_univ] using hfst univ) (by simpa using hπmass)
  exact transportCost_le_lintegral
    ⟨Measure.eq_of_le_of_measure_univ_eq hfst (by simpa only [Measure.fst_univ] using heq),
      Measure.eq_of_le_of_measure_univ_eq hsnd
        (by simpa only [Measure.snd_univ, ← hmass] using heq)⟩ c

/-- Relaxed transport minimizes after permitting an arbitrarily small positive source-mass
deficit. For probability measures this is the relaxed primal value of
Beiglböck--Léonard--Schachermayer. -/
def relaxedTransportCost (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨆ (ε : ℝ≥0∞) (_ : 0 < ε), partialTransportCost c μ ν ε

/-- The relaxed value as a supremum over strictly positive deficits. -/
theorem relaxedTransportCost_def :
    relaxedTransportCost c μ ν = ⨆ (ε : ℝ≥0∞) (_ : 0 < ε), partialTransportCost c μ ν ε :=
  (rfl)

/-- Every positive-deficit value lies below the relaxed value. -/
theorem partialTransportCost_le_relaxedTransportCost (hε : 0 < ε) :
    partialTransportCost c μ ν ε ≤ relaxedTransportCost c μ ν :=
  le_iSup_of_le ε (le_iSup_of_le hε le_rfl)

/-- Bound the relaxed value by bounding each positive-deficit value. -/
theorem relaxedTransportCost_le
    (h : ∀ ε : ℝ≥0∞, 0 < ε → partialTransportCost c μ ν ε ≤ a) :
    relaxedTransportCost c μ ν ≤ a :=
  iSup_le fun ε ↦ iSup_le fun hε ↦ h ε hε

/-- Relaxation can only decrease the ordinary transport value. -/
theorem relaxedTransportCost_le_transportCost :
    relaxedTransportCost c μ ν ≤ transportCost c μ ν :=
  relaxedTransportCost_le fun _ _ ↦ partialTransportCost_le_transportCost

/-- The relaxed value is monotone in the cost. -/
@[gcongr]
theorem relaxedTransportCost_mono (hcd : c ≤ d) :
    relaxedTransportCost c μ ν ≤ relaxedTransportCost d μ ν :=
  relaxedTransportCost_le fun _ hε ↦
    (partialTransportCost_mono hcd).trans (partialTransportCost_le_relaxedTransportCost hε)

/-- Completing a partial plan for a bounded cost adds at most the bound times the deficit.
No measurability of the cost is needed. -/
theorem transportCost_le_partialTransportCost_add [IsFiniteMeasure μ]
    (hmass : μ univ = ν univ) (C : NNReal) (hc : ∀ z, c z ≤ C) :
    transportCost c μ ν ≤ partialTransportCost c μ ν ε + C * ε := by
  rw [partialTransportCost_def]
  simp only [ENNReal.iInf_add]
  refine le_iInf fun π ↦ le_iInf fun hfst ↦ le_iInf fun hsnd ↦ le_iInf fun hπmass ↦ ?_
  obtain ⟨ρ, -, hπρ, hρmass⟩ := exists_isCoupling_add_of_le_marginals hmass hfst hsnd
  have hdeficit : ρ univ ≤ ε := by
    rw [hρmass, tsub_le_iff_right]
    simpa [add_comm] using hπmass
  calc transportCost c μ ν ≤ ∫⁻ z, c z ∂(π + ρ) := transportCost_le_lintegral hπρ c
    _ = (∫⁻ z, c z ∂π) + ∫⁻ z, c z ∂ρ := lintegral_add_measure _ _ _
    _ ≤ (∫⁻ z, c z ∂π) + C * ε := by
      gcongr
      calc ∫⁻ z, c z ∂ρ ≤ ∫⁻ _, (C : ℝ≥0∞) ∂ρ := lintegral_mono hc
        _ = C * ρ univ := lintegral_const _
        _ ≤ C * ε := by gcongr

/-- **Relaxation preserves bounded-cost transport.** For finite equal-mass measures and a
uniformly bounded nonnegative cost, the relaxed and ordinary primal values coincide. -/
theorem relaxedTransportCost_eq_transportCost_of_bounded [IsFiniteMeasure μ]
    (hmass : μ univ = ν univ) (C : NNReal) (hc : ∀ z, c z ≤ C) :
    relaxedTransportCost c μ ν = transportCost c μ ν := by
  refine le_antisymm relaxedTransportCost_le_transportCost ?_
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ ↦ ?_
  have hη' : (η : ℝ≥0∞) ≠ 0 := by exact_mod_cast hη.ne'
  obtain ⟨δ, hδ, hCδ⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := (C : ℝ≥0∞))
    ENNReal.coe_ne_top hη'
  have hδ' : 0 < (δ : ℝ≥0∞) := by exact_mod_cast hδ
  calc transportCost c μ ν ≤ partialTransportCost c μ ν δ + C * δ :=
        transportCost_le_partialTransportCost_add hmass C hc
    _ ≤ relaxedTransportCost c μ ν + η :=
      add_le_add (partialTransportCost_le_relaxedTransportCost hδ')
        (by simpa only [mul_comm] using hCδ.le)

end TauCeti
