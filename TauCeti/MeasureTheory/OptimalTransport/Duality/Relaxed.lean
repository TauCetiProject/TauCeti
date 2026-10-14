/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.DominatedMeasure
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Partial.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Duality.LowerSemicontinuous

/-!
# Weak duality for the relaxed transport value

The relaxed transport value `TauCeti.relaxedTransportCost c μ ν` minimizes the cost over partial
plans whose discarded mass is at most an arbitrarily small positive bound. It never exceeds the
ordinary value `TauCeti.transportCost c μ ν`, and for extended-valued Borel costs it can be
strictly smaller.
This file shows that it is still bounded below by every Kantorovich dual value: for finite
measures of equal mass and integrable potentials `φ`, `ψ` with `φ x + ψ y ≤ c (x, y)`, the
positive part of `∫ φ dμ + ∫ ψ dν` is at most the relaxed value. This is the easy half of the
duality theorem of Beiglböck--Léonard--Schachermayer, which identifies the relaxed value with the
dual value for every Borel cost on Polish spaces.

A partial plan `π` with marginals dominated by `μ` and `ν` couples its own marginals, so weak
duality bounds `∫ φ dπ.fst + ∫ ψ dπ.snd` by its cost. The remaining part of the dual value is the
dual value of the residual marginals `μ - π.fst` and `ν - π.snd`, whose masses are at most the
deficit; by uniform integrability of `|φ|` and `|ψ|` it is small when the deficit is small.

Combined with strong duality for lower semicontinuous costs, the relaxed and ordinary values
agree for every nonnegative lower semicontinuous cost on Polish spaces: discarding a small amount
of mass cannot lower such a transport cost by a fixed amount.

## Main statements

* `TauCeti.DualFeasible.exists_ofReal_kantorovichDualValue_le_partialTransportCost_add` — a
  feasible integrable pair bounds every partial value up to an error linear in the deficit plus
  an arbitrarily small slack;
* `TauCeti.DualFeasible.ofReal_kantorovichDualValue_le_relaxedTransportCost` — **weak duality for
  the relaxed value**, with the finite real form
  `TauCeti.DualFeasible.kantorovichDualValue_le_toReal_relaxedTransportCost` and the `EReal` form
  `TauCeti.DualFeasible.kantorovichDualValue_le_relaxedTransportCost`;
* `TauCeti.relaxedTransportCost_eq_transportCost_of_lowerSemicontinuous` — **relaxation is exact
  for lower semicontinuous costs** on Polish spaces.

## References

* M. Beiglböck, C. Léonard and W. Schachermayer, *A general duality theorem for the
  Monge--Kantorovich transport problem*, Studia Math. 209 (2012), 151--167.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {c : X × Y → ℝ≥0∞} {φ : X → ℝ} {ψ : Y → ℝ}

/-- **Weak duality against partial plans.** Let `μ` and `ν` be finite measures of equal mass and
`(φ, ψ)` an integrable pair satisfying `φ x + ψ y ≤ c (x, y)`. For every `η > 0` there is a
constant `C` such that, for every permitted deficit `ε`, the positive part of the dual value of
`(φ, ψ)` is at most the partial transport value with deficit `ε` plus `C * ε + η`. The constant
depends only on the potentials, the marginals, and `η`. -/
theorem DualFeasible.exists_ofReal_kantorovichDualValue_le_partialTransportCost_add
    [IsFiniteMeasure μ] (hfeas : DualFeasible (fun z ↦ (c z : EReal)) φ ψ) (hmass : μ univ = ν univ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ C : NNReal, ∀ ε : ℝ≥0∞,
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) ≤ partialTransportCost c μ ν ε + C * ε + η := by
  have : IsFiniteMeasure ν := ⟨hmass ▸ measure_lt_top μ univ⟩
  -- Uniform integrability of `|φ|` and `|ψ|` over measures dominated by the marginals.
  obtain ⟨A, hA⟩ := exists_lintegral_le_mul_measure_add_of_ne_top
    hφ.abs.lintegral_lt_top.ne (ENNReal.half_pos hη.ne')
  obtain ⟨B, hB⟩ := exists_lintegral_le_mul_measure_add_of_ne_top
    hψ.abs.lintegral_lt_top.ne (ENNReal.half_pos hη.ne')
  refine ⟨A + B, fun ε ↦ ?_⟩
  rw [partialTransportCost_def]
  simp only [ENNReal.iInf_add]
  refine le_iInf fun π ↦ le_iInf fun hfst ↦ le_iInf fun hsnd ↦ le_iInf fun hπmass ↦ ?_
  have : IsFiniteMeasure π.fst := isFiniteMeasure_of_le μ hfst
  have : IsFiniteMeasure π.snd := isFiniteMeasure_of_le ν hsnd
  -- The residual marginals have mass at most the deficit.
  have hμε : (μ - π.fst) univ ≤ ε := by
    rw [Measure.sub_apply MeasurableSet.univ hfst, Measure.fst_univ, tsub_le_iff_right]
    simpa [add_comm] using hπmass
  have hνε : (ν - π.snd) univ ≤ ε := by
    rw [Measure.sub_apply MeasurableSet.univ hsnd, Measure.snd_univ, ← hmass, tsub_le_iff_right]
    simpa [add_comm] using hπmass
  -- The dual value splits into the dual values of `(π.fst, π.snd)` and of the residual marginals.
  have hsplit : kantorovichDualValue μ ν φ ψ = kantorovichDualValue π.fst π.snd φ ψ +
      kantorovichDualValue (μ - π.fst) (ν - π.snd) φ ψ := by
    conv_lhs => rw [← Measure.sub_add_cancel_of_le hfst, ← Measure.sub_add_cancel_of_le hsnd]
    simp only [kantorovichDualValue_def]
    rw [integral_add_measure (hφ.mono_measure Measure.sub_le) (hφ.mono_measure hfst),
      integral_add_measure (hψ.mono_measure Measure.sub_le) (hψ.mono_measure hsnd)]
    ring
  -- Weak duality bounds the first part by the cost of `π`, which couples its own marginals.
  have hπ : ENNReal.ofReal (kantorovichDualValue π.fst π.snd φ ψ) ≤ ∫⁻ z, c z ∂π :=
    hfeas.ofReal_kantorovichDualValue_le_lintegral (hφ.mono_measure hfst)
      (hψ.mono_measure hsnd) ⟨rfl, rfl⟩
  -- The residual part is bounded by the integrals of `|φ|` and `|ψ|` against small measures.
  have hresφ : ENNReal.ofReal (∫ x, φ x ∂(μ - π.fst)) ≤ A * ε + η / 2 :=
    MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans <|
      (lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal (le_abs_self _)).trans <|
        (hA _ Measure.sub_le).trans (by gcongr)
  have hresψ : ENNReal.ofReal (∫ y, ψ y ∂(ν - π.snd)) ≤ B * ε + η / 2 :=
    MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans <|
      (lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal (le_abs_self _)).trans <|
        (hB _ Measure.sub_le).trans (by gcongr)
  calc ENNReal.ofReal (kantorovichDualValue μ ν φ ψ)
      ≤ ENNReal.ofReal (kantorovichDualValue π.fst π.snd φ ψ) +
          (ENNReal.ofReal (∫ x, φ x ∂(μ - π.fst)) + ENNReal.ofReal (∫ y, ψ y ∂(ν - π.snd))) := by
        rw [hsplit, kantorovichDualValue_def (μ - π.fst)]
        exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ENNReal.ofReal_add_le)
    _ ≤ ∫⁻ z, c z ∂π + ((A * ε + η / 2) + (B * ε + η / 2)) :=
        add_le_add hπ (add_le_add hresφ hresψ)
    _ = ∫⁻ z, c z ∂π + (A + B : NNReal) * ε + (η / 2 + η / 2) := by
        rw [ENNReal.coe_add, add_mul]
        ring
    _ = ∫⁻ z, c z ∂π + (A + B : NNReal) * ε + η := by rw [ENNReal.add_halves]

/-- **Weak duality for the relaxed transport value.** For finite measures of equal mass and an
integrable pair `(φ, ψ)` satisfying `φ x + ψ y ≤ c (x, y)`, the positive part of the dual value
is at most the relaxed transport value. No measurability or topology is assumed on the cost. -/
theorem DualFeasible.ofReal_kantorovichDualValue_le_relaxedTransportCost [IsFiniteMeasure μ]
    (hfeas : DualFeasible (fun z ↦ (c z : EReal)) φ ψ) (hmass : μ univ = ν univ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) :
    ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) ≤ relaxedTransportCost c μ ν :=
  le_relaxedTransportCost_of_forall_exists_le_add fun _ hη ↦
    hfeas.exists_ofReal_kantorovichDualValue_le_partialTransportCost_add hmass hφ hψ hη

/-- **Weak duality for the relaxed transport value in finite real form.** If the relaxed value is
finite, every integrable feasible dual value is at most its real representative. -/
theorem DualFeasible.kantorovichDualValue_le_toReal_relaxedTransportCost [IsFiniteMeasure μ]
    (hfeas : DualFeasible (fun z ↦ (c z : EReal)) φ ψ) (hmass : μ univ = ν univ)
    (hne : relaxedTransportCost c μ ν ≠ ⊤) (hφ : Integrable φ μ) (hψ : Integrable ψ ν) :
    kantorovichDualValue μ ν φ ψ ≤ (relaxedTransportCost c μ ν).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hne).1
    (hfeas.ofReal_kantorovichDualValue_le_relaxedTransportCost hmass hφ hψ)

/-- **Weak duality for the relaxed transport value.** Every integrable feasible dual value is at
most the relaxed transport value. The comparison in `EReal` remains meaningful when the relaxed
value is `∞`. -/
theorem DualFeasible.kantorovichDualValue_le_relaxedTransportCost [IsFiniteMeasure μ]
    (hfeas : DualFeasible (fun z ↦ (c z : EReal)) φ ψ) (hmass : μ univ = ν univ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) :
    (kantorovichDualValue μ ν φ ψ : EReal) ≤ (relaxedTransportCost c μ ν : ℝ≥0∞) :=
  EReal.coe_le_coe_ennreal_of_ofReal_le <|
    hfeas.ofReal_kantorovichDualValue_le_relaxedTransportCost hmass hφ hψ

section Polish

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
  [BorelSpace Y] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Relaxation is exact for lower semicontinuous costs.** For a nonnegative lower
semicontinuous cost on a product of Polish spaces and two probability measures, the relaxed and
ordinary transport values coincide, whether finite or infinite. -/
theorem relaxedTransportCost_eq_transportCost_of_lowerSemicontinuous
    (hc : LowerSemicontinuous c) : relaxedTransportCost c μ ν = transportCost c μ ν :=
  le_antisymm relaxedTransportCost_le_transportCost <|
    (isLUB_ofReal_kantorovichDualValue_integrable_of_lowerSemicontinuous hc).2
      fun _ ⟨_, _, hφ, hψ, hfeas, hr⟩ ↦ hr ▸
        hfeas.ofReal_kantorovichDualValue_le_relaxedTransportCost (by simp) hφ hψ

end Polish

end TauCeti
