/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import TauCeti.MeasureTheory.Integral.DominatedMeasure
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Partial.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Duality.LowerSemicontinuous

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.MeasureTheory.OptimalTransport.Cost.Partial.Truncation
import TauCeti.MeasureTheory.OptimalTransport.Duality.Borel

/-!
# Kantorovich duality for the relaxed transport value

The relaxed transport value `TauCeti.relaxedTransportCost c μ ν` minimizes the cost over partial
plans whose discarded mass is at most an arbitrarily small positive bound. It never exceeds the
ordinary value `TauCeti.transportCost c μ ν`, and for extended-valued Borel costs it can be
strictly smaller.

This file establishes both halves of the Beiglböck--Léonard--Schachermayer duality theorem for the
relaxed value, together with conditions under which relaxation is exact and an explicit `{0, 1, ∞}`
Borel counterexample where unrelaxed duality fails:

1. **Weak duality without regularity.** For finite measures of equal mass and integrable potentials
   `φ`, `ψ` with `φ x + ψ y ≤ c (x, y)`, the positive part of `∫ φ dμ + ∫ ψ dν` is at most the
   relaxed value. Every partial plan couples its own marginals, and uniform integrability of `|φ|`
   and `|ψ|` controls the dual value on the residual marginals `μ - π.fst` and `ν - π.snd`.
2. **Strong relaxed duality for arbitrary Borel costs on Polish spaces.** Truncating a Borel cost
   `c : X × Y → ℝ≥0∞` to `min c n` reduces `relaxedTransportCost c μ ν` to the supremum of bounded
   Borel transport costs (`TauCeti.relaxedTransportCost_eq_iSup_transportCost_min`), where strong
   bounded Borel duality (`TauCeti.isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le`)
   applies at each finite level and feasible potentials lift immediately to `c`.
3. **Exactness under lower semicontinuity or an integrable split upper envelope.** Lower
   semicontinuous costs satisfy unrelaxed strong duality directly, while Borel costs dominated by
   `a x + b y` with `∫⁻ a dμ ≠ ∞` and `∫⁻ b dν ≠ ∞` have zero relaxation gap
   (`TauCeti.relaxedTransportCost_eq_transportCost_of_le_split`) and therefore satisfy unrelaxed
   strong Kantorovich duality.
4. **Duality gap for `{0, 1, ∞}`-valued Borel costs.** On the unit interval `I = [0, 1]` with
   Lebesgue measure, `TauCeti.borelGapCost` (`0` for `x < y`, `1` on the diagonal, `∞` for `x > y`)
   has relaxed value and dual supremum `0` via small upward shifts on `[0, 1 - δ]`, whereas every
   full coupling concentrates on the diagonal and pays cost `1`.

## Main statements

* `TauCeti.DualFeasible.ofReal_kantorovichDualValue_le_relaxedTransportCost` — **weak duality for
  the relaxed value**, with finite real and `EReal` forms;
* `TauCeti.isLUB_ofReal_kantorovichDualValue_bounded_measurable_relaxedTransportCost` and
  `TauCeti.isLUB_ofReal_kantorovichDualValue_integrable_relaxedTransportCost` — **Beiglböck--
  Léonard--Schachermayer strong relaxed Kantorovich duality** for arbitrary Borel costs on Polish
  spaces over bounded Borel measurable or integrable potentials;
* `TauCeti.relaxedTransportCost_eq_transportCost_of_lowerSemicontinuous` — **relaxation is exact
  for lower semicontinuous costs** on Polish spaces;
* `TauCeti.isLUB_ofReal_kantorovichDualValue_integrable_of_measurable_of_le_split` — **unrelaxed
  Borel strong Kantorovich duality** under an integrable split upper envelope `c z ≤ a z.1 + b z.2`;
* `TauCeti.relaxedTransportCost_borelGapCost`, `TauCeti.transportCost_borelGapCost_self`, and
  `TauCeti.sSup_ofReal_kantorovichDualValue_integrable_lt_transportCost_borelGapCost` — explicit
  `{0, 1, ∞}` Borel cost on `[0, 1]` with relaxed/dual value `0` and unrelaxed transport cost `1`.

## References

* M. Beiglböck, C. Léonard and W. Schachermayer, *A general duality theorem for the
  Monge--Kantorovich transport problem*, Studia Math. 209 (2012), 151--167, Theorem 1.1 and
  Example 1.1.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal unitInterval

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

/-- **Beiglböck--Léonard--Schachermayer relaxed Kantorovich duality over bounded measurable
potentials.** For any Borel measurable cost `c : X × Y → ℝ≥0∞` on a product of Polish spaces and
any two probability measures, `relaxedTransportCost c μ ν` is the least upper bound of the positive
parts of the dual values of feasible bounded Borel potential pairs `(φ, ψ)`. -/
theorem isLUB_ofReal_kantorovichDualValue_bounded_measurable_relaxedTransportCost
    (hc : Measurable c) :
    IsLUB {r : ℝ≥0∞ | ∃ φ ψ, Measurable φ ∧ Measurable ψ ∧
      (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ (∃ M : ℝ, ∀ y, |ψ y| ≤ M) ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} (relaxedTransportCost c μ ν) := by
  constructor
  · rintro r ⟨φ, ψ, hφm, hψm, ⟨M₁, hM₁⟩, ⟨M₂, hM₂⟩, hfeas, rfl⟩
    exact hfeas.ofReal_kantorovichDualValue_le_relaxedTransportCost (by simp)
      (.of_bound hφm.aestronglyMeasurable M₁ (.of_forall hM₁))
      (.of_bound hψm.aestronglyMeasurable M₂ (.of_forall hM₂))
  · intro b hb
    rw [relaxedTransportCost_eq_iSup_transportCost_min (by simp) hc]
    refine iSup_le fun n : ℕ ↦ (isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le
      (μ := μ) (ν := ν) (B := (n : ℝ≥0)) (hc.min measurable_const) (fun _ ↦ by simp)).2 ?_
    rintro r ⟨φ, ψ, hφm, hψm, hφbdd, hψbdd, hfeas, rfl⟩
    exact hb ⟨φ, ψ, hφm, hψm, hφbdd, hψbdd,
      hfeas.mono_cost fun z ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 (min_le_left _ _), rfl⟩

/-- Supremum formula for Beiglböck--Léonard--Schachermayer relaxed Kantorovich duality over
bounded measurable potentials. -/
theorem relaxedTransportCost_eq_sSup_ofReal_kantorovichDualValue_bounded_measurable
    (hc : Measurable c) :
    relaxedTransportCost c μ ν = sSup {r : ℝ≥0∞ | ∃ φ ψ, Measurable φ ∧ Measurable ψ ∧
      (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ (∃ M : ℝ, ∀ y, |ψ y| ≤ M) ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} :=
  (isLUB_ofReal_kantorovichDualValue_bounded_measurable_relaxedTransportCost hc).sSup_eq.symm

/-- **Beiglböck--Léonard--Schachermayer relaxed Kantorovich duality over integrable potentials.**
For any Borel measurable cost `c : X × Y → ℝ≥0∞` on a product of Polish spaces and any two
probability measures, `relaxedTransportCost c μ ν` is the least upper bound of the positive parts
of the dual values of feasible integrable potential pairs `(φ, ψ)`. -/
theorem isLUB_ofReal_kantorovichDualValue_integrable_relaxedTransportCost (hc : Measurable c) :
    IsLUB {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} (relaxedTransportCost c μ ν) := by
  constructor
  · rintro r ⟨φ, ψ, hφ, hψ, hfeas, rfl⟩
    exact hfeas.ofReal_kantorovichDualValue_le_relaxedTransportCost (by simp) hφ hψ
  · intro b hb
    refine (isLUB_ofReal_kantorovichDualValue_bounded_measurable_relaxedTransportCost
      (μ := μ) (ν := ν) hc).2 ?_
    rintro r ⟨φ, ψ, hφm, hψm, ⟨M₁, hM₁⟩, ⟨M₂, hM₂⟩, hfeas, rfl⟩
    exact hb ⟨φ, ψ, .of_bound hφm.aestronglyMeasurable M₁ (.of_forall hM₁),
      .of_bound hψm.aestronglyMeasurable M₂ (.of_forall hM₂), hfeas, rfl⟩

/-- Supremum formula for Beiglböck--Léonard--Schachermayer relaxed Kantorovich duality over
integrable potentials. -/
theorem relaxedTransportCost_eq_sSup_ofReal_kantorovichDualValue_integrable (hc : Measurable c) :
    relaxedTransportCost c μ ν = sSup {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} :=
  (isLUB_ofReal_kantorovichDualValue_integrable_relaxedTransportCost hc).sSup_eq.symm

/-- **Unrelaxed Borel strong Kantorovich duality over bounded measurable potentials under an
integrable split upper envelope.** If `c` is Borel measurable on a product of Polish spaces and
`c z ≤ a z.1 + b z.2` for a.e.-measurable functions with finite marginal integrals, then
`transportCost c μ ν` equals the least upper bound of feasible bounded Borel dual values. -/
theorem isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le_split {a : X → ℝ≥0∞}
    {b : Y → ℝ≥0∞} (hc : Measurable c) (ha : AEMeasurable a μ) (hb : AEMeasurable b ν)
    (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞) (hsplit : ∀ z, c z ≤ a z.1 + b z.2) :
    IsLUB {r : ℝ≥0∞ | ∃ φ ψ, Measurable φ ∧ Measurable ψ ∧
      (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ (∃ M : ℝ, ∀ y, |ψ y| ≤ M) ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} (transportCost c μ ν) := by
  rw [← relaxedTransportCost_eq_transportCost_of_le_split (by simp) ha hb haint hbint hsplit]
  exact isLUB_ofReal_kantorovichDualValue_bounded_measurable_relaxedTransportCost hc

/-- Supremum formula for unrelaxed Borel strong Kantorovich duality over bounded measurable
potentials under an integrable split upper envelope. -/
theorem transportCost_eq_sSup_ofReal_kantorovichDualValue_bounded_measurable_of_le_split
    {a : X → ℝ≥0∞} {b : Y → ℝ≥0∞} (hc : Measurable c) (ha : AEMeasurable a μ)
    (hb : AEMeasurable b ν) (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞)
    (hsplit : ∀ z, c z ≤ a z.1 + b z.2) :
    transportCost c μ ν = sSup {r : ℝ≥0∞ | ∃ φ ψ, Measurable φ ∧ Measurable ψ ∧
      (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ (∃ M : ℝ, ∀ y, |ψ y| ≤ M) ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} :=
  (isLUB_ofReal_kantorovichDualValue_bounded_measurable_of_le_split
    hc ha hb haint hbint hsplit).sSup_eq.symm

/-- **Unrelaxed Borel strong Kantorovich duality over integrable potentials under an integrable
split upper envelope.** -/
theorem isLUB_ofReal_kantorovichDualValue_integrable_of_measurable_of_le_split {a : X → ℝ≥0∞}
    {b : Y → ℝ≥0∞} (hc : Measurable c) (ha : AEMeasurable a μ) (hb : AEMeasurable b ν)
    (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞) (hsplit : ∀ z, c z ≤ a z.1 + b z.2) :
    IsLUB {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} (transportCost c μ ν) := by
  rw [← relaxedTransportCost_eq_transportCost_of_le_split (by simp) ha hb haint hbint hsplit]
  exact isLUB_ofReal_kantorovichDualValue_integrable_relaxedTransportCost hc

/-- Supremum formula for unrelaxed Borel strong Kantorovich duality over integrable potentials
under an integrable split upper envelope. -/
theorem transportCost_eq_sSup_ofReal_kantorovichDualValue_integrable_of_measurable_of_le_split
    {a : X → ℝ≥0∞} {b : Y → ℝ≥0∞} (hc : Measurable c) (ha : AEMeasurable a μ)
    (hb : AEMeasurable b ν) (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞)
    (hsplit : ∀ z, c z ≤ a z.1 + b z.2) :
    transportCost c μ ν = sSup {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} :=
  (isLUB_ofReal_kantorovichDualValue_integrable_of_measurable_of_le_split
    hc ha hb haint hbint hsplit).sSup_eq.symm

end Polish

/-! ### Explicit `{0, 1, ∞}` Borel cost with an unrelaxed Kantorovich duality gap -/

section BorelGapCounterexample

/-- The `{0, 1, ∞}`-valued transport cost of Beiglböck--Léonard--Schachermayer (Example 1.1) on a
linearly ordered space: `0` strictly above the diagonal (`x < y`), `1` on the diagonal (`x = y`),
and `∞` strictly below the diagonal (`y < x`). -/
def borelGapCost {α : Type*} [LinearOrder α] (z : α × α) : ℝ≥0∞ :=
  if z.1 < z.2 then 0 else if z.1 = z.2 then 1 else ∞

/-- Defining piecewise formula for `borelGapCost`. -/
theorem borelGapCost_def {α : Type*} [LinearOrder α] (z : α × α) :
    borelGapCost z = if z.1 < z.2 then 0 else if z.1 = z.2 then 1 else ∞ := (rfl)

@[simp]
theorem borelGapCost_of_lt {α : Type*} [LinearOrder α] {x y : α} (h : x < y) :
    borelGapCost (x, y) = 0 := by simp [borelGapCost, h]

@[simp]
theorem borelGapCost_self {α : Type*} [LinearOrder α] (x : α) :
    borelGapCost (x, x) = 1 := by simp [borelGapCost]

@[simp]
theorem borelGapCost_of_gt {α : Type*} [LinearOrder α] {x y : α} (h : y < x) :
    borelGapCost (x, y) = ∞ := by simp [borelGapCost, asymm h, h.ne']

/-- On any second-countable order-topological Borel space, `borelGapCost` is Borel measurable. -/
@[fun_prop]
theorem measurable_borelGapCost {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] :
    Measurable (borelGapCost : α × α → ℝ≥0∞) :=
  Measurable.ite (isOpen_lt continuous_fst continuous_snd).measurableSet measurable_const <|
    Measurable.ite (isClosed_eq continuous_fst continuous_snd).measurableSet measurable_const
      measurable_const

/-- For **every** probability measure `μ` on the unit interval `I = [0, 1]`, the ordinary transport
cost of `borelGapCost` from `μ` to `μ` is `1`: any coupling giving positive mass to `{y < x}` pays
infinite cost, while any coupling supported on `{x ≤ y}` with equal marginals concentrates on the
diagonal `{x = y}` where `borelGapCost = 1`. -/
theorem transportCost_borelGapCost_self (μ : Measure I) [IsProbabilityMeasure μ] :
    transportCost borelGapCost μ μ = 1 := by
  refine le_antisymm ?_ (le_transportCost fun π hπ ↦ ?_)
  · refine (transportCost_le_lintegral μ.isCoupling_diagonalCoupling borelGapCost).trans_eq ?_
    rw [← μ.measurePreserving_diagonal.lintegral_comp measurable_borelGapCost]
    simp
  · have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    let A : Set (I × I) := {z | z.2 < z.1}
    have hA_meas : MeasurableSet A := (isOpen_lt continuous_snd continuous_fst).measurableSet
    rcases eq_or_ne (π A) 0 with hA0 | hA_pos
    · have hae_le : ∀ᵐ z ∂π, z.1 ≤ z.2 := by
        rw [Filter.Eventually, mem_ae_iff]
        convert hA0 using 2
        ext z; simp [A]
      let u : I → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (x : ℝ)
      have hu_meas : Measurable u := continuous_subtype_val.measurable.ennreal_ofReal
      let w : I × I → ℝ≥0∞ := fun z ↦ u z.2 - u z.1
      have hw_meas : Measurable w :=
        (hu_meas.comp measurable_snd).sub (hu_meas.comp measurable_fst)
      have hu_fin : ∫⁻ x, u x ∂μ ≠ ∞ := ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top <|
        (lintegral_mono fun x : I ↦ ENNReal.ofReal_le_one.2 x.2.2).trans_eq (by simp)
      have hadd_eq : (∫⁻ x, u x ∂μ) + ∫⁻ z, w z ∂π = (∫⁻ x, u x ∂μ) + 0 :=
        calc
          (∫⁻ x, u x ∂μ) + ∫⁻ z, w z ∂π
              = (∫⁻ z, u z.1 ∂π) + ∫⁻ z, w z ∂π := by
                rw [hπ.lintegral_comp_fst hu_meas.aemeasurable]
          _ = ∫⁻ z, (u z.1 + w z) ∂π := (lintegral_add_right _ hw_meas).symm
          _ = ∫⁻ z, u z.2 ∂π :=
            lintegral_congr_ae (hae_le.mono fun z hz ↦
              add_tsub_cancel_of_le (ENNReal.ofReal_le_ofReal hz))
          _ = (∫⁻ x, u x ∂μ) + 0 := by
            rw [hπ.lintegral_comp_snd hu_meas.aemeasurable, add_zero]
      have hw0 : w =ᵐ[π] 0 :=
        (lintegral_eq_zero_iff hw_meas).1 ((ENNReal.add_right_inj hu_fin).1 hadd_eq)
      have hae_cost : borelGapCost =ᵐ[π] 1 := by
        filter_upwards [hae_le, hw0] with z hz hwz
        have hge : (z.2 : ℝ) ≤ (z.1 : ℝ) :=
          (ENNReal.ofReal_le_ofReal_iff z.1.2.1).1 (tsub_eq_zero_iff_le.1 hwz)
        have hzeq : z.1 = z.2 := Subtype.ext (le_antisymm hz hge)
        rw [← Prod.eta z, hzeq]
        exact borelGapCost_self z.2
      rw [lintegral_congr_ae hae_cost]
      simp
    · calc
        (1 : ℝ≥0∞) ≤ ∞ := le_top
        _ = ∞ * π A := (ENNReal.top_mul hA_pos).symm
        _ = ∫⁻ _ in A, ∞ ∂π := (setLIntegral_const A ∞).symm
        _ = ∫⁻ z in A, borelGapCost z ∂π :=
          setLIntegral_congr_fun hA_meas fun z hz ↦ (borelGapCost_of_gt hz).symm
        _ ≤ ∫⁻ z, borelGapCost z ∂π := setLIntegral_le_lintegral _ _

/-- On the unit interval `I = [0, 1]` with Lebesgue measure, `borelGapCost` has relaxed transport
cost `0`: discarding `[1 - δ, 1]` and shifting `[0, 1 - δ]` upward by `δ` moves mass `1 - δ` inside
`{x < y}` at zero cost. -/
theorem relaxedTransportCost_borelGapCost :
    relaxedTransportCost borelGapCost (volume : Measure I) (volume : Measure I) = 0 := by
  refine le_antisymm (relaxedTransportCost_le fun ε hε ↦ ?_) zero_le
  rcases eq_or_ne ε ∞ with rfl | hε_top
  · simp
  have hε_real : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  let δ : ℝ := min (ε.toReal / 2) (1 / 2)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ_half : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_ε : δ ≤ ε.toReal := (min_le_left _ _).trans (by linarith)
  let a : I := ⟨1 - δ, ⟨by linarith, by linarith⟩⟩
  let s : Set I := Iic a
  let μ₀ : Measure I := (volume : Measure I).restrict s
  let g : I → I := fun x ↦ ⟨min ((x : ℝ) + δ) 1, ⟨le_min (add_nonneg x.2.1 hδ_pos.le) zero_le_one,
    min_le_right _ _⟩⟩
  have hg_meas : Measurable g :=
    (((continuous_subtype_val.add continuous_const).min continuous_const).subtype_mk _).measurable
  let π : Measure (I × I) := μ₀.map (fun x ↦ (x, g x))
  have hfst : π.fst ≤ volume := by
    rw [Measure.fst_map_prodMk measurable_id' hg_meas, Measure.map_id']
    exact Measure.restrict_le_self
  have hsnd : π.snd ≤ volume := by
    rw [Measure.snd_map_prodMk measurable_id' hg_meas, Measure.le_iff]
    intro t ht
    rw [Measure.map_apply hg_meas ht, Measure.restrict_apply (hg_meas ht),
      unitInterval.volume_apply, unitInterval.volume_apply]
    have hsub : Subtype.val '' (g ⁻¹' t ∩ s) ⊆ (fun r : ℝ ↦ r + δ) ⁻¹' (Subtype.val '' t) := by
      rintro _ ⟨x, ⟨hxt, hxs⟩, rfl⟩
      have hx_le : (x : ℝ) ≤ 1 - δ := hxs
      have hgx : (g x : ℝ) = (x : ℝ) + δ := min_eq_left (by linarith)
      exact ⟨g x, hxt, hgx⟩
    exact (measure_mono hsub).trans_eq (measure_preimage_add_right volume δ (Subtype.val '' t))
  have hmass : (volume : Measure I) univ ≤ π univ + ε := by
    rw [Measure.map_apply (measurable_id'.prodMk hg_meas) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ, unitInterval.volume_Iic, measure_univ]
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal ((1 - δ) + δ) := by ring_nf; simp
      _ = ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ :=
        ENNReal.ofReal_add (by linarith) hδ_pos.le
      _ ≤ ENNReal.ofReal (1 - δ) + ε :=
        add_le_add le_rfl ((ENNReal.ofReal_le_ofReal hδ_ε).trans ENNReal.ofReal_toReal_le)
  refine (partialTransportCost_le_lintegral hfst hsnd hmass).trans ?_
  rw [lintegral_map measurable_borelGapCost (measurable_id'.prodMk hg_meas)]
  have hzero : ∫⁻ x in s, borelGapCost (x, g x) ∂(volume : Measure I) = 0 := by
    have hcongr : ∫⁻ x in s, borelGapCost (x, g x) ∂(volume : Measure I) =
        ∫⁻ _ in s, 0 ∂(volume : Measure I) :=
      setLIntegral_congr_fun measurableSet_Iic fun x hx ↦ by
        have hx_le : (x : ℝ) ≤ 1 - δ := hx
        have hlt : x < g x := Subtype.mk_lt_mk.2 <| by
          simp only [min_eq_left (by linarith : (x : ℝ) + δ ≤ 1)]
          linarith
        exact borelGapCost_of_lt hlt
    simp [hcongr]
  exact hzero.le

/-- For `borelGapCost` on `(I, volume)`, the supremum of all integrable Kantorovich dual values is
`0`. -/
theorem sSup_ofReal_kantorovichDualValue_integrable_borelGapCost :
    sSup {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ (volume : Measure I) ∧
      Integrable ψ (volume : Measure I) ∧
      DualFeasible (fun z ↦ (borelGapCost z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue (volume : Measure I) (volume : Measure I) φ ψ) = r} =
      0 := by
  rw [← relaxedTransportCost_eq_sSup_ofReal_kantorovichDualValue_integrable measurable_borelGapCost,
    relaxedTransportCost_borelGapCost]

/-- `borelGapCost` on `(I, volume)` exhibits a strict gap `0 < 1` between the relaxed and ordinary
transport costs. -/
theorem relaxedTransportCost_lt_transportCost_borelGapCost :
    relaxedTransportCost borelGapCost (volume : Measure I) (volume : Measure I) <
      transportCost borelGapCost (volume : Measure I) (volume : Measure I) := by
  rw [relaxedTransportCost_borelGapCost, transportCost_borelGapCost_self]
  exact zero_lt_one

/-- `borelGapCost` on `(I, volume)` exhibits a strict Kantorovich duality gap `0 < 1` against
integrable potentials when the primal problem is not relaxed. -/
theorem sSup_ofReal_kantorovichDualValue_integrable_lt_transportCost_borelGapCost :
    sSup {r : ℝ≥0∞ | ∃ φ ψ, Integrable φ (volume : Measure I) ∧
      Integrable ψ (volume : Measure I) ∧
      DualFeasible (fun z ↦ (borelGapCost z : EReal)) φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue (volume : Measure I) (volume : Measure I) φ ψ) = r} <
      transportCost borelGapCost (volume : Measure I) (volume : Measure I) := by
  rw [sSup_ofReal_kantorovichDualValue_integrable_borelGapCost, transportCost_borelGapCost_self]
  exact zero_lt_one

end BorelGapCounterexample

end TauCeti
