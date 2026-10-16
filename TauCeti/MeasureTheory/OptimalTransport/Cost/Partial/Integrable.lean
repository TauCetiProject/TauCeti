/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.DominatedMeasure
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Partial.Basic

/-!
# Relaxation under integrable marginal envelopes

For finite equal-mass marginals, the relaxed transport value agrees with the ordinary value
whenever the nonnegative cost is bounded above by a sum of integrable marginal functions.
The cost need not be bounded or lower semicontinuous, and no topology is required.

Completing a partial plan adds a measure whose marginals are dominated by the prescribed
marginals. Its cost is uniformly small when its mass is small: approximate each envelope
by a bounded simple function and bound the two remainders by their marginal integrals.
The resulting quantitative completion estimate proves equality of the two primal values.
This does not assert equality for arbitrary extended-valued Borel costs.

The same envelope makes the cost uniformly integrable over all plans whose marginals are dominated
by `μ` and `ν`, couplings included (`TauCeti.exists_forall_setLIntegral_le_of_le_split`): by
Markov's inequality the region where the cost exceeds a level `R` has small mass for every such
plan once `R` is large.

## References

* M. Beiglböck, C. Léonard and W. Schachermayer, *A general duality theorem for the
  Monge--Kantorovich transport problem*, Studia Math. 209 (2012), 151--167.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {c : X × Y → ℝ≥0∞}
  {a : X → ℝ≥0∞} {b : Y → ℝ≥0∞}

/-- A split envelope with finite marginal integrals uniformly controls the cost of every
plan with dominated marginals by its mass plus an arbitrarily small error. -/
theorem exists_lintegral_le_mul_mass_add_of_le_split
    (ha : AEMeasurable a μ) (hb : AEMeasurable b ν)
    (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞)
    (hc : ∀ z, c z ≤ a z.1 + b z.2) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ C : ℝ≥0, ∀ ρ : Measure (X × Y), ρ.fst ≤ μ → ρ.snd ≤ ν →
      ∫⁻ z, c z ∂ρ ≤ C * ρ univ + η := by
  obtain ⟨A, hA⟩ := exists_lintegral_le_mul_measure_add_of_ne_top haint
    (ENNReal.half_pos hη.ne')
  obtain ⟨B, hB⟩ := exists_lintegral_le_mul_measure_add_of_ne_top hbint
    (ENNReal.half_pos hη.ne')
  refine ⟨A + B, fun ρ hfst hsnd ↦ ?_⟩
  have haρ := ha.mono_measure hfst
  have hbρ := hb.mono_measure hsnd
  have hρ : IsCoupling ρ ρ.fst ρ.snd := ⟨rfl, rfl⟩
  have hsplit : ∫⁻ z, a z.1 + b z.2 ∂ρ =
      (∫⁻ x, a x ∂ρ.fst) + ∫⁻ y, b y ∂ρ.snd := by
    have hbcomp : AEMeasurable (fun z : X × Y ↦ b z.2) ρ := by
      exact hbρ.comp_quasiMeasurePreserving hρ.measurePreserving_snd.quasiMeasurePreserving
    rw [lintegral_add_right' _ hbcomp]
    rw [hρ.lintegral_comp_fst haρ, hρ.lintegral_comp_snd hbρ]
  calc
    ∫⁻ z, c z ∂ρ ≤ ∫⁻ z, a z.1 + b z.2 ∂ρ := lintegral_mono hc
    _ = (∫⁻ x, a x ∂ρ.fst) + ∫⁻ y, b y ∂ρ.snd := hsplit
    _ ≤ (A * ρ.fst univ + η / 2) + (B * ρ.snd univ + η / 2) :=
      add_le_add (hA _ hfst) (hB _ hsnd)
    _ = (A * ρ univ + B * ρ univ) + (η / 2 + η / 2) := by
      rw [Measure.fst_univ, Measure.snd_univ]
      ac_rfl
    _ = (A + B : ℝ≥0) * ρ univ + η := by
      rw [ENNReal.coe_add, add_mul, ENNReal.add_halves]

/-- **Envelope-dominated costs are uniformly integrable over plans with dominated marginals.** If
the cost is bounded by a split envelope with finite marginal integrals, then for every `η > 0`
there is a level `R` such that every plan whose marginals are dominated by `μ` and `ν`, in
particular every coupling of `μ` and `ν`, spends at most `η` of its cost where the cost is at
least `R`. -/
theorem exists_forall_setLIntegral_le_of_le_split
    (ha : AEMeasurable a μ) (hb : AEMeasurable b ν)
    (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞)
    (hc : ∀ z, c z ≤ a z.1 + b z.2) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ≥0, ∀ π : Measure (X × Y), π.fst ≤ μ → π.snd ≤ ν →
      ∫⁻ z in {z | (R : ℝ≥0∞) ≤ c z}, c z ∂π ≤ η := by
  obtain ⟨C, hC⟩ := exists_lintegral_le_mul_mass_add_of_le_split
    ha hb haint hbint hc (ENNReal.half_pos hη.ne')
  set M := (∫⁻ x, a x ∂μ) + ∫⁻ y, b y ∂ν
  have hMtop : M ≠ ∞ := ENNReal.add_ne_top.2 ⟨haint, hbint⟩
  -- By Markov's inequality the region `{z | n ≤ c z}` has mass at most `M / n` for every
  -- plan with dominated marginals, so a large `n` makes its cost small.
  have hlim : Tendsto (fun n : ℕ ↦ (C : ℝ≥0∞) * (M * (n : ℝ≥0∞)⁻¹)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hMtop))
      (Or.inr ENNReal.coe_ne_top)
  obtain ⟨n, hnC, hn⟩ := ((hlim.eventually (gt_mem_nhds (ENNReal.half_pos hη.ne'))).and
    (eventually_gt_atTop 0)).exists
  refine ⟨n, fun π hfst hsnd ↦ ?_⟩
  simp only [ENNReal.coe_natCast]
  have haπ := ha.mono_measure hfst
  have hbπ' := hb.mono_measure hsnd
  have hπ : IsCoupling π π.fst π.snd := ⟨rfl, rfl⟩
  have hbπ : AEMeasurable (fun z : X × Y ↦ b z.2) π :=
    hbπ'.comp_quasiMeasurePreserving hπ.measurePreserving_snd.quasiMeasurePreserving
  have hmass : π {z | (n : ℝ≥0∞) ≤ c z} ≤ M * (n : ℝ≥0∞)⁻¹ := by
    calc π {z | (n : ℝ≥0∞) ≤ c z} ≤ π {z | (n : ℝ≥0∞) ≤ a z.1 + b z.2} :=
          measure_mono fun z hz ↦ le_trans hz (hc z)
      _ ≤ (∫⁻ z, a z.1 + b z.2 ∂π) / n :=
          meas_ge_le_lintegral_div
            ((haπ.comp_quasiMeasurePreserving
              hπ.measurePreserving_fst.quasiMeasurePreserving).add hbπ)
            (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)
      _ ≤ M * (n : ℝ≥0∞)⁻¹ := by
          rw [div_eq_mul_inv, lintegral_add_right' _ hbπ, hπ.lintegral_comp_fst haπ,
            hπ.lintegral_comp_snd hbπ']
          exact mul_le_mul_left
            (add_le_add (lintegral_mono' hfst le_rfl) (lintegral_mono' hsnd le_rfl)) _
  calc ∫⁻ z in {z | (n : ℝ≥0∞) ≤ c z}, c z ∂π
      ≤ C * π.restrict {z | (n : ℝ≥0∞) ≤ c z} univ + η / 2 :=
        hC _ ((Measure.fst_mono Measure.restrict_le_self).trans hfst)
          ((Measure.snd_mono Measure.restrict_le_self).trans hsnd)
    _ ≤ η / 2 + η / 2 := by
        rw [Measure.restrict_apply_univ]
        gcongr
        exact le_trans (by gcongr) hnC.le
    _ = η := ENNReal.add_halves η

/-- For an integrable split upper envelope, completion of a partial plan costs at most
`C * ε + η`, with `C` depending only on the envelope and the positive error `η`.
This estimate is uniform over all permitted deficits `ε`. -/
theorem exists_transportCost_le_partialTransportCost_add_of_le_split [IsFiniteMeasure μ]
    (hmass : μ univ = ν univ) (ha : AEMeasurable a μ) (hb : AEMeasurable b ν)
    (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞)
    (hc : ∀ z, c z ≤ a z.1 + b z.2) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ C : ℝ≥0, ∀ ε : ℝ≥0∞,
      transportCost c μ ν ≤ partialTransportCost c μ ν ε + C * ε + η := by
  obtain ⟨C, hC⟩ := exists_lintegral_le_mul_mass_add_of_le_split
    ha hb haint hbint hc hη
  exact ⟨C, fun _ ↦ transportCost_le_partialTransportCost_add_of_lintegral_le hmass hC⟩

/-- **Relaxation preserves transport under an integrable split upper envelope.**
For finite measures of equal mass, discarding arbitrarily small amounts of mass does not
change the transport value if the cost is bounded by `a x + b y`, with both marginal
integrals finite. No measurability hypothesis is imposed on the cost itself. -/
theorem relaxedTransportCost_eq_transportCost_of_le_split [IsFiniteMeasure μ]
    (hmass : μ univ = ν univ) (ha : AEMeasurable a μ) (hb : AEMeasurable b ν)
    (haint : ∫⁻ x, a x ∂μ ≠ ∞) (hbint : ∫⁻ y, b y ∂ν ≠ ∞)
    (hc : ∀ z, c z ≤ a z.1 + b z.2) :
    relaxedTransportCost c μ ν = transportCost c μ ν :=
  le_antisymm relaxedTransportCost_le_transportCost <|
    le_relaxedTransportCost_of_forall_exists_le_add fun _ hη ↦
      exists_transportCost_le_partialTransportCost_add_of_le_split hmass ha hb haint hbint hc hη

/-- **Relaxation preserves bounded-cost transport.** This is the constant-envelope case of
`relaxedTransportCost_eq_transportCost_of_le_split`: for finite equal-mass measures and a
uniformly bounded nonnegative cost, the relaxed and ordinary primal values coincide. -/
theorem relaxedTransportCost_eq_transportCost_of_bounded [IsFiniteMeasure μ]
    (hmass : μ univ = ν univ) (C : NNReal) (hc : ∀ z, c z ≤ C) :
    relaxedTransportCost c μ ν = transportCost c μ ν := by
  exact relaxedTransportCost_eq_transportCost_of_le_split
    (a := fun _ ↦ C) (b := fun _ ↦ 0) hmass aemeasurable_const aemeasurable_const
    (by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top μ univ))
    (by simp) (fun z ↦ by simpa using hc z)

end TauCeti
