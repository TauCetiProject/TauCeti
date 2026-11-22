/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
public import TauCeti.Probability.Process.Equidistribution
import Mathlib.Data.List.TFAE
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.Analysis.SpecificLimits.Cesaro.Basic
import TauCeti.MeasureTheory.Measure.AddCircle
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier
import TauCeti.Topology.Instances.AddCircle.LiftIco

/-!
# Weyl's equidistribution criteria on circles and tori

Fourier-analytic equidistribution criteria on `AddCircle T` and `UnitAddTorus d`:

* `TauCeti.asympEquidistributed_addCircle_iff`, `TauCeti.weyl_criterion_addCircle`,
  `TauCeti.asympEquidistributed_unitAddTorus_iff`, `TauCeti.weyl_criterion`: Weyl's criterion on
  `AddCircle T` and `UnitAddTorus d`.
* `TauCeti.asympEquidistributed_unitAddTorus_iff_forall_linear_comb`: reduction to 1D projections.
* `TauCeti.totallyAsympEquidistributed_unitAddTorus_iff_rational_twist`: total equidistribution via
  rationally twisted Weyl sums.
* `TauCeti.uniformDistribution_mod_one_tfae`: equivalence of Haar equidistribution on
  `UnitAddCircle`, fractional-part interval frequencies, and Weyl's exponential sums.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Proposition 1.1.2, Corollary 1.1.3, Exercises 1.1.1 and 1.1.4).
-/

public section

open Filter Finset MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace TauCeti


section WeylCriteria

/-- **Weyl's criterion on `AddCircle T` for an arbitrary limit measure**: a sequence is
asymptotically equidistributed for `μ` iff the Cesàro averages of every integer Fourier character
converge to its `μ`-integral. -/
theorem asympEquidistributed_addCircle_iff {T : ℝ} [Fact (0 < T)] {x : ℕ → AddCircle T}
    {μ : ProbabilityMeasure (AddCircle T)} :
    AsympEquidistributed x μ ↔ ∀ k : ℤ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (x i))
        atTop (𝓝 (∫ y, fourier k y ∂(μ : Measure (AddCircle T)))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_fourier_tendsto]
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_rclike]

/-- **Weyl's criterion on `AddCircle T`**: a sequence is asymptotically equidistributed for Haar
probability iff the Cesàro averages of every nonzero integer Fourier character tend to `0`. -/
theorem weyl_criterion_addCircle {T : ℝ} [Fact (0 < T)] {x : ℕ → AddCircle T} :
    AsympEquidistributed x AddCircle.haarAddCircle.toProbabilityMeasure ↔ ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (x i))
        atTop (𝓝 0) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_haarAddCircle_iff]
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_rclike]

variable {d : Type*} [Fintype d]

/-- **Weyl's criterion on `UnitAddTorus d` for an arbitrary limit measure**: a sequence is
asymptotically equidistributed for `μ` iff the Cesàro averages of every multivariate Fourier
character converge to its `μ`-integral. -/
theorem asympEquidistributed_unitAddTorus_iff {x : ℕ → UnitAddTorus d}
    {μ : ProbabilityMeasure (UnitAddTorus d)} :
    AsympEquidistributed x μ ↔ ∀ k : d → ℤ, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x i))
        atTop (𝓝 (∫ y, UnitAddTorus.mFourier k y ∂(μ : Measure (UnitAddTorus d)))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_mFourier_tendsto]
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_rclike]

/-- **Weyl's criterion on `UnitAddTorus d`**: a sequence is asymptotically equidistributed for
Haar probability (`volume`) iff the Cesàro averages of every nontrivial Fourier character tend
to `0`. -/
theorem weyl_criterion {x : ℕ → UnitAddTorus d} :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x i)) atTop (𝓝 0) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_volume_unitAddTorus_iff]
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_rclike]

/-- **Equidistribution on `UnitAddTorus d` via one-dimensional projections**: a sequence in
`UnitAddTorus d` is equidistributed for Haar probability iff every nonzero integer linear
combination of its coordinates is equidistributed on `UnitAddCircle`. -/
theorem asympEquidistributed_unitAddTorus_iff_forall_linear_comb {x : ℕ → UnitAddTorus d} :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → AsympEquidistributed (fun n ↦ ∑ i, k i • x n i)
        AddCircle.haarAddCircle.toProbabilityMeasure := by
  rw [weyl_criterion]
  refine ⟨fun hx k hk ↦ weyl_criterion_addCircle.mpr fun m hm ↦ ?_, fun h k hk ↦ ?_⟩
  · simpa only [UnitAddTorus.mFourier_zsmul] using hx (m • k) (smul_ne_zero hm hk)
  · simpa only [← UnitAddTorus.mFourier_eq_fourier_sum] using
      (weyl_criterion_addCircle.mp (h k hk)) 1 one_ne_zero

/-- **Total equidistribution by rational twists**: a sequence in `UnitAddTorus d` is totally
equidistributed for Haar probability iff all its rationally twisted Weyl sums vanish in the
limit. -/
theorem totallyAsympEquidistributed_unitAddTorus_iff_rational_twist {x : ℕ → UnitAddTorus d} :
    TotallyAsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∀ b : ℕ, 0 < b → ∀ a : ℤ,
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1),
          UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / b : ℝ) : UnitAddCircle))
          atTop (𝓝 0) := by
  rw [totallyAsympEquidistributed_def]; constructor
  · intro hx k hk b hb a; have : NeZero b := ⟨hb.ne'⟩
    have hmod (r : ℕ) : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x (b * i + r)) *
          fourier a ((((b * i + r : ℕ) : ℝ) / b : ℝ) : UnitAddCircle)) atTop (𝓝 (0 : ℂ)) := by
      have hlim := ((weyl_criterion.mp (hx b r hb)) k hk).mul_const
        (ZMod.stdAddChar ((r : ZMod b) * (a : ZMod b)))
      rw [zero_mul] at hlim; refine hlim.congr fun n ↦ ?_
      simp_rw [ZMod.fourier_natCast_div_eq_stdAddChar, Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_self, zero_mul, zero_add, ← sum_mul, Complex.real_smul, Nat.cast_one]
      push_cast; ring
    simpa [Complex.real_smul] using tendsto_cesaro_of_forall_mod (f := fun i ↦
      UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / b : ℝ) : UnitAddCircle))
      hb (L := fun _ ↦ 0) fun r _ ↦ hmod r
  · intro h q r hq; have : NeZero q := ⟨hq.ne'⟩
    rw [← (funext fun n ↦ by rw [Nat.mul_add, Nat.add_assoc, Nat.div_add_mod] :
        (fun n ↦ x (q * (n + r / q) + r % q)) = fun n ↦ x (q * n + r)),
      asympEquidistributed_comp_add_iff (x := fun n ↦ x (q * n + r % q)) (r / q), weyl_criterion]
    intro k hk; simpa [Complex.real_smul] using tendsto_cesaro_mul_add_of_ite_mod hq
      (Nat.mod_lt r hq) (ZMod.tendsto_cesaro_ite_mod_of_fourier (Nat.mod_lt r hq) (h k hk q hq))

end WeylCriteria

section UniformDistributionModOne

/-- Haar equidistribution implies convergence of fractional-part visit frequencies in `[a, b)`. -/
private theorem tendsto_fract_Ico_of_asympEquidistributed {u : ℕ → ℝ}
    (hu : AsympEquidistributed (fun n ↦ (u n : UnitAddCircle))
      AddCircle.haarAddCircle.toProbabilityMeasure)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ ↦ (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (b - a)) := by
  classical
  set E : Set UnitAddCircle := (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) ⁻¹' Ico a b
  have hm : Measurable (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) :=
    measurable_subtypeVal.comp (AddCircle.measurableEquivIco 1 0).measurable
  have hmeas : (AddCircle.haarAddCircle : Measure UnitAddCircle).real E = b - a := by
    rw [Measure.real, (by simp [AddCircle.volume_eq_smul_haarAddCircle] :
        (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume),
      ← Measure.map_apply hm measurableSet_Ico, AddCircle.map_coe_equivIco_volume 0,
      Measure.restrict_apply measurableSet_Ico, zero_add, Set.Ico_inter_Ico, max_eq_left ha,
      min_eq_left hb, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hfreq := hu.tendsto_frequency (E := E) (hm measurableSet_Ico) (measure_mono_null
    (AddCircle.frontier_preimage_equivIco_Ico_subset ha (b := b) (by linarith))
    (by rw [Measure.coe_toProbabilityMeasure, Set.insert_eq]
        exact measure_union_null (measure_singleton _) (measure_singleton _)))
  rw [Measure.coe_toProbabilityMeasure, hmeas] at hfreq
  exact hfreq.congr fun n ↦ congrArg (fun s : Finset ℕ ↦ (s.card : ℝ) / ((n + 1 : ℕ) : ℝ))
    (filter_congr fun i _ ↦ by simp [E, AddCircle.coe_equivIco_mk_apply])

/-- Convergence of fractional-part frequencies on `[a, b) ⊆ [0, 1]` implies Haar equidistribution on
`UnitAddCircle`. -/
private theorem asympEquidistributed_of_forall_fract_Ico {u : ℕ → ℝ}
    (hfreq : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → Tendsto (fun n : ℕ ↦
      (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (b - a))) :
    AsympEquidistributed (fun n ↦ (u n : UnitAddCircle))
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  classical
  have hν_prob : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := ⟨by simp⟩
  let ν : ProbabilityMeasure ℝ := (volume.restrict (Ico (0 : ℝ) 1)).toProbabilityMeasure
  let μ : ℕ → ProbabilityMeasure ℝ :=
    TauCeti.Probability.empiricalMeasure (fun i ↦ Int.fract (u i))
  have hpi : IsPiSystem {s : Set ℝ | ∃ a b : ℝ, s = Ico a b} := by
    rintro _ ⟨a₁, b₁, rfl⟩ _ ⟨a₂, b₂, rfl⟩ -; exact ⟨max a₁ a₂, min b₁ b₂, Ico_inter_Ico⟩
  have htend : Tendsto μ atTop (𝓝 ν) := by
    refine hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
      (by rintro _ ⟨a, b, rfl⟩; exact measurableSet_Ico) (fun U hU x hx ↦ by
        obtain ⟨a, b, ⟨hax, hxb⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
        exact ⟨Ico ((a + x) / 2) b, ⟨(a + x) / 2, b, rfl⟩, Ico_mem_nhds (by linarith) hxb,
          fun y hy ↦ hsub ⟨by linarith [hy.1], hy.2⟩⟩) ?_
    rintro _ ⟨c, d, rfl⟩; rw [← NNReal.tendsto_coe]
    have hμ (n : ℕ) : (μ n (Ico c d) : ℝ) =
        (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico (max c 0) (min d 1))).card : ℝ) /
          ((n + 1 : ℕ) : ℝ) := by
      rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def,
        TauCeti.Probability.empiricalMeasure_real_eq_frequency measurableSet_Ico n]
      refine congrArg (fun s : Finset ℕ ↦ (s.card : ℝ) / ((n + 1 : ℕ) : ℝ))
        (filter_congr fun i _ ↦ ?_)
      simp only [Set.mem_Ico]
      have h01 := Int.fract_nonneg (u i); have h1 := Int.fract_lt_one (u i)
      exact ⟨fun h ↦ ⟨max_le h.1 h01, lt_min h.2 h1⟩,
        fun h ↦ ⟨(le_max_left c 0).trans h.1, h.2.trans_le (min_le_left d 1)⟩⟩
    have hν : (ν (Ico c d) : ℝ) = (volume (Ico (max c 0) (min d 1))).toReal := by
      rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def]
      dsimp only [ν]; rw [Measure.coe_toProbabilityMeasure,
        Measure.restrict_apply measurableSet_Ico, Set.Ico_inter_Ico]
    rcases le_or_gt (max c 0) (min d 1) with hle | hlt
    · rw [Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hle)] at hν
      simpa only [hμ, hν] using hfreq _ _ (le_max_right _ _) hle (min_le_right _ _)
    · have hemp : Ico (max c 0) (min d 1) = ∅ := Ico_eq_empty_of_le hlt.le
      simp only [hemp, measure_empty, ENNReal.toReal_zero, mem_empty_iff_false, filter_false,
        Finset.card_empty, Nat.cast_zero, zero_div] at hμ hν
      simpa only [hμ, hν] using tendsto_const_nhds
  have hν_map : ν.map ((↑) : ℝ → UnitAddCircle) = AddCircle.haarAddCircle.toProbabilityMeasure :=
    ProbabilityMeasure.toMeasure_injective (by
      rw [ProbabilityMeasure.toMeasure_map, Measure.coe_toProbabilityMeasure,
        Measure.coe_toProbabilityMeasure, Measure.restrict_congr_set Ico_ae_eq_Ioc]
      simpa [AddCircle.volume_eq_smul_haarAddCircle] using
        (AddCircle.measurePreserving_mk 1 0).map_eq)
  simpa only [AddCircle.coe_fract] using (by
    rw [← hν_map]; exact (asympEquidistributed_def.mpr htend).map
      continuous_quotient_mk' AddCircle.measurable_mk' :
    AsympEquidistributed (fun i ↦ ((Int.fract (u i) : ℝ) : UnitAddCircle))
      AddCircle.haarAddCircle.toProbabilityMeasure)

/-- **Classical equivalence for uniform distribution modulo `1`**: for `u : ℕ → ℝ`, Haar
equidistribution of `n ↦ (u n : UnitAddCircle)`, convergence of fractional-part visit frequencies
in every interval `[a, b) ⊆ [0, 1]`, and vanishing of all nonzero Weyl exponential sums are
equivalent. -/
theorem uniformDistribution_mod_one_tfae (u : ℕ → ℝ) :
    List.TFAE [
      AsympEquidistributed (fun n ↦ (u n : UnitAddCircle))
        AddCircle.haarAddCircle.toProbabilityMeasure,
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        Tendsto (fun n : ℕ ↦
          (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
            ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (b - a)),
      ∀ k : ℤ, k ≠ 0 → Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), fourier k (u i : UnitAddCircle)) atTop (𝓝 0)] := by
  tfae_have 1 → 2 := fun hu _ _ ha hab hb ↦ tendsto_fract_Ico_of_asympEquidistributed hu ha hab hb
  tfae_have 2 → 1 := asympEquidistributed_of_forall_fract_Ico
  tfae_have 1 → 3 := fun hu _ hk ↦ weyl_criterion_addCircle.mp hu _ hk
  tfae_have 3 → 1 := weyl_criterion_addCircle.mpr
  tfae_finish

end UniformDistributionModOne

end TauCeti
