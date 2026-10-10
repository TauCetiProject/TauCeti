/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T14.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track — additions to `Mathlib/Probability/`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Averaging a triangular array of identically distributed errors

A statistical procedure indexed by a growing reference collection is fed, at stage `r`, the
`N r` errors `E r 0, …, E r (N r - 1)`.  Convergence *of each error* is not enough to control
their average: for a triangular array, `E r i → 0` for every fixed `i` is compatible with the
average staying bounded away from zero (put the mass at indices that escape to infinity).

What does suffice, and is what a sampling model actually supplies, is that at each stage the
errors are *identically distributed* — the same statistic applied to interchangeable members of
the collection.  Then the average has the same mean as a single error, so it converges in `L¹`
whenever a single error does, hence in measure, hence almost everywhere along a subsequence.

That last passage to a subsequence is not a defect of the argument.  It is unavoidable: `L¹`
convergence does not give almost-everywhere convergence.  A statement of this shape should
therefore be expected to carry a subsequence, and one that does is not thereby weaker than it
could have been.

## Main results

* `tendstoInMeasure_zero_of_nonneg_of_tendsto_integral` — a nonnegative sequence whose integrals
  vanish converges to zero in measure.
* `exists_subseq_ae_tendsto_zero_of_tendsto_integral` — and therefore, along a subsequence,
  almost everywhere.
* `tendsto_integral_of_tendsto_measure_ge_of_bounded` — for a uniformly bounded family,
  convergence in probability is convergence in `L¹`.
* `integral_average_of_integral_eq` — the average of identically distributed errors has the
  common mean.
* `exists_subseq_ae_tendsto_average` — the three combined: the average of an identically
  distributed triangular array vanishes almost everywhere along a subsequence.
* `exists_subseq_ae_tendsto_average_of_tendsto_measure_ge` — the same from convergence in
  probability of a single error, which is what a sampling model states.
-/

open Filter MeasureTheory Topology

public section

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/--
**Vanishing means force convergence in measure**, for nonnegative functions.

This is Markov's inequality with the tail probability read as the conclusion rather than the
hypothesis: `μ {A r ≥ ε} ≤ ε⁻¹ ∫ A r`, and the right side vanishes by assumption.
-/
theorem tendstoInMeasure_zero_of_nonneg_of_tendsto_integral
    (A : Nat → Ω → Real) (hA0 : ∀ r, 0 ≤ᵐ[μ] A r)
    (hAm : ∀ r, AEMeasurable (A r) μ) (hAi : ∀ r, Integrable (A r) μ)
    (hlim : Tendsto (fun r => ∫ ω, A r ω ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ A atTop 0 := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
  -- the Markov bound, stage by stage
  have hbound : ∀ r : Nat, μ {ω | ε ≤ edist (A r ω) ((0 : Ω → Real) ω)}
      ≤ (ENNReal.ofReal (∫ ω, A r ω ∂μ)) * ε⁻¹ := by
    intro r
    have hsub : μ {ω | ε ≤ edist (A r ω) ((0 : Ω → Real) ω)}
        ≤ μ {ω | ε ≤ ENNReal.ofReal (A r ω)} := by
      refine measure_mono_ae ?_
      filter_upwards [hA0 r] with ω hω hmem
      have hmem' : ε ≤ edist (A r ω) ((0 : Ω → Real) ω) := hmem
      have hed : edist (A r ω) ((0 : Ω → Real) ω) = ENNReal.ofReal (A r ω) := by
        rw [edist_dist]
        simp only [Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_nonneg hω]
      rw [hed] at hmem'
      exact hmem'
    have hmark := mul_meas_ge_le_lintegral₀
      (ENNReal.measurable_ofReal.comp_aemeasurable (hAm r)) ε
    have hlint : ∫⁻ ω, ENNReal.ofReal (A r ω) ∂μ = ENNReal.ofReal (∫ ω, A r ω ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hAi r) (hA0 r)).symm
    simp only [Function.comp_def] at hmark
    rw [hlint] at hmark
    calc μ {ω | ε ≤ edist (A r ω) ((0 : Ω → Real) ω)}
        ≤ μ {ω | ε ≤ ENNReal.ofReal (A r ω)} := hsub
      _ = (ε * μ {ω | ε ≤ ENNReal.ofReal (A r ω)}) * ε⁻¹ := by
          rw [mul_comm ε, mul_assoc, ENNReal.mul_inv_cancel (ne_of_gt hε) hεtop, mul_one]
      _ ≤ (ENNReal.ofReal (∫ ω, A r ω ∂μ)) * ε⁻¹ := by
          gcongr
  -- and the right-hand side vanishes
  have hrhs : Tendsto (fun r => (ENNReal.ofReal (∫ ω, A r ω ∂μ)) * ε⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => ENNReal.ofReal (∫ ω, A r ω ∂μ)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
      simpa [Function.comp_def] using this
    have h2 := ENNReal.Tendsto.mul_const h1
      (Or.inr (ENNReal.inv_ne_top.mpr (ne_of_gt hε)))
    simpa using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
    (fun _ => bot_le) hbound

/--
**Vanishing means force almost-everywhere convergence along a subsequence.**
-/
theorem exists_subseq_ae_tendsto_zero_of_tendsto_integral
    (A : Nat → Ω → Real) (hA0 : ∀ r, 0 ≤ᵐ[μ] A r)
    (hAm : ∀ r, AEMeasurable (A r) μ) (hAi : ∀ r, Integrable (A r) μ)
    (hlim : Tendsto (fun r => ∫ ω, A r ω ∂μ) atTop (𝓝 0)) :
    ∃ ns : Nat → Nat, StrictMono ns ∧
      ∀ᵐ ω ∂μ, Tendsto (fun u => A (ns u) ω) atTop (𝓝 0) := by
  obtain ⟨ns, hmono, hae⟩ :=
    (tendstoInMeasure_zero_of_nonneg_of_tendsto_integral A hA0 hAm hAi hlim).exists_seq_tendsto_ae
  exact ⟨ns, hmono, by simpa using hae⟩


/--
**Bounded convergence in probability is convergence in `L¹`.**

The elementary half of the equivalence: a nonnegative variable below `C` satisfies
`X ≤ ε + C · 1{X ≥ ε}` pointwise, so its mean is below `ε + C · P(X ≥ ε)`, and the tail vanishes
by assumption.  No uniform integrability is needed because the uniform bound supplies it.
-/
theorem tendsto_integral_of_tendsto_measure_ge_of_bounded [IsProbabilityMeasure μ]
    (X : Nat → Ω → Real) (hXm : ∀ r, Measurable (X r))
    (hX0 : ∀ r ω, 0 ≤ X r ω) (hXi : ∀ r, Integrable (X r) μ)
    {C : Real} (hC : ∀ r ω, X r ω ≤ C)
    (htail : ∀ ε : Real, 0 < ε →
      Tendsto (fun r => (μ {ω | ε ≤ X r ω}).toReal) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ ω, X r ω ∂μ) atTop (𝓝 0) := by
  classical
  have hne : Nonempty Ω := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h1 : μ Set.univ = 0 := by
      have : (Set.univ : Set Ω) = ∅ := Set.univ_eq_empty_iff.mpr hcon
      rw [this, measure_empty]
    rw [measure_univ] at h1
    exact one_ne_zero h1
  have hC0 : 0 ≤ C := le_trans (hX0 0 hne.some) (hC 0 _)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η : Real := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  -- `X ≤ η + C · 1{X ≥ η}` pointwise, so the mean is below `η + C · P(X ≥ η)`
  have hbound : ∀ r : Nat, ∫ ω, X r ω ∂μ ≤ η + C * (μ {ω | η ≤ X r ω}).toReal := by
    intro r
    have hmeas : MeasurableSet {ω | η ≤ X r ω} := measurableSet_le measurable_const (hXm r)
    set g : Ω → Real := fun ω =>
      η + C * Set.indicator {ω | η ≤ X r ω} (fun _ => (1 : Real)) ω with hg
    have hind : Integrable (Set.indicator {ω | η ≤ X r ω} (fun _ => (1 : Real))) μ :=
      Integrable.indicator (integrable_const (1 : Real)) hmeas
    have hgi : Integrable g μ := (integrable_const η).add (hind.const_mul C)
    have hle : ∀ ω, X r ω ≤ g ω := by
      intro ω
      by_cases hmem : η ≤ X r ω
      · have h1 : Set.indicator {ω | η ≤ X r ω} (fun _ => (1 : Real)) ω = 1 :=
          Set.indicator_of_mem (show ω ∈ {ω | η ≤ X r ω} from hmem) _
        rw [hg]
        simp only [h1, mul_one]
        have := hC r ω
        linarith
      · have h1 : Set.indicator {ω | η ≤ X r ω} (fun _ => (1 : Real)) ω = 0 :=
          Set.indicator_of_notMem (show ω ∉ {ω | η ≤ X r ω} from hmem) _
        rw [hg]
        simp only [h1, mul_zero, add_zero]
        push Not at hmem
        exact hmem.le
    calc ∫ ω, X r ω ∂μ ≤ ∫ ω, g ω ∂μ :=
          integral_mono_ae (hXi r) hgi (Filter.Eventually.of_forall hle)
      _ = η + C * (μ {ω | η ≤ X r ω}).toReal := by
          rw [hg, integral_add (integrable_const η) (hind.const_mul C), integral_const,
            integral_const_mul, integral_indicator_const (1 : Real) hmeas]
          simp [measureReal_def]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (htail η hη0) (δ / (2 * (C + 1))) (by positivity)
  refine ⟨N, fun r hr => ?_⟩
  have h1 := hN r hr
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h1
  have h2 : C * (μ {ω | η ≤ X r ω}).toReal < δ / 2 := by
    have hmul : C * (μ {ω | η ≤ X r ω}).toReal ≤ C * (δ / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left h1.le hC0
    have hlt : C * (δ / (2 * (C + 1))) < δ / 2 := by
      rw [mul_div_assoc'] at hmul ⊢
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hint0 : 0 ≤ ∫ ω, X r ω ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (hX0 r))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hint0]
  calc ∫ ω, X r ω ∂μ ≤ η + C * (μ {ω | η ≤ X r ω}).toReal := hbound r
    _ < δ / 2 + δ / 2 := by rw [hη]; linarith
    _ = δ := by ring

/--
**Identically distributed errors have an average with the common mean.**

Nothing about independence is used, and nothing about the errors beyond their integrals: only
that at a given stage they all have the same one.
-/
theorem integral_average_of_integral_eq [IsFiniteMeasure μ] {n : Nat} (E : Fin n → Ω → Real)
    (hE : ∀ i, Integrable (E i) μ) {e : Real} (hmean : ∀ i, ∫ ω, E i ω ∂μ = e) :
    ∫ ω, ((n : Real))⁻¹ * ∑ i, E i ω ∂μ = ((n : Real))⁻¹ * ((n : Real) * e) := by
  classical
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hE i)]
  simp [hmean, Finset.sum_const, Finset.card_univ]

/--
**The average of an identically distributed triangular array vanishes along a subsequence.**

At stage `r` the collection has `N r` members and each of their errors has mean `e r`; the mean
of the average is then `e r` as well, whatever `N r` is, so the average is controlled by a single
error even as the collection grows.  The subsequence is the one `L¹` convergence always costs.
-/
theorem exists_subseq_ae_tendsto_average [IsProbabilityMeasure μ]
    (N : Nat → Nat) (hN : ∀ r, 0 < N r) (E : ∀ r, Fin (N r) → Ω → Real)
    (hE0 : ∀ r i, 0 ≤ᵐ[μ] E r i) (hEi : ∀ r i, Integrable (E r i) μ)
    (e : Nat → Real) (hmean : ∀ r i, ∫ ω, E r i ω ∂μ = e r)
    (he : Tendsto e atTop (𝓝 0)) :
    ∃ ns : Nat → Nat, StrictMono ns ∧
      ∀ᵐ ω ∂μ, Tendsto (fun u => ((N (ns u) : Real))⁻¹ * ∑ i, E (ns u) i ω) atTop (𝓝 0) := by
  classical
  set A : Nat → Ω → Real := fun r ω => ((N r : Real))⁻¹ * ∑ i, E r i ω with hA
  have hNpos : ∀ r, (0 : Real) < (N r : Real) := fun r => by exact_mod_cast hN r
  have hA0 : ∀ r, 0 ≤ᵐ[μ] A r := by
    intro r
    have : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ E r i ω := ae_all_iff.mpr (hE0 r)
    filter_upwards [this] with ω hω
    have : (0 : Real) ≤ ∑ i, E r i ω := Finset.sum_nonneg fun i _ => hω i
    exact mul_nonneg (le_of_lt (inv_pos.mpr (hNpos r))) this
  have hAi : ∀ r, Integrable (A r) μ := by
    intro r
    exact (integrable_finsetSum _ (fun i _ => hEi r i)).const_mul _
  have hAm : ∀ r, AEMeasurable (A r) μ := fun r => (hAi r).aemeasurable
  have hAint : ∀ r, ∫ ω, A r ω ∂μ = e r := by
    intro r
    rw [hA]
    rw [integral_average_of_integral_eq (E r) (hEi r) (hmean r)]
    exact inv_mul_cancel_left₀ (hNpos r).ne' (e r)
  have hlim : Tendsto (fun r => ∫ ω, A r ω ∂μ) atTop (𝓝 0) := by
    refine he.congr fun r => (hAint r).symm
  exact exists_subseq_ae_tendsto_zero_of_tendsto_integral A hA0 hAm hAi hlim


/--
**The source hypothesis, discharged.**

The reading of "for all pairs `(i, i′) ∈ N × N`, `D_ii′ →P Δ(ϕi, ϕi′)`" that actually controls a
growing collection.  Pointwise convergence of a triangular array does *not* control its average --
put the mass at indices that escape -- so something must connect the indices.  What connects them
in a sampling model is that the errors at a given stage are the same statistic applied to
interchangeable members, hence identically distributed; then a single one of them governs the
whole average, and the subsequence is the one `L¹` convergence always costs.
-/
theorem exists_subseq_ae_tendsto_average_of_tendsto_measure_ge [IsProbabilityMeasure μ]
    (N : Nat → Nat) (hN : ∀ r, 0 < N r) (E : ∀ r, Fin (N r) → Ω → Real)
    (hEm : ∀ r i, Measurable (E r i))
    (hE0 : ∀ r i ω, 0 ≤ E r i ω) {C : Real} (hEC : ∀ r i ω, E r i ω ≤ C)
    (hid : ∀ r i j, ∫ ω, E r i ω ∂μ = ∫ ω, E r j ω ∂μ)
    (hzero : ∀ ε : Real, 0 < ε →
      Tendsto (fun r => (μ {ω | ε ≤ E r ⟨0, hN r⟩ ω}).toReal) atTop (𝓝 0)) :
    ∃ ns : Nat → Nat, StrictMono ns ∧
      ∀ᵐ ω ∂μ, Tendsto (fun u => ((N (ns u) : Real))⁻¹ * ∑ i, E (ns u) i ω) atTop (𝓝 0) := by
  classical
  have hEi : ∀ r i, Integrable (E r i) μ := by
    intro r i
    refine ⟨(hEm r i).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hE0 r i ω)]
    exact hEC r i ω
  refine exists_subseq_ae_tendsto_average N hN E
    (fun r i => Filter.Eventually.of_forall (hE0 r i)) hEi
    (fun r => ∫ ω, E r ⟨0, hN r⟩ ω ∂μ) (fun r i => hid r i ⟨0, hN r⟩) ?_
  exact tendsto_integral_of_tendsto_measure_ge_of_bounded
    (fun r => E r ⟨0, hN r⟩) (fun r => hEm r _) (fun r => hE0 r _) (fun r => hEi r _)
    (fun r => hEC r _) hzero


/--
**Per-index convergence does not control the average.**

The sharpness of the identical-distribution hypothesis, and the reason a growing collection needs
something to connect its indices.  Here the errors are `0` or `1`, every one of them is eventually
`0` at a fixed index -- so a reader checking "the error at each pair vanishes" sees nothing wrong
-- and yet the average is exactly `1 / 2` at every stage.  The mass simply moves to indices that
escape.
-/
theorem exists_triangular_array_tendsto_pointwise_average_eq_half :
    ∃ (N : Nat → Nat) (E : ∀ r : Nat, Fin (N r) → Real),
      (∀ r, 0 < N r) ∧
      (∀ r i, 0 ≤ E r i ∧ E r i ≤ 1) ∧
      (∀ i : Nat, ∀ r : Nat, i < r + 1 → ∀ h : i < N r, E r ⟨i, h⟩ = 0) ∧
      (∀ r, ((N r : Real))⁻¹ * ∑ i, E r i = 1 / 2) := by
  classical
  refine ⟨fun r => 2 * r + 2, fun r i => if r + 1 ≤ (i : Nat) then 1 else 0,
    fun r => ?_, fun r i => ?_, fun i r hir h => ?_, fun r => ?_⟩
  · simp only []
    omega
  · by_cases hc : r + 1 ≤ (i : Nat) <;> simp [hc]
  · have hne : ¬ (r + 1 ≤ i) := by omega
    simp [hne]
  · have hcard : (Finset.univ.filter fun i : Fin (2 * r + 2) => r + 1 ≤ (i : Nat)).card
        = r + 1 := by
      have hbij : (Finset.univ.filter fun i : Fin (2 * r + 2) => r + 1 ≤ (i : Nat))
          = (Finset.Ico (r + 1) (2 * r + 2)).attachFin (by
              intro m hm
              simp only [Finset.mem_Ico] at hm
              omega) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
          Finset.mem_Ico]
        omega
      rw [hbij, Finset.card_attachFin, Nat.card_Ico]
      omega
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, hcard]
    push_cast
    have h2 : (2 : Real) * (r : Real) + 2 ≠ 0 := by positivity
    field_simp
    ring

end TauCeti

end
