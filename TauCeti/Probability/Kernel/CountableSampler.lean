/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Cdf
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Cumulative-weight sampling on countable spaces

A probability law on the natural numbers partitions `[0,1)` into left-closed,
right-open cumulative-mass intervals. `Measure.natSampler` selects the interval
containing the supplied uniform variable. Empty intervals are skipped, including
at zero, so a state of zero mass is never selected. An injective enumeration
transports this construction to any nonempty countable measurable space with measurable singletons.

The samplers are jointly measurable in a measurable family of probability laws.
Their pushforward identities allow the independent-noise construction of Markov
chains to use this explicit endpoint convention instead of an abstract sampler.

The cumulative-weight construction is the usual inverse-transform method; see
J. R. Norris, *Markov Chains* (1997), §1.1. The independent-noise path-law theorem
is supplied by `TauCeti.Probability.hasLaw_randomizedChain`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Function

namespace MeasureTheory.Measure

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- The first state `n` whose cumulative mass `μ.real (Iic n)` is strictly above `u`.
The left endpoint belongs to the next nonempty interval; in particular zero-weight states
are never selected. -/
def natSampler (u : Ico (0 : ℝ) 1) : ℕ :=
  Nat.find (μ.exists_nat_lt_measureReal_Iic u.property.2)

/-- A sampled index is the first strict cumulative crossing. -/
theorem natSampler_eq_iff (u : Ico (0 : ℝ) 1) (n : ℕ) :
    μ.natSampler u = n ↔
      (u : ℝ) < μ.real (Iic n) ∧ ∀ j < n, μ.real (Iic j) ≤ u := by
  classical
  simp only [natSampler, Nat.find_eq_iff, not_lt]

/-- The interval assigned to `n` includes its left endpoint and excludes its right endpoint. -/
@[simp] theorem natSampler_eq_iff_mem_Ico (u : Ico (0 : ℝ) 1) (n : ℕ) :
    μ.natSampler u = n ↔ (u : ℝ) ∈ Ico (μ.real (Iio n)) (μ.real (Iic n)) := by
  rw [natSampler_eq_iff]
  cases n with
  | zero => simp [u.property.1]
  | succ n =>
    have heq : (Iio (n + 1) : Set ℕ) = Iic n := by ext j; simp
    rw [heq]
    constructor
    · rintro ⟨hu, hprev⟩
      exact ⟨hprev n (by omega), hu⟩
    · rintro ⟨hprev, hu⟩
      exact ⟨hu, fun j hj => (measureReal_mono (Iic_subset_Iic.2 (by omega))).trans hprev⟩

/-- Cumulative sampling is measurable jointly in any measurable family of probability laws. -/
theorem measurable_natSampler_family {Ω : Type*} [MeasurableSpace Ω]
    (ν : Ω → Measure ℕ) [∀ ω, IsProbabilityMeasure (ν ω)] (hν : Measurable ν) :
    Measurable fun p : Ω × Ico (0 : ℝ) 1 => (ν p.1).natSampler p.2 := by
  classical
  apply measurable_find
  intro n
  exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd)
    (((Measure.measurable_coe .of_discrete).comp (hν.comp measurable_fst)).ennreal_toReal)

/-- A fixed cumulative sampler is measurable. -/
@[fun_prop] theorem measurable_natSampler : Measurable μ.natSampler := by
  exact (measurable_natSampler_family (fun _ : Unit => μ) measurable_const).comp
    (measurable_const (a := ()).prodMk measurable_id)

/-- The preimage of each state is its cumulative-mass interval, including at zero. -/
theorem preimage_natSampler_singleton (n : ℕ) :
    μ.natSampler ⁻¹' {n} =
      Subtype.val ⁻¹' Ico (μ.real (Iio n)) (μ.real (Iic n)) := by
  ext u
  exact μ.natSampler_eq_iff_mem_Ico u n

/-- Uniform cumulative sampling has the prescribed law. -/
@[simp] theorem map_natSampler :
    ((volume : Measure ℝ).comap (Subtype.val : Ico (0 : ℝ) 1 → ℝ)).map μ.natSampler = μ := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply μ.measurable_natSampler .of_discrete,
    μ.preimage_natSampler_singleton, ← volume_set_coe_def,
    volume_preimage_coe measurableSet_Ico.nullMeasurableSet measurableSet_Ico]
  have hsub : Ico (μ.real (Iio n)) (μ.real (Iic n)) ⊆ Ico (0 : ℝ) 1 :=
    fun u hu => ⟨measureReal_nonneg.trans hu.1, hu.2.trans_le measureReal_le_one⟩
  rw [inter_eq_left.2 hsub, Real.volume_Ico]
  rw [← measureReal_sdiff Iio_subset_Iic_self .of_discrete, Iic_sdiff_Iio_same,
    ofReal_measureReal]

/-- Every sampled state has strictly positive mass, not just almost surely. -/
theorem measureReal_singleton_natSampler_pos (u : Ico (0 : ℝ) 1) :
    0 < μ.real {μ.natSampler u} := by
  have hu := (μ.natSampler_eq_iff_mem_Ico u (μ.natSampler u)).1 rfl
  rw [← Iic_sdiff_Iio_same, measureReal_sdiff Iio_subset_Iic_self .of_discrete]
  exact sub_pos.2 (hu.1.trans_lt hu.2)

section Countable

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Nonempty α] (ν : Measure α) [IsProbabilityMeasure ν] (e : α ↪ ℕ)

/-- Sample a countable law using the order supplied by an injective enumeration.
Finite enumerations and enumerations with gaps use the same construction. -/
def countableSampler (u : Ico (0 : ℝ) 1) : α :=
  invFun e ((ν.map e).natSampler u)

omit [Countable α] [MeasurableSingletonClass α] in
/-- The countable sampler decodes the natural-valued cumulative sampler. -/
theorem countableSampler_def (u : Ico (0 : ℝ) 1) :
    ν.countableSampler e u = invFun e ((ν.map e).natSampler u) := (rfl)

omit [Nonempty α] in
/-- The natural sampler never selects a gap in the enumeration. -/
theorem natSampler_map_mem_range (u : Ico (0 : ℝ) 1) :
    (ν.map e).natSampler u ∈ Set.range e := by
  have hpos := (ν.map e).measureReal_singleton_natSampler_pos u
  rw [map_measureReal_apply (measurable_of_countable e) .of_discrete] at hpos
  exact nonempty_of_measureReal_ne_zero hpos.ne'

/-- Encoding the sampled state recovers its sampled natural index. -/
@[simp] theorem apply_countableSampler (u : Ico (0 : ℝ) 1) :
    e (ν.countableSampler e u) = (ν.map e).natSampler u := by
  rw [countableSampler_def]
  exact invFun_eq (ν.natSampler_map_mem_range e u)

/-- A countable state is selected on its left-closed, right-open cumulative interval. -/
@[simp] theorem countableSampler_eq_iff (u : Ico (0 : ℝ) 1) (a : α) :
    ν.countableSampler e u = a ↔
      (u : ℝ) ∈ Ico (ν.real {b | e b < e a}) (ν.real {b | e b ≤ e a}) := by
  rw [← e.injective.eq_iff, apply_countableSampler,
    natSampler_eq_iff_mem_Ico, map_measureReal_apply (measurable_of_countable e) .of_discrete,
    map_measureReal_apply (measurable_of_countable e) .of_discrete]
  rfl

/-- Every sampled countable state has strictly positive mass, even at cumulative endpoints. -/
theorem measureReal_singleton_countableSampler_pos (u : Ico (0 : ℝ) 1) :
    0 < ν.real {ν.countableSampler e u} := by
  have hpos := (ν.map e).measureReal_singleton_natSampler_pos u
  rw [← ν.apply_countableSampler e u,
    map_measureReal_apply (measurable_of_countable e) .of_discrete] at hpos
  simpa only [Set.preimage_singleton, e.injective.eq_iff, Set.ofPred_eq_eq_singleton] using hpos

/-- Countable sampling is jointly measurable in a measurable family of probability laws. -/
theorem measurable_countableSampler_family {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ρ ω)] (hρ : Measurable ρ) :
    Measurable fun p : Ω × Ico (0 : ℝ) 1 => (ρ p.1).countableSampler e p.2 := by
  exact (measurable_of_countable (invFun e)).comp
    (measurable_natSampler_family (fun ω => (ρ ω).map e)
      ((Measure.measurable_map e (measurable_of_countable e)).comp hρ))

/-- A fixed countable sampler is measurable. -/
@[fun_prop] theorem measurable_countableSampler : Measurable (ν.countableSampler e) := by
  exact (measurable_countableSampler_family e (fun _ : Unit => ν) measurable_const).comp
    (measurable_const (a := ()).prodMk measurable_id)

/-- Uniform countable sampling has the prescribed law. -/
@[simp] theorem map_countableSampler :
    ((volume : Measure ℝ).comap (Subtype.val : Ico (0 : ℝ) 1 → ℝ)).map
      (ν.countableSampler e) = ν := by
  have hfun : ν.countableSampler e = invFun e ∘ (ν.map e).natSampler :=
    funext (ν.countableSampler_def e)
  rw [hfun, ← Measure.map_map (measurable_of_countable (invFun e))
    (ν.map e).measurable_natSampler, map_natSampler,
    Measure.map_map (measurable_of_countable (invFun e)) (measurable_of_countable e)]
  convert ν.map_id using 2
  exact funext (leftInverse_invFun e.injective)

end Countable

end MeasureTheory.Measure
