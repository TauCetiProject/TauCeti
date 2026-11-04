/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import Mathlib.Order.WellFounded
public import Mathlib.Probability.Distributions.Uniform
public import TauCeti.Probability.Kernel.Matrix
public import TauCeti.Probability.Kernel.Randomization
public import TauCeti.Probability.Quantile.Discrete

/-!
# Cumulative-weight uniform samplers on countable spaces

Given an enumeration of a countable state space `α` via an injection `e : α ↪ ℕ`, a probability
measure `μ` on `α` partitions the half-open unit interval `Set.Ico (0 : ℝ) 1` into half-open
cumulative-weight intervals

`Set.Ico (μ.real {y | e y < e x}) (μ.real {y | e y ≤ e x})`

of length `μ.real {x}`. Sending each `u ∈ Set.Ico (0 : ℝ) 1` to the unique state whose interval
contains `u` constructs an explicit measurable sampler `μ.countableSampler e : ℝ → α` pushing
Lebesgue measure restricted to `Set.Ico (0 : ℝ) 1` forward to `μ`.

Working on `Set.Ico (0 : ℝ) 1` with left-closed, right-open cumulative bins resolves both
zero-weight states and boundary levels deterministically:
* states with `μ {x} = 0` receive degenerate intervals `Set.Ico a a = ∅` and are never sampled at
  any `u ∈ Set.Ico (0 : ℝ) 1`;
* the left endpoint `u = 0` selects the first state of positive mass in the enumeration `e`, with
  no junk value on `Set.Ico (0 : ℝ) 1`;
* on `Set.Ioo (0 : ℝ) 1`, the natural-number sampler `μ.natSampler` agrees identically with the
  right-continuous `MeasureTheory.Measure.upperQuantile` of `(μ.map Nat.cast)`, while the
  left-continuous `MeasureTheory.Measure.quantile` convention `(a, b]` agrees off `{0}` and the
  countable set of cumulative jump levels, hence almost everywhere on `Set.Ico (0 : ℝ) 1`.

Parameterizing enumerations by `e : α ↪ ℕ` unifies finite state spaces (`Fin n` via
`Fin.valEmbedding` and finite bijections `Fin n ≃ α`), countably infinite state spaces (`ℕ` via
`Function.Embedding.refl ℕ` and bijections `ℕ ≃ α`), and arbitrary countable measurable-singleton
spaces, without requiring any topology or standard Borel structure on the state space. Applying the
construction fiberwise to a kernel `κ : Kernel β α` produces a sampler
`κ.countableSampler e : β → ℝ → α` that is jointly measurable in `(b, u) : β × ℝ` for every
measurable space `β` and every kernel `κ`, and turns independent uniform noise on
`Set.Ico (0 : ℝ) 1` into the composition-product `μ ⊗ₘ κ`.

## Main definitions

* `MeasureTheory.Measure.natSampler`: cumulative-weight sampler `ℝ → ℕ` for a measure on `ℕ`.
* `ProbabilityTheory.Kernel.natSampler`: fiberwise sampler `β → ℝ → ℕ` for a kernel into `ℕ`.
* `MeasureTheory.Measure.countableSampler`: cumulative-weight sampler `ℝ → α` along `e : α ↪ ℕ`.
* `ProbabilityTheory.Kernel.countableSampler`: jointly measurable sampler `β → ℝ → α` for a kernel
  `κ : Kernel β α` along `e : α ↪ ℕ`.

## Main results

* `MeasureTheory.Measure.natSampler_eq_iff`, `MeasureTheory.Measure.countableSampler_eq_iff`:
  half-open cumulative-interval characterizations on `Set.Ico (0 : ℝ) 1`.
* `MeasureTheory.Measure.natSampler_ne_of_measure_singleton_eq_zero`,
  `MeasureTheory.Measure.countableSampler_ne_of_measure_singleton_eq_zero`: zero-weight states are
  never sampled on `Set.Ico (0 : ℝ) 1`.
* `MeasureTheory.Measure.upperQuantile_map_natCast`,
  `MeasureTheory.Measure.coe_natSampler_ae_eq_quantile_map_natCast`: comparison between the
  `[a, b)` sampler on `[0, 1)` and the `upperQuantile` and `quantile` inverse-CDF conventions.
* `MeasureTheory.Measure.countableSampler_fin_eq_iff`,
  `MeasureTheory.Measure.countableSampler_equivFin_eq_iff`,
  `MeasureTheory.Measure.countableSampler_equivNat_eq_iff`: partial-sum characterizations for
  finite and countably infinite enumerations.
* `ProbabilityTheory.Kernel.measurable_uncurry_natSampler`,
  `ProbabilityTheory.Kernel.measurable_uncurry_countableSampler`: joint measurability in the
  current state and uniform variable.
* `MeasureTheory.Measure.map_countableSampler_volume_Ico`,
  `ProbabilityTheory.Kernel.map_prod_countableSampler_volume_Ico`: pushforward and
  composition-product laws under Lebesgue measure on `Set.Ico (0 : ℝ) 1`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.1, Theorem 1.1.2.
* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., American Mathematical
  Society (2017), §1.2.
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

section NatSampler

/-- Every level strictly below `1` is strictly exceeded by a finite cumulative mass of a
probability measure on `ℕ`. -/
theorem exists_nat_lt_measureReal_Iic (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u < 1) : ∃ k : ℕ, u < μ.real (Iic k) := by
  have hmid : (u + 1) / 2 < 1 := by linarith
  obtain ⟨k, hk⟩ := μ.exists_nat_le_measureReal_Iic hmid
  exact ⟨k, by linarith⟩

/-- Cumulative-weight sampler of a measure `μ` on `ℕ` at level `u : ℝ`.

For a probability measure `μ` and `u ∈ Set.Ico 0 1`, this returns the least natural number `k`
with `u < μ.real (Set.Iic k)`, assigning `k` the half-open interval
`Set.Ico (μ.real (Set.Iio k)) (μ.real (Set.Iic k))`. Levels below `0` or at and above all finite
cumulative masses of `μ` return `0`. -/
def natSampler (μ : Measure ℕ) (u : ℝ) : ℕ :=
  open Classical in
  if h : 0 ≤ u ∧ ∃ k : ℕ, u < μ.real (Iic k) then Nat.find h.2 else 0

/-- Negative levels return the fallback state `0`. -/
theorem natSampler_of_neg (μ : Measure ℕ) {u : ℝ} (hu : u < 0) : μ.natSampler u = 0 := by
  simp [natSampler, not_le.mpr hu]

/-- Levels at or above all cumulative masses of `μ` return `0`. -/
theorem natSampler_of_forall_measureReal_Iic_le (μ : Measure ℕ) {u : ℝ}
    (h : ∀ k : ℕ, μ.real (Iic k) ≤ u) : μ.natSampler u = 0 := by
  have hno : ¬∃ k : ℕ, u < μ.real (Iic k) := fun ⟨k, hk⟩ => hk.not_ge (h k)
  simp [natSampler, hno]

/-- Sampling the zero measure on `ℕ` identically returns `0`. -/
@[simp]
theorem natSampler_zero_measure (u : ℝ) : (0 : Measure ℕ).natSampler u = 0 := by
  rcases lt_or_ge u 0 with hu | hu
  · exact natSampler_of_neg 0 hu
  · exact natSampler_of_forall_measureReal_Iic_le 0 fun _ => by simp [hu]

/-- For a probability measure on `ℕ`, levels `1 ≤ u` return the fallback state `0`. -/
theorem natSampler_of_one_le (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ} (hu : 1 ≤ u) :
    μ.natSampler u = 0 :=
  μ.natSampler_of_forall_measureReal_Iic_le fun _ => measureReal_le_one.trans hu

/-- On `Set.Ico 0 1`, `natSampler` is given by `Nat.find` of strict cumulative crossing. -/
theorem natSampler_eq_find (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) :
    μ.natSampler u =
      (open Classical in Nat.find (μ.exists_nat_lt_measureReal_Iic hu.2)) := by
  classical
  have h : 0 ≤ u ∧ ∃ k : ℕ, u < μ.real (Iic k) :=
    ⟨hu.1, μ.exists_nat_lt_measureReal_Iic hu.2⟩
  simp [natSampler, hu.1, h.2]

/-- On `Set.Ico 0 1`, `μ.natSampler u` is the least index whose cumulative mass strictly exceeds
`u`. -/
theorem isLeast_natSampler (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) :
    IsLeast {k : ℕ | u < μ.real (Iic k)} (μ.natSampler u) := by
  classical
  rw [μ.natSampler_eq_find hu]
  exact ⟨Nat.find_spec (μ.exists_nat_lt_measureReal_Iic hu.2),
    fun _ hk => Nat.find_min' _ hk⟩

/-- Galois upper-bound characterization of `natSampler` on `Set.Ico 0 1`. -/
theorem natSampler_le_iff (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) {k : ℕ} :
    μ.natSampler u ≤ k ↔ u < μ.real (Iic k) := by
  obtain ⟨hmem, hmin⟩ := μ.isLeast_natSampler hu
  refine ⟨fun hle => hmem.trans_le (measureReal_mono (Iic_subset_Iic.mpr hle)), fun hk => hmin hk⟩

/-- Galois lower-bound characterization of `natSampler` on `Set.Ico 0 1`. -/
theorem le_natSampler_iff (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) {k : ℕ} :
    k ≤ μ.natSampler u ↔ μ.real (Iio k) ≤ u := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hu.1]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hIio : (Iio (m + 1) : Set ℕ) = Iic m := by
      ext j
      simp
    rw [hIio, ← not_lt, Nat.lt_succ_iff, μ.natSampler_le_iff hu, not_lt]

/-- **Half-open cumulative-interval characterization on `ℕ`.** At any level `u ∈ Set.Ico 0 1`,
`μ.natSampler u = k` holds if and only if `u` lies in the half-open interval
`Set.Ico (μ.real (Set.Iio k)) (μ.real (Set.Iic k))`. -/
@[simp]
theorem natSampler_eq_iff (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) (k : ℕ) :
    μ.natSampler u = k ↔ μ.real (Iio k) ≤ u ∧ u < μ.real (Iic k) := by
  rw [le_antisymm_iff, μ.natSampler_le_iff hu, μ.le_natSampler_iff hu, and_comm]

/-- `natSampler` is monotone on `Set.Ico 0 1`. -/
theorem monotoneOn_natSampler (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    MonotoneOn μ.natSampler (Ico (0 : ℝ) 1) := by
  intro u hu v hv huv
  rw [μ.le_natSampler_iff hv]
  exact ((μ.le_natSampler_iff hu).mp le_rfl).trans huv

/-- The cumulative mass on `Set.Iic k` splits into the strict lower cumulative mass on `Set.Iio k`
plus the atom at `k`. -/
theorem measureReal_Iic_nat_eq_add_singleton (μ : Measure ℕ) [IsFiniteMeasure μ] (k : ℕ) :
    μ.real (Iic k) = μ.real (Iio k) + μ.real {k} := by
  have hsplit : (Iic k : Set ℕ) = Iio k ∪ {k} := by
    ext j
    simp [Nat.le_iff_lt_or_eq]
  have hdisj : Disjoint (Iio k) ({k} : Set ℕ) := by simp
  rw [hsplit, measureReal_union hdisj .of_discrete]

/-- The preimage of `{k}` under `μ.natSampler` inside `Set.Ico 0 1` is the half-open cumulative
interval `Set.Ico (μ.real (Set.Iio k)) (μ.real (Set.Iic k))`. -/
theorem preimage_natSampler_singleton_inter_Ico (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ) :
    μ.natSampler ⁻¹' {k} ∩ Ico (0 : ℝ) 1 = Ico (μ.real (Iio k)) (μ.real (Iic k)) := by
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ico]
  constructor
  · rintro ⟨rfl, hu0, hu1⟩
    exact (μ.natSampler_eq_iff ⟨hu0, hu1⟩ _).mp rfl
  · rintro ⟨hlow, hhigh⟩
    have hu0 : 0 ≤ u := measureReal_nonneg.trans hlow
    have hu1 : u < 1 := hhigh.trans_le measureReal_le_one
    exact ⟨(μ.natSampler_eq_iff ⟨hu0, hu1⟩ k).mpr ⟨hlow, hhigh⟩, hu0, hu1⟩

/-- Every state sampled on `Set.Ico 0 1` has strictly positive mass. -/
theorem measure_singleton_natSampler_pos (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) :
    0 < μ {μ.natSampler u} := by
  obtain ⟨hlow, hhigh⟩ := (μ.natSampler_eq_iff hu (μ.natSampler u)).mp rfl
  rw [μ.measureReal_Iic_nat_eq_add_singleton] at hhigh
  have hreal : 0 < μ.real {μ.natSampler u} := by linarith
  exact pos_iff_ne_zero.mpr fun h0 => hreal.ne' ((measureReal_eq_zero_iff).mpr h0)

/-- Zero-weight states in `ℕ` are never sampled at any level in `Set.Ico 0 1`. -/
theorem natSampler_ne_of_measure_singleton_eq_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) {k : ℕ} (hk : μ {k} = 0) :
    μ.natSampler u ≠ k := by
  intro h
  have hpos := μ.measure_singleton_natSampler_pos hu
  rw [h, hk] at hpos
  exact lt_irrefl 0 hpos

/-- A zero-weight state in `ℕ` has empty preimage under `natSampler` in `Set.Ico 0 1`. -/
@[simp]
theorem preimage_natSampler_singleton_inter_Ico_of_measure_eq_zero (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {k : ℕ} (hk : μ {k} = 0) :
    μ.natSampler ⁻¹' {k} ∩ Ico (0 : ℝ) 1 = ∅ := by
  rw [μ.preimage_natSampler_singleton_inter_Ico, μ.measureReal_Iic_nat_eq_add_singleton,
    (measureReal_eq_zero_iff).mpr hk, add_zero, Ico_self]

/-- At the left endpoint `u = 0`, `μ.natSampler 0` selects the least natural number of positive
mass, skipping any initial zero-weight indices. -/
theorem isLeast_pos_natSampler_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsLeast {k : ℕ | 0 < μ {k}} (μ.natSampler 0) := by
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  refine ⟨μ.measure_singleton_natSampler_pos h0, fun k hk => ?_⟩
  rw [μ.natSampler_le_iff h0]
  have hk_real : 0 < μ.real {k} := ENNReal.toReal_pos hk.ne' (measure_ne_top μ {k})
  exact hk_real.trans_le (measureReal_mono (singleton_subset_iff.mpr (mem_Iic.mpr le_rfl)))

/-- Right-constancy of `natSampler` on each cumulative step: if `u ∈ Set.Ico 0 1`, then
`μ.natSampler` stays constant on `Set.Ico u (μ.real (Set.Iic (μ.natSampler u)))`. -/
theorem natSampler_eq_of_mem_Ico (μ : Measure ℕ) [IsProbabilityMeasure μ] {u v : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) (hv : v ∈ Ico u (μ.real (Iic (μ.natSampler u)))) :
    μ.natSampler v = μ.natSampler u := by
  have hv_Ico : v ∈ Ico (0 : ℝ) 1 := ⟨hu.1.trans hv.1, hv.2.trans_le measureReal_le_one⟩
  obtain ⟨hlow, _⟩ := (μ.natSampler_eq_iff hu (μ.natSampler u)).mp rfl
  exact (μ.natSampler_eq_iff hv_Ico (μ.natSampler u)).mpr ⟨hlow.trans hv.1, hv.2⟩

/-- **Endpoint convention bridge (`upperQuantile`).** On the open unit interval `Set.Ioo 0 1`, the
real cast of `μ.natSampler u` equals the right-continuous `upperQuantile` of `μ` cast to `ℝ`. -/
theorem upperQuantile_map_natCast (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (μ.map (Nat.cast : ℕ → ℝ)).upperQuantile u = μ.natSampler u := by
  have hu_Ico : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
  set k := μ.natSampler u
  obtain ⟨hlow, hhigh⟩ := (μ.natSampler_eq_iff hu_Ico k).mp rfl
  refine le_antisymm ?_ ?_
  · apply upperQuantile_le_of_lt_cdf _ hu.1
    simpa only [cdf_map_natCast μ (Nat.cast_nonneg k), Nat.floor_natCast] using hhigh
  · rw [le_upperQuantile_iff _ hu.1 hu.2,
      map_measureReal_apply (measurable_of_countable _) measurableSet_Iio]
    have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iio (k : ℝ) = Iio k := by
      ext j
      simp
    rwa [hpre]

/-- **Endpoint convention bridge (`quantile`, pointwise).** At any interior level `u ∈ Set.Ioo 0 1`
that is not one of the cumulative jump values `μ.real (Set.Iic j)`, the left-continuous `quantile`
and right-continuous `natSampler` agree. -/
theorem quantile_map_natCast_eq_natSampler_of_ne (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hne : ∀ j : ℕ, u ≠ μ.real (Iic j)) :
    (μ.map (Nat.cast : ℕ → ℝ)).quantile u = μ.natSampler u := by
  have hu_Ico : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
  set k := μ.natSampler u
  obtain ⟨hlow, hhigh⟩ := (μ.natSampler_eq_iff hu_Ico k).mp rfl
  rw [μ.quantile_map_natCast_eq_iff hu k]
  refine ⟨hhigh.le, fun j hj => ?_⟩
  by_contra! hjk
  have hj_lt : u < μ.real (Iic j) := lt_of_le_of_ne hj (hne j)
  have hle : μ.real (Iic j) ≤ μ.real (Iio k) :=
    measureReal_mono fun m hm => lt_of_le_of_lt hm hjk
  exact (hj_lt.trans_le hle).not_ge hlow

/-- **Endpoint convention bridge (`quantile`, almost everywhere).** On `Set.Ico 0 1`, the
right-continuous `[a, b)` sampler `natSampler` and the left-continuous `(a, b]` inverse CDF
`quantile` agree almost everywhere with respect to Lebesgue measure. -/
theorem coe_natSampler_ae_eq_quantile_map_natCast (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (fun u => (μ.natSampler u : ℝ)) =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
      (μ.map (Nat.cast : ℕ → ℝ)).quantile := by
  let jumps : Set ℝ := insert 0 (range fun j : ℕ => μ.real (Iic j))
  have hcount : jumps.Countable := (countable_range _).insert 0
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ico]
  filter_upwards [hcount.ae_notMem volume] with u hu hmem
  have hu0 : 0 < u := lt_of_le_of_ne hmem.1 fun h => hu (Or.inl h.symm)
  have hne : ∀ j : ℕ, u ≠ μ.real (Iic j) := fun j hj => hu (Or.inr ⟨j, hj.symm⟩)
  exact (μ.quantile_map_natCast_eq_natSampler_of_ne ⟨hu0, hmem.2⟩ hne).symm

end NatSampler

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

section NatSampler

variable {β : Type*} [MeasurableSpace β]

/-- Fiberwise cumulative-weight sampler of a kernel `κ : Kernel β ℕ`. -/
def natSampler (κ : Kernel β ℕ) (b : β) (u : ℝ) : ℕ :=
  (κ b).natSampler u

/-- `Kernel.natSampler` evaluates `Measure.natSampler` on each fiber `κ b`. -/
@[simp]
theorem natSampler_apply (κ : Kernel β ℕ) (b : β) (u : ℝ) :
    κ.natSampler b u = (κ b).natSampler u := (rfl)

/-- For a kernel constructed from row PMFs `Kernel.ofPMF p`, `natSampler` samples each row PMF
`(p b).toMeasure`. -/
theorem natSampler_ofPMF [Countable β] [MeasurableSingletonClass β] (p : β → PMF ℕ)
    (b : β) (u : ℝ) :
    (Kernel.ofPMF p).natSampler b u = (p b).toMeasure.natSampler u := by
  rw [natSampler_apply, ofPMF_apply]

/-- `Kernel.natSampler` is jointly measurable in the source point and uniform level, for any
measurable space `β` and any kernel `κ : Kernel β ℕ`. -/
@[fun_prop]
theorem measurable_uncurry_natSampler (κ : Kernel β ℕ) :
    Measurable (uncurry κ.natSampler) := by
  have hcum (j : ℕ) : Measurable fun p : β × ℝ => (κ p.1).real (Iic j) := by
    simp_rw [measureReal_def]
    exact ((κ.measurable_coe .of_discrete).ennreal_toReal).comp measurable_fst
  have hexists : MeasurableSet {p : β × ℝ | 0 ≤ p.2 ∧ ∃ m : ℕ, p.2 < (κ p.1).real (Iic m)} := by
    have heq : {p : β × ℝ | 0 ≤ p.2 ∧ ∃ m : ℕ, p.2 < (κ p.1).real (Iic m)} =
        (univ ×ˢ Ici (0 : ℝ)) ∩ ⋃ m : ℕ, {p : β × ℝ | p.2 < (κ p.1).real (Iic m)} := by
      ext p
      simp
    rw [heq]
    exact (MeasurableSet.univ.prod measurableSet_Ici).inter
      (MeasurableSet.iUnion fun m => measurableSet_lt measurable_snd (hcum m))
  refine measurable_to_countable' fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · have hpre0 : uncurry κ.natSampler ⁻¹' {0} =
        ({p : β × ℝ | 0 ≤ p.2 ∧ p.2 < (κ p.1).real (Iic 0)}) ∪
          {p : β × ℝ | 0 ≤ p.2 ∧ ∃ m : ℕ, p.2 < (κ p.1).real (Iic m)}ᶜ := by
      ext ⟨b, u⟩
      simp only [mem_preimage, mem_singleton_iff, uncurry, natSampler_apply, Measure.natSampler,
        mem_union, mem_ofPred_eq, mem_compl_iff]
      by_cases h : 0 ≤ u ∧ ∃ m : ℕ, u < (κ b).real (Iic m)
      · classical
        simp [h, Nat.find_eq_zero]
      · simp [h]
    rw [hpre0]
    exact ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (hcum 0))).union hexists.compl
  · have hprek : uncurry κ.natSampler ⁻¹' {k} =
        {p : β × ℝ | 0 ≤ p.2 ∧ p.2 < (κ p.1).real (Iic k)} ∩
          ⋂ j ∈ Finset.range k, {p : β × ℝ | (κ p.1).real (Iic j) ≤ p.2} := by
      ext ⟨b, u⟩
      simp only [mem_preimage, mem_singleton_iff, uncurry, natSampler_apply, Measure.natSampler,
        mem_inter_iff, mem_ofPred_eq, Finset.mem_range, mem_iInter]
      by_cases h : 0 ≤ u ∧ ∃ m : ℕ, u < (κ b).real (Iic m)
      · classical
        rw [dite_eq_left_of_eq_true (eq_true h), Nat.find_eq_iff]
        refine ⟨fun ⟨huk, hmin⟩ => ⟨⟨h.1, huk⟩, fun j hj => not_lt.mp (hmin j hj)⟩,
          fun ⟨⟨_, huk⟩, hmin⟩ => ⟨huk, fun j hj => not_lt.mpr (hmin j hj)⟩⟩
      · rw [dite_eq_right_of_eq_false (eq_false h)]
        refine ⟨fun h0 => absurd h0.symm hk, fun ⟨⟨hu0, huk⟩, _⟩ => absurd ⟨hu0, k, huk⟩ h⟩
    rw [hprek]
    refine ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (hcum k))).inter ?_
    exact Finset.measurableSet_biInter (Finset.range k) fun j _ =>
      measurableSet_le (hcum j) measurable_snd

/-- For each fixed state `b`, `κ.natSampler b` is measurable. -/
@[fun_prop]
theorem measurable_natSampler (κ : Kernel β ℕ) (b : β) : Measurable (κ.natSampler b) :=
  (κ.measurable_uncurry_natSampler).of_uncurry_left

end NatSampler

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

section NatSamplerLaw

/-- `Measure.natSampler` is a measurable map `ℝ → ℕ`. -/
@[fun_prop]
theorem measurable_natSampler (μ : Measure ℕ) : Measurable μ.natSampler :=
  (ProbabilityTheory.Kernel.const Unit μ).measurable_natSampler ()

/-- Conditioning Lebesgue measure on `Set.Ico (0 : ℝ) 1` agrees with restricting it to
`Set.Ico (0 : ℝ) 1`. -/
theorem cond_volume_Ico_zero_one :
    ProbabilityTheory.cond (volume : Measure ℝ) (Ico (0 : ℝ) 1) =
      volume.restrict (Ico (0 : ℝ) 1) := by
  rw [ProbabilityTheory.cond, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, inv_one, one_smul]

/-- **Inverse transform sampling on `ℕ` from `[0, 1)`.** `Measure.natSampler` pushes Lebesgue
measure restricted to `Set.Ico (0 : ℝ) 1` forward to `μ`. -/
@[simp]
theorem map_natSampler_volume_Ico (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ico (0 : ℝ) 1)).map μ.natSampler = μ := by
  apply Measure.ext_iff_singleton.mpr
  intro k
  rw [Measure.map_apply μ.measurable_natSampler .of_discrete,
    Measure.restrict_apply (μ.measurable_natSampler .of_discrete),
    μ.preimage_natSampler_singleton_inter_Ico, Real.volume_Ico,
    μ.measureReal_Iic_nat_eq_add_singleton, add_sub_cancel_left,
    ofReal_measureReal]

/-- `Measure.natSampler` is measure-preserving from `volume.restrict (Set.Ico 0 1)` to `μ`. -/
theorem measurePreserving_natSampler (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    MeasurePreserving μ.natSampler (volume.restrict (Ico (0 : ℝ) 1)) μ :=
  ⟨μ.measurable_natSampler, μ.map_natSampler_volume_Ico⟩

/-- Applying `μ.natSampler` to any random variable with law `volume.restrict (Set.Ico 0 1)`
produces a random variable with law `μ`. -/
theorem hasLaw_natSampler_of_hasLaw (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U (volume.restrict (Ico (0 : ℝ) 1)) P) :
    HasLaw (fun ω => μ.natSampler (U ω)) μ P :=
  (μ.measurePreserving_natSampler).hasLaw.fun_comp hU

/-- Applying `μ.natSampler` to a random variable uniform on `Set.Ico (0 : ℝ) 1` produces a random
variable with law `μ`. -/
theorem hasLaw_natSampler_of_isUniform (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : pdf.IsUniform U (Ico (0 : ℝ) 1) P) :
    HasLaw (fun ω => μ.natSampler (U ω)) μ P := by
  rw [pdf.IsUniform, cond_volume_Ico_zero_one] at hU
  exact μ.hasLaw_natSampler_of_hasLaw hU

end NatSamplerLaw

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

section NatSamplerLaw

variable {β : Type*} [MeasurableSpace β]

/-- Each fiber of `κ.natSampler` pushes `volume.restrict (Set.Ico 0 1)` forward to `κ b`. -/
@[simp]
theorem map_natSampler_volume_Ico (κ : Kernel β ℕ) [IsMarkovKernel κ] (b : β) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (κ.natSampler b) = κ b :=
  (κ b).map_natSampler_volume_Ico

/-- Pairing the current state with `κ.natSampler` driven by independent uniform noise on
`Set.Ico (0 : ℝ) 1` realizes the composition-product `μ ⊗ₘ κ`. -/
theorem map_prod_natSampler_volume_Ico (κ : Kernel β ℕ) [IsMarkovKernel κ]
    (μ : Measure β) [SFinite μ] :
    (μ.prod (volume.restrict (Ico (0 : ℝ) 1))).map
        (fun p => (p.1, κ.natSampler p.1 p.2)) =
      μ ⊗ₘ κ := by
  have : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := ⟨by simp⟩
  exact κ.map_prod_eq_compProd_of_map (volume.restrict (Ico (0 : ℝ) 1)) κ.natSampler
    κ.measurable_uncurry_natSampler κ.map_natSampler_volume_Ico

end NatSamplerLaw

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

/-! ### Enumerated countable-state samplers -/

section CountableSampler

private def decodeNatEmbedding {α : Type*} [Nonempty α] (e : α ↪ ℕ) (k : ℕ) : α :=
  open Classical in
  if hk : k ∈ range e then hk.choose else argmin e

private theorem decodeNatEmbedding_apply {α : Type*} [Nonempty α] (e : α ↪ ℕ) (x : α) :
    decodeNatEmbedding e (e x) = x := by
  have hx : e x ∈ range e := ⟨x, rfl⟩
  simp only [decodeNatEmbedding, hx, ↓reduceDIte]
  exact e.injective hx.choose_spec

private theorem decodeNatEmbedding_zero {α : Type*} [Nonempty α] (e : α ↪ ℕ) :
    decodeNatEmbedding e 0 = argmin e := by
  by_cases h0 : 0 ∈ range e
  · simp only [decodeNatEmbedding, h0, ↓reduceDIte]
    apply e.injective
    have hspec : e h0.choose = 0 := h0.choose_spec
    have hle : e (argmin e) ≤ e h0.choose := argmin_le e h0.choose
    omega
  · simp [decodeNatEmbedding, h0]

/-- Cumulative-weight sampler of a measure `μ` on a nonempty state space `α` along an injective
enumeration `e : α ↪ ℕ`.

For a probability measure `μ` on a measurable-singleton space `α` and `u ∈ Set.Ico 0 1`, this
returns the unique state `x : α` whose cumulative-weight interval
`Set.Ico (μ.real {y | e y < e x}) (μ.real {y | e y ≤ e x})` contains `u`. Levels outside
`Set.Ico 0 1` return the first state `Function.argmin e` in the enumeration. -/
def countableSampler {α : Type*} [MeasurableSpace α] [Nonempty α] (μ : Measure α)
    (e : α ↪ ℕ) (u : ℝ) : α :=
  decodeNatEmbedding e ((μ.map e).natSampler u)

/-- Along the identity embedding `Function.Embedding.refl ℕ`, `countableSampler` agrees identically
with `natSampler`. -/
@[simp]
theorem countableSampler_refl (μ : Measure ℕ) :
    μ.countableSampler (.refl ℕ) = μ.natSampler := by
  funext u
  have hmap : μ.map (.refl ℕ : ℕ ↪ ℕ) = μ := Measure.map_id
  rw [countableSampler, hmap]
  exact decodeNatEmbedding_apply (.refl ℕ) (μ.natSampler u)

variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- Negative levels return the first state `Function.argmin e` of the enumeration. -/
theorem countableSampler_of_neg (μ : Measure α) (e : α ↪ ℕ) {u : ℝ} (hu : u < 0) :
    μ.countableSampler e u = argmin e := by
  rw [countableSampler, (μ.map e).natSampler_of_neg hu, decodeNatEmbedding_zero]

/-- Sampling the zero measure returns `Function.argmin e`. -/
@[simp]
theorem countableSampler_zero_measure (e : α ↪ ℕ) (u : ℝ) :
    (0 : Measure α).countableSampler e u = argmin e := by
  rw [countableSampler, Measure.map_zero, natSampler_zero_measure, decodeNatEmbedding_zero]

section MeasurableSingleton

variable [MeasurableSingletonClass α]

/-- For a probability measure `μ`, levels `1 ≤ u` return `Function.argmin e`. -/
theorem countableSampler_of_one_le (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : 1 ≤ u) :
    μ.countableSampler e u = argmin e := by
  have : Countable α := e.injective.countable
  have : IsProbabilityMeasure (μ.map e) :=
    (isProbabilityMeasure_map_iff (measurable_of_countable e).aemeasurable).mpr inferInstance
  rw [countableSampler, (μ.map e).natSampler_of_one_le hu, decodeNatEmbedding_zero]

omit [Nonempty α] in
/-- Every level strictly below `1` is strictly exceeded by a cumulative mass along `e`. -/
theorem exists_lt_measureReal_le_of_lt_one (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : u < 1) :
    ∃ x : α, u < μ.real {y | e y ≤ e x} := by
  have : Countable α := e.injective.countable
  have he : Measurable e := measurable_of_countable e
  have : IsProbabilityMeasure (μ.map e) :=
    (isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  set k := (μ.map e).natSampler (max 0 u)
  have hmem : max 0 u ∈ Ico (0 : ℝ) 1 := ⟨le_max_left 0 u, max_lt zero_lt_one hu⟩
  have hpos : 0 < (μ.map e) {k} := (μ.map e).measure_singleton_natSampler_pos hmem
  rw [Measure.map_apply he .of_discrete] at hpos
  obtain ⟨x, hx⟩ : (e ⁻¹' {k}).Nonempty := nonempty_iff_ne_empty.mpr fun hemp => by
    rw [hemp, measure_empty] at hpos
    exact lt_irrefl 0 hpos
  have hk_eq : e x = k := hx
  refine ⟨x, ?_⟩
  have hhigh : max 0 u < (μ.map e).real (Iic k) :=
    (((μ.map e).natSampler_eq_iff hmem k).mp rfl).2
  rw [← hk_eq, map_measureReal_apply he .of_discrete] at hhigh
  exact (le_max_right 0 u).trans_lt hhigh

/-- Encoding `μ.countableSampler e u` recovers `(μ.map e).natSampler u` on `Set.Ico 0 1`. -/
theorem apply_countableSampler_eq_natSampler (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    e (μ.countableSampler e u) = (μ.map e).natSampler u := by
  have : Countable α := e.injective.countable
  have he : Measurable e := measurable_of_countable e
  have : IsProbabilityMeasure (μ.map e) :=
    (isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  set k := (μ.map e).natSampler u
  have hpos : 0 < (μ.map e) {k} := (μ.map e).measure_singleton_natSampler_pos hu
  rw [Measure.map_apply he .of_discrete] at hpos
  have hne : (e ⁻¹' {k}).Nonempty := nonempty_iff_ne_empty.mpr fun hemp => by
    rw [hemp, measure_empty] at hpos
    exact lt_irrefl 0 hpos
  have hk_range : k ∈ range e := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx⟩
  simp only [countableSampler, decodeNatEmbedding, k, hk_range, ↓reduceDIte]
  exact hk_range.choose_spec

/-- **Half-open cumulative-interval characterization along an enumeration.** For `u ∈ Set.Ico 0 1`,
`μ.countableSampler e u = x` holds if and only if `u` lies in
`Set.Ico (μ.real {y | e y < e x}) (μ.real {y | e y ≤ e x})`. -/
@[simp]
theorem countableSampler_eq_iff (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (x : α) :
    μ.countableSampler e u = x ↔
      μ.real {y | e y < e x} ≤ u ∧ u < μ.real {y | e y ≤ e x} := by
  have : Countable α := e.injective.countable
  have he : Measurable e := measurable_of_countable e
  have : IsProbabilityMeasure (μ.map e) :=
    (isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  rw [← e.injective.eq_iff, μ.apply_countableSampler_eq_natSampler e hu,
    (μ.map e).natSampler_eq_iff hu (e x),
    map_measureReal_apply he .of_discrete, map_measureReal_apply he .of_discrete]
  rfl

/-- On `Set.Ico 0 1`, `μ.countableSampler e u` is the state of minimal index in `e` whose
cumulative mass strictly exceeds `u`. -/
theorem countableSampler_eq_argminOn (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    μ.countableSampler e u =
      argminOn e {x : α | u < μ.real {y | e y ≤ e x}}
        (μ.exists_lt_measureReal_le_of_lt_one e hu.2) := by
  set s := {x : α | u < μ.real {y | e y ≤ e x}}
  set hs := μ.exists_lt_measureReal_le_of_lt_one e hu.2
  set x₀ := argminOn e s hs
  have hx₀_mem : u < μ.real {y | e y ≤ e x₀} := argminOn_mem e s hs
  rw [μ.countableSampler_eq_iff e hu x₀]
  refine ⟨?_, hx₀_mem⟩
  by_contra! hlt
  obtain ⟨hlow, hhigh⟩ := (μ.countableSampler_eq_iff e hu (μ.countableSampler e u)).mp rfl
  have hlt_idx : e (μ.countableSampler e u) < e x₀ := by
    by_contra! hge
    have hmono : μ.real {y | e y < e x₀} ≤ μ.real {y | e y < e (μ.countableSampler e u)} :=
      measureReal_mono fun y hy => lt_of_lt_of_le hy hge
    exact (hlt.trans_le hmono).not_ge hlow
  exact hlt_idx.not_ge (argminOn_le e s hhigh)

omit [Nonempty α] in
/-- Cumulative mass along `e` up to `x` splits into the strict lower cumulative mass plus the atom
at `x`. -/
theorem measureReal_le_embedding_eq_add_singleton (μ : Measure α) [IsFiniteMeasure μ]
    (e : α ↪ ℕ) (x : α) :
    μ.real {y | e y ≤ e x} = μ.real {y | e y < e x} + μ.real {x} := by
  have : Countable α := e.injective.countable
  have hsplit : {y : α | e y ≤ e x} = {y : α | e y < e x} ∪ {x} := by
    ext y
    simp only [mem_ofPred_eq, mem_union, mem_singleton_iff, Nat.le_iff_lt_or_eq, e.injective.eq_iff]
  have hdisj : Disjoint {y : α | e y < e x} ({x} : Set α) := by
    simp [disjoint_singleton_right]
  rw [hsplit, measureReal_union hdisj .of_discrete]

/-- The preimage of `{x}` under `μ.countableSampler e` inside `Set.Ico 0 1` is the half-open
interval `Set.Ico (μ.real {y | e y < e x}) (μ.real {y | e y ≤ e x})`. -/
theorem preimage_countableSampler_singleton_inter_Ico (μ : Measure α) [IsProbabilityMeasure μ]
    (e : α ↪ ℕ) (x : α) :
    μ.countableSampler e ⁻¹' {x} ∩ Ico (0 : ℝ) 1 =
      Ico (μ.real {y | e y < e x}) (μ.real {y | e y ≤ e x}) := by
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ico]
  constructor
  · rintro ⟨rfl, hu0, hu1⟩
    exact (μ.countableSampler_eq_iff e ⟨hu0, hu1⟩ _).mp rfl
  · rintro ⟨hlow, hhigh⟩
    have hu0 : 0 ≤ u := measureReal_nonneg.trans hlow
    have hu1 : u < 1 := hhigh.trans_le measureReal_le_one
    exact ⟨(μ.countableSampler_eq_iff e ⟨hu0, hu1⟩ x).mpr ⟨hlow, hhigh⟩, hu0, hu1⟩

/-- Every state sampled on `Set.Ico 0 1` has strictly positive mass. -/
theorem measure_singleton_countableSampler_pos (μ : Measure α) [IsProbabilityMeasure μ]
    (e : α ↪ ℕ) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    0 < μ {μ.countableSampler e u} := by
  obtain ⟨hlow, hhigh⟩ := (μ.countableSampler_eq_iff e hu (μ.countableSampler e u)).mp rfl
  rw [μ.measureReal_le_embedding_eq_add_singleton e] at hhigh
  have hreal : 0 < μ.real {μ.countableSampler e u} := by linarith
  exact pos_iff_ne_zero.mpr fun h0 => hreal.ne' ((measureReal_eq_zero_iff).mpr h0)

/-- Zero-weight states in `α` are never sampled on `Set.Ico 0 1`. -/
theorem countableSampler_ne_of_measure_singleton_eq_zero (μ : Measure α) [IsProbabilityMeasure μ]
    (e : α ↪ ℕ) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) {x : α} (hx : μ {x} = 0) :
    μ.countableSampler e u ≠ x := by
  intro h
  have hpos := μ.measure_singleton_countableSampler_pos e hu
  rw [h, hx] at hpos
  exact lt_irrefl 0 hpos

/-- A zero-weight state in `α` has empty preimage under `countableSampler` in `Set.Ico 0 1`. -/
@[simp]
theorem preimage_countableSampler_singleton_inter_Ico_of_measure_eq_zero (μ : Measure α)
    [IsProbabilityMeasure μ] (e : α ↪ ℕ) {x : α} (hx : μ {x} = 0) :
    μ.countableSampler e ⁻¹' {x} ∩ Ico (0 : ℝ) 1 = ∅ := by
  rw [μ.preimage_countableSampler_singleton_inter_Ico,
    μ.measureReal_le_embedding_eq_add_singleton, (measureReal_eq_zero_iff).mpr hx,
    add_zero, Ico_self]

/-- At the left endpoint `u = 0`, `μ.countableSampler e 0` selects the state of positive mass with
least index under `e`. -/
theorem minimalFor_pos_countableSampler_zero (μ : Measure α) [IsProbabilityMeasure μ]
    (e : α ↪ ℕ) :
    MinimalFor (fun x => 0 < μ {x}) e (μ.countableSampler e 0) := by
  have : Countable α := e.injective.countable
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  refine ⟨μ.measure_singleton_countableSampler_pos e h0, fun y hy _ => ?_⟩
  by_contra! hlt
  obtain ⟨hlow, _⟩ := (μ.countableSampler_eq_iff e h0 (μ.countableSampler e 0)).mp rfl
  have hy_real : 0 < μ.real {y} := ENNReal.toReal_pos hy.ne' (measure_ne_top μ {y})
  have hle : μ.real {y} ≤ μ.real {z | e z < e (μ.countableSampler e 0)} :=
    measureReal_mono (singleton_subset_iff.mpr hlt)
  exact (hy_real.trans_le hle).not_ge hlow

/-- Right-constancy of `countableSampler` on each cumulative step: if `u ∈ Set.Ico 0 1`, then
`μ.countableSampler e` stays constant on
`Set.Ico u (μ.real {y | e y ≤ e (μ.countableSampler e u)})`. -/
theorem countableSampler_eq_of_mem_Ico (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u v : ℝ} (hu : u ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Ico u (μ.real {y | e y ≤ e (μ.countableSampler e u)})) :
    μ.countableSampler e v = μ.countableSampler e u := by
  have hv_Ico : v ∈ Ico (0 : ℝ) 1 := ⟨hu.1.trans hv.1, hv.2.trans_le measureReal_le_one⟩
  obtain ⟨hlow, _⟩ := (μ.countableSampler_eq_iff e hu (μ.countableSampler e u)).mp rfl
  exact (μ.countableSampler_eq_iff e hv_Ico (μ.countableSampler e u)).mpr ⟨hlow.trans hv.1, hv.2⟩

end MeasurableSingleton

/-! #### Finite and countably infinite partial-sum characterizations -/

/-- **Finite state space (`Fin n`) characterization.** Along `Fin.valEmbedding : Fin n ↪ ℕ`,
`μ.countableSampler` partitions `Set.Ico 0 1` by the finite partial sums over `Finset.Iio i` and
`Finset.Iic i`. -/
theorem countableSampler_fin_eq_iff {n : ℕ} [NeZero n] (μ : Measure (Fin n))
    [IsProbabilityMeasure μ] {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (i : Fin n) :
    μ.countableSampler Fin.valEmbedding u = i ↔
      ∑ j ∈ Finset.Iio i, μ.real {j} ≤ u ∧ u < ∑ j ∈ Finset.Iic i, μ.real {j} := by
  rw [μ.countableSampler_eq_iff Fin.valEmbedding hu i, sum_measureReal_singleton,
    sum_measureReal_singleton]
  have hlt : ({y : Fin n | Fin.valEmbedding y < Fin.valEmbedding i} : Set (Fin n)) =
      (Finset.Iio i : Set (Fin n)) := by
    ext j
    simp [Fin.val_fin_lt]
  have hle : ({y : Fin n | Fin.valEmbedding y ≤ Fin.valEmbedding i} : Set (Fin n)) =
      (Finset.Iic i : Set (Fin n)) := by
    ext j
    simp [Fin.val_fin_le]
  rw [hlt, hle]

/-- **Explicit finite enumeration (`Fin n ≃ α`) characterization.** Given a finite enumeration
`s : Fin n ≃ α`, sampling along `s.symm.toEmbedding.trans Fin.valEmbedding` partitions
`Set.Ico 0 1` by the partial sums `∑ j ∈ Finset.Iio i, μ.real {s j}` and
`∑ j ∈ Finset.Iic i, μ.real {s j}`. -/
theorem countableSampler_equivFin_eq_iff {n : ℕ} [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Fin n ≃ α) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) (i : Fin n) :
    μ.countableSampler (s.symm.toEmbedding.trans Fin.valEmbedding) u = s i ↔
      ∑ j ∈ Finset.Iio i, μ.real {s j} ≤ u ∧ u < ∑ j ∈ Finset.Iic i, μ.real {s j} := by
  let e : α ↪ ℕ := s.symm.toEmbedding.trans Fin.valEmbedding
  have : Countable α := e.injective.countable
  rw [μ.countableSampler_eq_iff e hu (s i)]
  have hlt : {y : α | e y < e (s i)} = ((Finset.Iio i).map s.toEmbedding : Set α) := by
    ext y
    simp only [e, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Fin.valEmbedding_apply,
      Equiv.symm_apply_apply, mem_ofPred_eq, Finset.coe_map, mem_image, Finset.mem_coe,
      Finset.mem_Iio, Fin.val_fin_lt]
    exact ⟨fun h => ⟨s.symm y, h, s.apply_symm_apply y⟩,
      fun ⟨j, hj, hy⟩ => hy ▸ (s.symm_apply_apply j).symm ▸ hj⟩
  have hle : {y : α | e y ≤ e (s i)} = ((Finset.Iic i).map s.toEmbedding : Set α) := by
    ext y
    simp only [e, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Fin.valEmbedding_apply,
      Equiv.symm_apply_apply, mem_ofPred_eq, Finset.coe_map, mem_image, Finset.mem_coe,
      Finset.mem_Iic, Fin.val_fin_le]
    exact ⟨fun h => ⟨s.symm y, h, s.apply_symm_apply y⟩,
      fun ⟨j, hj, hy⟩ => hy ▸ (s.symm_apply_apply j).symm ▸ hj⟩
  rw [hlt, hle, ← sum_measureReal_singleton, ← sum_measureReal_singleton, Finset.sum_map,
    Finset.sum_map]
  rfl

/-- **Explicit countably infinite enumeration (`ℕ ≃ α`) characterization.** Given a bijection
`s : ℕ ≃ α`, sampling along `s.symm.toEmbedding` partitions `Set.Ico 0 1` by the finite prefix sums
`∑ j ∈ Finset.range k, μ.real {s j}` and `∑ j ∈ Finset.range (k + 1), μ.real {s j}`. -/
theorem countableSampler_equivNat_eq_iff [MeasurableSingletonClass α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : ℕ ≃ α) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (k : ℕ) :
    μ.countableSampler s.symm.toEmbedding u = s k ↔
      ∑ j ∈ Finset.range k, μ.real {s j} ≤ u ∧
        u < ∑ j ∈ Finset.range (k + 1), μ.real {s j} := by
  have : Countable α := s.symm.injective.countable
  rw [μ.countableSampler_eq_iff s.symm.toEmbedding hu (s k)]
  have hlt : {y : α | s.symm.toEmbedding y < s.symm.toEmbedding (s k)} =
      ((Finset.range k).map s.toEmbedding : Set α) := by
    ext y
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply, mem_ofPred_eq, Finset.coe_map,
      mem_image, Finset.mem_coe, Finset.mem_range]
    exact ⟨fun h => ⟨s.symm y, h, s.apply_symm_apply y⟩,
      fun ⟨j, hj, hy⟩ => hy ▸ (s.symm_apply_apply j).symm ▸ hj⟩
  have hle : {y : α | s.symm.toEmbedding y ≤ s.symm.toEmbedding (s k)} =
      ((Finset.range (k + 1)).map s.toEmbedding : Set α) := by
    ext y
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply, mem_ofPred_eq, Finset.coe_map,
      mem_image, Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h => ⟨s.symm y, h, s.apply_symm_apply y⟩,
      fun ⟨j, hj, hy⟩ => hy ▸ (s.symm_apply_apply j).symm ▸ hj⟩
  rw [hlt, hle, ← sum_measureReal_singleton, ← sum_measureReal_singleton, Finset.sum_map,
    Finset.sum_map]
  rfl

end CountableSampler

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

section CountableSampler

variable {β α : Type*} [MeasurableSpace β] [MeasurableSpace α] [Nonempty α]

/-- Fiberwise cumulative-weight sampler of a kernel `κ : Kernel β α` along an injective enumeration
`e : α ↪ ℕ`. -/
def countableSampler (κ : Kernel β α) (e : α ↪ ℕ) (b : β) (u : ℝ) : α :=
  (κ b).countableSampler e u

/-- `Kernel.countableSampler` evaluates `Measure.countableSampler` on each fiber `κ b`. -/
@[simp]
theorem countableSampler_apply (κ : Kernel β α) (e : α ↪ ℕ) (b : β) (u : ℝ) :
    κ.countableSampler e b u = (κ b).countableSampler e u := (rfl)

/-- Along `Function.Embedding.refl ℕ`, `Kernel.countableSampler` agrees with `Kernel.natSampler`. -/
@[simp]
theorem countableSampler_refl (κ : Kernel β ℕ) :
    κ.countableSampler (.refl ℕ) = κ.natSampler := by
  funext b u
  simp

/-- For a kernel constructed from row PMFs `Kernel.ofPMF p`, `countableSampler` samples each row
PMF `(p b).toMeasure`. -/
theorem countableSampler_ofPMF [Countable β] [MeasurableSingletonClass β] (p : β → PMF α)
    (e : α ↪ ℕ) (b : β) (u : ℝ) :
    (Kernel.ofPMF p).countableSampler e b u = (p b).toMeasure.countableSampler e u := by
  rw [countableSampler_apply, ofPMF_apply]

variable [MeasurableSingletonClass α]

/-- `Kernel.countableSampler` is jointly measurable in the current state `b : β` and uniform level
`u : ℝ`, for any measurable space `β` and any kernel `κ : Kernel β α`. -/
@[fun_prop]
theorem measurable_uncurry_countableSampler (κ : Kernel β α) (e : α ↪ ℕ) :
    Measurable (uncurry (κ.countableSampler e)) := by
  have : Countable α := e.injective.countable
  have he : Measurable e := measurable_of_countable e
  have hdec : Measurable (MeasureTheory.Measure.decodeNatEmbedding e) :=
    measurable_of_countable _
  have heq : uncurry (κ.countableSampler e) =
      MeasureTheory.Measure.decodeNatEmbedding e ∘ uncurry (κ.map e).natSampler := by
    funext ⟨b, u⟩
    simp [countableSampler, MeasureTheory.Measure.countableSampler, Kernel.map_apply κ he b]
  rw [heq]
  exact hdec.comp (κ.map e).measurable_uncurry_natSampler

/-- For each fixed state `b : β`, `κ.countableSampler e b` is measurable. -/
@[fun_prop]
theorem measurable_countableSampler (κ : Kernel β α) (e : α ↪ ℕ) (b : β) :
    Measurable (κ.countableSampler e b) :=
  (κ.measurable_uncurry_countableSampler e).of_uncurry_left

end CountableSampler

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

section CountableSamplerLaw

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]

/-- `Measure.countableSampler` is measurable. -/
@[fun_prop]
theorem measurable_countableSampler (μ : Measure α) (e : α ↪ ℕ) :
    Measurable (μ.countableSampler e) :=
  (ProbabilityTheory.Kernel.const Unit μ).measurable_countableSampler e ()

/-- **Inverse transform sampling on a countable space from `[0, 1)`.** Along any injective
enumeration `e : α ↪ ℕ`, `μ.countableSampler e` pushes Lebesgue measure restricted to
`Set.Ico (0 : ℝ) 1` forward to `μ`. -/
@[simp]
theorem map_countableSampler_volume_Ico (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (μ.countableSampler e) = μ := by
  have : Countable α := e.injective.countable
  apply Measure.ext_iff_singleton.mpr
  intro x
  rw [Measure.map_apply (μ.measurable_countableSampler e) .of_discrete,
    Measure.restrict_apply (μ.measurable_countableSampler e .of_discrete),
    μ.preimage_countableSampler_singleton_inter_Ico e x, Real.volume_Ico,
    μ.measureReal_le_embedding_eq_add_singleton e x, add_sub_cancel_left,
    ofReal_measureReal]

/-- `μ.countableSampler e` is measure-preserving from `volume.restrict (Set.Ico 0 1)` to `μ`. -/
theorem measurePreserving_countableSampler (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ) :
    MeasurePreserving (μ.countableSampler e) (volume.restrict (Ico (0 : ℝ) 1)) μ :=
  ⟨μ.measurable_countableSampler e, μ.map_countableSampler_volume_Ico e⟩

/-- Applying `μ.countableSampler e` to any random variable with law `volume.restrict (Set.Ico 0 1)`
produces a random variable with law `μ`. -/
theorem hasLaw_countableSampler_of_hasLaw (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U (volume.restrict (Ico (0 : ℝ) 1)) P) :
    HasLaw (fun ω => μ.countableSampler e (U ω)) μ P :=
  (μ.measurePreserving_countableSampler e).hasLaw.fun_comp hU

/-- Applying `μ.countableSampler e` to a random variable uniform on `Set.Ico (0 : ℝ) 1` produces a
random variable with law `μ`. -/
theorem hasLaw_countableSampler_of_isUniform (μ : Measure α) [IsProbabilityMeasure μ]
    (e : α ↪ ℕ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : pdf.IsUniform U (Ico (0 : ℝ) 1) P) :
    HasLaw (fun ω => μ.countableSampler e (U ω)) μ P := by
  rw [pdf.IsUniform, cond_volume_Ico_zero_one] at hU
  exact μ.hasLaw_countableSampler_of_hasLaw e hU

end CountableSamplerLaw

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

section CountableSamplerLaw

variable {β α : Type*} [MeasurableSpace β] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Nonempty α]

/-- Each fiber of `κ.countableSampler e` pushes `volume.restrict (Set.Ico 0 1)` forward to `κ b`. -/
@[simp]
theorem map_countableSampler_volume_Ico (κ : Kernel β α) [IsMarkovKernel κ] (e : α ↪ ℕ) (b : β) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (κ.countableSampler e b) = κ b :=
  (κ b).map_countableSampler_volume_Ico e

/-- Pairing the current state with `κ.countableSampler e` driven by independent uniform noise on
`Set.Ico (0 : ℝ) 1` realizes the composition-product `μ ⊗ₘ κ`. -/
theorem map_prod_countableSampler_volume_Ico (κ : Kernel β α) [IsMarkovKernel κ] (e : α ↪ ℕ)
    (μ : Measure β) [SFinite μ] :
    (μ.prod (volume.restrict (Ico (0 : ℝ) 1))).map
        (fun p => (p.1, κ.countableSampler e p.1 p.2)) =
      μ ⊗ₘ κ := by
  have : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := ⟨by simp⟩
  exact κ.map_prod_eq_compProd_of_map (volume.restrict (Ico (0 : ℝ) 1)) (κ.countableSampler e)
    (κ.measurable_uncurry_countableSampler e) (κ.map_countableSampler_volume_Ico e)

end CountableSamplerLaw

end ProbabilityTheory.Kernel

namespace Matrix.rowStochastic

/-- **Finite stochastic-matrix transition sampler.** For a row-stochastic matrix `M` on `Fin n` and
`u ∈ Set.Ico 0 1`, `(toKernel M).countableSampler Fin.valEmbedding i u = j` holds if and only if
`u` lies between the strict and weak partial sums of row `i` up to column `j`. -/
theorem countableSampler_toKernel_fin_eq_iff {n : ℕ} [NeZero n]
    (M : Matrix.rowStochastic ℝ≥0 (Fin n)) (i : Fin n) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1)
    (j : Fin n) :
    (toKernel M).countableSampler Fin.valEmbedding i u = j ↔
      ∑ k ∈ Finset.Iio j, (M.val i k : ℝ) ≤ u ∧ u < ∑ k ∈ Finset.Iic j, (M.val i k : ℝ) := by
  rw [ProbabilityTheory.Kernel.countableSampler_apply,
    (toKernel M i).countableSampler_fin_eq_iff hu j]
  have hentry (k : Fin n) : (toKernel M i).real {k} = (M.val i k : ℝ) := by
    rw [measureReal_def, toKernel_apply_singleton, ENNReal.coe_toReal]
  simp_rw [hentry]

end Matrix.rowStochastic
