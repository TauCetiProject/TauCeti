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
* on `Set.Ico (0 : ℝ) 1`, the natural-number sampler `μ.natSampler` agrees identically with the
  right-continuous `MeasureTheory.Measure.upperQuantile` of `(μ.map Nat.cast)`, while the
  left-continuous `MeasureTheory.Measure.quantile` convention `(a, b]` agrees off `{0}` and the
  countable set of cumulative jump levels, hence almost everywhere on `Set.Ico (0 : ℝ) 1`.

Defining `MeasureTheory.Measure.natSampler` directly via `Nat.find` on native cumulative masses
`μ.real (Set.Iic k)` rather than through `ProbabilityTheory.cdf` avoids the probability-measure
normalization fallback of `condCDF`, so `ProbabilityTheory.Kernel.natSampler` and
`ProbabilityTheory.Kernel.countableSampler` are jointly measurable for every kernel `κ` without
assuming `IsMarkovKernel κ`.

Parameterizing enumerations by `e : α ↪ ℕ` unifies finite state spaces (`Fin n` via
`Fin.valEmbedding` and finite bijections `Fin n ≃ α`), countably infinite state spaces (`ℕ` via
`Function.Embedding.refl ℕ`, where `countableSampler_refl` reduces to `natSampler`, and bijections
`ℕ ≃ α`), and arbitrary countable measurable-singleton spaces, without requiring any topology or
standard Borel structure on the state space. Applying the construction fiberwise to a kernel
`κ : Kernel β α` produces a sampler `κ.countableSampler e : β → ℝ → α` that is jointly measurable
in `(b, u) : β × ℝ` for every measurable space `β` and every kernel `κ`; when `[IsMarkovKernel κ]`
and `[SFinite μ]`, pairing the current state with independent uniform noise on `Set.Ico (0 : ℝ) 1`
realizes the composition-product `μ ⊗ₘ κ`.

## Main definitions

* `MeasureTheory.Measure.natSampler`: cumulative-weight sampler `ℝ → ℕ` for a measure on `ℕ`.
* `ProbabilityTheory.Kernel.natSampler`: fiberwise sampler `β → ℝ → ℕ` for a kernel into `ℕ`.
* `MeasureTheory.Measure.countableSampler`: cumulative-weight sampler `ℝ → α` along `e : α ↪ ℕ`.
* `ProbabilityTheory.Kernel.countableSampler`: jointly measurable sampler `β → ℝ → α` for a kernel
  `κ : Kernel β α` along `e : α ↪ ℕ`.

## Main results

* `MeasureTheory.Measure.natSampler_eq_iff`, `MeasureTheory.Measure.countableSampler_eq_iff`:
  half-open cumulative-interval characterizations on `Set.Ico (0 : ℝ) 1`.
* `MeasureTheory.Measure.countableSampler_ne_of_measure_singleton_eq_zero`: zero-weight states are
  never sampled on `Set.Ico (0 : ℝ) 1`.
* `MeasureTheory.Measure.upperQuantile_map_natCast_eq_natSampler`,
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

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.1.
* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., American Mathematical
  Society (2017), §1.2.
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

section NatSampler

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

/-- Every state sampled on `Set.Ico 0 1` has strictly positive mass. -/
theorem measure_singleton_natSampler_pos (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) :
    0 < μ {μ.natSampler u} := by
  obtain ⟨hlow, hhigh⟩ := (μ.natSampler_eq_iff hu (μ.natSampler u)).mp rfl
  rw [← Iio_union_right, measureReal_union (by simp) .of_discrete] at hhigh
  have hreal : 0 < μ.real {μ.natSampler u} := by linarith
  exact pos_iff_ne_zero.mpr fun h0 => hreal.ne' ((measureReal_eq_zero_iff).mpr h0)

/-- **Endpoint convention bridge (`upperQuantile`).** On the half-open unit interval `Set.Ico 0 1`,
the real cast of `μ.natSampler u` equals the right-continuous `upperQuantile` of `μ` cast to `ℝ`. -/
theorem upperQuantile_map_natCast_eq_natSampler (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) :
    (μ.map (Nat.cast : ℕ → ℝ)).upperQuantile u = μ.natSampler u := by
  set k := μ.natSampler u
  obtain ⟨hlow, hhigh⟩ := (μ.natSampler_eq_iff hu k).mp rfl
  have hk_mem : u < cdf (μ.map (Nat.cast : ℕ → ℝ)) k := by
    simpa only [cdf_map_natCast μ (Nat.cast_nonneg k), Nat.floor_natCast] using hhigh
  have hlb : ∀ x ∈ {x : ℝ | u < cdf (μ.map (Nat.cast : ℕ → ℝ)) x}, (k : ℝ) ≤ x := by
    intro x hx
    by_contra! hxk
    rcases lt_or_ge x 0 with hx0 | hx0
    · rw [mem_ofPred_eq, cdf_map_natCast_of_neg μ hx0] at hx
      exact hx.not_ge hu.1
    · rw [mem_ofPred_eq, cdf_map_natCast μ hx0] at hx
      have hfloor : ⌊x⌋₊ < k := (Nat.floor_lt hx0).mpr hxk
      exact (hx.trans_le (measureReal_mono (Iic_subset_Iio.mpr hfloor))).not_ge hlow
  rw [upperQuantile_def]
  exact le_antisymm (csInf_le ⟨k, hlb⟩ hk_mem) (le_csInf ⟨k, hk_mem⟩ hlb)

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

/-- `Kernel.natSampler` is jointly measurable in the source point and uniform level, for any
measurable space `β` and any kernel `κ : Kernel β ℕ`. -/
@[fun_prop]
theorem measurable_uncurry_natSampler (κ : Kernel β ℕ) :
    Measurable (uncurry κ.natSampler) := by
  classical
  have hcum (j : ℕ) : Measurable fun p : β × ℝ => (κ p.1).real (Iic j) := by
    simp_rw [measureReal_def]
    exact ((κ.measurable_coe .of_discrete).ennreal_toReal).comp measurable_fst
  let s : Set (β × ℝ) := {p | 0 ≤ p.2 ∧ ∃ m : ℕ, p.2 < (κ p.1).real (Iic m)}
  have hs : MeasurableSet s := by
    have heq : s = {p | (0 : ℝ) ≤ p.2} ∩ ⋃ m : ℕ, {p | p.2 < (κ p.1).real (Iic m)} := by
      ext p
      simp [s]
    rw [heq]
    exact (measurableSet_le measurable_const measurable_snd).inter
      (MeasurableSet.iUnion fun m => measurableSet_lt measurable_snd (hcum m))
  have hfind : Measurable fun q : s => Nat.find q.2.2 :=
    measurable_find (fun q => q.2.2) fun k =>
      measurableSet_lt (measurable_snd.comp measurable_subtype_coe)
        ((hcum k).comp measurable_subtype_coe)
  convert Measurable.dite (s := s) (g := fun _ => 0) hfind measurable_const hs with p
  by_cases hp : 0 ≤ p.2 ∧ ∃ m : ℕ, p.2 < (κ p.1).real (Iic m) <;>
    simp [uncurry, natSampler, Measure.natSampler, s, hp]

/-- For each fixed state `b`, `κ.natSampler b` is measurable. -/
@[fun_prop]
theorem measurable_natSampler (κ : Kernel β ℕ) (b : β) : Measurable (κ.natSampler b) :=
  (κ.measurable_uncurry_natSampler).of_uncurry_left

end NatSampler

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

/-- `Measure.natSampler` is a measurable map `ℝ → ℕ`. -/
@[fun_prop]
theorem measurable_natSampler (μ : Measure ℕ) : Measurable μ.natSampler :=
  (ProbabilityTheory.Kernel.const Unit μ).measurable_natSampler ()

/-! ### Enumerated countable-state samplers -/

section CountableSampler

/-- Cumulative-weight sampler of a measure `μ` on a nonempty state space `α` along an injective
enumeration `e : α ↪ ℕ`.

For a probability measure `μ` on a measurable-singleton space `α` and `u ∈ Set.Ico 0 1`, this
returns the unique state `x : α` whose cumulative-weight interval
`Set.Ico (μ.real {y | e y < e x}) (μ.real {y | e y ≤ e x})` contains `u`. Levels outside
`Set.Ico 0 1` return the fallback state `Function.invFun e 0`. -/
def countableSampler {α : Type*} [MeasurableSpace α] [Nonempty α] (μ : Measure α)
    (e : α ↪ ℕ) (u : ℝ) : α :=
  Function.invFun e ((μ.map e).natSampler u)

/-- Along the identity embedding `Function.Embedding.refl ℕ`, `countableSampler` agrees identically
with `natSampler`. -/
@[simp]
theorem countableSampler_refl (μ : Measure ℕ) :
    μ.countableSampler (.refl ℕ) = μ.natSampler := by
  funext u
  rw [countableSampler, show μ.map (.refl ℕ : ℕ ↪ ℕ) = μ from Measure.map_id]
  exact Function.leftInverse_invFun (Embedding.refl ℕ).injective (μ.natSampler u)

variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- Negative levels return the fallback state `Function.invFun e 0`. -/
theorem countableSampler_of_neg (μ : Measure α) (e : α ↪ ℕ) {u : ℝ} (hu : u < 0) :
    μ.countableSampler e u = Function.invFun e 0 := by
  rw [countableSampler, (μ.map e).natSampler_of_neg hu]

/-- Sampling the zero measure returns the fallback state `Function.invFun e 0`. -/
@[simp]
theorem countableSampler_zero_measure (e : α ↪ ℕ) (u : ℝ) :
    (0 : Measure α).countableSampler e u = Function.invFun e 0 := by
  rw [countableSampler, Measure.map_zero, natSampler_zero_measure]

/-- For a probability measure `μ`, levels `1 ≤ u` return the fallback state
`Function.invFun e 0`. -/
theorem countableSampler_of_one_le (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : 1 ≤ u) :
    μ.countableSampler e u = Function.invFun e 0 := by
  rw [countableSampler, (μ.map e).natSampler_of_one_le hu]

section MeasurableSingleton

variable [MeasurableSingletonClass α]

omit [Nonempty α] in
/-- On `Set.Ico 0 1`, `(μ.map e).natSampler u` lies in the range of `e`. -/
theorem natSampler_map_mem_range (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    (μ.map e).natSampler u ∈ range e := by
  have : Countable α := e.injective.countable
  have hpos : 0 < (μ.map e) {(μ.map e).natSampler u} :=
    (μ.map e).measure_singleton_natSampler_pos hu
  rw [Measure.map_apply (measurable_of_countable e) .of_discrete] at hpos
  obtain ⟨x, hx⟩ : (e ⁻¹' {(μ.map e).natSampler u}).Nonempty :=
    nonempty_iff_ne_empty.mpr fun hemp => by
      rw [hemp, measure_empty] at hpos
      exact lt_irrefl 0 hpos
  exact ⟨x, hx⟩

omit [Nonempty α] in
/-- Every level strictly below `1` is strictly exceeded by a cumulative mass along `e`. -/
theorem exists_lt_measureReal_le_of_lt_one (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : u < 1) :
    ∃ x : α, u < μ.real {y | e y ≤ e x} := by
  have : Countable α := e.injective.countable
  have hmem : max 0 u ∈ Ico (0 : ℝ) 1 := ⟨le_max_left 0 u, max_lt zero_lt_one hu⟩
  obtain ⟨x, hx⟩ := μ.natSampler_map_mem_range e hmem
  refine ⟨x, ?_⟩
  have hhigh : max 0 u < (μ.map e).real (Iic (e x)) := by
    rw [hx]
    exact (((μ.map e).natSampler_eq_iff hmem _).mp rfl).2
  rw [map_measureReal_apply (measurable_of_countable e) .of_discrete] at hhigh
  exact (le_max_right 0 u).trans_lt hhigh

/-- Encoding `μ.countableSampler e u` recovers `(μ.map e).natSampler u` on `Set.Ico 0 1`. -/
theorem apply_countableSampler_eq_natSampler (μ : Measure α) [IsProbabilityMeasure μ] (e : α ↪ ℕ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    e (μ.countableSampler e u) = (μ.map e).natSampler u :=
  Function.invFun_eq (μ.natSampler_map_mem_range e hu)

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
  rw [← e.injective.eq_iff, μ.apply_countableSampler_eq_natSampler e hu,
    (μ.map e).natSampler_eq_iff hu (e x),
    map_measureReal_apply he .of_discrete, map_measureReal_apply he .of_discrete]
  simp only [preimage, mem_Iio, mem_Iic]

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

omit [Nonempty α] in
private theorem measureReal_setOf_symm_mem {ι : Type*} [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : ι ≃ α) (t : Finset ι) :
    μ.real {y : α | s.symm y ∈ t} = ∑ j ∈ t, μ.real {s j} := by
  have hset : {y : α | s.symm y ∈ t} = (t.map s.toEmbedding : Set α) := by
    ext y
    simp
  rw [hset, ← sum_measureReal_singleton, Finset.sum_map]
  simp only [Equiv.toEmbedding_apply]

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
  rw [μ.countableSampler_eq_iff e hu (s i)]
  simp only [e, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Fin.valEmbedding_apply,
    Equiv.symm_apply_apply, Fin.val_fin_lt, Fin.val_fin_le]
  simp only [← Finset.mem_Iio, ← Finset.mem_Iic, measureReal_setOf_symm_mem]

/-- **Explicit countably infinite enumeration (`ℕ ≃ α`) characterization.** Given a bijection
`s : ℕ ≃ α`, sampling along `s.symm.toEmbedding` partitions `Set.Ico 0 1` by the finite prefix sums
`∑ j ∈ Finset.range k, μ.real {s j}` and `∑ j ∈ Finset.range (k + 1), μ.real {s j}`. -/
theorem countableSampler_equivNat_eq_iff [MeasurableSingletonClass α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : ℕ ≃ α) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (k : ℕ) :
    μ.countableSampler s.symm.toEmbedding u = s k ↔
      ∑ j ∈ Finset.range k, μ.real {s j} ≤ u ∧
        u < ∑ j ∈ Finset.range (k + 1), μ.real {s j} := by
  rw [μ.countableSampler_eq_iff s.symm.toEmbedding hu (s k)]
  simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply, ← Nat.lt_succ_iff,
    ← Finset.mem_range, measureReal_setOf_symm_mem]

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
  have hinv : Measurable (Function.invFun e) := measurable_of_countable _
  have heq : uncurry (κ.countableSampler e) =
      Function.invFun e ∘ uncurry (κ.map e).natSampler := by
    funext ⟨b, u⟩
    simp [countableSampler, MeasureTheory.Measure.countableSampler, Kernel.map_apply κ he b]
  rw [heq]
  exact hinv.comp (κ.map e).measurable_uncurry_natSampler

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
    HasLaw (fun ω => μ.countableSampler e (U ω)) μ P :=
  μ.hasLaw_countableSampler_of_hasLaw e (by simpa [pdf.IsUniform, ProbabilityTheory.cond] using hU)

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
