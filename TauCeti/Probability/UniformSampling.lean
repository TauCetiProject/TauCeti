/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Alexander Richard Towell
-/
module

public import Mathlib.Probability.UniformOn
public import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Measure.Real
import TauCeti.Data.Fintype.Card.Embedding
import TauCeti.Probability.ConditionalProbability

/-!
# Uniform sampling with and without replacement

This file gives the finite sampling estimate underlying quantitative finite de Finetti theorems.
When the finite function space `ι → κ` is nonempty, a uniform random map `x : ι → κ` has two
coordinates collide with probability at most

`(Fintype.card ι).choose 2 / Fintype.card κ`.

The exact collision probability on a nonempty function space is
`1 - (Fintype.card κ).descFactorial (Fintype.card ι) / (Fintype.card κ) ^ Fintype.card ι`.
When the function space is empty, Mathlib's `uniformOn` is instead the zero measure; the union
bound remains valid under that convention, but the complement formula requires nonemptiness.

When `ι` and `κ` are finite, singletons of `κ` are measurable and injective maps exist,
conditioning the random map to be injective is uniform sampling without replacement.  The main
results compare every event under the uniform measures on all maps and on injective maps.  The
exact comparisons `uniformOn_injective_le_add` and `uniformOn_univ_le_injective_add`, whose error
term is the collision measure, hold for Mathlib's `uniformOn` for all types `ι` and `κ` and every
measurable structure on `κ`, including the degenerate cases where `uniformOn` is the zero measure
(no injective map exists, or the set of maps is infinite); without measurable singletons they
compare these measures, which need not be sampling probabilities.  The quantitative forms, with the
collision bound `(Fintype.card ι).choose 2 / Fintype.card κ` as error, assume finite types with
measurable singletons.  In the feasible case these inequalities are the coupling step used to
compare a finite exchangeable law with the product of its empirical measure.

The exact formula counts embeddings using Mathlib's `Fintype.card_embedding_eq`. The simpler
estimate is the classical union bound over unordered coordinate pairs, using
`measure_biUnion_finset_le` and `Fintype.card_product_filter_lt`. Both use Mathlib's
`ProbabilityTheory.uniformOn`; no sampling distribution is redefined here.

## Main results

* `uniformOn_not_injective_le`, `uniformOn_not_injective_le_one_sub_descFactorial_div_pow`, and
  their `.real` companions bound the uniform-measure mass of collisions;
* `descFactorial_div_pow_le_one` and `one_sub_descFactorial_div_pow_eq_ofReal` bound the
  injectivity probability `n.descFactorial m / n ^ m` by `1` and rewrite the collision error
  `1 - n.descFactorial m / n ^ m` from `ℝ≥0∞` to `ENNReal.ofReal` of its real form;
* `uniformOn_injective_apply_eq`, `uniformOn_not_injective_apply_eq`, and their `.real` forms
  compute the exact uniform-measure masses;
* `uniformOn_injective_eq_zero_of_isEmpty`,
  `uniformOn_injective_eq_uniformOn_univ_of_subsingleton`, and
  `uniformOn_not_injective_eq_zero_of_subsingleton` (with its `.real` companion) treat the
  infeasible and subsingleton-sample regimes;
* `uniformOn_injective_le_add` and `uniformOn_univ_le_injective_add` compare arbitrary events
  under the uniform measures on injective maps and on all maps (sampling without and with
  replacement, for finite types with measurable singletons); they specialise the conditioning
  comparisons `MeasureTheory.Measure.cond_inter_le_add_compl` and
  `MeasureTheory.Measure.cond_le_inter_add_compl` to the counting measure;
* `uniformOn_injective_le_add_choose_two_div` and
  `uniformOn_univ_le_injective_add_choose_two_div` give the quantitative forms.
* `uniformOn_injective_mem_range_and_mem_range` computes the probability that a uniform
  injective map hits two given distinct elements.

These comparisons feed quantitative finite de Finetti bounds.
-/

public section

noncomputable section

open Finset Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The real-valued mass of an event under a uniform measure is the ratio of its cardinality to
the cardinality of the sampling set. This also covers the zero measure when the sampling set is
empty or infinite, where both sides vanish. -/
theorem uniformOn_toReal {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (S T : Set Ω) :
    (uniformOn S T).toReal =
      (Nat.card {x : Ω // x ∈ S ∩ T} : ℝ) /
        (Nat.card {x : Ω // x ∈ S} : ℝ) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  rcases S.finite_or_infinite with hS | hS
  · simp [uniformOn, cond_apply hS.measurableSet, Measure.count_apply_finite _ hS,
      Measure.count_apply_finite _ (hS.inter_of_left T), ← Set.ncard_eq_toFinset_card,
      div_eq_inv_mul]
  · simp [uniformOn_eq_zero.2 (.inl hS), hS.ncard]

variable {ι κ : Type*}

section

variable [Fintype ι] [Fintype κ]

/-- The uniform-measure mass of injective maps is the number of ordered injections divided by
the number of maps. This is an injectivity probability when the function space is nonempty;
when the function space is empty, `uniformOn` is the zero measure and both sides are zero. -/
@[simp]
theorem uniformOn_injective_apply_eq [MeasurableSpace κ] [MeasurableSingletonClass κ] :
    uniformOn (Set.univ : Set (ι → κ)) {f | Function.Injective f} =
      (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  classical
  simp [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite _), ← Fintype.card_subtype,
    Fintype.card_subtype_injective]

/-- Real-valued form of `uniformOn_injective_apply_eq`. -/
@[simp]
theorem uniformOn_real_injective_apply_eq [MeasurableSpace κ] [MeasurableSingletonClass κ] :
    (uniformOn (Set.univ : Set (ι → κ))).real {f | Function.Injective f} =
      (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι := by
  simp [measureReal_def]

/-- The exact collision probability for a uniform random map on a nonempty finite function
space. The descending factorial counts ordered samples without replacement, so this retains
the overlap between pairwise collision events discarded by the union bound. -/
@[simp]
theorem uniformOn_not_injective_apply_eq [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [Nonempty (ι → κ)] :
    uniformOn (Set.univ : Set (ι → κ)) {f | ¬ Function.Injective f} =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  rw [← Set.compl_ofPred, prob_compl_eq_one_sub (Set.toFinite _).measurableSet,
    uniformOn_injective_apply_eq]

/-- Real-valued form of `uniformOn_not_injective_apply_eq`. -/
@[simp]
theorem uniformOn_real_not_injective_apply_eq [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [Nonempty (ι → κ)] :
    (uniformOn (Set.univ : Set (ι → κ))).real {f | ¬ Function.Injective f} =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι := by
  rw [← Set.compl_ofPred, probReal_compl_eq_one_sub (Set.toFinite _).measurableSet,
    uniformOn_real_injective_apply_eq]

/-- The injectivity probability `n.descFactorial m / n ^ m` of a uniform map from an `m`-element
type to an `n`-element type is at most `1`. -/
theorem descFactorial_div_pow_le_one (m n : ℕ) : (n.descFactorial m : ℝ) / (n : ℝ) ^ m ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Nat.descFactorial_le_pow n m) (by positivity)

/-- The collision error `1 - n.descFactorial m / n ^ m` in `ℝ≥0∞` is the `ENNReal.ofReal` of its
real counterpart. -/
theorem one_sub_descFactorial_div_pow_eq_ofReal (m n : ℕ) :
    1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m =
      ENNReal.ofReal (1 - n.descFactorial m / (n : ℝ) ^ m) := by
  have hle : (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m ≤ 1 :=
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Nat.descFactorial_le_pow n m)
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  congr 1
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hle)]
  simp

/-- Unconditional upper bound form of `uniformOn_not_injective_apply_eq`: when `ι → κ` is
nonempty the two sides are equal, and when `ι → κ` is empty the uniform measure is zero while
`1 - 0 / 0 = 1`. -/
theorem uniformOn_not_injective_le_one_sub_descFactorial_div_pow [MeasurableSpace κ]
    [MeasurableSingletonClass κ] :
    uniformOn (Set.univ : Set (ι → κ)) {f | ¬ Function.Injective f} ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty (ι → κ) with h | h
  · simp [Measure.eq_zero_of_isEmpty (uniformOn (Set.univ : Set (ι → κ)))]
  · exact uniformOn_not_injective_apply_eq.le

/-- Real-valued form of `uniformOn_not_injective_le_one_sub_descFactorial_div_pow`. -/
theorem uniformOn_real_not_injective_le_one_sub_descFactorial_div_pow [MeasurableSpace κ]
    [MeasurableSingletonClass κ] :
    (uniformOn (Set.univ : Set (ι → κ))).real {f | ¬ Function.Injective f} ≤
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty (ι → κ) with h | h
  · rw [Measure.eq_zero_of_isEmpty (uniformOn (Set.univ : Set (ι → κ))), measureReal_zero_apply]
    exact sub_nonneg.2 (descFactorial_div_pow_le_one _ _)
  · exact uniformOn_real_not_injective_apply_eq.le

end

section Degenerate

/-- When no embedding `ι ↪ κ` exists, there are no injective maps and the uniform measure on
injective selections is zero. -/
@[simp high]
theorem uniformOn_injective_eq_zero_of_isEmpty [MeasurableSpace κ] [IsEmpty (ι ↪ κ)] :
    uniformOn {f : ι → κ | Function.Injective f} = 0 := by
  have h : {f : ι → κ | Function.Injective f} = ∅ :=
    Set.eq_empty_of_forall_notMem fun f hf => isEmptyElim (⟨f, hf⟩ : ι ↪ κ)
  simp [h]

/-- On a subsingleton sample index, every map `ι → κ` is injective, so the uniform measure on
injective selections coincides with the uniform measure on all selections. -/
@[simp]
theorem uniformOn_injective_eq_uniformOn_univ_of_subsingleton [Subsingleton ι] [MeasurableSpace κ] :
    uniformOn {f : ι → κ | Function.Injective f} = uniformOn (Set.univ : Set (ι → κ)) := by
  congr 1
  exact Set.eq_univ_of_forall fun f => Function.injective_of_subsingleton f

/-- On a subsingleton sample index, no selection has a coordinate collision. -/
@[simp high]
theorem uniformOn_not_injective_eq_zero_of_subsingleton [Subsingleton ι] [MeasurableSpace κ]
    (s : Set (ι → κ)) :
    uniformOn s {f : ι → κ | ¬ Function.Injective f} = 0 := by
  have h : {f : ι → κ | ¬ Function.Injective f} = ∅ :=
    Set.eq_empty_of_forall_notMem fun f hf => hf (Function.injective_of_subsingleton f)
  simp [h]

/-- Real-valued form of `uniformOn_not_injective_eq_zero_of_subsingleton`. -/
@[simp high]
theorem uniformOn_real_not_injective_eq_zero_of_subsingleton [Subsingleton ι] [MeasurableSpace κ]
    (s : Set (ι → κ)) :
    (uniformOn s).real {f : ι → κ | ¬ Function.Injective f} = 0 := by
  simp [measureReal_def]

end Degenerate

section

variable [Fintype κ]

/-- Under uniform sampling with replacement, two distinct coordinates agree with probability
`1 / Fintype.card κ`.

The result is stated for arbitrary finite index and value types.  The only measurable structure
needed is discreteness of finite sets, expressed by `MeasurableSingletonClass`. -/
@[simp]
theorem uniformOn_apply_eq_apply [Finite ι] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [Nonempty κ]
    (i j : ι) (hij : i ≠ j) :
    uniformOn (Set.univ : Set (ι → κ)) {x | x i = x j} =
      1 / (Fintype.card κ : ℝ≥0∞) := by
  classical
  cases nonempty_fintype ι
  -- The `card κ ^ (card ι - 1)` maps identifying `i` and `j`, times `card κ`, are all maps.
  have hcard : Fintype.card κ * Set.ncard {x : ι → κ | x i = x j} =
      Fintype.card κ ^ Fintype.card ι := by
    rw [← Nat.card_coe_set_eq, Set.coe_ofPred, Nat.card_eq_fintype_card,
      Fintype.card_subtype_apply_eq_apply hij, ← pow_succ',
      Nat.sub_add_cancel (Fintype.card_pos_iff.2 ⟨i⟩)]
  rw [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite _),
    ← Set.ncard_eq_toFinset_card _, ENNReal.div_eq_div_iff (by simp) (by simp) (by simp) (by simp),
    Fintype.card_fun, mul_one]
  exact_mod_cast hcard

end

section

variable [Fintype ι]

variable (ι) in
private def coordinatePairs [LinearOrder ι] : Finset (ι × ι) :=
  Finset.univ.filter fun p => p.1 < p.2

private theorem mem_coordinatePairs [LinearOrder ι] (p : ι × ι) :
    p ∈ coordinatePairs ι ↔ p.1 < p.2 := by
  simp [coordinatePairs]

private theorem card_coordinatePairs [LinearOrder ι] :
    (coordinatePairs ι).card = (Fintype.card ι).choose 2 := by
  simpa [coordinatePairs] using Fintype.card_product_filter_lt (α := ι)

private theorem not_injective_set_eq_iUnion [LinearOrder ι] :
    {x : ι → κ | ¬Function.Injective x} =
      ⋃ p ∈ coordinatePairs ι, {x | x p.1 = x p.2} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    rw [Function.not_injective_iff] at hx
    obtain ⟨i, j, hij, hne⟩ := hx
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(i, j), mem_coordinatePairs _ |>.2 hlt, hij⟩
    · exact ⟨(j, i), mem_coordinatePairs _ |>.2 hgt, hij.symm⟩
  · rintro ⟨⟨i, j⟩, hp, hij⟩ h_inj
    exact (mem_coordinatePairs _ |>.1 hp).ne (h_inj hij)

variable [Fintype κ]

/-- **Collision bound for uniform sampling.**  When the function space `ι → κ` is nonempty, a
uniform map from `ι` to `κ` fails to be injective with probability at most
`(Fintype.card ι).choose 2 / Fintype.card κ`.  When the function space is empty, `uniformOn` is the
zero measure and the inequality remains valid under that convention.

This is the union bound over the unordered pairs of coordinates.  It remains valid when the
right-hand side exceeds one, avoiding an unnecessary size assumption on the sample. -/
theorem uniformOn_not_injective_le [MeasurableSpace κ] [MeasurableSingletonClass κ] :
    uniformOn (Set.univ : Set (ι → κ)) {x | ¬Function.Injective x} ≤
      (Fintype.card ι).choose 2 / Fintype.card κ := by
  classical
  let _ : LinearOrder ι := (Fintype.equivFin ι).linearOrder
  cases isEmpty_or_nonempty κ with
  | inl hκ =>
      have : {x : ι → κ | ¬Function.Injective x} = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => hx fun a => isEmptyElim (x a)
      simp [this]
  | inr hκ =>
      rw [not_injective_set_eq_iUnion]
      calc
        uniformOn (Set.univ : Set (ι → κ))
            (⋃ p ∈ coordinatePairs ι, {x | x p.1 = x p.2})
          ≤ ∑ p ∈ coordinatePairs ι,
              uniformOn (Set.univ : Set (ι → κ)) {x | x p.1 = x p.2} :=
            measure_biUnion_finset_le _ _
        _ = ∑ _p ∈ coordinatePairs ι, 1 / (Fintype.card κ : ℝ≥0∞) :=
          Finset.sum_congr rfl fun p hp =>
            uniformOn_apply_eq_apply p.1 p.2 (mem_coordinatePairs p |>.1 hp).ne
        _ = (Fintype.card ι).choose 2 / Fintype.card κ := by
          rw [Finset.sum_const, nsmul_eq_mul, card_coordinatePairs]
          simp [div_eq_mul_inv]

/-- Real-valued form of `uniformOn_not_injective_le`, valid without `[Nonempty κ]`. -/
theorem uniformOn_real_not_injective_le [MeasurableSpace κ] [MeasurableSingletonClass κ] :
    (uniformOn (Set.univ : Set (ι → κ))).real {x | ¬Function.Injective x} ≤
      (Fintype.card ι).choose 2 / (Fintype.card κ : ℝ) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have : {x : ι → κ | ¬Function.Injective x} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => hx fun a => isEmptyElim (x a)
    simp [this, measureReal_def]
  · have hfin : ((Fintype.card ι).choose 2 : ℝ≥0∞) / Fintype.card κ ≠ ∞ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [Fintype.card_ne_zero])
    simpa [measureReal_def] using ENNReal.toReal_mono hfin uniformOn_not_injective_le

end

/-- The uniform measure on injective maps differs from the uniform measure on all maps only on the
collision event: for every event `A`, the former is at most the latter plus the collision measure.

This holds for Mathlib's `uniformOn` for all types `ι` and `κ` and every measurable structure on
`κ`.  It includes the degenerate cases where the set of injective maps is empty or infinite, so
that its `uniformOn` measure is zero; this covers an infinite index type, or a nonempty index type
with an infinite codomain type.  When `ι` and `κ` are finite, singletons of `κ` are measurable and
an injective map `ι → κ` exists, the left side is the probability of `A` under uniform sampling
without replacement, and the right side is its probability under uniform sampling with
replacement plus the collision probability.  Without measurable singletons the set of injective
maps need not be measurable, and these measures need not be the sampling probabilities. -/
theorem uniformOn_injective_le_add [MeasurableSpace κ] (A : Set (ι → κ)) :
    uniformOn {x : ι → κ | Function.Injective x} A ≤
      uniformOn Set.univ A + uniformOn Set.univ {x : ι → κ | ¬Function.Injective x} := by
  by_cases h0 : uniformOn {x : ι → κ | Function.Injective x} A = 0
  · simp [h0]
  -- A finite nonempty set of injective maps forces `ι → κ` to be finite.
  have : Finite (ι → κ) := by
    obtain ⟨f, hf⟩ : {x : ι → κ | Function.Injective x}.Nonempty :=
      Set.ne_empty_iff_nonempty.1 fun h ↦ h0 (by simp [h])
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · infer_instance
    classical
    have := (finite_of_uniformOn_ne_zero h0).to_subtype
    have : Finite κ := Finite.of_injective
      (fun y ↦ (⟨Equiv.swap (f i₀) y ∘ f, (Equiv.injective _).comp hf⟩ :
        ↑{x : ι → κ | Function.Injective x}))
      fun y z h ↦ by simpa using congrFun (congrArg Subtype.val h) i₀
    have := Finite.of_injective f hf
    infer_instance
  simpa only [uniformOn, Set.univ_inter, Set.compl_ofPred] using
    Measure.cond_inter_le_add_compl Measure.count Set.univ {x : ι → κ | Function.Injective x} A
      (measure_ne_top _ _)

/-- The uniform measure on all maps differs from the uniform measure on injective maps only on the
collision event: for every event `A`, the former is at most the latter plus the collision measure.

This holds for Mathlib's `uniformOn` for all types `ι` and `κ` and every measurable structure on
`κ`, including the degenerate cases: when no injective map exists, the measure on injective maps is
zero and every map is a collision; when `ι → κ` is infinite, the uniform measure on all maps is
zero.  When `ι` and `κ` are finite, singletons of `κ` are measurable and an injective map `ι → κ`
exists, the left side is the probability of `A` under uniform sampling with replacement, and the
right side is its probability under uniform sampling without replacement plus the collision
probability.  Without measurable singletons the set of injective maps and the collision event need
not be measurable, and these measures need not be the sampling probabilities. -/
theorem uniformOn_univ_le_injective_add [MeasurableSpace κ] (A : Set (ι → κ)) :
    uniformOn Set.univ A ≤ uniformOn {x : ι → κ | Function.Injective x} A +
      uniformOn Set.univ {x : ι → κ | ¬Function.Injective x} := by
  simpa only [uniformOn, Set.univ_inter, Set.compl_ofPred] using
    Measure.cond_le_inter_add_compl Measure.count Set.univ {x : ι → κ | Function.Injective x} A

variable [Fintype ι] [Fintype κ]

/-- **Quantitative finite-sampling bound, injective maps to all maps.**  For every event `A`, its
uniform measure among injective maps is at most its uniform measure among all maps plus
`(Fintype.card ι).choose 2 / Fintype.card κ`.

When an injective map `ι → κ` exists, this compares uniform sampling without replacement to uniform
sampling with replacement.  The inequality also holds in the degenerate case. -/
theorem uniformOn_injective_le_add_choose_two_div [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (A : Set (ι → κ)) :
    uniformOn {x : ι → κ | Function.Injective x} A ≤
      uniformOn Set.univ A + (Fintype.card ι).choose 2 / Fintype.card κ :=
  (uniformOn_injective_le_add A).trans <|
    add_le_add le_rfl uniformOn_not_injective_le

/-- **Quantitative finite-sampling bound, all maps to injective maps.**  For every event `A`, its
uniform measure among all maps is at most its uniform measure among injective maps plus
`(Fintype.card ι).choose 2 / Fintype.card κ`.

When an injective map `ι → κ` exists, this compares uniform sampling with replacement to uniform
sampling without replacement.  The inequality also holds in the degenerate case. -/
theorem uniformOn_univ_le_injective_add_choose_two_div [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (A : Set (ι → κ)) :
    uniformOn Set.univ A ≤ uniformOn {x : ι → κ | Function.Injective x} A +
      (Fintype.card ι).choose 2 / Fintype.card κ :=
  (uniformOn_univ_le_injective_add A).trans <|
    add_le_add le_rfl uniformOn_not_injective_le

section TwoHit

variable {a b : κ}

/-- **Two-hit mass.** For distinct indices `a b : κ` and `|ι| ≤ |κ|`, a uniform injective index
map `k : ι → κ` has both `a` and `b` in its range with probability
`|ι| (|ι| - 1) / (|κ| (|κ| - 1))`.

Without `|ι| ≤ |κ|` there is no injective index map, the left side is `0`, and the right side is
positive once `|ι| ≥ 2`. -/
theorem uniformOn_injective_mem_range_and_mem_range [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (hab : a ≠ b) (hικ : Fintype.card ι ≤ Fintype.card κ) :
    uniformOn {k : ι → κ | Injective k} {k | a ∈ Set.range k ∧ b ∈ Set.range k} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  classical
  have hκ : 2 ≤ Fintype.card κ := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  have h2 : ((Fintype.card κ).descFactorial 2 : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 hκ))
  have hm : ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 hικ))
  have hset : {k : ι → κ | Injective k} = (({k | Injective k} : Finset (ι → κ)) : Set _) := by
    simp
  have hevt : {k : ι → κ | a ∈ Set.range k ∧ b ∈ Set.range k} =
      (({k | a ∈ Set.range k ∧ b ∈ Set.range k} : Finset (ι → κ)) : Set _) := by
    simp
  rw [hset, hevt, uniformOn_apply_finset, ← filter_and,
    ← Fintype.card_subtype (fun k : ι → κ => Injective k), Fintype.card_subtype_injective,
    ENNReal.div_eq_div_iff h2 (ENNReal.natCast_ne_top _) hm (ENNReal.natCast_ne_top _)]
  exact_mod_cast descFactorial_two_mul_card_filter_injective_mem_range_and_mem_range hab

end TwoHit

end Probability

end TauCeti
