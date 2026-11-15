/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Alexander Richard Towell
-/
module

public import Mathlib.Probability.UniformOn
public import Mathlib.Data.Fintype.CardEmbedding
import TauCeti.Data.Fintype.Card.Embedding

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

When injective maps exist, conditioning the random map to be injective is uniform sampling without
replacement.  The main results compare every event under the uniform measures on all maps and on
injective maps, with the collision bound as error.  These inequalities remain valid when no
injective map exists (when Mathlib's `uniformOn` is the zero measure); in the feasible case they are
the coupling step used to compare a finite exchangeable law with the product of its empirical
measure.

The exact formula counts embeddings using Mathlib's `Fintype.card_embedding_eq`. The simpler
estimate is the classical union bound over unordered coordinate pairs, using
`measure_biUnion_finset_le` and `Fintype.card_product_filter_lt`. Both use Mathlib's
`ProbabilityTheory.uniformOn`; no sampling distribution is redefined here.

## Main results

* `uniformOn_not_injective_le` and `uniformOn_not_injective_le_one_sub_descFactorial_div_pow`
  bound the uniform-measure mass of collisions;
* `uniformOn_injective_apply_eq`, `uniformOn_not_injective_apply_eq`, and their `.real` forms
  compute the exact uniform-measure masses;
* `uniformOn_injective_eq_zero_iff`, `uniformOn_injective_of_subsingleton`, and
  `uniformOn_univ_pi_of_subsingleton` treat the infeasible and subsingleton-sample regimes;
* `uniformOn_inter_le_add_compl` and `uniformOn_le_inter_add_compl` give the general conditioning
  comparison;
* `uniformOn_injective_le_add` and `uniformOn_univ_le_injective_add` compare arbitrary events
  under sampling without and with replacement;
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

/-- Converting the exact finite-sampling collision expression from `ℝ≥0∞` to `ℝ` preserves
subtraction, since `(n)_m ≤ n ^ m` for all `n` and `m` (including `n = 0`). -/
theorem toReal_one_sub_descFactorial_div_pow (n m : ℕ) :
    ((1 : ℝ≥0∞) - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m).toReal =
      1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m := by
  have hle : (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m ≤ 1 :=
    ENNReal.div_le_of_le_mul <| by
      rw [one_mul]
      exact_mod_cast Nat.descFactorial_le_pow n m
  simp [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top]

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
  rw [measureReal_def, uniformOn_not_injective_apply_eq, toReal_one_sub_descFactorial_div_pow]

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

end

section Degenerate

/-- When no embedding `ι ↪ κ` exists, there are no injective maps and the uniform measure on
injective selections is zero. -/
@[simp]
theorem uniformOn_injective_eq_zero_of_isEmpty [MeasurableSpace κ] [IsEmpty (ι ↪ κ)] :
    uniformOn {f : ι → κ | Function.Injective f} = 0 := by
  have h : {f : ι → κ | Function.Injective f} = ∅ :=
    Set.eq_empty_of_forall_notMem fun f hf => isEmptyElim (⟨f, hf⟩ : ι ↪ κ)
  simp [h]

/-- For a finite target with measurable singletons, the uniform measure on injective maps `ι → κ`
vanishes if and only if no embedding `ι ↪ κ` exists. No finiteness assumption on `ι` is needed:
when `ι` is infinite there is no embedding into `κ` and both sides hold. -/
theorem uniformOn_injective_eq_zero_iff [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] :
    uniformOn {f : ι → κ | Function.Injective f} = 0 ↔ IsEmpty (ι ↪ κ) := by
  refine ⟨fun h => ⟨fun e => ?_⟩, fun _ => uniformOn_injective_eq_zero_of_isEmpty⟩
  have : Finite ι := Finite.of_injective e e.injective
  let _ : IsProbabilityMeasure (uniformOn {f : ι → κ | Function.Injective f}) :=
    isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨e, e.injective⟩
  exact NeZero.ne _ h

/-- On a subsingleton sample index, every map `ι → κ` is injective, so the uniform measure on
injective selections coincides with the uniform measure on all selections. -/
@[simp]
theorem uniformOn_injective_of_subsingleton [Subsingleton ι] [MeasurableSpace κ] :
    uniformOn {f : ι → κ | Function.Injective f} = uniformOn (Set.univ : Set (ι → κ)) := by
  congr 1
  exact Set.eq_univ_of_forall fun f => Function.injective_of_subsingleton f

/-- On a subsingleton sample index, no selection has a coordinate collision. -/
@[simp]
theorem uniformOn_not_injective_of_subsingleton [Subsingleton ι] [MeasurableSpace κ]
    (s : Set (ι → κ)) :
    uniformOn s {f : ι → κ | ¬ Function.Injective f} = 0 := by
  have h : {f : ι → κ | ¬ Function.Injective f} = ∅ :=
    Set.eq_empty_of_forall_notMem fun f hf => hf (Function.injective_of_subsingleton f)
  simp [h]

/-- On a subsingleton sample index, the product of uniform laws on `κ` coincides with the uniform
law on `ι → κ` without any finiteness or measurable-singleton assumption on `κ`. -/
theorem uniformOn_univ_pi_of_subsingleton [Fintype ι] [Subsingleton ι] [MeasurableSpace κ] :
    (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ)) =
      uniformOn (Set.univ : Set (ι → κ)) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨i₀⟩
  · rw [Measure.pi_of_empty]
    have huniv : ({isEmptyElim} : Set (ι → κ)) = Set.univ :=
      Set.eq_univ_of_forall fun f => Subsingleton.elim f isEmptyElim
    have : MeasurableSingletonClass (ι → κ) := ⟨fun f => by
      have hf : ({f} : Set (ι → κ)) = Set.univ :=
        Set.eq_univ_of_forall fun g => Subsingleton.elim g f
      exact hf ▸ .univ⟩
    ext s hs
    classical
    rw [← huniv, uniformOn_singleton, Measure.dirac_apply' _ hs]
    simp [Set.indicator]
  · obtain ⟨i₀⟩ := i₀
    let _ : Unique ι := uniqueOfSubsingleton i₀
    obtain rfl : ‹Fintype ι› = Unique.fintype := Subsingleton.elim _ _
    set e := MeasurableEquiv.funUnique ι κ
    have hmap₁ : (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ)).map e =
        uniformOn (Set.univ : Set κ) :=
      (measurePreserving_funUnique (uniformOn (Set.univ : Set κ)) ι).map_eq
    have hmap₂ : (uniformOn (Set.univ : Set (ι → κ))).map e = uniformOn (Set.univ : Set κ) := by
      ext s hs
      rw [Measure.map_apply e.measurable hs, uniformOn, uniformOn, cond_apply .univ,
        cond_apply .univ, Set.univ_inter, Set.univ_inter, Measure.count_apply .univ,
        Measure.count_apply .univ, Measure.count_apply (hs.preimage e.measurable),
        Measure.count_apply hs, Set.encard_univ, Set.encard_univ, ENat.card_congr e.toEquiv,
        Set.encard_preimage_of_injective_subset_range e.injective (by simp)]
    calc
      (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ))
          = ((Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ)).map e).map e.symm :=
            e.map_symm_map.symm
      _ = ((uniformOn (Set.univ : Set (ι → κ))).map e).map e.symm := by rw [hmap₁, hmap₂]
      _ = uniformOn (Set.univ : Set (ι → κ)) := e.map_symm_map

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

end

/-- Conditioning the uniform measure on a finite set `s` on an event `E` can increase the
probability of an event `A` by at most the original probability of `Eᶜ`, provided `s ∩ E` is
nonempty.  When `s ∩ E` is empty, Mathlib's `uniformOn (s ∩ E)` is the zero measure and the
inequality remains valid under that convention.

This is the upper half of the elementary coupling bound between a uniform law and its
conditioning. -/
theorem uniformOn_inter_le_add_compl {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {s : Set Ω} (E A : Set Ω) (hs : s.Finite) :
    uniformOn (s ∩ E) A ≤ uniformOn s A + uniformOn s Eᶜ := by
  rcases s.eq_empty_or_nonempty with rfl | hs'
  · simp
  calc
    uniformOn (s ∩ E) A
      = uniformOn (s ∩ E) A * uniformOn s E + uniformOn (s ∩ E) A * uniformOn s Eᶜ := by
        rw [← mul_add, uniformOn_compl E hs hs', mul_one]
    _ ≤ uniformOn s A + uniformOn s Eᶜ := by
      rw [← uniformOn_inter' hs]
      exact add_le_add (measure_mono Set.inter_subset_left)
        (mul_le_of_le_one_left bot_le prob_le_one)

/-- Conditioning the uniform measure on a finite set `s` on an event `E` can decrease the
probability of an event `A` by at most the original probability of `Eᶜ`, provided `s ∩ E` is
nonempty.  When `s ∩ E` is empty, Mathlib's `uniformOn (s ∩ E)` is the zero measure and the
inequality remains valid under that convention.

This is the lower half of the elementary coupling bound between a uniform law and its
conditioning. -/
theorem uniformOn_le_inter_add_compl {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {s : Set Ω} (E A : Set Ω) (hs : s.Finite) :
    uniformOn s A ≤ uniformOn (s ∩ E) A + uniformOn s Eᶜ := by
  rw [← uniformOn_add_compl_eq E A hs]
  exact add_le_add (mul_le_of_le_one_right bot_le prob_le_one)
    (mul_le_of_le_one_left bot_le prob_le_one)

/-- The uniform measure on injective maps differs from the uniform measure on all maps only on the
collision event: for every event `A`, the former is at most the latter plus the collision measure.

When an injective map `ι → κ` exists, these are the probabilities for uniform sampling without and
with replacement, respectively.  The inequality also holds when the set of injective maps is empty,
in which case its `uniformOn` measure is zero. -/
theorem uniformOn_injective_le_add [Finite ι] [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ]
    (A : Set (ι → κ)) :
    uniformOn {x : ι → κ | Function.Injective x} A ≤
      uniformOn Set.univ A + uniformOn Set.univ {x : ι → κ | ¬Function.Injective x} := by
  simpa only [Set.univ_inter, Set.compl_ofPred] using
    uniformOn_inter_le_add_compl {x : ι → κ | Function.Injective x} A Set.finite_univ

/-- The uniform measure on all maps differs from the uniform measure on injective maps only on the
collision event: for every event `A`, the former is at most the latter plus the collision measure.

When an injective map `ι → κ` exists, these are the probabilities for uniform sampling with and
without replacement, respectively.  The inequality also holds when the set of injective maps is
empty, in which case its `uniformOn` measure is zero. -/
theorem uniformOn_univ_le_injective_add [Finite ι] [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ]
    (A : Set (ι → κ)) :
    uniformOn Set.univ A ≤ uniformOn {x : ι → κ | Function.Injective x} A +
      uniformOn Set.univ {x : ι → κ | ¬Function.Injective x} := by
  simpa only [Set.univ_inter, Set.compl_ofPred] using
    uniformOn_le_inter_add_compl {x : ι → κ | Function.Injective x} A Set.finite_univ

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
