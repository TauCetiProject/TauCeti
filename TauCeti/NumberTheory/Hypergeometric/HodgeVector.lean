/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import TauCeti.NumberTheory.Hypergeometric.Dictionary
public import TauCeti.NumberTheory.Hypergeometric.Zigzag
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The weight and the Hodge vector of a hypergeometric parameter pair

The zigzag walk of a parameter pair `(α, β)` records each class of `α` at the height from which
its up-step leaves. In block form, the `c` copies of a class `a ∈ α` of multiplicity `c` are
recorded at the heights `Z(rep a) - c, …, Z(rep a) - 1`, with `Z` the counting function. If the
recorded heights range over `[m, m + w]`, then `w` is the *weight* of the pair and the number
`h_p` of classes recorded at height `m + p` is its `p`-th *Hodge number*; the list
`(h_0, …, h_w)` is the *Hodge vector*. These are the numbers the LMFDB displays as the weight and
the Hodge vector of a hypergeometric family, and by a theorem of Fedorov they are the Hodge numbers
of the variation of Hodge structure attached to the family.

This file defines these invariants and proves their basic properties:

* a height is recorded exactly when the walk takes an up-step from it (as sets, not counting
  multiplicities);
* for positive degree the recorded heights fill `[m, m + w]`, so every Hodge number `h_p` with
  `p ≤ w` is positive, and those with `p > w` vanish;
* the Hodge numbers add up to the degree;
* the shift `(α, β) ↦ (μ + α, μ + β)` translates all recorded heights by the same integer, so it
  preserves the weight, the Hodge numbers and the Hodge vector.

For the pair of degree `0` nothing is recorded; then `m = w = 0` and the Hodge vector is `(0)`.

## Main declarations

* `TauCeti.Hypergeometric.Parameters.recordedHeights`: the recorded heights, with
  `mem_recordedHeights`, `card_recordedHeights` and the walk forms
  `mem_recordedHeights_iff_exists_height` and `mem_recordedHeights_iff_exists_height_succ`.
* `TauCeti.Hypergeometric.Parameters.minHeight`, `maxHeight`, with `isLeast_minHeight`,
  `isGreatest_maxHeight` and `toFinset_recordedHeights` (the recorded heights fill the interval).
* `TauCeti.Hypergeometric.Parameters.weight`, `hodgeNumber` and `hodgeVector`, with
  `hodgeNumber_pos_iff`, `sum_range_hodgeNumber` and `sum_hodgeVector`.
* `TauCeti.Hypergeometric.Parameters.recordedHeights_vadd`, `weight_vadd` and
  `hodgeVector_vadd`: invariance under shifts.
* `TauCeti.Hypergeometric.CyclotomicData.weight`, `hodgeVector`: the weight and the Hodge vector
  of a cyclotomic datum, those of its parameter pair.

## References

* D. P. Roberts and F. Rodriguez-Villegas, *Hypergeometric motives*, Notices Amer. Math. Soc. 69
  (2022) (the zigzag procedure for the Hodge numbers).
* R. Fedorov, *Variations of Hodge structures for hypergeometric differential operators and
  parabolic Higgs bundles*, Int. Math. Res. Not. IMRN (2018), Theorem 1.
* The LMFDB knowl `hgm.zigzagplot`.
-/

public section

namespace TauCeti.Hypergeometric

namespace Parameters

variable (P : Parameters) {a : AddCircle (1 : ℚ)} {h : ℤ} {i p : ℕ}

/-! ### The recorded heights -/

/-- The heights at which the zigzag walk records the classes of `α`, in block form: the `c`
copies of a class `a ∈ α` of multiplicity `c` are recorded at `Z(rep a) - c, …, Z(rep a) - 1`,
with `Z` the counting function. For `α = (1/2, 1/2)`, `β = (1, 1)` this is `{0, 1}`. -/
noncomputable def recordedHeights : Multiset ℤ :=
  ∑ a ∈ P.α.toFinset,
    (Multiset.range (P.α.count a)).map fun j : ℕ ↦ P.countingFunction (rep a) - 1 - j

theorem recordedHeights_def : P.recordedHeights = ∑ a ∈ P.α.toFinset,
    (Multiset.range (P.α.count a)).map fun j : ℕ ↦ P.countingFunction (rep a) - 1 - j := (rfl)

theorem mem_recordedHeights : h ∈ P.recordedHeights ↔
    ∃ a ∈ P.α, ∃ j < P.α.count a, P.countingFunction (rep a) - 1 - j = h := by
  simp [recordedHeights_def, Multiset.mem_sum]

@[simp]
theorem card_recordedHeights : Multiset.card P.recordedHeights = P.degree := by
  simp [recordedHeights_def, Multiset.card_sum, ← card_α]

@[simp]
theorem recordedHeights_eq_zero_iff : P.recordedHeights = 0 ↔ P.degree = 0 := by
  rw [← Multiset.card_eq_zero, card_recordedHeights]

/-- The recorded heights in walk form: they are the heights of the walk at the entries of the
sorted list that come from `α`, the positions of its up-steps. -/
theorem mem_recordedHeights_iff_exists_height : h ∈ P.recordedHeights ↔
    ∃ i, ∃ hi : i < P.sortedReps.length,
      (P.sortedReps[i] : AddCircle (1 : ℚ)) ∈ P.α ∧ P.height i = h := by
  rw [mem_recordedHeights]
  constructor
  · -- The copy recorded at `Z(rep a) - 1 - j` leaves from position `blockStart a + (c - 1 - j)`.
    rintro ⟨a, ha, j, hj, rfl⟩
    have hblock := P.take_count_drop_blockStart a
    rw [P.count_add_of_mem_α ha] at hblock
    have hlen := congrArg List.length hblock
    rw [List.length_take, List.length_drop, List.length_replicate, min_eq_left_iff] at hlen
    refine ⟨P.blockStart a + (P.α.count a - 1 - j), by omega, ?_, ?_⟩
    · have hget := List.getElem_of_eq hblock (i := P.α.count a - 1 - j)
        (by rw [List.length_take, List.length_drop]; omega)
      simp only [List.getElem_take, List.getElem_drop, List.getElem_replicate] at hget
      rw [hget, coe_rep]
      exact ha
    · rw [P.height_blockStart_add_of_mem_α ha (by omega)]
      push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + j ≤ P.α.count a)]
      ring
  · -- Conversely, an `α`-entry at position `i` is a copy in the block of its class.
    rintro ⟨i, hi, hα, rfl⟩
    have h₁ := P.blockStart_le hi
    have h₂ := P.lt_blockStart_add_count hi
    set a : AddCircle (1 : ℚ) := ((P.sortedReps[i] : ℚ) : AddCircle (1 : ℚ))
    rw [P.count_add_of_mem_α hα] at h₂
    refine ⟨a, hα, P.α.count a - 1 - (i - P.blockStart a), by omega, ?_⟩
    have := P.height_blockStart_add_of_mem_α hα (j := i - P.blockStart a) (by omega)
    rw [Nat.add_sub_cancel' h₁] at this
    rw [this]
    push_cast [Nat.sub_sub, Nat.cast_sub h₁, Nat.cast_sub (by omega : 1 + (i - P.blockStart a) ≤
      P.α.count a)]
    ring

/-- The recorded heights in up-step form: they are the heights from which the walk takes an
up-step. -/
theorem mem_recordedHeights_iff_exists_height_succ : h ∈ P.recordedHeights ↔
    ∃ i < 2 * P.degree, P.height i = h ∧ P.height (i + 1) = h + 1 := by
  rw [mem_recordedHeights_iff_exists_height]
  constructor
  · rintro ⟨i, hi, hα, rfl⟩
    refine ⟨i, by simpa using hi, rfl, ?_⟩
    rw [P.height_succ hi, P.step_of_mem hα]
  · rintro ⟨i, hi, rfl, h'⟩
    have hi' : i < P.sortedReps.length := by simpa using hi
    refine ⟨i, hi', by_contra fun hα ↦ ?_, rfl⟩
    have := P.height_succ hi'
    rw [P.step_of_notMem hα] at this
    omega

/-! ### The extreme heights -/

/-- The least recorded height `m`; it is `0` when nothing is recorded. -/
noncomputable def minHeight : ℤ := sInf (P.recordedHeights.toFinset : Set ℤ)

/-- The greatest recorded height `m + w`; it is `0` when nothing is recorded. -/
noncomputable def maxHeight : ℤ := sSup (P.recordedHeights.toFinset : Set ℤ)

theorem minHeight_def : P.minHeight = sInf (P.recordedHeights.toFinset : Set ℤ) := (rfl)

theorem maxHeight_def : P.maxHeight = sSup (P.recordedHeights.toFinset : Set ℤ) := (rfl)

theorem minHeight_le (hh : h ∈ P.recordedHeights) : P.minHeight ≤ h :=
  csInf_le (Finset.bddBelow _) (by simpa using hh)

theorem le_maxHeight (hh : h ∈ P.recordedHeights) : h ≤ P.maxHeight :=
  le_csSup (Finset.bddAbove _) (by simpa using hh)

theorem minHeight_mem (hd : 0 < P.degree) : P.minHeight ∈ P.recordedHeights := by
  have hne : P.recordedHeights ≠ 0 := by simpa using hd.ne'
  simpa [minHeight_def] using
    Int.csInf_mem (Finset.coe_nonempty.2 (Multiset.toFinset_nonempty.2 hne)) (Finset.bddBelow _)

theorem maxHeight_mem (hd : 0 < P.degree) : P.maxHeight ∈ P.recordedHeights := by
  have hne : P.recordedHeights ≠ 0 := by simpa using hd.ne'
  simpa [maxHeight_def] using
    Int.csSup_mem (Finset.coe_nonempty.2 (Multiset.toFinset_nonempty.2 hne)) (Finset.bddAbove _)

theorem isLeast_minHeight (hd : 0 < P.degree) :
    IsLeast {h | h ∈ P.recordedHeights} P.minHeight :=
  ⟨P.minHeight_mem hd, fun _ ↦ P.minHeight_le⟩

theorem isGreatest_maxHeight (hd : 0 < P.degree) :
    IsGreatest {h | h ∈ P.recordedHeights} P.maxHeight :=
  ⟨P.maxHeight_mem hd, fun _ ↦ P.le_maxHeight⟩

theorem minHeight_of_degree_eq_zero (hd : P.degree = 0) : P.minHeight = 0 := by
  simp [minHeight_def, (P.recordedHeights_eq_zero_iff).2 hd]

theorem maxHeight_of_degree_eq_zero (hd : P.degree = 0) : P.maxHeight = 0 := by
  simp [maxHeight_def, (P.recordedHeights_eq_zero_iff).2 hd]

theorem minHeight_le_maxHeight : P.minHeight ≤ P.maxHeight := by
  rcases Nat.eq_zero_or_pos P.degree with hd | hd
  · rw [P.minHeight_of_degree_eq_zero hd, P.maxHeight_of_degree_eq_zero hd]
  · exact P.minHeight_le (P.maxHeight_mem hd)

/-- For positive degree the recorded heights fill the interval between their extremes: between
two recorded heights the walk passes every intermediate height on an up-step. -/
theorem toFinset_recordedHeights (hd : 0 < P.degree) :
    P.recordedHeights.toFinset = Finset.Icc P.minHeight P.maxHeight := by
  ext h
  simp only [Multiset.mem_toFinset, Finset.mem_Icc]
  refine ⟨fun hh ↦ ⟨P.minHeight_le hh, P.le_maxHeight hh⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  obtain rfl | h₂ := h₂.eq_or_lt
  · exact P.maxHeight_mem hd
  -- The least recorded height is reached at a position `i`, the greatest at a position `j`.
  obtain ⟨i, hi, -, hmin⟩ := P.mem_recordedHeights_iff_exists_height.1 (P.minHeight_mem hd)
  obtain ⟨j, hj, -, hmax⟩ := P.mem_recordedHeights_iff_exists_height.1 (P.maxHeight_mem hd)
  rw [length_sortedReps] at hi hj
  -- A nonnegative `h` lies between the start `0` and position `j`, a negative one between
  -- position `i` and the end `0` of the walk.
  obtain ⟨k, hk, rfl, hk'⟩ : ∃ k < 2 * P.degree, P.height k = h ∧ P.height (k + 1) = h + 1 := by
    rcases le_or_gt 0 h with h0 | h0
    · obtain ⟨k, -, hk, hk'⟩ := P.exists_height_eq_of_le_of_lt (Nat.zero_le j) hj.le
        (by simpa using h0) (by omega)
      exact ⟨k, by omega, hk'⟩
    · obtain ⟨k, -, hk, hk'⟩ := P.exists_height_eq_of_le_of_lt (h := h) hi.le
        (le_refl (2 * P.degree)) (by omega) (by rwa [height_two_mul_degree])
      exact ⟨k, hk, hk'⟩
  exact P.mem_recordedHeights_iff_exists_height_succ.2 ⟨k, hk, rfl, hk'⟩

/-- For positive degree, a height is recorded exactly when it lies between the extremes. -/
theorem mem_recordedHeights_iff_mem_Icc (hd : 0 < P.degree) :
    h ∈ P.recordedHeights ↔ h ∈ Set.Icc P.minHeight P.maxHeight := by
  rw [← Multiset.mem_toFinset, P.toFinset_recordedHeights hd, Finset.mem_Icc, Set.mem_Icc]

/-! ### The weight and the Hodge numbers -/

/-- The weight `w` of a parameter pair: the spread `maxHeight - minHeight` of its recorded
heights. -/
noncomputable def weight : ℕ := (P.maxHeight - P.minHeight).toNat

theorem weight_def : P.weight = (P.maxHeight - P.minHeight).toNat := (rfl)

theorem natCast_weight : (P.weight : ℤ) = P.maxHeight - P.minHeight :=
  Int.toNat_of_nonneg (sub_nonneg.2 P.minHeight_le_maxHeight)

theorem minHeight_add_weight : P.minHeight + P.weight = P.maxHeight := by
  rw [natCast_weight]
  ring

theorem weight_of_degree_eq_zero (hd : P.degree = 0) : P.weight = 0 := by
  simp [weight_def, P.minHeight_of_degree_eq_zero hd, P.maxHeight_of_degree_eq_zero hd]

/-- The Hodge number `h_p`: the number of classes of `α` recorded at height `minHeight + p`. -/
noncomputable def hodgeNumber (p : ℕ) : ℕ := P.recordedHeights.count (P.minHeight + p)

theorem hodgeNumber_def (p : ℕ) :
    P.hodgeNumber p = P.recordedHeights.count (P.minHeight + p) := (rfl)

/-- For positive degree, the Hodge number `h_p` is positive exactly up to the weight. -/
theorem hodgeNumber_pos_iff (hd : 0 < P.degree) : 0 < P.hodgeNumber p ↔ p ≤ P.weight := by
  rw [hodgeNumber_def, Multiset.count_pos, P.mem_recordedHeights_iff_mem_Icc hd, Set.mem_Icc,
    ← minHeight_add_weight]
  omega

theorem hodgeNumber_eq_zero_of_weight_lt (hp : P.weight < p) : P.hodgeNumber p = 0 := by
  refine Multiset.count_eq_zero.2 fun hh ↦ ?_
  have := P.le_maxHeight hh
  rw [← minHeight_add_weight] at this
  omega

theorem hodgeNumber_of_degree_eq_zero (hd : P.degree = 0) (p : ℕ) : P.hodgeNumber p = 0 := by
  simp [hodgeNumber_def, (P.recordedHeights_eq_zero_iff).2 hd]

/-- The Hodge numbers add up to the degree. -/
theorem sum_range_hodgeNumber :
    ∑ p ∈ Finset.range (P.weight + 1), P.hodgeNumber p = P.degree := by
  -- Reindex by the heights `minHeight + p`, which cover every recorded height.
  have hinj : Set.InjOn (fun p : ℕ ↦ P.minHeight + p) (Finset.range (P.weight + 1)) :=
    fun p _ q _ hpq ↦ by simpa using hpq
  rw [← card_recordedHeights, ← Multiset.sum_count_eq_card (s := (Finset.range
    (P.weight + 1)).image fun p : ℕ ↦ P.minHeight + p), Finset.sum_image hinj]
  · simp only [hodgeNumber_def]
  intro h hh
  have h₁ := P.minHeight_le hh
  have h₂ := P.le_maxHeight hh
  rw [← minHeight_add_weight] at h₂
  simp only [Finset.mem_image, Finset.mem_range]
  exact ⟨(h - P.minHeight).toNat, by omega, by omega⟩

/-- The Hodge vector `(h_0, …, h_w)`, the Hodge numbers up to the weight. -/
noncomputable def hodgeVector : List ℕ := (List.range (P.weight + 1)).map P.hodgeNumber

theorem hodgeVector_def : P.hodgeVector = (List.range (P.weight + 1)).map P.hodgeNumber := (rfl)

@[simp]
theorem length_hodgeVector : P.hodgeVector.length = P.weight + 1 := by
  simp [hodgeVector_def]

@[simp]
theorem getElem_hodgeVector (hp : p < P.hodgeVector.length) :
    P.hodgeVector[p] = P.hodgeNumber p := by
  simp [hodgeVector_def]

@[simp]
theorem sum_hodgeVector : P.hodgeVector.sum = P.degree := by
  rw [hodgeVector_def, ← P.sum_range_hodgeNumber, Finset.sum_eq_multiset_sum, Finset.range_val,
    ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]

theorem hodgeVector_of_degree_eq_zero (hd : P.degree = 0) : P.hodgeVector = [0] := by
  simp [hodgeVector_def, P.weight_of_degree_eq_zero hd, P.hodgeNumber_of_degree_eq_zero hd]

/-! ### Shifts -/

/-- A shift by `μ` translates the recorded heights by `-Z(1 - rep μ)`. -/
theorem recordedHeights_vadd (μ : AddCircle (1 : ℚ)) :
    (μ +ᵥ P).recordedHeights =
      P.recordedHeights.map (· - P.countingFunction (1 - rep μ)) := by
  have hinj : Function.Injective (μ + ·) := add_right_injective μ
  rw [recordedHeights_def, recordedHeights_def, vadd_α, Multiset.toFinset_map,
    Finset.sum_image fun _ _ _ _ h ↦ hinj h, ← Multiset.mapAddMonoidHom_apply (· - _),
    map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Multiset.count_map_eq_count' _ _ hinj, Multiset.mapAddMonoidHom_apply,
    Multiset.map_map, Function.comp_def, P.countingFunction_vadd_rep_add]
  congr 1
  ext j
  ring

theorem minHeight_vadd (μ : AddCircle (1 : ℚ)) :
    (μ +ᵥ P).minHeight = P.minHeight - P.countingFunction (1 - rep μ) := by
  rcases Nat.eq_zero_or_pos P.degree with hd | hd
  · rw [(μ +ᵥ P).minHeight_of_degree_eq_zero (by rwa [degree_vadd]),
      P.minHeight_of_degree_eq_zero hd, P.countingFunction_of_degree_eq_zero hd, sub_zero]
  refine ((μ +ᵥ P).isLeast_minHeight (by rwa [degree_vadd])).unique ⟨?_, ?_⟩
  · exact (P.recordedHeights_vadd μ).symm ▸ Multiset.mem_map.2 ⟨_, P.minHeight_mem hd, rfl⟩
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.1 ((P.recordedHeights_vadd μ) ▸ hx)
    linarith [P.minHeight_le hh]

theorem maxHeight_vadd (μ : AddCircle (1 : ℚ)) :
    (μ +ᵥ P).maxHeight = P.maxHeight - P.countingFunction (1 - rep μ) := by
  rcases Nat.eq_zero_or_pos P.degree with hd | hd
  · rw [(μ +ᵥ P).maxHeight_of_degree_eq_zero (by rwa [degree_vadd]),
      P.maxHeight_of_degree_eq_zero hd, P.countingFunction_of_degree_eq_zero hd, sub_zero]
  refine ((μ +ᵥ P).isGreatest_maxHeight (by rwa [degree_vadd])).unique ⟨?_, ?_⟩
  · exact (P.recordedHeights_vadd μ).symm ▸ Multiset.mem_map.2 ⟨_, P.maxHeight_mem hd, rfl⟩
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.1 ((P.recordedHeights_vadd μ) ▸ hx)
    linarith [P.le_maxHeight hh]

@[simp]
theorem weight_vadd (μ : AddCircle (1 : ℚ)) : (μ +ᵥ P).weight = P.weight := by
  simp [weight_def, minHeight_vadd, maxHeight_vadd]

@[simp]
theorem hodgeNumber_vadd (μ : AddCircle (1 : ℚ)) (p : ℕ) :
    (μ +ᵥ P).hodgeNumber p = P.hodgeNumber p := by
  rw [hodgeNumber_def, recordedHeights_vadd, minHeight_vadd, show
    P.minHeight - P.countingFunction (1 - rep μ) + p =
      P.minHeight + p - P.countingFunction (1 - rep μ) by ring,
    Multiset.count_map_eq_count' _ _ (sub_left_injective), hodgeNumber_def]

@[simp]
theorem hodgeVector_vadd (μ : AddCircle (1 : ℚ)) : (μ +ᵥ P).hodgeVector = P.hodgeVector := by
  simp [hodgeVector_def]

end Parameters

/-! ### Cyclotomic data -/

namespace CyclotomicData

variable (D : CyclotomicData)

/-- The weight of a cyclotomic datum: the weight of its parameter pair. -/
noncomputable def weight : ℕ := D.toParameters.weight

theorem weight_def : D.weight = D.toParameters.weight := (rfl)

/-- The Hodge vector of a cyclotomic datum: the Hodge vector of its parameter pair. -/
noncomputable def hodgeVector : List ℕ := D.toParameters.hodgeVector

theorem hodgeVector_def : D.hodgeVector = D.toParameters.hodgeVector := (rfl)

end CyclotomicData

end TauCeti.Hypergeometric
