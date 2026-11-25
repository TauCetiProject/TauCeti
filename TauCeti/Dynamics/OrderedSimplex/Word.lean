/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import TauCeti.Dynamics.OrderedSimplex.Branch

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.List

/-!
# Words of accelerated branches and the renewal count

A *word* is a finite list `u = [a₁, …, a_m]` of letters `a = (A, j)` of the accelerated branches
`F_a` on the ordered simplex. Words act *chronologically*: the first letter acts first, so
`F_u = F_{a_m} ∘ ⋯ ∘ F_{a₁}`, and the *delay* of `u` at `w` is the sum of the delays
`τ_a = log q_a` collected along the orbit,
`T_u (w) = τ_{a₁} (w) + τ_{a₂} (F_{a₁} w) + ⋯ + τ_{a_m} (F_{a_{m-1}} ⋯ F_{a₁} w)`.
Homogeneously, `T_u (w) = log ((γ_u y)_n / y_n)` for the linear map
`γ_u = γ_{a_m} ⋯ γ_{a₁}` of the accelerated generators and any `y` in the ordered cone over `w`,
so `T_u` measures the growth of the last coordinate along the orbit of the semigroup.
Reading off the last letter of a word from the image of an interior point shows that the
accelerated generators freely generate their semigroup `Γ'`: distinct words have distinct linear
maps `γ_u`, so counting words counts the elements of `Γ'`.

The *renewal count* `N (w, r)` is the number of words, the empty word included, whose delay at
`w` is at most `r`. Since every delay is at least `log (3 / 2)` and a letter with large `A` has a
large delay, only finitely many words contribute for each `r`. Splitting the nonempty words by
their first letter gives the renewal equation
`N (w, r) = 1{r ≥ 0} + ∑_a N (F_a w, r - τ_a (w))`, which is the starting point for the
asymptotic count of the orbit through the transfer operators `L_s f = ∑_a q_a^{-s} f ∘ F_a`.

## Main definitions

* `TauCeti.wordMap u x`: the map `F_u` of the word `u`, read chronologically.
* `TauCeti.wordDelay u x`: the delay `T_u (w)`.
* `TauCeti.wordMove u`: the linear map `γ_u = γ_{a_m} ⋯ γ_{a₁}` of `ℝ^{d+2}`.
* `TauCeti.wordCount d x r`: the renewal count `N (w, r)`.

## Main results

* `TauCeti.wordMap_append`, `TauCeti.wordDelay_append`, `TauCeti.wordMove_append`: the
  concatenation rules `F_{u ++ v} = F_v ∘ F_u`, `T_{u ++ v} (w) = T_u (w) + T_v (F_u w)` and
  `γ_{u ++ v} = γ_v γ_u`.
* `TauCeti.wordMove_of_mem_orderedCone`, `TauCeti.wordDelay_simplexChart`: the homogeneous
  identity `γ_u y = y_n e^{T_u (w)} (F_u (w), 1)` and its consequence
  `T_u (w) = log ((γ_u y)_n / y_n)`.
* `TauCeti.length_mul_log_le_wordDelay`, `TauCeti.fst_add_three_le_two_mul_exp_wordDelay`: on the
  simplex `T_u (w) ≥ |u| log (3 / 2)`, and every letter `(A, j)` of `u` has
  `A + 3 ≤ 2 e^{T_u (w)}`.
* `TauCeti.eq_of_wordMap_eq_of_wordDelay_eq`, `TauCeti.wordMove_injective`: at an interior point
  `w` of the simplex a word is determined by `F_u (w)` and `T_u (w)`; hence the accelerated
  generators freely generate their semigroup.
* `TauCeti.finite_setOf_wordDelay_le`: only finitely many words have delay at most `r`.
* `TauCeti.wordCount_mono`, `TauCeti.continuousWithinAt_wordCount_Ici`,
  `TauCeti.measurable_wordCount`, `TauCeti.wordCount_eq_zero_of_neg`, `TauCeti.wordCount_eq_one`:
  `N (w, ·)` is nondecreasing, right-continuous and measurable, vanishes on `r < 0` and equals
  `1` on `0 ≤ r < log (3 / 2)`.
* `TauCeti.wordCount_eq_add_finsum`, `TauCeti.finite_support_wordCount_branchMap`: the renewal
  equation, a finite sum at each `r`.

## References

* A. Gamburd, M. Magee, R. Ronan, *An asymptotic formula for integer points on Markoff–Hurwitz
  varieties*, Ann. of Math. 190 (2019), (1.7), (4.1), and p. 756 with footnote 5 (freeness).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {d : ℕ}

/-! ### Word maps and delays -/

/-- The map `F_u` of a word read chronologically: the first letter acts first,
`F_{a :: u} = F_u ∘ F_a`, and the empty word acts as the identity. -/
noncomputable def wordMap : List (ℕ × Fin d) → (Fin d → ℝ) → Fin d → ℝ
  | [], x => x
  | a :: u, x => wordMap u (branchMap a x)

@[simp]
theorem wordMap_nil (x : Fin d → ℝ) : wordMap [] x = x :=
  (rfl)

@[simp]
theorem wordMap_cons (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordMap (a :: u) x = wordMap u (branchMap a x) :=
  (rfl)

/-- Concatenation of words composes their maps chronologically: `F_{u ++ v} = F_v ∘ F_u`. -/
@[simp]
theorem wordMap_append (u v : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordMap (u ++ v) x = wordMap v (wordMap u x) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih => simp [ih]

/-- Every word map sends the ordered simplex into itself. -/
theorem wordMap_mem_orderedSimplex (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : wordMap u x ∈ orderedSimplex d := by
  induction u generalizing x with
  | nil => exact hx
  | cons a _ ih => exact ih (branchMap_mem_orderedSimplex a hx)

/-- Every word map sends the ordered simplex into itself. -/
theorem mapsTo_wordMap (u : List (ℕ × Fin d)) :
    MapsTo (wordMap u) (orderedSimplex d) (orderedSimplex d) :=
  fun _ hx => wordMap_mem_orderedSimplex u hx

/-- The delay `T_u (w)` of a word read chronologically: the empty word has delay `0`, and
`T_{a :: u} (w) = log q_a (w) + T_u (F_a w)`. -/
noncomputable def wordDelay : List (ℕ × Fin d) → (Fin d → ℝ) → ℝ
  | [], _ => 0
  | a :: u, x => Real.log (branchDenom a x) + wordDelay u (branchMap a x)

@[simp]
theorem wordDelay_nil (x : Fin d → ℝ) : wordDelay [] x = 0 :=
  (rfl)

@[simp]
theorem wordDelay_cons (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (a :: u) x = Real.log (branchDenom a x) + wordDelay u (branchMap a x) :=
  (rfl)

/-- The delay of a concatenation: `T_{u ++ v} (w) = T_u (w) + T_v (F_u w)`. -/
@[simp]
theorem wordDelay_append (u v : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (u ++ v) x = wordDelay u x + wordDelay v (wordMap u x) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih => simp [ih, add_assoc]

/-- On the simplex every letter contributes a delay of at least `log (3 / 2)`, so
`T_u (w) ≥ |u| log (3 / 2)`. -/
theorem length_mul_log_le_wordDelay (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : u.length * Real.log (3 / 2) ≤ wordDelay u x := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    have h₁ := log_three_halves_le_log_branchDenom a (le_one_half_of_mem_orderedSimplex hx a.2)
    have h₂ := ih (branchMap_mem_orderedSimplex a hx)
    simp only [wordDelay_cons, List.length_cons, Nat.cast_succ]
    linarith

/-- Delays are nonnegative on the simplex. -/
theorem wordDelay_nonneg (u : List (ℕ × Fin d)) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    0 ≤ wordDelay u x :=
  (mul_nonneg u.length.cast_nonneg (Real.log_nonneg (by norm_num))).trans
    (length_mul_log_le_wordDelay u hx)

/-- On the simplex every letter `(A, j)` of a word `u` satisfies `A + 3 ≤ 2 e^{T_u (w)}`: its
own delay is at least `log ((A + 3) / 2)`, and the other delays are nonnegative. -/
theorem fst_add_three_le_two_mul_exp_wordDelay {u : List (ℕ × Fin d)} {a : ℕ × Fin d}
    (ha : a ∈ u) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    (a.1 : ℝ) + 3 ≤ 2 * Real.exp (wordDelay u x) := by
  induction u generalizing x with
  | nil => simp at ha
  | cons b u ih =>
    have hb := wordDelay_nonneg u (branchMap_mem_orderedSimplex b hx)
    have hq := branchDenom_pos_of_mem_orderedSimplex b hx
    rw [wordDelay_cons, Real.exp_add, Real.exp_log hq]
    rcases List.mem_cons.mp ha with rfl | ha
    · have h := add_three_div_two_le_branchDenom a (le_one_half_of_mem_orderedSimplex hx a.2)
      have := le_mul_of_one_le_right hq.le (Real.one_le_exp hb)
      linarith
    · have h := ih ha (branchMap_mem_orderedSimplex b hx)
      have := le_mul_of_one_le_left (Real.exp_pos (wordDelay u (branchMap b x))).le
        (one_le_branchDenom b ((le_one_half_of_mem_orderedSimplex hx b.2).trans (by norm_num)))
      linarith

/-! ### The homogeneous meaning of the delay -/

/-- The linear map `γ_u = γ_{a_m} ⋯ γ_{a₁}` of the word `u = [a₁, …, a_m]`, where the letter
`a = (A, j)` stands for the accelerated generator `γ_{n-1}^A γ_j`: the empty word gives the
identity, and `γ_{a :: u} = γ_u γ_{n-1}^A γ_j`. -/
noncomputable def wordMove : List (ℕ × Fin d) → Module.End ℝ (Fin (d + 2) → ℝ)
  | [] => 1
  | a :: u => wordMove u * (linearMove (Fin.last d) ^ a.1 * linearMove a.2.castSucc)

@[simp]
theorem wordMove_nil : wordMove ([] : List (ℕ × Fin d)) = 1 :=
  (rfl)

@[simp]
theorem wordMove_cons (a : ℕ × Fin d) (u : List (ℕ × Fin d)) :
    wordMove (a :: u) = wordMove u * (linearMove (Fin.last d) ^ a.1 * linearMove a.2.castSucc) :=
  (rfl)

/-- Concatenation of words multiplies their linear maps in reverse order:
`γ_{u ++ v} = γ_v γ_u`. -/
@[simp]
theorem wordMove_append (u v : List (ℕ × Fin d)) :
    wordMove (u ++ v) = wordMove v * wordMove u := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, mul_assoc]

/-- **The homogeneous identity** for words in chart coordinates:
`γ_u (w, 1) = e^{T_u (w)} (F_u (w), 1)` on the simplex. -/
theorem wordMove_simplexLift (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    wordMove u (simplexLift x) = Real.exp (wordDelay u x) • simplexLift (wordMap u x) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    have hq := branchDenom_pos_of_mem_orderedSimplex a hx
    simp [linearMove_last_pow_linearMove_simplexLift a hq.ne',
      ih (branchMap_mem_orderedSimplex a hx), smul_smul, Real.exp_add, Real.exp_log hq]

/-- **The homogeneous identity** for words on the ordered cone: for `y ∈ H_n` over `w`,
`γ_u y = y_n e^{T_u (w)} (F_u (w), 1)`. -/
theorem wordMove_of_mem_orderedCone (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    wordMove u y = (y (Fin.last _) * Real.exp (wordDelay u (simplexChart y))) •
      simplexLift (wordMap u (simplexChart y)) := by
  conv_lhs => rw [← last_smul_simplexLift_simplexChart hy]
  rw [map_smul, wordMove_simplexLift u (simplexChart_mem_orderedSimplex hy), smul_smul]

/-- The linear map of every word maps the ordered cone into itself. -/
theorem wordMove_mem_orderedCone (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : wordMove u y ∈ orderedCone d := by
  rw [wordMove_of_mem_orderedCone u hy]
  exact smul_mem_orderedCone
    (simplexLift_mem_orderedCone
      (wordMap_mem_orderedSimplex u (simplexChart_mem_orderedSimplex hy)))
    (mul_pos (pos_last_of_mem_orderedCone hy) (Real.exp_pos _))

/-- The word map `F_u` is the projective action of `γ_u` on the ordered cone. -/
theorem simplexChart_wordMove (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : simplexChart (wordMove u y) = wordMap u (simplexChart y) := by
  rw [wordMove_of_mem_orderedCone u hy,
    simplexChart_smul _ (mul_pos (pos_last_of_mem_orderedCone hy) (Real.exp_pos _)).ne',
    simplexChart_simplexLift]

/-- The delay of a word is the logarithmic growth of the last coordinate along the orbit:
`T_u (w) = log ((γ_u y)_n / y_n)` for every `y` in the ordered cone over `w`. -/
theorem wordDelay_simplexChart (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    wordDelay u (simplexChart y) = Real.log (wordMove u y (Fin.last _) / y (Fin.last _)) := by
  rw [wordMove_of_mem_orderedCone u hy]
  simp [(pos_last_of_mem_orderedCone hy).ne']

/-! ### Freeness -/

/-- Every word map sends the interior of the simplex into itself. -/
theorem wordMap_mem_interior_orderedSimplex (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ interior (orderedSimplex d)) : wordMap u x ∈ interior (orderedSimplex d) := by
  induction u generalizing x with
  | nil => exact hx
  | cons a _ ih => exact ih (branchMap_mem_interior_orderedSimplex a hx)

/-- At an interior point `w` of the simplex a word `u` is determined by its image point
`F_u (w)` together with its delay `T_u (w)`. -/
theorem eq_of_wordMap_eq_of_wordDelay_eq {u v : List (ℕ × Fin d)} {x : Fin d → ℝ}
    (hx : x ∈ interior (orderedSimplex d)) (hmap : wordMap u x = wordMap v x)
    (hdelay : wordDelay u x = wordDelay v x) : u = v := by
  have hpos (w : List (ℕ × Fin d)) (hw : w ≠ []) : 0 < wordDelay w x :=
    (mul_pos (Nat.cast_pos.mpr (List.length_pos_iff.mpr hw)) (Real.log_pos (by norm_num))).trans_le
      (length_mul_log_le_wordDelay w (interior_subset hx))
  induction u using List.reverseRecOn generalizing v with
  | nil =>
    rcases eq_or_ne v [] with rfl | hv
    · rfl
    · exact absurd hdelay (by simpa using (hpos v hv).ne)
  | append_singleton u a ih =>
    rcases List.eq_nil_or_concat' v with rfl | ⟨v, b, rfl⟩
    · exact absurd hdelay (by simpa using (hpos (u ++ [a]) (by simp)).ne')
    · simp only [wordMap_append, wordMap_cons, wordMap_nil] at hmap
      obtain ⟨rfl, hm⟩ := (branchMap_eq_branchMap_iff (wordMap_mem_interior_orderedSimplex u hx)
        (wordMap_mem_orderedSimplex v (interior_subset hx))).mp hmap
      simp only [wordDelay_append, wordDelay_cons, wordDelay_nil, add_zero, hm] at hdelay
      rw [ih hm (add_right_cancel hdelay)]

/-- **Freeness.** The accelerated generators `γ_{n-1}^A γ_j` freely generate the semigroup
`Γ'`: distinct words have distinct linear maps `γ_u`. -/
theorem wordMove_injective :
    Function.Injective (wordMove : List (ℕ × Fin d) → Module.End ℝ (Fin (d + 2) → ℝ)) := by
  intro u v h
  obtain ⟨x, hx⟩ := interior_orderedSimplex_nonempty d
  have hy := simplexLift_mem_orderedCone (interior_subset hx)
  refine eq_of_wordMap_eq_of_wordDelay_eq hx ?_ ?_
  · have hu := simplexChart_wordMove u hy
    have hv := simplexChart_wordMove v hy
    rw [simplexChart_simplexLift] at hu hv
    rw [← hu, ← hv, h]
  · have hu := wordDelay_simplexChart u hy
    have hv := wordDelay_simplexChart v hy
    rw [simplexChart_simplexLift] at hu hv
    rw [hu, hv, h]

/-- **Freeness.** Two words have the same linear map exactly when they are equal. -/
@[simp]
theorem wordMove_inj {u v : List (ℕ × Fin d)} : wordMove u = wordMove v ↔ u = v :=
  wordMove_injective.eq_iff

/-! ### The renewal count -/

/-- The renewal count `N (w, r)`: the number of words, the empty word included, whose delay at
`w` is at most `r`. On the simplex only finitely many words contribute
(`TauCeti.finite_setOf_wordDelay_le`). -/
noncomputable def wordCount (d : ℕ) (x : Fin d → ℝ) (r : ℝ) : ℕ :=
  {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.ncard

theorem wordCount_def (d : ℕ) (x : Fin d → ℝ) (r : ℝ) :
    wordCount d x r = {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.ncard :=
  (rfl)

/-- Only finitely many letters `(A, j)` have `A + 3 ≤ c`. -/
private theorem finite_setOf_fst_add_three_le (c : ℝ) :
    {a : ℕ × Fin d | (a.1 : ℝ) + 3 ≤ c}.Finite :=
  ((finite_Iic ⌊c⌋₊).prod finite_univ).subset fun a ha =>
    ⟨Nat.le_floor (by linarith [show (a.1 : ℝ) + 3 ≤ c from ha]), mem_univ _⟩

/-- On the simplex only finitely many words have delay at most `r`: such a word has length at
most `r / log (3 / 2)`, and each of its letters `(A, j)` has `A + 3 ≤ 2 e^r`. -/
theorem finite_setOf_wordDelay_le {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.Finite := by
  set T := {a : ℕ × Fin d | (a.1 : ℝ) + 3 ≤ 2 * Real.exp r}
  have : Finite T := (finite_setOf_fst_add_three_le _).to_subtype
  refine ((List.finite_length_le T ⌊r / Real.log (3 / 2)⌋₊).image
    (List.map Subtype.val)).subset fun u (hu : wordDelay u x ≤ r) => ?_
  have hT : ∀ a ∈ u, a ∈ T := fun a ha =>
    (fst_add_three_le_two_mul_exp_wordDelay ha hx).trans (by gcongr)
  lift u to List T using hT
  refine ⟨u, mem_ofPred.mpr ?_, rfl⟩
  have hlen := length_mul_log_le_wordDelay (u.map Subtype.val) hx
  rw [List.length_map] at hlen
  exact Nat.le_floor ((le_div_iff₀ (Real.log_pos (by norm_num))).mpr (hlen.trans hu))

/-- The renewal count vanishes at negative times. -/
theorem wordCount_eq_zero_of_neg {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) {r : ℝ}
    (hr : r < 0) : wordCount d x r = 0 := by
  rw [wordCount_def, ncard_eq_zero (finite_setOf_wordDelay_le hx r)]
  exact eq_empty_of_forall_notMem fun u (hu : wordDelay u x ≤ r) =>
    (wordDelay_nonneg u hx).not_gt (hu.trans_lt hr)

/-- Before the first delay only the empty word counts: `N (w, r) = 1` for
`0 ≤ r < log (3 / 2)`. -/
theorem wordCount_eq_one {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) {r : ℝ} (h₀ : 0 ≤ r)
    (hr : r < Real.log (3 / 2)) : wordCount d x r = 1 := by
  rw [wordCount_def, ncard_eq_one]
  refine ⟨[], eq_singleton_iff_unique_mem.mpr ⟨by simpa using h₀, fun u hu => ?_⟩⟩
  cases u with
  | nil => rfl
  | cons a u =>
    have h := length_mul_log_le_wordDelay (a :: u) hx
    simp only [mem_ofPred_eq] at hu
    simp only [List.length_cons, Nat.cast_succ] at h
    nlinarith [u.length.cast_nonneg (α := ℝ)]

/-- The renewal count is nondecreasing in time. -/
theorem wordCount_mono {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Monotone (wordCount d x) := fun r _ h =>
  ncard_le_ncard (fun _ (hu : _ ≤ r) => hu.trans h) (finite_setOf_wordDelay_le hx _)

/-- The renewal count is right-continuous in time: it is locally constant to the right of each
`r`, since only finitely many delays lie in `(r, r + 1]`. -/
theorem continuousWithinAt_wordCount_Ici {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    ContinuousWithinAt (wordCount d x) (Ici r) r := by
  have hF := finite_setOf_wordDelay_le hx (r + 1)
  have hev : ∀ᶠ r' in 𝓝 r, r' < r + 1 ∧
      ∀ u ∈ {u : List (ℕ × Fin d) | wordDelay u x ≤ r + 1},
        r < wordDelay u x → r' < wordDelay u x := by
    refine (eventually_lt_nhds (lt_add_one r)).and ((eventually_all_finite hF).2 fun u _ => ?_)
    by_cases h : r < wordDelay u x
    · exact (eventually_lt_nhds h).mono fun _ h' _ => h'
    · exact Eventually.of_forall fun _ h' => absurd h' h
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with r' ⟨h₁, h₂⟩ (hr' : r ≤ r')
  rw [wordCount_def, wordCount_def]
  congr 1
  ext u
  simp only [mem_ofPred_eq]
  exact ⟨fun hu => hu.trans hr',
    fun hu => not_lt.mp fun hlt => (h₂ u (hu.trans h₁.le) hlt).not_ge hu⟩

/-- The renewal count is a measurable function of time. -/
theorem measurable_wordCount {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Measurable (wordCount d x) :=
  (wordCount_mono hx).measurable

/-- A letter `a` contributes to the renewal equation at time `r` only if `A + 3 ≤ 2 e^r`. -/
private theorem fst_add_three_le_of_wordCount_ne_zero {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) {r : ℝ} {a : ℕ × Fin d}
    (h : wordCount d (branchMap a x) (r - Real.log (branchDenom a x)) ≠ 0) :
    (a.1 : ℝ) + 3 ≤ 2 * Real.exp r := by
  obtain ⟨u, hu⟩ := nonempty_of_ncard_ne_zero h
  have hu' : wordDelay (a :: u) x ≤ r := by
    simp only [mem_ofPred_eq] at hu
    rw [wordDelay_cons]
    linarith
  exact (fst_add_three_le_two_mul_exp_wordDelay (u := a :: u) (by simp) hx).trans (by gcongr)

/-- At each time only finitely many letters contribute to the renewal equation. -/
theorem finite_support_wordCount_branchMap {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (r : ℝ) :
    (Function.support fun a : ℕ × Fin d =>
      wordCount d (branchMap a x) (r - Real.log (branchDenom a x))).Finite :=
  (finite_setOf_fst_add_three_le (2 * Real.exp r)).subset fun _ ha =>
    fst_add_three_le_of_wordCount_ne_zero hx ha

/-- **The renewal equation** `N (w, r) = 1{r ≥ 0} + ∑_a N (F_a w, r - τ_a (w))` on the simplex:
the empty word counts exactly when `r ≥ 0`, and a nonempty word `a :: u` counts exactly when `u`
counts at `F_a w` with the delay `τ_a (w)` subtracted. The sum is finite
(`TauCeti.finite_support_wordCount_branchMap`). -/
theorem wordCount_eq_add_finsum {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    wordCount d x r = (if 0 ≤ r then 1 else 0) +
      ∑ᶠ a : ℕ × Fin d, wordCount d (branchMap a x) (r - Real.log (branchDenom a x)) := by
  set T := {a : ℕ × Fin d | (a.1 : ℝ) + 3 ≤ 2 * Real.exp r}
  have hT : T.Finite := finite_setOf_fst_add_three_le _
  set S : ℕ × Fin d → Set (List (ℕ × Fin d)) := fun a =>
    {u | wordDelay u (branchMap a x) ≤ r - Real.log (branchDenom a x)}
  have hS : ∀ a, (S a).Finite := fun a =>
    finite_setOf_wordDelay_le (branchMap_mem_orderedSimplex a hx) _
  have hdecomp : {u : List (ℕ × Fin d) | wordDelay u x ≤ r} =
      {u | u = [] ∧ 0 ≤ r} ∪ ⋃ a ∈ T, List.cons a '' S a := by
    ext u
    cases u with
    | nil => simp
    | cons a u =>
      simp only [mem_ofPred_eq, wordDelay_cons, mem_union, reduceCtorEq, false_and, false_or,
        mem_iUnion, mem_image, List.cons.injEq, exists_prop, S]
      refine ⟨fun h => ⟨a, ?_, u, by linarith, rfl, rfl⟩, ?_⟩
      · refine (fst_add_three_le_two_mul_exp_wordDelay (u := a :: u) (by simp) hx).trans ?_
        rw [wordDelay_cons]
        gcongr
      · rintro ⟨b, -, v, hv, rfl, rfl⟩
        linarith
  have hdisj : Disjoint {u : List (ℕ × Fin d) | u = [] ∧ 0 ≤ r} (⋃ a ∈ T, List.cons a '' S a) := by
    rw [disjoint_left]
    rintro _ ⟨rfl, -⟩ h
    simp at h
  have hpair : T.PairwiseDisjoint fun a => List.cons a '' S a := by
    intro a _ b _ hab
    rw [Function.onFun, disjoint_left]
    rintro _ ⟨u, -, rfl⟩ ⟨v, -, h⟩
    exact hab (List.cons.inj h).1.symm
  rw [wordCount_def, hdecomp, ncard_union_eq hdisj ((finite_singleton []).subset fun _ hu => hu.1)
    (hT.biUnion fun a _ => (hS a).image _),
    hT.ncard_biUnion (fun a _ => (hS a).image _) hpair]
  congr 1
  · split_ifs with h <;> simp [h]
  · simp only [ncard_image_of_injective _ List.cons_injective]
    rw [← finsum_mem_univ fun a => wordCount d (branchMap a x) (r - Real.log (branchDenom a x))]
    exact finsum_mem_inter_support_eq' _ T univ fun a ha =>
      ⟨fun _ => mem_univ _, fun _ => fst_add_three_le_of_wordCount_ne_zero hx ha⟩

end TauCeti
