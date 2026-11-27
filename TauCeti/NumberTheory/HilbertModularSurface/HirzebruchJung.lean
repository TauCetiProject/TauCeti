/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Algebra.ContinuedFractions.Translations
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Hirzebruch–Jung continued fractions of rational numbers

Given integers `0 < r < n`, the **Hirzebruch–Jung (minus) continued fraction**
`n / r = [[b₁, …, bₗ]]` is defined recursively by taking the ceiling quotient
`b₁ = ⌈n / r⌉ ≥ 2` and remainder `r' = b₁ * r - n` (`0 ≤ r' < r`), terminating when
`r' = 0` and otherwise recursing on `(r, r')`:

```text
n / r = b₁ - 1 / (b₂ - 1 / (⋯ - 1 / bₗ)).
```

Equivalently, `n / r` corresponds to the product of `SL₂(ℤ)` step matrices
`∏ i, !![bᵢ, -1; 1, 0]`, which transforms `(n, r)` down to `(1, 0)` in the coprime case.
Reversing the list of digits corresponds to transposing-and-conjugating this matrix product,
which replaces `r mod n` by its multiplicative inverse `r' mod n`. Compared with Mathlib's
regular continued fraction `GenContFract.of ((n : ℚ) / r) = [a₀; a₁, a₂, …]`, each
odd-indexed partial quotient `a₂ₖ₊₁` contributes `a₂ₖ₊₁ - 1` copies of `2`, while
even-indexed partial quotients shift by `+1` or `+2` according to Hirzebruch's conversion
identity.

## Main definitions

* `TauCeti.HilbertModularSurface.hjExpansion`: the minus continued fraction digit list
  `hjExpansion n r : List ℕ` (totalized to `[]` when `r = 0` or `n ≤ r`).
* `TauCeti.HilbertModularSurface.hjLength`: the length of `hjExpansion n r`.
* `TauCeti.HilbertModularSurface.hjEval`: rational evaluation `[[b₁, …, bₗ]]` of a digit list.
* `TauCeti.HilbertModularSurface.hjStepMatrix`, `TauCeti.HilbertModularSurface.hjMatrix`: the
  `2 × 2` integer matrices `!![b, -1; 1, 0]` and their list product.
* `TauCeti.HilbertModularSurface.regCF`, `TauCeti.HilbertModularSurface.regToHJ`: the Euclidean
  regular continued fraction digit list of `n / r` and its conversion to Hirzebruch–Jung digits.

## Main statements

* `TauCeti.HilbertModularSurface.two_le_mem_hjExpansion`: every digit of `hjExpansion n r` is at
  least `2`.
* `TauCeti.HilbertModularSurface.hjEval_hjExpansion`: for `r < n`,
  `hjEval (hjExpansion n r) = n / r`.
* `TauCeti.HilbertModularSurface.hjExpansion_mul_left`,
  `TauCeti.HilbertModularSurface.hjExpansion_div_gcd`: invariance under common positive scaling.
* `TauCeti.HilbertModularSurface.hjExpansion_hjMatrix`,
  `TauCeti.HilbertModularSurface.hjMatrix_hjExpansion_col0_eq_div_gcd`: correspondence between
  `hjExpansion` and the first column of `hjMatrix`.
* `TauCeti.HilbertModularSurface.hjExpansion_reverse`: for `r, r' < n` with `r * r' ≡ 1 [MOD n]`,
  `hjExpansion n r' = (hjExpansion n r).reverse`.
* `TauCeti.HilbertModularSurface.hjExpansion_eq_regToHJ_of_genContFract`: comparison between
  `hjExpansion n r` and Mathlib's `GenContFract.of ((n : ℚ) / r)`.

## References

* F. Hirzebruch, *Hilbert modular surfaces*, L'Enseignement Mathématique 19 (1973), §2.5,
  equation (19).
* W. Fulton, *Introduction to Toric Varieties*, Princeton Univ. Press (1993), §2.6.
-/

public section

namespace TauCeti.HilbertModularSurface

open scoped Matrix

/-! ### Definition and basic properties -/

/-- The Hirzebruch–Jung (minus) continued fraction `[[b₁, …, bₗ]]` of `n / r`, where
`b₁ = ⌈n / r⌉ = (n + r - 1) / r ≥ 2` and the next remainder is `r' = b₁ * r - n < r`.
Totalized to `[]` when `r = 0` or `n ≤ r`. -/
def hjExpansion (n r : ℕ) : List ℕ :=
  if r = 0 ∨ n ≤ r then []
  else
    let b := (n + r - 1) / r
    b :: hjExpansion r (b * r - n)
termination_by r
decreasing_by
  have hnot : ¬(r = 0 ∨ n ≤ r) := by assumption
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h => hnot (Or.inl h)
  have _ : r < n := Nat.lt_of_not_ge fun h => hnot (Or.inr h)
  have hle : ((n + r - 1) / r) * r ≤ n + r - 1 := Nat.div_mul_le_self (n + r - 1) r
  omega

/-- At `r = 0`, `hjExpansion` is empty. -/
@[simp]
theorem hjExpansion_zero (n : ℕ) : hjExpansion n 0 = [] := by
  rw [hjExpansion]
  simp

/-- When `n ≤ r`, `hjExpansion n r` is empty. -/
@[simp]
theorem hjExpansion_of_le {n r : ℕ} (h : n ≤ r) : hjExpansion n r = [] := by
  rw [hjExpansion]
  simp [h]

/-- Recursive step of `hjExpansion` for `0 < r < n`. -/
theorem hjExpansion_of_lt {n r : ℕ} (hr : 0 < r) (h : r < n) :
    hjExpansion n r =
      ((n + r - 1) / r) :: hjExpansion r (((n + r - 1) / r) * r - n) := by
  rw [hjExpansion]
  have hcond : ¬(r = 0 ∨ n ≤ r) := by omega
  simp [hcond]

/-- `hjExpansion n r` is empty if and only if `r = 0` or `n ≤ r`. -/
@[simp]
theorem hjExpansion_eq_nil_iff {n r : ℕ} : hjExpansion n r = [] ↔ r = 0 ∨ n ≤ r := by
  by_cases h : r = 0 ∨ n ≤ r
  · rcases h with rfl | h
    · simp
    · simp [h]
  · have hr : 0 < r := Nat.pos_of_ne_zero fun hr0 => h (Or.inl hr0)
    have hlt : r < n := Nat.lt_of_not_ge fun hle => h (Or.inr hle)
    simp [hjExpansion_of_lt hr hlt, h]

/-- For `0 < r < n`, `hjExpansion n r` is nonempty. -/
theorem hjExpansion_ne_nil {n r : ℕ} (hr : 0 < r) (h : r < n) : hjExpansion n r ≠ [] := by
  rw [ne_eq, hjExpansion_eq_nil_iff]
  omega

/-- Every digit in `hjExpansion n r` is at least `2`. -/
theorem two_le_mem_hjExpansion {n r b : ℕ} (hb : b ∈ hjExpansion n r) : 2 ≤ b := by
  induction r using Nat.strong_induction_on generalizing n with
  | ind r ih =>
    by_cases h : r = 0 ∨ n ≤ r
    · rcases h with rfl | h
      · simp at hb
      · simp [h] at hb
    · have hr0 : 0 < r := Nat.pos_of_ne_zero fun hr => h (Or.inl hr)
      have hnr : r < n := Nat.lt_of_not_ge fun hle => h (Or.inr hle)
      rw [hjExpansion_of_lt hr0 hnr, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact (Nat.le_div_iff_mul_le hr0).mpr (by omega)
      · have hle : ((n + r - 1) / r) * r ≤ n + r - 1 := Nat.div_mul_le_self (n + r - 1) r
        exact ih (((n + r - 1) / r) * r - n) (by omega) hb

/-- The length of the Hirzebruch–Jung continued fraction of `n / r`. -/
def hjLength (n r : ℕ) : ℕ :=
  (hjExpansion n r).length

/-- Characterization of `hjLength`. -/
theorem hjLength_eq (n r : ℕ) : hjLength n r = (hjExpansion n r).length := by
  rw [hjLength]

@[simp]
theorem hjLength_zero (n : ℕ) : hjLength n 0 = 0 := by
  simp [hjLength]

@[simp]
theorem hjLength_of_le {n r : ℕ} (h : n ≤ r) : hjLength n r = 0 := by
  simp [hjLength, h]

@[simp]
theorem hjLength_eq_zero_iff {n r : ℕ} : hjLength n r = 0 ↔ r = 0 ∨ n ≤ r := by
  simp [hjLength]

/-- For `0 < r < n`, `hjLength n r` is positive. -/
theorem hjLength_pos {n r : ℕ} (hr : 0 < r) (h : r < n) : 0 < hjLength n r :=
  List.length_pos_of_ne_nil (hjExpansion_ne_nil hr h)

/-! ### Finite examples -/

/-- `hjExpansion 3 1 = [3]`. -/
theorem hjExpansion_three_one : hjExpansion 3 1 = [3] := by
  rw [hjExpansion_of_lt (by omega) (by omega)]
  norm_num

/-- `hjExpansion 3 2 = [2, 2]`. -/
theorem hjExpansion_three_two : hjExpansion 3 2 = [2, 2] := by
  rw [hjExpansion_of_lt (by omega) (by omega)]
  norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]
  norm_num

/-- `hjExpansion 5 2 = [3, 2]`. -/
theorem hjExpansion_five_two : hjExpansion 5 2 = [3, 2] := by
  rw [hjExpansion_of_lt (by omega) (by omega)]
  norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]
  norm_num

/-- `hjExpansion 5 3 = [2, 3]`. -/
theorem hjExpansion_five_three : hjExpansion 5 3 = [2, 3] := by
  rw [hjExpansion_of_lt (by omega) (by omega)]
  norm_num
  exact hjExpansion_three_one

/-- `hjExpansion 6 5 = [2, 2, 2, 2, 2]`. -/
theorem hjExpansion_six_five : hjExpansion 6 5 = [2, 2, 2, 2, 2] := by
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num

/-- `hjExpansion 12 5 = [3, 2, 3]`. -/
theorem hjExpansion_twelve_five : hjExpansion 12 5 = [3, 2, 3] := by
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num
  exact hjExpansion_five_three

/-- `hjExpansion 12 7 = [2, 4, 2]`. -/
theorem hjExpansion_twelve_seven : hjExpansion 12 7 = [2, 4, 2] := by
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num
  rw [hjExpansion_of_lt (by omega) (by omega)]; norm_num

/-- `hjExpansion 4 2 = hjExpansion 2 1` (both equal `[2]`). -/
theorem hjExpansion_four_two : hjExpansion 4 2 = hjExpansion 2 1 := by
  have h42 : hjExpansion 4 2 = [2] := by
    rw [hjExpansion_of_lt (by omega) (by omega)]
    simp
  have h21 : hjExpansion 2 1 = [2] := by
    rw [hjExpansion_of_lt (by omega) (by omega)]
    simp
  rw [h42, h21]

/-! ### Rational evaluation -/

/-- Evaluate a Hirzebruch–Jung digit list `[[b₁, …, bₗ]]` in `ℚ`:
`[] ↦ 0`, `[b] ↦ b`, and `b :: c :: cs ↦ b - ([[c, …]])⁻¹`. -/
def hjEval : List ℕ → ℚ
  | [] => 0
  | [b] => (b : ℚ)
  | b :: c :: cs => (b : ℚ) - (hjEval (c :: cs))⁻¹

@[simp]
theorem hjEval_nil : hjEval [] = 0 := by
  rw [hjEval]

@[simp]
theorem hjEval_singleton (b : ℕ) : hjEval [b] = (b : ℚ) := by
  rw [hjEval]

/-- Evaluation of a list of length at least two. -/
theorem hjEval_cons_cons (b c : ℕ) (cs : List ℕ) :
    hjEval (b :: c :: cs) = (b : ℚ) - (hjEval (c :: cs))⁻¹ := by
  rw [hjEval]

/-- Evaluation of `b :: cs` when `cs` is nonempty. -/
theorem hjEval_cons_of_ne_nil {b : ℕ} {cs : List ℕ} (hcs : cs ≠ []) :
    hjEval (b :: cs) = (b : ℚ) - (hjEval cs)⁻¹ := by
  cases cs with
  | nil => exact (hcs rfl).elim
  | cons c cs' => rw [hjEval]

/-- Every nonempty list of integers at least `2` evaluates to a rational strictly greater
than `1`. -/
theorem one_lt_hjEval {L : List ℕ} (hL : L ≠ []) (hb : ∀ b ∈ L, 2 ≤ b) :
    1 < hjEval L := by
  induction L with
  | nil => exact (hL rfl).elim
  | cons b cs ih =>
    have hb2 : (2 : ℚ) ≤ b := by exact_mod_cast hb b (by simp)
    cases cs with
    | nil =>
      rw [hjEval_singleton]
      linarith
    | cons c cs' =>
      have hih : 1 < hjEval (c :: cs') :=
        ih (by simp) fun x hx => hb x (by simp [hx])
      have hinv : (hjEval (c :: cs'))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hih
      rw [hjEval_cons_cons]
      linarith

/-- For `r < n`, the Hirzebruch–Jung expansion `hjExpansion n r` evaluates back to `n / r`. -/
theorem hjEval_hjExpansion {n r : ℕ} (h : r < n) :
    hjEval (hjExpansion n r) = (n : ℚ) / r := by
  induction r using Nat.strong_induction_on generalizing n with
  | ind r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp
    · rw [hjExpansion_of_lt hr0 h]
      set b := (n + r - 1) / r
      set r' := b * r - n
      have hle : b * r ≤ n + r - 1 := Nat.div_mul_le_self (n + r - 1) r
      have hlt : n + r - 1 < b * r + r := by
        have := Nat.div_add_mod (n + r - 1) r
        have := Nat.mod_lt (n + r - 1) hr0
        have : b * r = r * ((n + r - 1) / r) := mul_comm b r
        omega
      have hnb : n ≤ b * r := by omega
      have hr'lt : r' < r := by omega
      have hbQ : (b : ℚ) * r - r' = n := by
        have hsum : r' + n = b * r := by omega
        have hsumQ : (r' : ℚ) + n = b * r := by exact_mod_cast hsum
        linarith
      rcases Nat.eq_zero_or_pos r' with hr'0 | hr'pos
      · have hbn : b * r = n := by omega
        rw [hr'0, hjExpansion_zero, hjEval_singleton]
        have hbnQ : (b : ℚ) * r = n := by exact_mod_cast hbn
        have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr0.ne'
        field_simp
        exact hbnQ
      · rw [hjEval_cons_of_ne_nil (hjExpansion_ne_nil hr'pos hr'lt), ih r' hr'lt hr'lt]
        have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr0.ne'
        have _ : (r' : ℚ) ≠ 0 := by exact_mod_cast hr'pos.ne'
        field_simp
        linarith

/-! ### Scaling invariance -/

/-- `hjExpansion` is invariant under multiplying both arguments by a nonzero natural number. -/
theorem hjExpansion_mul_left (k n r : ℕ) (hk : k ≠ 0) :
    hjExpansion (k * n) (k * r) = hjExpansion n r := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  induction r using Nat.strong_induction_on generalizing n with
  | ind r ih =>
    by_cases h : r = 0 ∨ n ≤ r
    · rcases h with rfl | h
      · simp
      · rw [hjExpansion_of_le h, hjExpansion_of_le (Nat.mul_le_mul_left k h)]
    · have hr0 : 0 < r := Nat.pos_of_ne_zero fun hr => h (Or.inl hr)
      have hnr : r < n := Nat.lt_of_not_ge fun hle => h (Or.inr hle)
      have hknr : k * r < k * n := Nat.mul_lt_mul_of_pos_left hnr hk0
      set b := (n + r - 1) / r
      have h1 : b * r ≤ n + r - 1 := Nat.div_mul_le_self (n + r - 1) r
      have h2 : n + r - 1 < b * r + r := by
        have := Nat.div_add_mod (n + r - 1) r
        have := Nat.mod_lt (n + r - 1) hr0
        have : b * r = r * ((n + r - 1) / r) := mul_comm b r
        omega
      have hkr : 0 < k * r := Nat.mul_pos hk0 hr0
      have hceil : (k * n + k * r - 1) / (k * r) = b := by
        have hlow : b * (k * r) ≤ k * n + k * r - 1 := by
          have hbr : b * r + 1 ≤ n + r := by omega
          have : b * (k * r) + k ≤ k * n + k * r := by nlinarith
          omega
        have hhigh : k * n + k * r - 1 < (b + 1) * (k * r) := by
          have hnr' : n + r ≤ (b + 1) * r := by
            have : (b + 1) * r = b * r + r := by ring
            omega
          have hle1 : 1 ≤ k * n + k * r := by nlinarith
          zify [hle1]; nlinarith
        exact Nat.le_antisymm
          (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hkr).mpr hhigh))
          ((Nat.le_div_iff_mul_le hkr).mpr hlow)
      rw [hjExpansion_of_lt hkr hknr, hjExpansion_of_lt hr0 hnr, hceil]
      have hrem : b * (k * r) - k * n = k * (b * r - n) := by
        have : b * (k * r) = k * (b * r) := by ring
        rw [this, ← Nat.mul_sub_left_distrib]
      rw [hrem, ih (b * r - n) (by omega) r]

/-- Dividing both arguments by `Nat.gcd n r` preserves `hjExpansion`. -/
theorem hjExpansion_div_gcd (n r : ℕ) :
    hjExpansion (n / n.gcd r) (r / n.gcd r) = hjExpansion n r := by
  set d := n.gcd r
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have hn0 : n = 0 := (Nat.gcd_eq_zero_iff.mp hd).1
    have hr0 : r = 0 := (Nat.gcd_eq_zero_iff.mp hd).2
    simp [hn0, hr0]
  · have hmul := hjExpansion_mul_left d (n / d) (r / d) hd.ne'
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n r),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)] at hmul
    exact hmul.symm

/-! ### Matrix representation and reversal symmetry -/

/-- The `2 × 2` integer step matrix `!![b, -1; 1, 0]` of determinant `1`. -/
def hjStepMatrix (b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![b, -1; 1, 0]

@[simp]
theorem hjStepMatrix_zero_zero (b : ℤ) : hjStepMatrix b 0 0 = b := by
  rw [hjStepMatrix]; rfl

@[simp]
theorem hjStepMatrix_zero_one (b : ℤ) : hjStepMatrix b 0 1 = -1 := by
  rw [hjStepMatrix]; rfl

@[simp]
theorem hjStepMatrix_one_zero (b : ℤ) : hjStepMatrix b 1 0 = 1 := by
  rw [hjStepMatrix]; rfl

@[simp]
theorem hjStepMatrix_one_one (b : ℤ) : hjStepMatrix b 1 1 = 0 := by
  rw [hjStepMatrix]; rfl

/-- Each step matrix `hjStepMatrix b` has determinant `1`. -/
@[simp]
theorem det_hjStepMatrix (b : ℤ) : (hjStepMatrix b).det = 1 := by
  simp [Matrix.det_fin_two]

/-- The matrix product `∏ b ∈ L, !![b, -1; 1, 0]` associated with a digit list `L`. -/
def hjMatrix (L : List ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (L.map fun b => hjStepMatrix (b : ℤ)).prod

@[simp]
theorem hjMatrix_nil : hjMatrix [] = 1 := by
  simp [hjMatrix]

@[simp]
theorem hjMatrix_cons (b : ℕ) (L : List ℕ) :
    hjMatrix (b :: L) = hjStepMatrix (b : ℤ) * hjMatrix L := by
  simp [hjMatrix]

@[simp]
theorem hjMatrix_append (L₁ L₂ : List ℕ) :
    hjMatrix (L₁ ++ L₂) = hjMatrix L₁ * hjMatrix L₂ := by
  simp [hjMatrix]

/-- Every matrix `hjMatrix L` has determinant `1`. -/
@[simp]
theorem det_hjMatrix (L : List ℕ) : (hjMatrix L).det = 1 := by
  induction L with
  | nil => simp
  | cons b L ih => simp [Matrix.det_mul, ih]

private lemma hjStepMatrix_mul_apply {b : ℤ} (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (hjStepMatrix b * M) 0 0 = b * M 0 0 - M 1 0 ∧
    (hjStepMatrix b * M) 0 1 = b * M 0 1 - M 1 1 ∧
    (hjStepMatrix b * M) 1 0 = M 0 0 ∧
    (hjStepMatrix b * M) 1 1 = M 0 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-- Sign, ordering, and congruence inequalities for `hjMatrix L` when `L ≠ []` and all entries are
at least `2`. -/
theorem hjMatrix_entries {L : List ℕ} (hL : L ≠ []) (hb : ∀ b ∈ L, 2 ≤ b) :
    let M := hjMatrix L
    0 < M 1 0 ∧ M 1 0 < M 0 0 ∧
      0 < -M 0 1 ∧ 0 ≤ -M 1 1 ∧ -M 1 1 ≤ -M 0 1 ∧ -M 0 1 < M 0 0 := by
  induction L with
  | nil => exact (hL rfl).elim
  | cons b L ih =>
    have hb2 : (2 : ℤ) ≤ b := by exact_mod_cast hb b (by simp)
    cases L with
    | nil =>
      dsimp only
      rw [hjMatrix_cons, hjMatrix_nil, mul_one]
      simp only [hjStepMatrix_zero_zero, hjStepMatrix_zero_one, hjStepMatrix_one_zero,
        hjStepMatrix_one_one, neg_neg, neg_zero]
      omega
    | cons c L' =>
      obtain ⟨h10, h00, h01, h11, h11_01, h01_00⟩ :=
        ih (by simp) fun x hx => hb x (by simp [hx])
      obtain ⟨e00, e01, e10, e11⟩ :=
        hjStepMatrix_mul_apply (b := (b : ℤ)) (hjMatrix (c :: L'))
      have hdet : (hjMatrix (b :: c :: L')).det = 1 := det_hjMatrix (b :: c :: L')
      rw [Matrix.det_fin_two] at hdet
      dsimp only
      rw [hjMatrix_cons, e00, e01, e10, e11]
      rw [hjMatrix_cons, e00, e01, e10, e11] at hdet
      set M := hjMatrix (c :: L')
      have hP00 : M 0 0 < b * M 0 0 - M 1 0 := by nlinarith
      have hlt : -(b * M 0 1 - M 1 1) < b * M 0 0 - M 1 0 := by nlinarith
      refine ⟨by omega, hP00, by nlinarith, by omega, by nlinarith, hlt⟩

/-- Recovering `L` as `hjExpansion` of the first column of `hjMatrix L`. -/
theorem hjExpansion_hjMatrix {L : List ℕ} (hb : ∀ b ∈ L, 2 ≤ b) :
    hjExpansion (hjMatrix L 0 0).natAbs (hjMatrix L 1 0).natAbs = L := by
  induction L with
  | nil => simp
  | cons b L ih =>
    have hb2 : 2 ≤ b := hb b (by simp)
    cases L with
    | nil =>
      rw [hjMatrix_cons, hjMatrix_nil, mul_one]
      simp only [hjStepMatrix_zero_zero, hjStepMatrix_one_zero, Int.natAbs_natCast]
      rw [hjExpansion_of_lt (by omega) (by omega)]
      simp
    | cons c L' =>
      obtain ⟨h10, h00, -, -, -, -⟩ :=
        hjMatrix_entries (L := c :: L') (by simp) fun x hx => hb x (by simp [hx])
      have ih_rec := ih fun x hx => hb x (by simp [hx])
      obtain ⟨e00, -, e10, -⟩ := hjStepMatrix_mul_apply (b := (b : ℤ)) (hjMatrix (c :: L'))
      have hP_pos : 0 < b * hjMatrix (c :: L') 0 0 - hjMatrix (c :: L') 1 0 := by
        have : (2 : ℤ) ≤ b := by exact_mod_cast hb2
        nlinarith
      have hQ_nat : ((hjMatrix (b :: c :: L')) 1 0).natAbs = (hjMatrix (c :: L') 0 0).natAbs := by
        rw [hjMatrix_cons, e10]
      set p := (hjMatrix (c :: L') 0 0).natAbs
      set q := (hjMatrix (c :: L') 1 0).natAbs
      have hpZ : (p : ℤ) = hjMatrix (c :: L') 0 0 := Int.natAbs_of_nonneg (by omega)
      have hqZ : (q : ℤ) = hjMatrix (c :: L') 1 0 := Int.natAbs_of_nonneg (by omega)
      have hqp : 0 < q ∧ q < p := by omega
      have hqbp : q ≤ b * p := by
        have : p ≤ b * p := Nat.le_mul_of_pos_left p (by omega); omega
      have hP_nat : ((hjMatrix (b :: c :: L')) 0 0).natAbs = b * p - q := by
        zify [hqbp]; rw [hjMatrix_cons, e00, abs_of_nonneg hP_pos.le, hpZ, hqZ]
      have hdiv : (b * p - q + p - 1) / p = b := by
        have hlow : b * p ≤ b * p - q + p - 1 := by omega
        have hle1 : 1 ≤ b * p - q + p := by omega
        have hhigh : b * p - q + p - 1 < (b + 1) * p := by zify [hle1, hqbp]; nlinarith
        exact Nat.le_antisymm
          (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (hqp.1.trans hqp.2)).mpr hhigh))
          ((Nat.le_div_iff_mul_le (hqp.1.trans hqp.2)).mpr hlow)
      have hlt_pq : p < b * p - q := by
        have : 2 * p ≤ b * p := Nat.mul_le_mul_right p hb2; omega
      rw [hP_nat, hQ_nat, hjExpansion_of_lt (hqp.1.trans hqp.2) hlt_pq, hdiv,
        Nat.sub_sub_self hqbp, ih_rec]

/-- The first column of `hjMatrix (hjExpansion n r)` equals `(n / d, r / d)` for `r < n`,
where `d = Nat.gcd n r`. -/
theorem hjMatrix_hjExpansion_col0_eq_div_gcd {n r : ℕ} (h : r < n) :
    hjMatrix (hjExpansion n r) 0 0 = ((n / n.gcd r : ℕ) : ℤ) ∧
    hjMatrix (hjExpansion n r) 1 0 = ((r / n.gcd r : ℕ) : ℤ) := by
  induction r using Nat.strong_induction_on generalizing n with
  | ind r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [Nat.div_self h]
    · rw [hjExpansion_of_lt hr h]
      set b := (n + r - 1) / r
      set r' := b * r - n
      have hle : b * r ≤ n + r - 1 := Nat.div_mul_le_self (n + r - 1) r
      have hlt : n + r - 1 < b * r + r := by
        have := Nat.div_add_mod (n + r - 1) r; have := Nat.mod_lt (n + r - 1) hr
        have : b * r = r * ((n + r - 1) / r) := mul_comm b r; omega
      have hnb : n ≤ b * r := by omega
      have hr'lt : r' < r := by omega
      rcases Nat.eq_zero_or_pos r' with hr'0 | _
      · have hbn : b * r = n := by omega
        have hd : n.gcd r = r := by rw [← hbn]; exact Nat.gcd_mul_left_left b r
        rw [hr'0, hjExpansion_zero, hjMatrix_cons, hjMatrix_nil, mul_one, hd, Nat.div_self hr]
        simp only [hjStepMatrix_zero_zero, hjStepMatrix_one_zero, Int.natCast_one, and_true]
        rw [← hbn, Nat.mul_div_cancel b hr]
      · obtain ⟨ih0, ih1⟩ := ih r' hr'lt hr'lt
        obtain ⟨e00, -, e10, -⟩ :=
          hjStepMatrix_mul_apply (b := (b : ℤ)) (hjMatrix (hjExpansion r r'))
        have hgcd : r.gcd r' = n.gcd r := by
          refine Nat.dvd_antisymm (Nat.dvd_gcd ?_ (Nat.gcd_dvd_left r r')) (Nat.dvd_gcd
            (Nat.gcd_dvd_right n r) (Nat.dvd_sub (dvd_trans (Nat.gcd_dvd_right n r)
              (dvd_mul_left r b)) (Nat.gcd_dvd_left n r)))
          refine (Nat.dvd_add_right (Nat.gcd_dvd_right r r')).mp ?_
          rw [Nat.sub_add_cancel hnb]
          exact dvd_trans (Nat.gcd_dvd_left r r') (dvd_mul_left r b)
        set d := n.gcd r
        have hd0 : 0 < d := Nat.gcd_pos_of_pos_right n hr
        have hdr : d * (r / d) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
        have hdr' : d * (r' / d) = r' := Nat.mul_div_cancel' (hgcd ▸ Nat.gcd_dvd_right r r')
        have hdn : d * (n / d) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
        have hsub_le : r' / d ≤ b * (r / d) := by
          apply Nat.le_of_mul_le_mul_left _ hd0
          rw [hdr', mul_left_comm, hdr]; exact Nat.sub_le (b * r) n
        have hdiv_eq : b * (r / d) - r' / d = n / d := by
          apply Nat.eq_of_mul_eq_mul_left hd0
          rw [Nat.mul_sub_left_distrib, mul_left_comm, hdr, hdr', hdn]; omega
        rw [hjMatrix_cons, e00, e10, ih0, ih1, hgcd]
        refine ⟨?_, rfl⟩
        zify [hsub_le]; exact_mod_cast hdiv_eq

/-- When `r < n` and `Nat.Coprime n r`, the first column of `hjMatrix (hjExpansion n r)`
is `(n, r)`. -/
theorem hjMatrix_hjExpansion_col0 {n r : ℕ} (h : r < n) (hcop : Nat.Coprime n r) :
    hjMatrix (hjExpansion n r) 0 0 = (n : ℤ) ∧
    hjMatrix (hjExpansion n r) 1 0 = (r : ℤ) := by
  have hcol := hjMatrix_hjExpansion_col0_eq_div_gcd h
  rw [hcop.gcd_eq_one, Nat.div_one, Nat.div_one] at hcol
  exact hcol

private theorem hjMatrix_reverse (L : List ℕ) :
    hjMatrix L.reverse =
      !![(1 : ℤ), 0; 0, -1] * (hjMatrix L)ᵀ * !![(1 : ℤ), 0; 0, -1] := by
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![(1 : ℤ), 0; 0, -1]
  have hSS : S * S = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> decide
  have hSstep (b : ℤ) : S * (hjStepMatrix b)ᵀ * S = hjStepMatrix b := by
    refine Matrix.ext ?_
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩ <;>
      simp only [S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
        hjStepMatrix_zero_zero, hjStepMatrix_zero_one, hjStepMatrix_one_zero,
        hjStepMatrix_one_one, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> ring
  induction L with
  | nil => simp [hSS]
  | cons b L ih =>
    rw [List.reverse_cons, hjMatrix_append]
    nth_rw 2 [hjMatrix_cons]
    rw [Matrix.transpose_mul, hjMatrix_cons, hjMatrix_nil, mul_one]
    calc
      hjMatrix L.reverse * hjStepMatrix (b : ℤ)
        = (S * (hjMatrix L)ᵀ * S) * (S * (hjStepMatrix (b : ℤ))ᵀ * S) := by
          rw [ih, hSstep]
      _ = S * ((hjMatrix L)ᵀ * (S * S) * (hjStepMatrix (b : ℤ))ᵀ) * S := by
          simp only [Matrix.mul_assoc]
      _ = S * ((hjMatrix L)ᵀ * (hjStepMatrix (b : ℤ))ᵀ) * S := by
          rw [hSS, Matrix.mul_one]

private lemma hjMatrix_reverse_zero_zero (L : List ℕ) :
    hjMatrix L.reverse 0 0 = hjMatrix L 0 0 := by
  rw [hjMatrix_reverse]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

private lemma hjMatrix_reverse_one_zero (L : List ℕ) :
    hjMatrix L.reverse 1 0 = -hjMatrix L 0 1 := by
  rw [hjMatrix_reverse]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Reversal symmetry of the Hirzebruch–Jung expansion: if `r, r' < n` and `r * r' ≡ 1 [MOD n]`,
then `hjExpansion n r' = (hjExpansion n r).reverse`. -/
theorem hjExpansion_reverse {n r r' : ℕ} (hr : r < n) (hr' : r' < n)
    (hmod : r * r' ≡ 1 [MOD n]) :
    hjExpansion n r' = (hjExpansion n r).reverse := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have hn1 : n = 1 :=
      Nat.eq_one_of_dvd_one (Nat.modEq_zero_iff_dvd.mp (by simpa using hmod.symm))
    have : r' = 0 := by omega
    subst hn1 this
    simp
  · rcases Nat.eq_zero_or_pos r' with rfl | _
    · have hn1 : n = 1 :=
        Nat.eq_one_of_dvd_one (Nat.modEq_zero_iff_dvd.mp (by simpa using hmod.symm))
      omega
    · have hcop : Nat.Coprime n r := (Nat.coprime_of_mul_modEq_one r' hmod).symm
      set L := hjExpansion n r
      have hL : L ≠ [] := hjExpansion_ne_nil hr0 hr
      have hb : ∀ b ∈ L, 2 ≤ b := fun _ hb => two_le_mem_hjExpansion hb
      obtain ⟨hM00, hM10⟩ := hjMatrix_hjExpansion_col0 hr hcop
      obtain ⟨-, -, h01pos, h11nn, -, h01lt⟩ := hjMatrix_entries hL hb
      set s := (-hjMatrix L 0 1).natAbs
      set t := (-hjMatrix L 1 1).natAbs
      have hdet : (hjMatrix L).det = 1 := det_hjMatrix L
      rw [Matrix.det_fin_two, hM00, hM10] at hdet
      have hrs : r * s = n * t + 1 := by
        have hsZ : hjMatrix L 0 1 = -(s : ℤ) := by omega
        have htZ : hjMatrix L 1 1 = -(t : ℤ) := by omega
        rw [hsZ, htZ] at hdet
        exact_mod_cast (by linarith : (r : ℤ) * s = n * t + 1)
      have hsn : s < n := by
        have : (n : ℤ) = hjMatrix L 0 0 := hM00.symm
        exact Int.ofNat_lt.mp (by omega)
      have hs_eq : r' = s := by
        have hrs_mod : s * r ≡ 1 [MOD n] := by rw [mul_comm, hrs, Nat.ModEq, Nat.mul_add_mod]
        have h1 : r' ≡ s * r * r' [MOD n] := by simpa using hrs_mod.symm.mul_right r'
        have hcong : r' ≡ s [MOD n] := h1.trans (by simpa [mul_assoc] using hmod.mul_left s)
        rw [← Nat.mod_eq_of_lt hr', hcong, Nat.mod_eq_of_lt hsn]
      have hrev := hjExpansion_hjMatrix (L := L.reverse) (by simpa using hb)
      have hMrev0 : (hjMatrix L.reverse 0 0).natAbs = n := by
        rw [hjMatrix_reverse_zero_zero, hM00, Int.natAbs_natCast]
      have hMrev1 : (hjMatrix L.reverse 1 0).natAbs = r' := by
        rw [hjMatrix_reverse_one_zero]; exact hs_eq.symm
      rwa [hMrev0, hMrev1] at hrev

/-! ### Comparison with regular continued fractions (`GenContFract.of`) -/

/-- The finite list of regular continued fraction partial quotients `[a₀, a₁, …, aₖ]` of
`n / r`, computed by the Euclidean algorithm. -/
def regCF (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | r + 1 => (n / (r + 1)) :: regCF (r + 1) (n % (r + 1))
termination_by r => r
decreasing_by
  exact Nat.mod_lt n (Nat.succ_pos r)

@[simp]
theorem regCF_zero (n : ℕ) : regCF n 0 = [] := by
  rw [regCF]

theorem regCF_of_pos {n r : ℕ} (hr : 0 < r) :
    regCF n r = (n / r) :: regCF r (n % r) := by
  rcases r with _ | r
  · exact (Nat.not_lt_zero 0 hr).elim
  · rw [regCF]

/-- Hirzebruch's conversion from a list of regular continued fraction partial quotients
`[a₀, a₁, …, aₖ]` to Hirzebruch–Jung minus continued fraction digits. -/
def regToHJ : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | [a, b] => (a + 1) :: List.replicate (b - 1) 2
  | a :: b :: c :: rest =>
      (a + 1) :: List.replicate (b - 1) 2 ++ regToHJ ((c + 1) :: rest)
termination_by L => L.length

@[simp]
theorem regToHJ_nil : regToHJ [] = [] := by
  rw [regToHJ]

@[simp]
theorem regToHJ_singleton (a : ℕ) : regToHJ [a] = [a] := by
  rw [regToHJ]

@[simp]
theorem regToHJ_pair (a b : ℕ) :
    regToHJ [a, b] = (a + 1) :: List.replicate (b - 1) 2 := by
  rw [regToHJ]

@[simp]
theorem regToHJ_cons_cons_cons (a b c : ℕ) (rest : List ℕ) :
    regToHJ (a :: b :: c :: rest) =
      (a + 1) :: List.replicate (b - 1) 2 ++ regToHJ ((c + 1) :: rest) := by
  rw [regToHJ]

private lemma hjExpansion_replicate_two (k m m' : ℕ) (hm : m' < m) :
    hjExpansion ((k + 1) * m + m') (k * m + m') =
      List.replicate k 2 ++ hjExpansion (m + m') m' := by
  induction k with
  | zero => simp
  | succ j ih =>
    have hm0 : 0 < m := by omega
    have hv0 : 0 < (j + 1) * m + m' := by
      have : 1 * m ≤ (j + 1) * m := Nat.mul_le_mul_right m (by omega)
      omega
    have hvu : (j + 1) * m + m' < (j + 2) * m + m' := by
      have : (j + 2) * m = (j + 1) * m + m := by ring
      omega
    have hdiv : ((j + 2) * m + m' + ((j + 1) * m + m') - 1) / ((j + 1) * m + m') = 2 := by
      have hlow : 2 * ((j + 1) * m + m') ≤ (j + 2) * m + m' + ((j + 1) * m + m') - 1 := by
        have : (j + 2) * m + (j + 1) * m = 2 * ((j + 1) * m) + m := by ring
        omega
      have hle1 : 1 ≤ (j + 2) * m + m' + ((j + 1) * m + m') := by omega
      have hhigh : (j + 2) * m + m' + ((j + 1) * m + m') - 1 < 3 * ((j + 1) * m + m') := by
        zify [hle1]
        have : (0 : ℤ) ≤ j * m := by positivity
        linarith
      exact Nat.le_antisymm
        (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hv0).mpr hhigh))
        ((Nat.le_div_iff_mul_le hv0).mpr hlow)
    have hrem_le : (j + 2) * m + m' ≤ 2 * ((j + 1) * m + m') := by
      have : (j + 2) * m ≤ 2 * ((j + 1) * m) := by
        zify
        have : (0 : ℤ) ≤ j * m := by positivity
        linarith
      omega
    have hrem : 2 * ((j + 1) * m + m') - ((j + 2) * m + m') = j * m + m' := by
      zify [hrem_le]
      ring
    have hadd : (j + 1 + 1) * m + m' = (j + 2) * m + m' := by ring
    rw [hadd, hjExpansion_of_lt hv0 hvu, hdiv, hrem, ih]
    simp [List.replicate_succ]

private lemma hjExpansion_mod_step {n r : ℕ} (hr0 : 0 < r) (h : r < n) (hm0 : 0 < n % r) :
    hjExpansion n r =
      (n / r + 1) :: List.replicate (r / (n % r) - 1) 2 ++
        hjExpansion (n % r + r % (n % r)) (r % (n % r)) := by
  set a₀ := n / r
  set m := n % r
  have hdiv : n = a₀ * r + m := by rw [mul_comm]; exact (Nat.div_add_mod n r).symm
  have hm_lt : m < r := Nat.mod_lt n hr0
  have ha₁ : 1 ≤ r / m := Nat.div_pos hm_lt.le hm0
  set a₁ := r / m
  set m' := r % m
  have hr_div : r = a₁ * m + m' := by rw [mul_comm]; exact (Nat.div_add_mod r m).symm
  have hm'_lt : m' < m := Nat.mod_lt r hm0
  have hceil : (n + r - 1) / r = a₀ + 1 := by
    have hle1 : 1 ≤ a₀ * r + m + r := by omega
    have hlow : (a₀ + 1) * r ≤ n + r - 1 := by rw [hdiv]; zify [hle1]; linarith
    have hhigh : n + r - 1 < (a₀ + 2) * r := by rw [hdiv]; zify [hle1]; linarith
    exact Nat.le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hr0).mpr hhigh))
      ((Nat.le_div_iff_mul_le hr0).mpr hlow)
  have hrem : (a₀ + 1) * r - n = r - m := by
    have hn_le : n ≤ (a₀ + 1) * r := by nlinarith
    have hm_le : m ≤ r := by omega
    zify [hn_le, hm_le]
    nlinarith
  have hr_eq : r = ((a₁ - 1) + 1) * m + m' := by rw [Nat.sub_add_cancel ha₁]; exact hr_div
  have hrm_eq : r - m = (a₁ - 1) * m + m' := by
    have hm_le : m ≤ r := by omega
    zify [hm_le, ha₁]; nlinarith
  rw [hjExpansion_of_lt hr0 h, hceil, hrem]
  conv_lhs => arg 2; arg 1; rw [hr_eq]
  conv_lhs => arg 2; arg 2; rw [hrm_eq]
  rw [hjExpansion_replicate_two (a₁ - 1) m m' hm'_lt]
  rfl

/-- For `r < n`, `hjExpansion n r` equals `regToHJ (regCF n r)`. -/
theorem hjExpansion_eq_regToHJ_regCF {n r : ℕ} (h : r < n) :
    hjExpansion n r = regToHJ (regCF n r) := by
  induction r using Nat.strong_induction_on generalizing n with
  | ind r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp
    · set a₀ := n / r
      set m := n % r
      have hm_lt : m < r := Nat.mod_lt n hr0
      rw [regCF_of_pos hr0]
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · have hnr : n = a₀ * r := by
          rw [mul_comm]
          exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm0)).symm
        have hm_eq : n % r = 0 := hm0
        rw [hm_eq, regCF_zero, regToHJ_singleton, hjExpansion_of_lt hr0 h]
        have hceil : (n + r - 1) / r = a₀ := by
          have hlow : a₀ * r ≤ n + r - 1 := by omega
          have hle1 : 1 ≤ a₀ * r + r := by omega
          have hhigh : n + r - 1 < (a₀ + 1) * r := by rw [hnr]; zify [hle1]; linarith
          exact Nat.le_antisymm
            (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hr0).mpr hhigh))
            ((Nat.le_div_iff_mul_le hr0).mpr hlow)
        rw [hceil, ← hnr, Nat.sub_self, hjExpansion_zero]
      · rw [hjExpansion_mod_step hr0 h hm0, regCF_of_pos hm0]
        set m' := r % m
        rcases Nat.eq_zero_or_pos m' with hm'0 | hm'0
        · rw [hm'0, regCF_zero, regToHJ_pair]
          simp [m]
        · rw [regCF_of_pos hm'0, regToHJ_cons_cons_cons]
          congr 2
          have hm'_lt_r : m' < r := lt_of_lt_of_le (Nat.mod_lt r hm0) (Nat.le_of_lt hm_lt)
          have ih' := ih m' hm'_lt_r (n := m + m') (by omega)
          rw [regCF_of_pos hm'0, Nat.add_div_right _ hm'0, Nat.add_mod_right m m'] at ih'
          exact ih'

/-- The head term of Mathlib's `GenContFract.of ((n : ℚ) / r)` agrees with
`(regCF n r).headD 0`. -/
theorem of_h_eq_headD_regCF (n r : ℕ) :
    (GenContFract.of ((n : ℚ) / r)).h = ((regCF n r).headD 0 : ℤ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [GenContFract.of_h_eq_floor, Rat.floor_natCast_div_natCast, regCF_of_pos hr]
    rfl

private lemma of_partDens_none_of_dvd {n r : ℕ} (h : r = 0 ∨ n % r = 0) (k : ℕ) :
    (GenContFract.of ((n : ℚ) / r)).partDens.get? k = none ∧ (regCF n r).tail = [] := by
  have hs : (GenContFract.of ((n : ℚ) / r)).s = Stream'.Seq.nil ∧ (regCF n r).tail = [] := by
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨?_, by simp⟩
      simpa using GenContFract.of_s_of_int ℚ 0
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      have hm0 : n % r = 0 := h.resolve_left hr0
      have hfr : Int.fract ((n : ℚ) / r) = 0 := by
        rw [Int.fract_div_natCast_eq_div_natCast_mod, hm0]; simp
      have hrat : (n : ℚ) / r = (((n / r : ℕ) : ℤ) : ℚ) := by
        have := eq_of_sub_eq_zero hfr
        rwa [Rat.floor_natCast_div_natCast] at this
      refine ⟨?_, ?_⟩
      · rw [hrat]; exact GenContFract.of_s_of_int ℚ _
      · rw [regCF_of_pos hr, List.tail_cons, hm0, regCF_zero]
  exact ⟨GenContFract.partDen_none_iff_s_none.mpr (by simp [hs.1]), hs.2⟩

private lemma of_partDens_succ_eq (n r k : ℕ) :
    (GenContFract.of ((n : ℚ) / r)).partDens.get? (k + 1) =
      (GenContFract.of ((r : ℚ) / (n % r : ℕ))).partDens.get? k := by
  have hinv : (Int.fract ((n : ℚ) / r))⁻¹ = (r : ℚ) / (n % r : ℕ) := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  cases hs : (GenContFract.of ((n : ℚ) / r)).s.get? (k + 1) with
  | none =>
    have hs1 := GenContFract.partDen_none_iff_s_none.mpr hs
    rw [GenContFract.of_s_succ, hinv] at hs
    rw [hs1, GenContFract.partDen_none_iff_s_none.mpr hs]
  | some gp =>
    have hs1 := GenContFract.partDen_eq_s_b hs
    rw [GenContFract.of_s_succ, hinv] at hs
    rw [hs1, GenContFract.partDen_eq_s_b hs]

/-- The partial denominators of Mathlib's `GenContFract.of ((n : ℚ) / r)` are the tail of
`regCF n r`. -/
theorem of_partDens_get?_eq_tail_regCF (n r k : ℕ) :
    (GenContFract.of ((n : ℚ) / r)).partDens.get? k =
      ((regCF n r).tail[k]?.map (Nat.cast : ℕ → ℚ)) := by
  induction k generalizing n r with
  | zero =>
    rcases eq_or_ne r 0 with rfl | hr0
    · obtain ⟨hp, ht⟩ := of_partDens_none_of_dvd (n := n) (r := 0) (Or.inl rfl) 0
      rw [hp, ht]; rfl
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      rcases eq_or_ne (n % r) 0 with hm0 | hm0
      · obtain ⟨hp, ht⟩ := of_partDens_none_of_dvd (Or.inr hm0) 0
        rw [hp, ht]; rfl
      · have hm_pos : 0 < n % r := Nat.pos_of_ne_zero hm0
        have hfr : Int.fract ((n : ℚ) / r) ≠ 0 := by
          rw [Int.fract_div_natCast_eq_div_natCast_mod]
          exact div_ne_zero (by exact_mod_cast hm0) (by exact_mod_cast hr0)
        have hinv : (Int.fract ((n : ℚ) / r))⁻¹ = (r : ℚ) / (n % r : ℕ) := by
          rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
        have hs : (GenContFract.of ((n : ℚ) / r)).s.get? 0 =
            some ⟨1, ⌊(Int.fract ((n : ℚ) / r))⁻¹⌋⟩ := GenContFract.of_s_head hfr
        rw [GenContFract.partDen_eq_s_b hs, hinv, Rat.floor_natCast_div_natCast,
          ← Int.natCast_ediv, regCF_of_pos hr, List.tail_cons, regCF_of_pos hm_pos]
        simp only [List.getElem?_cons_zero, Option.map_some, Int.cast_natCast]
  | succ k ih =>
    rcases eq_or_ne r 0 with rfl | hr0
    · obtain ⟨hp, ht⟩ := of_partDens_none_of_dvd (n := n) (r := 0) (Or.inl rfl) (k + 1)
      rw [hp, ht]; rfl
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      rcases eq_or_ne (n % r) 0 with hm0 | hm0
      · obtain ⟨hp, ht⟩ := of_partDens_none_of_dvd (Or.inr hm0) (k + 1)
        rw [hp, ht]; rfl
      · have hm_pos : 0 < n % r := Nat.pos_of_ne_zero hm0
        rw [of_partDens_succ_eq n r k, ih r (n % r), regCF_of_pos hr, List.tail_cons,
          regCF_of_pos hm_pos, List.tail_cons]
        rfl

/-- Comparison with Mathlib's regular continued fraction: for `0 < r < n`, if
`GenContFract.of ((n : ℚ) / r)` has head `a₀` and partial denominators `as`, then
`hjExpansion n r = regToHJ (a₀ :: as)`. -/
theorem hjExpansion_eq_regToHJ_of_genContFract {n r a₀ : ℕ} {as : List ℕ}
    (hr : 0 < r) (h : r < n)
    (hh : (GenContFract.of ((n : ℚ) / r)).h = (a₀ : ℤ))
    (has : ∀ k : ℕ,
      (GenContFract.of ((n : ℚ) / r)).partDens.get? k = as[k]?.map (Nat.cast : ℕ → ℚ)) :
    hjExpansion n r = regToHJ (a₀ :: as) := by
  have ha₀ : a₀ = n / r := by
    rw [of_h_eq_headD_regCF, regCF_of_pos hr] at hh
    exact_mod_cast hh.symm
  have has_eq : as = (regCF n r).tail := by
    apply List.ext_getElem?
    intro k
    have hk := (has k).symm.trans (of_partDens_get?_eq_tail_regCF n r k)
    exact Option.map_injective Nat.cast_injective hk
  rw [hjExpansion_eq_regToHJ_regCF h, regCF_of_pos hr]
  rw [regCF_of_pos hr, List.tail_cons] at has_eq
  rw [ha₀, has_eq]

end TauCeti.HilbertModularSurface
