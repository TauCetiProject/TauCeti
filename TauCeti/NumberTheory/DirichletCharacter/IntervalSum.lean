/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Periodic
import TauCeti.NumberTheory.DirichletCharacter.PartialSum

/-!
# Interval sums of Dirichlet characters

For a Dirichlet character `χ` of level `q`, an integer `M` and a natural number `N`, the
*interval sum* `S_χ(M, N) = ∑_{M < n ≤ M + N} χ n` is the sum of `χ` over the `N` consecutive
integers following `M`. Explicit Pólya–Vinogradov and Burgess inequalities are bounds for these
sums, and they are stated equivalently as bounds for the *maximal interval sum*
`M_χ = max_{0 ≤ M < q, 0 ≤ N ≤ q} ‖S_χ(M, N)‖`, a maximum over finitely many sums.

A nonprincipal character sums to zero over a full period, so its interval sums depend only on
`M` and `N` modulo `q`, and `M_χ` bounds every interval sum. For an even nonprincipal
character with values in a domain the initial sums are antisymmetric about the middle of a
period, and if `χ` takes values in `ℝ` or `ℂ` (more generally an `RCLike` field), then `M_χ` is
exactly twice the largest initial sum `‖∑_{0 < n ≤ N} χ n‖`; for every nonprincipal character
with values in a normed field it is at most twice that.
These are the elementary identities used by Pomerance (*Remarks on the Pólya–Vinogradov
inequality*, Integers 11 (2011)) and by Frolenkov (*Numerically explicit version of the
Pólya–Vinogradov inequality*, arXiv:1107.0381, equation (1)).

## Main definitions

* `DirichletCharacter.intervalSum χ M N`: the interval sum `∑_{M < n ≤ M + N} χ n`.
* `DirichletCharacter.maxIntervalSum χ`: the maximal interval sum `M_χ`, for a character with
  values in a normed field.

## Main statements

* `DirichletCharacter.intervalSum_periodic`: interval sums are `q`-periodic in the left endpoint.
* `DirichletCharacter.intervalSum_level_eq_zero`: a nonprincipal character has interval sum `0`
  over every full period.
* `DirichletCharacter.intervalSum_neg`: reflecting the interval multiplies the sum by `χ (-1)`.
* `DirichletCharacter.isGreatest_maxIntervalSum`: for a nonprincipal character, `M_χ` is the
  largest norm of an interval sum; `isGreatest_maxIntervalSum_Icc` is the same over closed
  intervals.
* `DirichletCharacter.maxIntervalSum_inv`: a complex character and its inverse have the same
  maximal interval sum.
* `DirichletCharacter.Even.intervalSum_level_sub_one_sub`: for an even nonprincipal character,
  `∑_{0 < n ≤ q - 1 - N} χ n = -∑_{0 < n ≤ N} χ n`.
* `DirichletCharacter.Even.maxIntervalSum_eq_two_mul_sup'`: for an even nonprincipal character
  with values in an `RCLike` field, `M_χ = 2 max_{0 ≤ N < q} ‖∑_{0 < n ≤ N} χ n‖`;
  `maxIntervalSum_le_two_mul` is the inequality for every nonprincipal character with values in a
  normed field.
-/

public section

open Finset

namespace DirichletCharacter

section CommSemiring

variable {R : Type*} [CommSemiring R] {q : ℕ} (χ : DirichletCharacter R q)

/-- The **interval sum** `S_χ(M, N) = ∑_{M < n ≤ M + N} χ n` of a Dirichlet character over the
`N` consecutive integers following `M`. -/
def intervalSum (M : ℤ) (N : ℕ) : R :=
  ∑ n ∈ Ioc M (M + N), χ n

theorem intervalSum_def (M : ℤ) (N : ℕ) : χ.intervalSum M N = ∑ n ∈ Ioc M (M + N), χ n :=
  (rfl)

/-- The interval sum as a sum over `range N`: `S_χ(M, N) = ∑_{k < N} χ (M + 1 + k)`. -/
theorem intervalSum_eq_sum_range (M : ℤ) (N : ℕ) :
    χ.intervalSum M N = ∑ k ∈ range N, χ ((M : ZMod q) + 1 + k) := by
  rw [intervalSum_def, Int.Ioc_eq_finset_map, add_sub_cancel_left, Int.toNat_natCast, sum_map]
  simp

@[simp]
theorem intervalSum_zero (M : ℤ) : χ.intervalSum M 0 = 0 := by
  simp [intervalSum_eq_sum_range]

@[simp]
theorem intervalSum_one (M : ℤ) : χ.intervalSum M 1 = χ ((M : ZMod q) + 1) := by
  simp [intervalSum_eq_sum_range]

/-- Interval sums are additive in the length: `S_χ(M, N + N') = S_χ(M, N) + S_χ(M + N, N')`. -/
theorem intervalSum_add (M : ℤ) (N N' : ℕ) :
    χ.intervalSum M (N + N') = χ.intervalSum M N + χ.intervalSum (M + N) N' := by
  simp only [intervalSum_def, Nat.cast_add, ← add_assoc]
  rw [← Ioc_union_Ioc_eq_Ioc (b := M + N) (by omega) (by omega),
    sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]

/-- Extending an interval on the right by one adds the value at the new endpoint. -/
theorem intervalSum_succ (M : ℤ) (N : ℕ) :
    χ.intervalSum M (N + 1) = χ.intervalSum M N + χ ((M : ZMod q) + N + 1) := by
  rw [intervalSum_add, intervalSum_one, Int.cast_add, Int.cast_natCast]

/-- An interval sum of length `N + 1` is its first term plus the sum over the remaining `N`
integers. -/
theorem intervalSum_succ' (M : ℤ) (N : ℕ) :
    χ.intervalSum M (N + 1) = χ ((M : ZMod q) + 1) + χ.intervalSum (M + 1) N := by
  rw [add_comm N, intervalSum_add, intervalSum_one, Nat.cast_one]

/-- A sum over a closed interval `[M, M + N]` is the interval sum `S_χ(M - 1, N + 1)`. -/
theorem sum_Icc_eq_intervalSum (M : ℤ) (N : ℕ) :
    ∑ n ∈ Icc M (M + N), χ n = χ.intervalSum (M - 1) (N + 1) := by
  rw [intervalSum_def, ← Ioc_sub_one_left_eq_Icc]
  congr 2
  push_cast
  ring

/-- An initial interval sum is the sum over `[1, N]` of natural numbers:
`S_χ(0, N) = ∑_{1 ≤ n ≤ N} χ n`. -/
theorem intervalSum_zero_eq_sum_Icc (N : ℕ) : χ.intervalSum 0 N = ∑ n ∈ Icc 1 N, χ n := by
  rw [intervalSum_eq_sum_range, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [add_comm]

/-- Interval sums are `q`-periodic in the left endpoint. -/
theorem intervalSum_periodic (N : ℕ) : Function.Periodic (χ.intervalSum · N) (q : ℤ) := by
  intro M
  simp [intervalSum_eq_sum_range]

/-- An interval sum depends only on the left endpoint modulo the level. -/
theorem intervalSum_emod (M : ℤ) (N : ℕ) : χ.intervalSum (M % q) N = χ.intervalSum M N := by
  rw [Int.emod_def, mul_comm]
  exact (χ.intervalSum_periodic N).sub_int_mul_eq (M / q)

/-- Reflecting an interval about the origin multiplies its sum by `χ (-1)`:
`∑_{-M-N-1 < n ≤ -M-1} χ n = χ (-1) ∑_{M < n ≤ M + N} χ n`. -/
theorem intervalSum_neg (M : ℤ) (N : ℕ) :
    χ.intervalSum (-M - N - 1) N = χ (-1) * χ.intervalSum M N := by
  rw [intervalSum_eq_sum_range, intervalSum_eq_sum_range, mul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [← map_mul]
  congr 1
  have hk : k < N := mem_range.mp hk
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

end CommSemiring

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {q : ℕ} {χ : DirichletCharacter R q}

/-- A nonprincipal character has interval sum `0` over every full period. -/
theorem intervalSum_level_eq_zero (hχ : χ ≠ 1) (M : ℤ) : χ.intervalSum M q = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact χ.intervalSum_zero M
  have : NeZero q := ⟨hq⟩
  -- Moving the interval one step to the right drops `χ (M + 1)` and adds `χ (M + q + 1)`, which
  -- is the same value.
  have hstep (M : ℤ) : χ.intervalSum (M + 1) q = χ.intervalSum M q := by
    have h := (χ.intervalSum_succ M q).symm.trans (χ.intervalSum_succ' M q)
    rw [ZMod.natCast_self, add_zero] at h
    exact add_left_cancel (h.symm.trans (add_comm _ _))
  have hconst (M : ℤ) : χ.intervalSum M q = χ.intervalSum (-1) q := by
    induction M using Int.induction_on with
    | zero => simpa using hstep (-1)
    | succ M ih => rw [hstep, ih]
    | pred M ih => rw [← ih, ← hstep (-M - 1), sub_add_cancel]
  rw [hconst, intervalSum_eq_sum_range]
  simpa using χ.sum_range_level_eq_zero hχ

/-- For a nonprincipal character, adding a full period to the length does not change an
interval sum. -/
theorem intervalSum_add_level (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    χ.intervalSum M (N + q) = χ.intervalSum M N := by
  rw [intervalSum_add, intervalSum_level_eq_zero hχ, add_zero]

/-- For a nonprincipal character, an interval sum depends only on the length modulo the
level. -/
theorem intervalSum_mod_level (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    χ.intervalSum M (N % q) = χ.intervalSum M N := by
  exact Function.Periodic.map_mod_nat (f := (χ.intervalSum M ·))
    (fun N ↦ intervalSum_add_level hχ M N) N

end Domain

section NormedField

variable {F : Type*} [NormedField F] {q : ℕ}

/-- An interval sum of length `N` has norm at most `N`. -/
theorem norm_intervalSum_le (χ : DirichletCharacter F q) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ ≤ N := by
  rw [intervalSum_eq_sum_range]
  exact (norm_sum_le _ _).trans <| by
    simpa using sum_le_sum fun k (_ : k ∈ range N) ↦ χ.norm_le_one ((M : ZMod q) + 1 + k)

variable [NeZero q] (χ : DirichletCharacter F q)

/-- The **maximal interval sum** `M_χ = max_{0 ≤ M < q, 0 ≤ N ≤ q} ‖S_χ(M, N)‖` of a Dirichlet
character with values in a normed field. For a nonprincipal character it bounds every interval
sum (`norm_intervalSum_le_maxIntervalSum`). -/
noncomputable def maxIntervalSum : ℝ :=
  (range q ×ˢ range (q + 1)).sup' (by simp [NeZero.ne q])
    fun p ↦ ‖χ.intervalSum p.1 p.2‖

theorem maxIntervalSum_def :
    χ.maxIntervalSum = (range q ×ˢ range (q + 1)).sup' (by simp [NeZero.ne q])
      fun p ↦ ‖χ.intervalSum p.1 p.2‖ :=
  (rfl)

theorem norm_intervalSum_le_maxIntervalSum_of_lt {M N : ℕ} (hM : M < q) (hN : N ≤ q) :
    ‖χ.intervalSum M N‖ ≤ χ.maxIntervalSum := by
  rw [maxIntervalSum_def]
  exact le_sup' (f := fun p : ℕ × ℕ ↦ ‖χ.intervalSum p.1 p.2‖) (b := (M, N))
    (mem_product.mpr ⟨mem_range.mpr hM, mem_range.mpr (by omega)⟩)

/-- The maximal interval sum is attained. -/
theorem exists_norm_intervalSum_eq_maxIntervalSum :
    ∃ M < q, ∃ N ≤ q, ‖χ.intervalSum M N‖ = χ.maxIntervalSum := by
  obtain ⟨⟨M, N⟩, hp, h⟩ := exists_mem_eq_sup' (s := range q ×ˢ range (q + 1))
    (by simp [NeZero.ne q]) fun p ↦ ‖χ.intervalSum p.1 p.2‖
  simp only [mem_product, mem_range] at hp
  exact ⟨M, hp.1, N, by omega, h.symm⟩

theorem maxIntervalSum_nonneg : 0 ≤ χ.maxIntervalSum :=
  (norm_nonneg _).trans (χ.norm_intervalSum_le_maxIntervalSum_of_lt (NeZero.pos q) le_rfl)

/-- The maximal interval sum is at most the level, since it is a maximum over intervals of
length at most `q`. -/
theorem maxIntervalSum_le_level : χ.maxIntervalSum ≤ q := by
  obtain ⟨M, -, N, hN, h⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
  exact h ▸ (χ.norm_intervalSum_le M N).trans (Nat.cast_le.mpr hN)

variable {χ}

/-- An interval sum of a nonprincipal character has norm at most the level. -/
theorem norm_intervalSum_le_level (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) : ‖χ.intervalSum M N‖ ≤ q := by
  rw [← intervalSum_mod_level hχ]
  exact (χ.norm_intervalSum_le M _).trans (Nat.cast_le.mpr (Nat.mod_lt N (NeZero.pos q)).le)

/-- For a nonprincipal character, the maximal interval sum bounds the norm of every interval
sum. -/
theorem norm_intervalSum_le_maxIntervalSum (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ ≤ χ.maxIntervalSum := by
  -- Reduce `M` modulo `q` by periodicity and `N` modulo `q` by the vanishing over a period.
  have h0 := Int.emod_nonneg M (Int.natCast_ne_zero.mpr (NeZero.ne q))
  rw [← χ.intervalSum_emod, ← intervalSum_mod_level hχ, ← Int.toNat_of_nonneg h0]
  refine χ.norm_intervalSum_le_maxIntervalSum_of_lt ?_ (Nat.mod_lt N (NeZero.pos q)).le
  have := Int.emod_lt_of_pos M (Int.natCast_pos.mpr (NeZero.pos q))
  omega

/-- For a nonprincipal character, `M_χ` is the largest norm of an interval sum. -/
theorem isGreatest_maxIntervalSum (hχ : χ ≠ 1) :
    IsGreatest (Set.range fun p : ℤ × ℕ ↦ ‖χ.intervalSum p.1 p.2‖) χ.maxIntervalSum := by
  obtain ⟨M, -, N, -, h⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
  exact ⟨⟨(M, N), h⟩, Set.forall_mem_range.mpr fun p ↦
    norm_intervalSum_le_maxIntervalSum hχ p.1 p.2⟩

/-- For a nonprincipal character, a bound for `M_χ` is the same as a bound for every interval
sum. -/
theorem maxIntervalSum_le_iff (hχ : χ ≠ 1) {c : ℝ} :
    χ.maxIntervalSum ≤ c ↔ ∀ (M : ℤ) (N : ℕ), ‖χ.intervalSum M N‖ ≤ c := by
  refine ⟨fun h M N ↦ (norm_intervalSum_le_maxIntervalSum hχ M N).trans h, fun h ↦ ?_⟩
  obtain ⟨M, -, N, -, hMN⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
  exact hMN ▸ h M N


/-- For a nonprincipal character, `M_χ` is also the largest norm of a sum over a closed
interval `[M, M + N]`. -/
theorem isGreatest_maxIntervalSum_Icc (hχ : χ ≠ 1) :
    IsGreatest (Set.range fun p : ℤ × ℕ ↦ ‖∑ n ∈ Icc p.1 (p.1 + p.2), χ n‖)
      χ.maxIntervalSum := by
  refine ⟨?_, Set.forall_mem_range.mpr fun p ↦ ?_⟩
  · obtain ⟨M, -, N, -, h⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
    rcases N with _ | N
    · -- The maximum is `0`, so every closed interval attains it.
      refine ⟨(0, 0), le_antisymm ?_ ?_⟩
      · dsimp only
        rw [sum_Icc_eq_intervalSum]
        exact norm_intervalSum_le_maxIntervalSum hχ _ _
      · rw [← h, intervalSum_zero, norm_zero]
        exact norm_nonneg _
    · refine ⟨((M : ℤ) + 1, N), ?_⟩
      simpa [sum_Icc_eq_intervalSum] using h
  · rw [sum_Icc_eq_intervalSum]
    exact norm_intervalSum_le_maxIntervalSum hχ _ _

end NormedField

section Complex

variable {q : ℕ}

/-- The interval sums of the inverse of a complex character are the complex conjugates of
those of the character. -/
theorem intervalSum_inv (χ : DirichletCharacter ℂ q) (M : ℤ) (N : ℕ) :
    χ⁻¹.intervalSum M N = star (χ.intervalSum M N) := by
  simp [intervalSum_def, star_sum, MulChar.star_apply']

/-- A complex character and its inverse have the same maximal interval sum. -/
@[simp]
theorem maxIntervalSum_inv [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ⁻¹.maxIntervalSum = χ.maxIntervalSum := by
  simp only [maxIntervalSum_def, intervalSum_inv, Complex.star_def, Complex.norm_conj]

end Complex

section Parity

variable {R : Type*} [CommRing R] [IsDomain R] {q : ℕ} {χ : DirichletCharacter R q}

/-- For an even nonprincipal character, the initial sums are antisymmetric about the middle of
a period: `∑_{0 < n ≤ q - 1 - N} χ n = -∑_{0 < n ≤ N} χ n` for `N < q`. -/
theorem Even.intervalSum_level_sub_one_sub (hχe : χ.Even) (hχ : χ ≠ 1) {N : ℕ} (hN : N < q) :
    χ.intervalSum 0 (q - 1 - N) = -χ.intervalSum 0 N := by
  have hq : q ≠ 1 := by
    rintro rfl
    exact hχ (Subsingleton.elim _ _)
  -- The rest `(q - 1 - N, q]` of the period is the reflection of `(-1, N]`, whose sum is that
  -- of `(0, N]` because `χ 0 = 0`.
  have hrest : χ.intervalSum ((q - 1 - N : ℕ) : ℤ) (N + 1) = χ.intervalSum 0 N := by
    have hneg : χ.intervalSum (-((N + 1 : ℕ) : ℤ)) (N + 1) = χ.intervalSum (-1) (N + 1) := by
      have h := χ.intervalSum_neg (-1) (N + 1)
      rw [hχe, one_mul] at h
      convert h using 2
      ring
    have hinit : χ.intervalSum (-1) (N + 1) = χ.intervalSum 0 N := by
      simp [intervalSum_succ', χ.map_zero' hq]
    rw [show ((q - 1 - N : ℕ) : ℤ) = -((N + 1 : ℕ) : ℤ) + q by omega]
    exact (χ.intervalSum_periodic (N + 1) _).trans (hneg.trans hinit)
  have h := χ.intervalSum_add 0 (q - 1 - N) (N + 1)
  rw [show q - 1 - N + (N + 1) = q by omega, intervalSum_level_eq_zero hχ, zero_add, hrest] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end Parity

section ParityNorm

variable {F : Type*} [NormedField F] {q : ℕ} [NeZero q] {χ : DirichletCharacter F q}

/-- For a nonprincipal character, `M_χ` is at most twice any bound for the initial sums
`‖∑_{0 < n ≤ N} χ n‖`, `N < q`. -/
theorem maxIntervalSum_le_two_mul (hχ : χ ≠ 1) {c : ℝ}
    (hc : ∀ N < q, ‖χ.intervalSum 0 N‖ ≤ c) : χ.maxIntervalSum ≤ 2 * c := by
  obtain ⟨M, hM, N, -, h⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
  -- `S_χ(M, N)` is the difference of the initial sums up to `M + N` and up to `M`.
  have hsplit := χ.intervalSum_add 0 M N
  rw [zero_add, ← intervalSum_mod_level hχ 0 (M + N)] at hsplit
  rw [← h, eq_sub_of_add_eq' hsplit.symm, two_mul]
  exact (norm_sub_le _ _).trans
    (add_le_add (hc _ (Nat.mod_lt _ (NeZero.pos q))) (hc M hM))

end ParityNorm

section ParityRCLike

variable {F : Type*} [RCLike F] {q : ℕ} [NeZero q] {χ : DirichletCharacter F q}

/-- For an even nonprincipal character, `M_χ` is at least twice every initial sum. -/
theorem Even.two_mul_norm_intervalSum_zero_le (hχe : χ.Even) (hχ : χ ≠ 1) (N : ℕ) :
    2 * ‖χ.intervalSum 0 N‖ ≤ χ.maxIntervalSum := by
  rw [← intervalSum_mod_level hχ]
  set N₀ := N % q
  have hN₀ : N₀ < q := Nat.mod_lt N (NeZero.pos q)
  -- If `a ≤ b < q` and `S_χ(0, b) = -S_χ(0, a)`, the interval `(a, b]` has sum `-2 S_χ(0, a)`.
  have key {a b : ℕ} (hab : a ≤ b) (hb : b < q) (h : χ.intervalSum 0 b = -χ.intervalSum 0 a) :
      2 * ‖χ.intervalSum 0 a‖ ≤ χ.maxIntervalSum := by
    have hs := χ.intervalSum_add 0 a (b - a)
    rw [Nat.add_sub_cancel' hab, h, zero_add] at hs
    have : χ.intervalSum a (b - a) = -(2 * χ.intervalSum 0 a) := by
      linear_combination (-1 : F) * hs
    calc 2 * ‖χ.intervalSum 0 a‖ = ‖χ.intervalSum a (b - a)‖ := by
          rw [this, norm_neg, norm_mul, RCLike.norm_ofNat]
      _ ≤ _ := χ.norm_intervalSum_le_maxIntervalSum_of_lt (hab.trans_lt hb) (by omega)
  -- Apply it to `N₀` and its mirror point `q - 1 - N₀`, in whichever order they come.
  have hmirror := hχe.intervalSum_level_sub_one_sub hχ hN₀
  rcases le_total N₀ (q - 1 - N₀) with hle | hle
  · exact key hle (by omega) hmirror
  · simpa only [hmirror, norm_neg] using key hle hN₀ (by rw [hmirror, neg_neg])

/-- For an even nonprincipal character, `M_χ` is twice the largest initial sum:
`M_χ = 2 max_{0 ≤ N < q} ‖∑_{0 < n ≤ N} χ n‖`. -/
theorem Even.maxIntervalSum_eq_two_mul_sup' (hχe : χ.Even) (hχ : χ ≠ 1) :
    χ.maxIntervalSum = 2 * (range q).sup' (nonempty_range_iff.mpr (NeZero.ne q))
      fun N ↦ ‖χ.intervalSum 0 N‖ := by
  refine le_antisymm (maxIntervalSum_le_two_mul hχ fun N hN ↦
    le_sup' (fun N ↦ ‖χ.intervalSum 0 N‖) (mem_range.mpr hN)) ?_
  obtain ⟨N, -, h⟩ := exists_mem_eq_sup' (nonempty_range_iff.mpr (NeZero.ne q))
    fun N ↦ ‖χ.intervalSum 0 N‖
  rw [h]
  exact hχe.two_mul_norm_intervalSum_zero_le hχ N

end ParityRCLike

end DirichletCharacter
