/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.SuccPred.Int
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sums over intervals of natural numbers and integers

A sum `∑ k ∈ Ico m (n + 1), f k` whose summands split as `f m = β m`, `f n = γ n`, and
`f k = γ k + β k` for `m < k < n` regroups as the sum over `m ≤ k < n` of the adjacent pairs
`β k + γ (k + 1)`. The codomain is any additive commutative monoid. In a not necessarily
associative ring, a constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it.
For an integer interval `[-a, b]` with `a, b : ℕ`, adding the term `F 0` to
`∑ i ∈ Icc (-(a : ℤ)) b, F i` splits the sum into the nonnegative part `∑ j ∈ range (b + 1), F j`
and the nonpositive part `∑ j ∈ range (a + 1), F (-(j : ℤ))`. The centred interval `[-n, n]`
reindexes as `range (2 n + 1)` shifted by `-n`. In a ring, the partial sums
`∑_{1 ≤ k ≤ n} (-1) ^ (k + 1)` of the alternating sequence `1, -1, 1, …` are `0` or `1`.
The sum of squares `∑_{r < n} r ^ 2 = n (n - 1) (2 n - 1) / 6` holds in `ℕ`, and with the
denominator cleared it holds in any ring, as does Gauss's sum `2 ∑_{r < n} r = n (n - 1)`.
Read backwards, `∑_{j < n} (n - j) = n (n + 1) / 2` in `ℕ`.
Counted with sign, the integers between `0` and any `k : ℤ` sum to `k (k - 1) / 2`, the signed
form of Gauss's sum; more generally, the signed partial sums of a sequence indexed by `ℤ` form its
discrete primitive vanishing at `0`. Grouping `i < n` into blocks of length `H`, the quotients
`i / H` sum to `H (q choose 2) + ρ q` for `n = H q + ρ` with `ρ < H`.
A sum over `Icc 0 N` of a sequence vanishing at `0` is its sum over `Icc 1 N`.
A window sum `∑_{j - L ≤ k < j + L} f k` is the sum over `d < 2 L` of the shifts of `f` that read
`f` at `j + d - L` where this index is defined, and vanish otherwise.
Along a sequence of sets `V : ℕ → Set M` with `0 ∈ V n` and `V (n + 1) + V (n + 1) ⊆ V n`, any
sequence satisfying `x i ∈ V (i + 1)` has tail sums `∑ i ∈ Ico n (n + m), x i` in `V n`.
For naturals `N` and `K`, writing the weight `⌊K N / n⌋` of `∑_{N < n ≤ K N} ⌊K N / n⌋ f(n)` as the
number of `1 ≤ j < K` with `n ≤ K N / j` and swapping the sums gives
`∑_{1 ≤ j < K} ∑_{N < n ≤ K N / j} f(n)`.
For `0 < n ≤ H`, each distance `k = |n - n'|` with `0 < n' ≤ H` lies in `[0, H)` and is taken
by at most two `n'`, so `∑_{0 < n' ≤ H} w(|n - n'|) ≤ 2 w(0) + 2 ∑_{1 ≤ k ≤ H} w(k)` for `w ≥ 0`.

## Main results

* `Finset.sum_range_sum_range_ite_int_sub_eq_nsmul`: pairs `i, j < N` with integer difference
  `k` contribute `N - k.natAbs` copies of a fixed element of an additive commutative monoid.

* `Finset.sum_Ico_eq_sum_Ico_add`: the regrouping of `∑ k ∈ Ico m (n + 1), f k` into the pairs
  `β k + γ (k + 1)`.
* `Finset.sum_Ico_one_sub_one_const`: `∑ _k ∈ Ico 1 (n - 1), c = (n - 2) * c` for `2 ≤ n`.
* `Finset.sum_Icc_eq_add_sum_range`: `(∑ i ∈ Icc (-(a : ℤ)) b, F i) + F 0` equals the sum of `F j`
  over `j ∈ range (b + 1)` plus the sum of `F (-(j : ℤ))` over `j ∈ range (a + 1)`.
* `Finset.sum_Ioc_neg_zero_eq_sum_range`: the sum of `F j` over `-a < j ≤ 0` is the sum of
  `F (-(k : ℤ))` over `k < a`.
* `Finset.sum_Icc_neg_natCast_eq_sum_range`: the sum of `F j` over `-n ≤ j ≤ n` is the sum of
  `F (k - n)` over `k < 2 n + 1`.
* `Finset.sum_range_natCast_mul_two`, `Finset.sum_range_id_sq_mul_six`, `Finset.sum_range_id_sq`,
  `Finset.sum_range_natCast_sq_mul_six`: Gauss's sum in a ring and the sum of squares below `n`.
* `Finset.sum_range_div`: `∑ i < n, i / H = H (q choose 2) + ρ q` with `q = n / H`, `ρ = n % H`.
* `Finset.sum_range_sub_mul_two`: twice the sum of `r + 1 - j` over `j < e` is `e (2 r + 3 - e)`.
* `Finset.sum_range_sub_id`: the sum of `n - j` over `j < n` is `n (n + 1) / 2`.
* `Finset.sum_Icc_neg_one_pow_add_one`: `∑ k ∈ Icc 1 n, (-1) ^ (k + 1)` is `0` for even `n` and
  `1` for odd `n`.
* `Finset.sum_Ico_zero_add_one_sub_sum_Ico_add_one_zero`: the signed partial sums
  `∑_{0 ≤ j < i} a j - ∑_{i ≤ j < 0} a j` of a sequence `a : ℤ → M` increase by `a i` from `i` to
  `i + 1`.
* `Finset.two_mul_sum_Ico_zero_sub_sum_Ico_zero`: twice `∑_{0 ≤ j < k} j - ∑_{k ≤ j < 0} j` is
  `k (k - 1)` for every `k : ℤ`.
* `Finset.sum_Icc_zero_eq_sum_Icc_one`: a sum over `Icc 0 N` of a sequence vanishing at `0` is
  its sum over `Icc 1 N`.
* `Finset.sum_Ico_sub_add_eq_sum_range_indicator`: a window sum `∑_{j - L ≤ k < j + L} f k` as the
  sum of `2 L` shifts of `f`.
* `Finset.sum_Ico_mem_of_add_subset`: tail-sum bounds along a doubling sequence
  `V (n + 1) + V (n + 1) ⊆ V n` for errors `x i ∈ V (i + 1)`.
* `Finset.prod_Ico_mul_mul_endpoints`, `Finset.sum_Ico_add_add_endpoints`: trapezoidal pairing of
  adjacent products or sums over `Ico a n` (`a ≤ n` in `ℤ`) with the two endpoints.
* `Finset.sum_Ioc_div_smul_eq_sum_Ico_sum_Ioc`:
  `∑_{N < n ≤ K N} ⌊K N / n⌋ f(n) = ∑_{1 ≤ j < K} ∑_{N < n ≤ K N / j} f(n)`.
* `Finset.sum_Ioc_dist_le`: `∑_{0 < n' ≤ H} w(|n - n'|) ≤ 2 w(0) + 2 ∑_{1 ≤ k ≤ H} w(k)` for
  `0 < n ≤ H` and nonnegative `w`.
-/

public section

namespace Finset

open scoped Pointwise

/-- Counting pairs of natural numbers below `N` with prescribed integer difference, with
one copy of `c` for each pair. There are `N - |k|` such pairs, truncated to zero. -/
theorem sum_range_sum_range_ite_int_sub_eq_nsmul {M : Type*} [AddCommMonoid M]
    (N : ℕ) (k : ℤ) (c : M) :
    (∑ i ∈ range N, ∑ j ∈ range N, if (i : ℤ) - j = k then c else 0) =
      (N - k.natAbs) • c := by
  have hnat (m : ℕ) :
      (∑ i ∈ range N, ∑ j ∈ range N, if (i : ℤ) - j = (m : ℤ) then c else 0) =
        (N - m) • c := by
    have hi (i : ℕ) (hi : i ∈ range N) :
        (∑ j ∈ range N, if (i : ℤ) - j = (m : ℤ) then c else 0) =
          if m ≤ i then c else 0 := by
      by_cases hmi : m ≤ i
      · rw [ite_eq_left hmi, sum_eq_single (i - m)]
        · rw [ite_eq_left (by omega)]
        · intro j _hj hne
          rw [ite_eq_right (by omega)]
        · intro hnot
          exact (hnot (mem_range.mpr
            (lt_of_le_of_lt (Nat.sub_le i m) (mem_range.mp hi)))).elim
      · rw [ite_eq_right hmi]
        apply sum_eq_zero
        intro j _
        rw [ite_eq_right (by omega)]
    rw [sum_congr rfl hi, ← sum_filter, sum_const]
    have hs : (range N).filter (m ≤ ·) = Ico m N := by
      ext i
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    rw [hs, Nat.card_Ico]
  rcases k.eq_nat_or_neg with ⟨m, rfl | rfl⟩
  · simpa using hnat m
  · rw [sum_comm]
    have heq (i j : ℕ) : (i : ℤ) - j = -(m : ℤ) ↔ (j : ℤ) - i = (m : ℤ) := by omega
    simp_rw [heq]
    simpa using hnat m

/-- If `m < n`, the summands `f m = β m`, `f n = γ n`, and `f k = γ k + β k` for
`m < k < n` regroup as the adjacent pairs `β k + γ (k + 1)` over `m ≤ k < n`. -/
theorem sum_Ico_eq_sum_Ico_add {M : Type*} [AddCommMonoid M] {f β γ : ℕ → M} {m n : ℕ}
    (hmn : m < n) (hfirst : f m = β m) (hmid : ∀ k ∈ Ico (m + 1) n, f k = γ k + β k)
    (hlast : f n = γ n) :
    ∑ k ∈ Ico m (n + 1), f k = ∑ k ∈ Ico m n, (β k + γ (k + 1)) := by
  -- peel off the endpoint summands
  have hf : ∑ k ∈ Ico m (n + 1), f k = f m + ∑ k ∈ Ico (m + 1) n, f k + f n := by
    rw [sum_eq_sum_Ico_succ_bot (by omega), sum_Ico_succ_top (by omega), add_assoc]
  -- peel off the first `β`-summand
  have hβ : ∑ k ∈ Ico m n, β k = β m + ∑ k ∈ Ico (m + 1) n, β k :=
    sum_eq_sum_Ico_succ_bot hmn β
  -- shift the `γ`-summands down by one and peel off the last one
  have hγ : ∑ k ∈ Ico m n, γ (k + 1) = ∑ k ∈ Ico (m + 1) n, γ k + γ n := by
    rw [sum_Ico_add' γ, sum_Ico_succ_top (by omega : m + 1 ≤ n)]
  simp only [hf, sum_congr rfl hmid, sum_add_distrib, hβ, hγ, hfirst, hlast]
  abel

/-- A constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it. -/
theorem sum_Ico_one_sub_one_const {R : Type*} [NonAssocRing R] {n : ℕ} (hn : 2 ≤ n) (c : R) :
    ∑ _k ∈ Ico 1 (n - 1), c = ((n : R) - 2) * c := by
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.sub_sub, Nat.cast_sub hn, Nat.cast_ofNat]

/-- Splitting an integer interval `[-a, b]` into its parts `0 ≤ j ≤ b` and `-a ≤ -j ≤ 0`, which
overlap in `0`. -/
theorem sum_Icc_eq_add_sum_range {M : Type*} [AddCommMonoid M] (F : ℤ → M) (a b : ℕ) :
    (∑ i ∈ Icc (-(a : ℤ)) b, F i) + F 0 =
      (∑ j ∈ range (b + 1), F j) + ∑ j ∈ range (a + 1), F (-(j : ℤ)) := by
  classical
  set s : Finset ℤ := (range (b + 1)).image (fun j : ℕ ↦ (j : ℤ)) with hs
  set t : Finset ℤ := (range (a + 1)).image (fun j : ℕ ↦ -(j : ℤ)) with ht
  have hunion : s ∪ t = Icc (-(a : ℤ)) b := by
    ext i
    simp only [hs, ht, mem_union, mem_image, mem_range, mem_Icc]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
    · intro hi
      rcases le_or_gt 0 i with h | h
      · exact Or.inl ⟨i.toNat, by omega, by omega⟩
      · exact Or.inr ⟨(-i).toNat, by omega, by omega⟩
  have hinter : s ∩ t = {(0 : ℤ)} := by
    ext i
    simp only [hs, ht, mem_inter, mem_image, mem_range, mem_singleton]
    constructor
    · rintro ⟨⟨j, _, rfl⟩, k, _, hk'⟩
      omega
    · rintro rfl
      exact ⟨⟨0, by omega, by simp⟩, 0, by omega, by simp⟩
  have hkey := sum_union_inter (s₁ := s) (s₂ := t) (f := F)
  rw [hunion, hinter, sum_singleton] at hkey
  rw [hkey, hs, ht, sum_image (fun _ _ _ _ h ↦ by exact_mod_cast h),
    sum_image (fun _ _ _ _ h ↦ by omega)]

/-- Reindexing a nonpositive integer interval: the sum of `F j` over `-a < j ≤ 0` is the sum of
`F (-(k : ℤ))` over `k < a`. -/
theorem sum_Ioc_neg_zero_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ℤ → M) (a : ℕ) :
    ∑ j ∈ Ioc (-(a : ℤ)) 0, F j = ∑ k ∈ range a, F (-(k : ℤ)) := by
  refine sum_nbij' (fun j ↦ (-j).toNat) (fun k ↦ -(k : ℤ)) (fun j hj ↦ ?_) (fun k hk ↦ ?_)
    (fun j hj ↦ ?_) (fun k _ ↦ by simp) (fun j hj ↦ ?_)
  · simp only [mem_Ioc, mem_range] at hj ⊢
    omega
  · simp only [mem_Ioc, mem_range] at hk ⊢
    omega
  · simp only [mem_Ioc] at hj
    omega
  · simp only [mem_Ioc] at hj
    rw [Int.toNat_of_nonneg (by omega), neg_neg]

/-- Reindexing a centred integer interval: the sum of `F j` over `-n ≤ j ≤ n` is the sum of
`F (k - n)` over `k < 2 n + 1`. -/
theorem sum_Icc_neg_natCast_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ℤ → M) (n : ℕ) :
    ∑ j ∈ Icc (-(n : ℤ)) n, F j = ∑ k ∈ range (2 * n + 1), F (k - n) := by
  refine sum_nbij' (fun j ↦ (j + n).toNat) (fun k ↦ (k : ℤ) - n) (fun j hj ↦ ?_) (fun k hk ↦ ?_)
    (fun j hj ↦ ?_) (fun k _ ↦ by simp) (fun j hj ↦ ?_)
  · simp only [mem_Icc, mem_range] at hj ⊢
    omega
  · simp only [mem_Icc, mem_range] at hk ⊢
    omega
  · simp only [mem_Icc] at hj
    omega
  · simp only [mem_Icc] at hj
    rw [Int.toNat_of_nonneg (by omega), add_sub_cancel_right]

/-- Gauss's sum cast into a not necessarily associative ring: twice the sum of the natural numbers
below `n` is `n (n - 1)`. -/
theorem sum_range_natCast_mul_two {R : Type*} [NonAssocRing R] (n : ℕ) :
    (∑ r ∈ range n, (r : R)) * 2 = n * (n - 1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have h := congrArg (Nat.cast : ℕ → R) (sum_range_id_mul_two n)
  push_cast [Nat.cast_sub hn] at h
  exact h

/-- Six times the sum of the squares of the natural numbers below `n` is `n (n - 1) (2 n - 1)`. -/
theorem sum_range_id_sq_mul_six (n : ℕ) :
    (∑ i ∈ range n, i ^ 2) * 6 = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel, show 2 * (n + 1 + 1) - 1 = 2 * n + 3 by omega,
        show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
      ring

/-- The sum of the squares of the natural numbers below `n` is `n (n - 1) (2 n - 1) / 6`. -/
theorem sum_range_id_sq (n : ℕ) : ∑ i ∈ range n, i ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  rw [← sum_range_id_sq_mul_six, Nat.mul_div_cancel _ (by decide)]

/-- The quotients `i / H` for `i < H q + ρ` with `ρ ≤ H` sum to `H (q choose 2) + ρ q`. -/
private theorem sum_range_mul_add_div {H ρ : ℕ} (hρ : ρ ≤ H) (q : ℕ) :
    ∑ i ∈ range (H * q + ρ), i / H = H * q.choose 2 + ρ * q := by
  rcases H.eq_zero_or_pos with rfl | hH
  · simp [Nat.le_zero.mp hρ]
  -- A block `H q ≤ i < H q + ρ'` with `ρ' ≤ H` has constant quotient `q`.
  have hblock {ρ' : ℕ} (hρ' : ρ' ≤ H) (q : ℕ) : ∑ i ∈ range ρ', (H * q + i) / H = ρ' * q := by
    rw [sum_congr rfl fun i hi ↦ by
      rw [Nat.mul_add_div hH, Nat.div_eq_of_lt ((mem_range.mp hi).trans_le hρ'), add_zero],
      sum_const, card_range, smul_eq_mul]
  -- The complete blocks below `H q` contribute `H (q choose 2)`.
  have hfull (q : ℕ) : ∑ i ∈ range (H * q), i / H = H * q.choose 2 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, sum_range_add, ih, hblock le_rfl, Nat.choose_succ_succ,
        Nat.choose_one_right]
      ring
  rw [sum_range_add, hfull, hblock hρ]

/-- **Block sums of quotients.** Write `n = H q + ρ` with `q = n / H` and `ρ = n % H`. The
quotients `i / H` for `i < n` sum to `H (q choose 2) + ρ q`: the complete block
`H k ≤ i < H (k + 1)` contributes `H k` for each `k < q`, and the last block `H q ≤ i < n`
contributes `ρ q`. -/
theorem sum_range_div (n H : ℕ) :
    ∑ i ∈ range n, i / H = H * (n / H).choose 2 + n % H * (n / H) := by
  rcases H.eq_zero_or_pos with rfl | hH
  · simp
  conv_lhs => rw [← Nat.div_add_mod n H]
  exact sum_range_mul_add_div (Nat.mod_lt n hH).le _

/-- The sum of the squares of the natural numbers below `n`, cast into a ring, is
`n (n - 1) (2 n - 1)` after multiplying by `6`. -/
theorem sum_range_natCast_sq_mul_six {R : Type*} [Ring R] (n : ℕ) :
    (∑ r ∈ range n, (r : R) ^ 2) * 6 = n * (n - 1) * (2 * n - 1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have h := congrArg (Nat.cast : ℕ → R) (sum_range_id_sq_mul_six n)
  push_cast [Nat.cast_sub hn, Nat.cast_sub (by omega : 1 ≤ 2 * n)] at h
  exact h

/-- Twice the number of pairs `(j, i)` with `j < e` and `i + j ≤ r`, that is, the sum of `r + 1 - j`
over `j < e`, doubled. -/
theorem sum_range_sub_mul_two (r e : ℕ) (he : e ≤ r + 1) :
    (∑ j ∈ range e, ((r + 1 - j : ℕ) : ℤ)) * 2 = e * (2 * r + 3 - e) := by
  rw [sum_congr rfl fun j hj ↦ Nat.cast_sub (by grind), sum_sub_distrib, sub_mul,
    sum_range_natCast_mul_two]
  simp
  ring

/-- Gauss's sum read backwards: the sum of `n - j` over `j < n` is `1 + 2 + ⋯ + n`, which is
`n (n + 1) / 2`. -/
theorem sum_range_sub_id (n : ℕ) : ∑ j ∈ range n, (n - j) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero, ih]
    grind

/-- The partial sums `∑_{1 ≤ k ≤ n} (-1) ^ (k + 1)` of the alternating sequence `1, -1, 1, …` are
`0` for even `n` and `1` for odd `n`; this is Mathlib's `neg_one_geom_sum` with the index shifted
by one. -/
theorem sum_Icc_neg_one_pow_add_one {R : Type*} [Ring R] (n : ℕ) :
    ∑ k ∈ Icc 1 n, (-1 : R) ^ (k + 1) = if Even n then 0 else 1 := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, add_tsub_cancel_right, ← neg_one_geom_sum]
  simp [pow_add]

/-- The signed partial sums `∑_{0 ≤ j < i} a j - ∑_{i ≤ j < 0} a j` of a sequence `a` indexed by
`ℤ` increase by `a i` from `i` to `i + 1`: they are the discrete primitive of `a` vanishing at
`0`. -/
theorem sum_Ico_zero_add_one_sub_sum_Ico_add_one_zero {M : Type*} [AddCommGroup M] (a : ℤ → M)
    (i : ℤ) : ∑ j ∈ Ico 0 (i + 1), a j - ∑ j ∈ Ico (i + 1) 0, a j =
      ∑ j ∈ Ico 0 i, a j - ∑ j ∈ Ico i 0, a j + a i := by
  rcases le_or_gt 0 i with h | h
  · rw [Ico_eq_empty_of_le (by omega : (0 : ℤ) ≤ i + 1), Ico_eq_empty_of_le h,
      ← insert_Ico_right_eq_Ico_add_one h, sum_insert right_notMem_Ico]
    abel
  · rw [Ico_eq_empty_of_le (by omega : i + 1 ≤ 0), Ico_eq_empty_of_le h.le,
      ← insert_Ico_add_one_left_eq_Ico h, sum_insert (by simp)]
    abel

/-- Counted with sign, the integers between `0` and `k` sum to `k (k - 1) / 2`: twice
`∑_{0 ≤ j < k} j - ∑_{k ≤ j < 0} j` is `k (k - 1)`. For `k ≥ 0` only the first sum is nonempty
and this is Gauss's sum; for `k < 0` only the second one is. -/
theorem two_mul_sum_Ico_zero_sub_sum_Ico_zero (k : ℤ) :
    2 * (∑ j ∈ Ico 0 k, j - ∑ j ∈ Ico k 0, j) = k * (k - 1) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [sum_Ico_zero_add_one_sub_sum_Ico_add_one_zero (fun j => j)]
    linear_combination ih
  | pred i ih =>
    have := sum_Ico_zero_add_one_sub_sum_Ico_add_one_zero (fun j => j) (-(i : ℤ) - 1)
    rw [sub_add_cancel] at this
    linear_combination ih - 2 * this

/-- A window sum `∑_{j - L ≤ k < j + L} f k` is the sum of `2 L` shifts of `f`: the `d`-th one
reads `f` at `j + d - L`, where this index is defined. -/
theorem sum_Ico_sub_add_eq_sum_range_indicator {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (L j : ℕ) :
    ∑ k ∈ Ico (j - L) (j + L), f k =
      ∑ d ∈ range (2 * L), {i | L ≤ i + d}.indicator (f ∘ fun i ↦ i + d - L) j := by
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Function.comp_apply]
  rw [← sum_filter]
  refine sum_nbij' (fun k ↦ k + L - j) (fun d ↦ j + d - L) (fun k hk ↦ ?_) (fun d hd ↦ ?_)
    (fun k hk ↦ ?_) (fun d hd ↦ ?_) fun k hk ↦ ?_
  all_goals simp only [mem_Ico, mem_filter, mem_range] at *
  all_goals first | omega | (congr 1; omega)

/-- Tail sums of errors satisfying `x i ∈ V (i + 1)` along a doubling sequence
`V (n + 1) + V (n + 1) ⊆ V n` stay inside `V n`. -/
theorem sum_Ico_mem_of_add_subset {M : Type*} [AddCommMonoid M]
    {V : ℕ → Set M} (h0 : ∀ n, (0 : M) ∈ V n)
    (hadd : ∀ n, V (n + 1) + V (n + 1) ⊆ V n)
    {x : ℕ → M} (hx : ∀ n, x n ∈ V (n + 1)) (m n : ℕ) :
    ∑ i ∈ Ico n (n + m), x i ∈ V n := by
  induction m generalizing n with
  | zero => simpa using h0 n
  | succ m ih =>
    have hlt : n < n + (m + 1) := by omega
    have hend : n + (m + 1) = (n + 1) + m := by omega
    rw [sum_eq_sum_Ico_succ_bot hlt, hend]
    exact hadd n (Set.add_mem_add (hx n) (ih (n + 1)))

/-- Trapezoidal pairing on an integer interval `a ≤ n`: multiplying `g j * g (j + 1)` over
`j ∈ Ico a n` together with the two endpoint values `g a` and `g n` yields the square of
`∏ j ∈ Icc a n, g j`. -/
@[to_additive /-- Trapezoidal pairing on an integer interval `a ≤ n`: summing `g j + g (j + 1)`
over `j ∈ Ico a n` together with the two endpoint values `g a` and `g n` yields
`2 • ∑ j ∈ Icc a n, g j`. -/]
theorem prod_Ico_mul_mul_endpoints {M : Type*} [CommMonoid M] (g : ℤ → M) {a n : ℤ}
    (han : a ≤ n) :
    (∏ j ∈ Ico a n, (g j * g (j + 1))) * g a * g n = (∏ j ∈ Icc a n, g j) ^ 2 := by
  have hshift : ∏ j ∈ Ico a n, g (j + 1) = ∏ j ∈ Ioc a n, g j := by
    rw [prod_Ico_add' (f := g), Ico_add_one_add_one_eq_Ioc]
  calc (∏ j ∈ Ico a n, (g j * g (j + 1))) * g a * g n
      = ((∏ j ∈ Ico a n, g j) * g n) * (g a * ∏ j ∈ Ico a n, g (j + 1)) := by
          rw [prod_mul_distrib]; ac_rfl
    _ = (∏ j ∈ Icc a n, g j) * ∏ j ∈ Icc a n, g j := by
          rw [prod_Ico_mul_eq_prod_Icc han, hshift, mul_prod_Ioc_eq_prod_Icc han]
    _ = (∏ j ∈ Icc a n, g j) ^ 2 := (pow_two _).symm

/-- A sum over `Finset.Icc 0 N` of a sequence vanishing at `0` is its sum over
`Finset.Icc 1 N`. -/
theorem sum_Icc_zero_eq_sum_Icc_one {M : Type*} [AddCommMonoid M] {f : ℕ → M} (h0 : f 0 = 0)
    (N : ℕ) : ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, h0, zero_add, ← Icc_add_one_left_eq_Ioc,
    zero_add]

/-- For naturals `N` and `K`, writing the weight `⌊K N / n⌋` as the number of `1 ≤ j < K` with
`n ≤ K N / j` and swapping the sums:
`∑_{N < n ≤ K N} ⌊K N / n⌋ f(n) = ∑_{1 ≤ j < K} ∑_{N < n ≤ K N / j} f(n)`. -/
theorem sum_Ioc_div_smul_eq_sum_Ico_sum_Ioc {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (N K : ℕ) :
    ∑ n ∈ Ioc N (K * N), (K * N / n) • f n = ∑ j ∈ Ico 1 K, ∑ n ∈ Ioc N (K * N / j), f n := by
  have hcard : ∀ n ∈ Ioc N (K * N), K * N / n = #{j ∈ Ico 1 K | n ≤ K * N / j} := by
    intro n hn
    obtain ⟨hNn, hnKN⟩ := mem_Ioc.mp hn
    have hn0 : 0 < n := (Nat.zero_le N).trans_lt hNn
    have hK : 0 < K := Nat.pos_of_ne_zero fun hK ↦ by rw [hK, zero_mul] at hnKN; omega
    have hlt : K * N / n < K :=
      (Nat.div_lt_iff_lt_mul hn0).mpr ((Nat.mul_lt_mul_left hK).mpr hNn)
    have hfilter : {j ∈ Ico 1 K | n ≤ K * N / j} = Icc 1 (K * N / n) := by
      ext j
      simp only [mem_filter, mem_Ico, mem_Icc]
      constructor
      · rintro ⟨⟨hj, -⟩, h⟩
        exact ⟨hj, (Nat.le_div_iff_mul_le hn0).mpr
          (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hj).mp h)⟩
      · rintro ⟨hj, h⟩
        exact ⟨⟨hj, h.trans_lt hlt⟩, (Nat.le_div_iff_mul_le hj).mpr
          (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hn0).mp h)⟩
    rw [hfilter, Nat.card_Icc, add_tsub_cancel_right]
  calc ∑ n ∈ Ioc N (K * N), (K * N / n) • f n
      = ∑ n ∈ Ioc N (K * N), ∑ j ∈ Ico 1 K, if n ≤ K * N / j then f n else 0 :=
        sum_congr rfl fun n hn ↦ by rw [hcard n hn, ← sum_filter, sum_const]
    _ = ∑ j ∈ Ico 1 K, ∑ n ∈ Ioc N (K * N), if n ≤ K * N / j then f n else 0 := sum_comm
    _ = ∑ j ∈ Ico 1 K, ∑ n ∈ Ioc N (K * N / j), f n := by
        refine sum_congr rfl fun j _ ↦ ?_
        rw [← sum_filter]
        congr 1
        ext n
        simp only [mem_filter, mem_Ioc]
        exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans (Nat.div_le_self _ _)⟩, h.2⟩⟩

/-- For `0 < n ≤ H`, the distances `|n - n'|` with `0 < n' ≤ H` lie in `[0, H)` and each is taken
at most twice, so `∑_{0 < n' ≤ H} w(|n - n'|) ≤ 2 w(0) + 2 ∑_{1 ≤ k ≤ H} w(k)` for `w ≥ 0`. -/
theorem sum_Ioc_dist_le {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] {w : ℕ → R}
    (hw : ∀ k, 0 ≤ w k) {n H : ℕ} (hn : n ∈ Ioc 0 H) :
    ∑ n' ∈ Ioc 0 H, w (Nat.dist n n') ≤ 2 * w 0 + 2 * ∑ k ∈ Icc 1 H, w k := by
  have hmaps : ∀ n' ∈ Ioc 0 H, Nat.dist n n' ∈ insert 0 (Icc 1 H) := by
    intro n' hn'
    simp only [mem_Ioc] at hn hn'
    simp only [mem_insert, mem_Icc, Nat.dist]
    omega
  rw [← sum_fiberwise_of_maps_to hmaps, ← mul_add, ← sum_insert (by simp), mul_sum]
  refine sum_le_sum fun k _ ↦ ?_
  rw [sum_congr rfl fun n' hn' ↦ by rw [(mem_filter.1 hn').2], sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hw k)
  have hcard : {n' ∈ Ioc 0 H | Nat.dist n n' = k}.card ≤ ({n + k, n - k} : Finset ℕ).card :=
    card_le_card fun n' hn' ↦ by
      obtain ⟨-, hk⟩ := mem_filter.1 hn'
      unfold Nat.dist at hk
      simp only [mem_insert, mem_singleton]
      omega
  simpa using Nat.mono_cast (α := R) (hcard.trans card_le_two)

end Finset
