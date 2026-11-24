/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Set.Finite.Basic
public import TauCeti.Algebra.Order.BigOperators.Dominance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Newton vectors of the general linear group

The isocrystals of height `n` over an algebraically closed field of characteristic `p` are
classified by their slopes (Dieudonné–Manin), so the set `B(GL_n)` of `σ`-conjugacy classes is
the set of *Newton vectors*: weakly decreasing rational vectors `ν₁ ≥ ⋯ ≥ νₙ` in which a slope `λ`
occurring with multiplicity `m` satisfies `m λ ∈ ℤ`. This file develops the combinatorics of
these vectors that the Newton stratification needs.

* The order on `B(GL_n)` is the dominance order `TauCeti.Dominates`: equal total slopes and
  inequalities of the leading partial sums. For integer vectors it is the coroot order
  (`TauCeti.GeneralLinear.dominates_iff_rootLE_flip`).
* For an integral cocharacter `μ`, the set `B(GL_n, μ)` of `μ`-admissible classes consists of the
  Newton vectors dominated by `μ`. It is finite: the coordinates of an admissible vector lie
  between the last and the first coordinate of `μ`, and the multiplicity condition makes
  `n! • ν` integral.
* The pairing `⟨2ρ, ν⟩ = ∑_{i < j} (νᵢ - νⱼ)` with the sum of the positive roots of the
  upper-triangular Borel is the invariant `d_b = ⟨2ρ, ν_b⟩` of a Newton class, the dimension of
  its central leaf in the geometric applications. It is strictly monotone for dominance:
  `ν ≼ ν'` gives `⟨2ρ, ν⟩ ≤ ⟨2ρ, ν'⟩`, with equality only for `ν = ν'`. The reason is the
  prefix-sum formula `⟨2ρ, x⟩ = ∑_{k = 0}^{n} (2 ∑_{i < k} xᵢ - ∑_i xᵢ)`.

For `μ = (1, 0)` the admissible set has exactly the two elements `(1, 0)` (ordinary) and
`(1/2, 1/2)` (basic). The multiplicity condition is what excludes vectors such as `(3/4, 1/4)`,
which are weakly decreasing and dominated by `(1, 0)`: a slope of multiplicity one must be an
integer.

## Main definitions

* `TauCeti.GeneralLinear.twoWeylVectorPairing`: the pairing `⟨2ρ, x⟩ = ∑_{i < j} (xᵢ - xⱼ)`.
* `TauCeti.GeneralLinear.IsNewtonVector`: weakly decreasing rational vectors satisfying the
  multiplicity condition.
* `TauCeti.GeneralLinear.admissibleNewtonVectors μ`: the Newton vectors dominated by the integral
  cocharacter `μ`.

## Main results

* `TauCeti.GeneralLinear.twoWeylVectorPairing_eq_sum_zsmul`: `⟨2ρ, x⟩ = ∑ᵢ (n - 1 - 2i) • xᵢ`, the
  coordinates of `2ρ` of `TauCeti.GeneralLinear.twoWeylVector_diagonalRootBase_apply`.
* `TauCeti.Dominates.twoWeylVectorPairing_le`, `TauCeti.Dominates.twoWeylVectorPairing_lt`,
  `TauCeti.Dominates.twoWeylVectorPairing_eq_iff`: the pairing is strictly monotone for
  dominance.
* `TauCeti.GeneralLinear.IsNewtonVector.exists_factorial_mul_eq_intCast`: the coordinates of a
  Newton vector of height `n` lie in `(1 / n!) ℤ`.
* `TauCeti.GeneralLinear.admissibleNewtonVectors_finite`: `B(GL_n, μ)` is finite.
* `TauCeti.GeneralLinear.admissibleNewtonVectors_one_zero`: `B(GL_2, (1, 0))` consists of the
  ordinary and the basic class.

## References

* A. Caraiani and P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), §3.1.
* R. Kottwitz, *Isocrystals with additional structure*, Compositio Math. 56 (1985), §4.
* M. Rapoport and M. Richartz, *On the classification and specialization of `F`-isocrystals with
  additional structure*, Compositio Math. 103 (1996), Theorem 1.15.
-/

public section

open Finset

namespace TauCeti.GeneralLinear

variable {M : Type*} {n : ℕ}

section Pairing

variable [AddCommGroup M]

/-- The pairing `⟨2ρ, x⟩ = ∑_{i < j} (xᵢ - xⱼ)` of a vector `x` of (rational) coweight coordinates
of the diagonal torus of `GL_n` with the sum `2ρ` of the positive roots `eᵢ - eⱼ`, `i < j`, of the
upper-triangular Borel subgroup. For the Newton vector `ν_b` of a class `b ∈ B(GL_n)` this is the
invariant `d_b = ⟨2ρ, ν_b⟩`. -/
def twoWeylVectorPairing (x : Fin n → M) : M :=
  ∑ i, ∑ j ∈ Ioi i, (x i - x j)

/-- The defining formula of `TauCeti.GeneralLinear.twoWeylVectorPairing`: the sum over the
positive roots `eᵢ - eⱼ`, `i < j`. -/
theorem twoWeylVectorPairing_def (x : Fin n → M) :
    twoWeylVectorPairing x = ∑ i, ∑ j ∈ Ioi i, (x i - x j) :=
  (rfl)

/-- **The coordinates of `2ρ`.** `⟨2ρ, x⟩ = ∑ᵢ (n - 1 - 2i) xᵢ`. -/
theorem twoWeylVectorPairing_eq_sum_zsmul (x : Fin n → M) :
    twoWeylVectorPairing x = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) • x i := by
  have hcomm : ∑ i : Fin n, ∑ j ∈ Ioi i, x j = ∑ j : Fin n, ∑ _i ∈ Iio j, x j :=
    sum_comm' fun i j ↦ by simp
  simp only [twoWeylVectorPairing_def, sum_sub_distrib, hcomm, sum_const, Fin.card_Ioi,
    Fin.card_Iio]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  rw [Nat.sub_sub, ← natCast_zsmul, ← natCast_zsmul, Nat.cast_sub (by omega)]
  push_cast
  module

/-- **The prefix-sum formula for `⟨2ρ, x⟩`.**
`⟨2ρ, x⟩ = ∑_{k = 0}^{n} (2 ∑_{i < k} xᵢ - ∑ᵢ xᵢ)`. -/
theorem twoWeylVectorPairing_eq_sum_prefixSum (x : Fin n → M) :
    twoWeylVectorPairing x = ∑ k ∈ range (n + 1), (2 • prefixSum k x - ∑ i, x i) := by
  -- The coordinate `xᵢ` enters the prefix sums of lengths `i + 1, …, n`.
  have sum_range_prefixSum :
      ∑ k ∈ range (n + 1), prefixSum k x = ∑ i : Fin n, (n - (i : ℕ)) • x i := by
    simp only [prefixSum_def]
    rw [sum_comm' (t' := univ) (s' := fun i : Fin n ↦ (range (n + 1)).filter fun k ↦ (i : ℕ) < k)
      fun k i ↦ by simp]
    refine sum_congr rfl fun i _ ↦ ?_
    have hfilter : (range (n + 1)).filter (fun k ↦ (i : ℕ) < k) = Ioc (i : ℕ) n := by
      ext k
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    rw [sum_const, hfilter, Nat.card_Ioc]
  rw [sum_sub_distrib, sum_nsmul, sum_range_prefixSum, twoWeylVectorPairing_eq_sum_zsmul,
    sum_const, card_range, ← sum_nsmul, ← sum_nsmul, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  simp only [← natCast_zsmul, Nat.cast_sub hi.le]
  push_cast
  module

end Pairing

end TauCeti.GeneralLinear

namespace TauCeti.Dominates

open TauCeti.GeneralLinear

variable {M : Type*} {n : ℕ}

section Pairing

/-- The difference of the pairings with `2ρ` along a dominance `x ≼ y` is twice the sum of the
differences of the prefix sums. -/
private theorem twoWeylVectorPairing_sub [AddCommGroup M] [LE M] {x y : Fin n → M}
    (h : Dominates x y) :
    twoWeylVectorPairing y - twoWeylVectorPairing x =
      ∑ k ∈ range (n + 1), 2 • (prefixSum k y - prefixSum k x) := by
  rw [twoWeylVectorPairing_eq_sum_prefixSum, twoWeylVectorPairing_eq_sum_prefixSum,
    ← sum_sub_distrib, (dominates_def.mp h).1]
  exact sum_congr rfl fun _ _ ↦ by rw [nsmul_sub]; abel

variable [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- **`⟨2ρ, ·⟩` is monotone for dominance.** -/
theorem twoWeylVectorPairing_le {x y : Fin n → M} (h : Dominates x y) :
    twoWeylVectorPairing x ≤ twoWeylVectorPairing y := by
  have hle := (dominates_iff_forall_prefixSum_le.mp h).2
  refine sub_nonneg.mp ?_
  rw [h.twoWeylVectorPairing_sub]
  exact sum_nonneg fun k _ ↦ nsmul_nonneg (sub_nonneg.mpr (hle k)) 2

/-- **`⟨2ρ, ·⟩` is strictly monotone for dominance**: along a dominance `x ≼ y` the pairings
are equal only when `x = y`. -/
theorem twoWeylVectorPairing_eq_iff {x y : Fin n → M} (h : Dominates x y) :
    twoWeylVectorPairing x = twoWeylVectorPairing y ↔ x = y := by
  refine ⟨fun heq ↦ ?_, fun hxy ↦ hxy ▸ rfl⟩
  have hle := (dominates_iff_forall_prefixSum_le.mp h).2
  have hsum : ∑ k ∈ range (n + 1), 2 • (prefixSum k y - prefixSum k x) = 0 := by
    rw [← h.twoWeylVectorPairing_sub, heq, sub_self]
  rw [sum_eq_zero_iff_of_nonneg fun k _ ↦ nsmul_nonneg (sub_nonneg.mpr (hle k)) 2] at hsum
  refine eq_of_forall_prefixSum_eq fun k ↦ ?_
  rcases le_or_gt k n with hk | hk
  · have h2 := hsum k (mem_range.mpr (Nat.lt_succ_of_le hk))
    rw [two_nsmul, add_eq_zero_iff_of_nonneg (sub_nonneg.mpr (hle k)) (sub_nonneg.mpr (hle k)),
      and_self, sub_eq_zero] at h2
    exact h2.symm
  · rw [prefixSum_of_le hk.le, prefixSum_of_le hk.le, (dominates_def.mp h).1]

/-- **`⟨2ρ, ·⟩` is strictly monotone for dominance**: a strict dominance `x ≼ y`, `x ≠ y`, gives
`⟨2ρ, x⟩ < ⟨2ρ, y⟩`. -/
theorem twoWeylVectorPairing_lt {x y : Fin n → M} (h : Dominates x y) (hne : x ≠ y) :
    twoWeylVectorPairing x < twoWeylVectorPairing y :=
  h.twoWeylVectorPairing_le.lt_of_ne fun heq ↦ hne (h.twoWeylVectorPairing_eq_iff.mp heq)

end Pairing

end TauCeti.Dominates

namespace TauCeti.GeneralLinear

variable {n : ℕ}

/-- A **Newton vector** of height `n`: a weakly decreasing vector `ν₁ ≥ ⋯ ≥ νₙ` of rational slopes
in which every slope `λ`, occurring with multiplicity `m`, satisfies `m λ ∈ ℤ`. By the
Dieudonné–Manin classification these are the slope vectors of the isocrystals of height `n`, that
is, the elements of `B(GL_n)`. -/
structure IsNewtonVector (ν : Fin n → ℚ) : Prop where
  /-- The slopes are weakly decreasing. -/
  antitone : Antitone ν
  /-- A slope `λ` of multiplicity `m` satisfies `m λ ∈ ℤ`. -/
  exists_card_mul_eq_intCast : ∀ i, ∃ m : ℤ, (#{j | ν j = ν i} : ℚ) * ν i = m

/-- **The coordinates of a Newton vector of height `n` lie in `(1 / n!) ℤ`**: the multiplicity of
each slope divides `n!`. -/
theorem IsNewtonVector.exists_factorial_mul_eq_intCast {ν : Fin n → ℚ} (hν : IsNewtonVector ν)
    (i : Fin n) : ∃ m : ℤ, (n.factorial : ℚ) * ν i = m := by
  obtain ⟨m, hm⟩ := hν.exists_card_mul_eq_intCast i
  have hpos : 0 < #{j | ν j = ν i} := card_pos.mpr ⟨i, by simp⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hpos ((card_filter_le _ _).trans (card_fin n).le)
  exact ⟨c * m, by rw [hc]; push_cast; rw [← hm]; ring⟩

/-- The **`μ`-admissible Newton vectors** `B(GL_n, μ)` of an integral cocharacter `μ`: the Newton
vectors dominated by `μ`, that is, with the total slope of `μ` and leading partial sums at most
those of `μ`. For the dominant representative `μ` of a conjugacy class of cocharacters these are
the classes `b ∈ B(GL_n)` with `ν_b ≼ μ`; for `GL_n` the condition `κ(b) = μ♭` on the Kottwitz
invariant is the equality of total slopes. -/
def admissibleNewtonVectors (μ : Fin n → ℤ) : Set (Fin n → ℚ) :=
  {ν | IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ)}

@[simp]
theorem mem_admissibleNewtonVectors {μ : Fin n → ℤ} {ν : Fin n → ℚ} :
    ν ∈ admissibleNewtonVectors μ ↔ IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ) :=
  Iff.rfl

/-- **`B(GL_n, μ)` is finite.** The coordinates of an admissible Newton vector lie between the
last and the first coordinate of `μ`, and in `(1 / n!) ℤ`. -/
theorem admissibleNewtonVectors_finite (μ : Fin n → ℤ) : (admissibleNewtonVectors μ).Finite := by
  -- The rationals in `[a, b]` lying in `(1 / N) ℤ` form a finite set.
  have finite_setOf_mul_eq_intCast (N : ℕ) (hN : 0 < N) (a b : ℚ) :
      {q : ℚ | a ≤ q ∧ q ≤ b ∧ ∃ m : ℤ, (N : ℚ) * q = m}.Finite := by
    refine ((Set.finite_Icc ⌊N * a⌋ ⌈N * b⌉).image fun m : ℤ ↦ (m : ℚ) / N).subset ?_
    rintro q ⟨ha, hb, m, hm⟩
    have : (0 : ℚ) < N := by exact_mod_cast hN
    refine ⟨m, ⟨Int.floor_le_iff.mpr ?_, Int.le_ceil_iff.mpr ?_⟩, ?_⟩
    · rw [← hm]; nlinarith
    · rw [← hm]; nlinarith
    · simp only [← hm]
      field_simp
  cases n with
  | zero => exact Set.toFinite _
  | succ n =>
    refine (Set.Finite.pi (t := fun _ ↦ {q : ℚ | (μ (Fin.last n) : ℚ) ≤ q ∧ q ≤ μ 0 ∧
        ∃ m : ℤ, ((n + 1).factorial : ℚ) * q = m}) fun _ ↦
      finite_setOf_mul_eq_intCast _ (Nat.factorial_pos _) _ _).subset ?_
    rintro ν ⟨hν, hdom⟩ i -
    exact ⟨hdom.apply_last_le_apply hν.antitone i, hdom.apply_le_apply_zero hν.antitone i,
      hν.exists_factorial_mul_eq_intCast i⟩

/-- **`B(GL_2, (1, 0))` has exactly two elements**: the ordinary class with slopes `(1, 0)` and the
basic class with slopes `(1/2, 1/2)`. -/
theorem admissibleNewtonVectors_one_zero :
    admissibleNewtonVectors ![1, 0] = {![1, 0], ![1 / 2, 1 / 2]} := by
  have hcard (ν : Fin 2 → ℚ) (i : Fin 2) :
      (#{j | ν j = ν i} : ℚ) = (if ν 0 = ν i then 1 else 0) + (if ν 1 = ν i then 1 else 0) := by
    rw [card_filter, Fin.sum_univ_two]
    push_cast [apply_ite (Nat.cast (R := ℚ))]
    simp
  ext ν
  simp only [mem_admissibleNewtonVectors, dominates_iff_fin_two, Set.mem_insert_iff,
    Set.mem_singleton_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_zero]
  constructor
  · rintro ⟨hν, hsum, h0⟩
    have h10 : ν 1 ≤ ν 0 := hν.antitone (Fin.zero_le 1)
    rcases h10.lt_or_eq with hlt | heq
    · -- The slope `ν 0` has multiplicity one, so it is an integer in `[1/2, 1]`.
      obtain ⟨m, hm⟩ := hν.exists_card_mul_eq_intCast 0
      simp only [hcard, ↓reduceIte, hlt.ne, add_zero, one_mul] at hm
      have hm1 : m = 1 := by
        have hlo : (0 : ℚ) < m := by linarith
        have hhi : (m : ℚ) ≤ 1 := by linarith
        have : (0 : ℤ) < m := by exact_mod_cast hlo
        have : m ≤ (1 : ℤ) := by exact_mod_cast hhi
        omega
      left
      ext i
      fin_cases i
      · simp [hm, hm1]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hm, hm1] at hsum
        push_cast at hsum
        linarith
    · right
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        linarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linarith
  · rintro (rfl | rfl)
    · refine ⟨⟨Fin.antitone_iff_succ_le.mpr fun i ↦ ?_, fun i ↦ ?_⟩, by simp, le_rfl⟩
      · fin_cases i
        simp
      · fin_cases i
        · exact ⟨1, by rw [hcard]; simp⟩
        · exact ⟨0, by simp⟩
    · refine ⟨⟨fun i j _ ↦ ?_, fun i ↦ ⟨1, ?_⟩⟩, by norm_num, by norm_num⟩
      · fin_cases i <;> fin_cases j <;> simp
      · rw [hcard]
        fin_cases i <;> norm_num

end TauCeti.GeneralLinear
