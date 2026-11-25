/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Sort
public import TauCeti.NumberTheory.BoundingSieve
import TauCeti.Data.Multiset.Sort

/-!
# Brun's combinatorial sieve weights and first-failure brackets

Given a squarefree integer `P`, real parameters `y` and `β`, and a parity `parity : ℕ`, Brun's
combinatorial sieve retains those divisors `d ∣ P` whose prime factors `p₁ > ⋯ > p_r` in strictly
decreasing order satisfy `p_m < (y / (p₁ ⋯ p_m)) ^ (1 / β)` at every 1-indexed position `m` with
`m % 2 = parity % 2`, assigning them their Möbius weight `μ d` and `0` to all other integers.

Partitioning the non-admissible prime subsets of a finite prime set `S₀` according to their
shortest failing decreasing prefix gives Kedlaya's exact first-failure identity:
`∑_{A ⊆ S₀ admissible} (-1)^|A| ∏_{p ∈ A} g(p) - ∏_{p ∈ S₀} (1 - g(p))` has sign
`(-1)^(parity + 1)` times a sum over minimal-failing subsets `B ⊆ S₀`. Specializing to `g ≡ 1` on
`r.primeFactors` yields the pointwise lower (`parity = 0`) and upper (`parity = 1`) divisor-sum
brackets on every `r ∣ P`, while specializing to `s.nu` on `s.prodPrimes.primeFactors` yields the
main-term sandwich `s.mainSum λ⁻ ≤ V ≤ s.mainSum λ⁺` and reduces the main-term defect to
elementary symmetric sums of prime densities above `max 2 (z ^ ((1 - β⁻¹) ^ n))`.

## Main definitions and results

* `TauCeti.IsBrunAdmissible`, `TauCeti.isBrunAdmissible_def`: Brun's parity-selected decreasing
  prefix-product admissibility predicate on finite sets of primes.
* `TauCeti.brunWeights`: Brun's combinatorial sieve coefficients `λ_ε(d)`, together with
  `brunWeights_def`, `brunWeights_one`, `brunWeights_eq_zero_of_notMem_divisors`,
  `abs_brunWeights_le_one`, `brunWeights_eq_moebius_iff`, `brunWeights_ne_zero_iff`, and the strict
  support bound `lt_of_brunWeights_ne_zero`.
* `TauCeti.sum_divisors_brunWeights_zero_le`, `TauCeti.le_sum_divisors_brunWeights_one`:
  pointwise lower and upper Möbius divisor brackets on divisors `r ∣ P`.
* `BoundingSieve.sum_brunWeights_zero_le_siftedSum`,
  `BoundingSieve.siftedSum_le_sum_brunWeights_one`,
  `BoundingSieve.mainSum_brunWeights_zero_le`, `BoundingSieve.le_mainSum_brunWeights_one`:
  sifted-sum and main-sum brackets for `BoundingSieve`.
* `BoundingSieve.brun_mainSum_defect_le`: combinatorial reduction of the Brun main-sum defect to
  elementary symmetric sums over primes in `[max 2 (z ^ ((1 - β⁻¹) ^ n)), z)`.

## References

* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12, Lemma 12.1 and §§12.2–12.4.
* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
-/

public noncomputable section

open Finset Nat ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TauCeti

/-- Step inequality `(l[i] : ℝ) < (y / ((l.take (i + 1)).prod : ℝ)) ^ (1 / β)` at 0-based index `i`
of a prime list `l`. -/
private def brunStepLt (y β : ℝ) (l : List ℕ) (i : ℕ) (hi : i < l.length) : Prop :=
  ((l[i]'hi : ℕ) : ℝ) < (y / (((l.take (i + 1)).prod : ℕ) : ℝ)) ^ (1 / β)

/-- A finite set `A : Finset ℕ` is Brun-admissible for `(y, β, parity)` if its strictly decreasing
sorted list `p₁ > ⋯ > p_r` satisfies `(p_m : ℝ) < (y / (p₁ ⋯ p_m)) ^ (1 / β)` at every 1-indexed
position `m` with `m % 2 = parity % 2`. -/
def IsBrunAdmissible (y β : ℝ) (parity : ℕ) (A : Finset ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < (A.sort (· ≥ ·)).length),
    (i + 1) % 2 = parity % 2 →
      (((A.sort (· ≥ ·))[i]'hi : ℕ) : ℝ) <
        (y / ((((A.sort (· ≥ ·)).take (i + 1)).prod : ℕ) : ℝ)) ^ (1 / β)

/-- Explicit step-inequality formula for `TauCeti.IsBrunAdmissible`. -/
theorem isBrunAdmissible_def (y β : ℝ) (parity : ℕ) (A : Finset ℕ) :
    IsBrunAdmissible y β parity A ↔
      ∀ (i : ℕ) (hi : i < (A.sort (· ≥ ·)).length),
        (i + 1) % 2 = parity % 2 →
          (((A.sort (· ≥ ·))[i]'hi : ℕ) : ℝ) <
            (y / ((((A.sort (· ≥ ·)).take (i + 1)).prod : ℕ) : ℝ)) ^ (1 / β) :=
  Iff.rfl

open Classical in
/-- Brun's combinatorial sieve coefficients `λ_ε(d)`. For `d ∈ P.divisors` whose prime-factor set
satisfies `IsBrunAdmissible y β parity`, `brunWeights P y β parity d = μ d`; otherwise `0`. -/
def brunWeights (P : ℕ) (y β : ℝ) (parity d : ℕ) : ℝ :=
  if d ∈ P.divisors ∧ IsBrunAdmissible y β parity d.primeFactors then (μ d : ℝ) else 0

open Classical in
/-- Explicit formula for `TauCeti.brunWeights` in terms of `TauCeti.IsBrunAdmissible`. -/
theorem brunWeights_def (P : ℕ) (y β : ℝ) (parity d : ℕ) :
    brunWeights P y β parity d =
      if d ∈ P.divisors ∧ IsBrunAdmissible y β parity d.primeFactors then (μ d : ℝ) else 0 :=
  (rfl)

/-- `brunWeights` depends on `parity` only modulo `2`. -/
theorem brunWeights_mod_two (P : ℕ) (y β : ℝ) (parity d : ℕ) :
    brunWeights P y β (parity % 2) d = brunWeights P y β parity d := by
  classical
  have h : IsBrunAdmissible y β (parity % 2) d.primeFactors ↔
      IsBrunAdmissible y β parity d.primeFactors := by
    simp only [IsBrunAdmissible, Nat.mod_mod]
  simp only [brunWeights_def, h]

/-- For `P ≠ 0`, `brunWeights P y β parity 1 = 1` because `1` has empty prime-factor set. -/
theorem brunWeights_one {P : ℕ} (hP : P ≠ 0) (y β : ℝ) (parity : ℕ) :
    brunWeights P y β parity 1 = 1 := by
  classical
  have h1 : 1 ∈ P.divisors := Nat.one_mem_divisors.mpr hP
  rw [brunWeights_def, ite_eq_left_iff.mpr]
  · simp
  · intro hnot
    refine False.elim (hnot ⟨h1, fun i hi _ ↦ ?_⟩)
    simp at hi

/-- `brunWeights P y β parity d = 0` outside the positive divisors of `P`. -/
theorem brunWeights_eq_zero_of_notMem_divisors {P d : ℕ} (hd : d ∉ P.divisors) (y β : ℝ)
    (parity : ℕ) : brunWeights P y β parity d = 0 := by
  classical
  rw [brunWeights_def, ite_eq_right_iff.mpr (fun h ↦ False.elim (hd h.1))]

/-- `brunWeights` vanishes at `d = 0`. -/
@[simp]
theorem brunWeights_zero (P : ℕ) (y β : ℝ) (parity : ℕ) :
    brunWeights P y β parity 0 = 0 :=
  brunWeights_eq_zero_of_notMem_divisors (by simp) y β parity

/-- `brunWeights` vanishes when `P = 0`. -/
@[simp]
theorem brunWeights_zero_left (y β : ℝ) (parity d : ℕ) :
    brunWeights 0 y β parity d = 0 :=
  brunWeights_eq_zero_of_notMem_divisors (by simp) y β parity

/-- Every Brun coefficient has absolute value at most `1`, unconditionally in all parameters. -/
theorem abs_brunWeights_le_one (P : ℕ) (y β : ℝ) (parity d : ℕ) :
    |brunWeights P y β parity d| ≤ 1 := by
  rw [brunWeights_def]
  split_ifs
  · exact_mod_cast abs_moebius_le_one (n := d)
  · simp

/-- For squarefree `P` and `d ∣ P`, `brunWeights P y β parity d = μ d` if and only if
`d.primeFactors` is Brun-admissible. -/
theorem brunWeights_eq_moebius_iff {P d : ℕ} (hP : Squarefree P) (hd : d ∣ P) (y β : ℝ)
    (parity : ℕ) :
    brunWeights P y β parity d = (μ d : ℝ) ↔ IsBrunAdmissible y β parity d.primeFactors := by
  have hdmem : d ∈ P.divisors := Nat.mem_divisors.mpr ⟨hd, hP.ne_zero⟩
  have hμ0 : (μ d : ℝ) ≠ 0 := by
    exact_mod_cast moebius_ne_zero_iff_squarefree.mpr (hP.squarefree_of_dvd hd)
  rw [brunWeights_def]
  split_ifs with h
  · exact iff_of_true rfl h.2
  · exact iff_of_false hμ0.symm fun hadm ↦ h ⟨hdmem, hadm⟩

/-- For squarefree `P`, `brunWeights P y β parity d ≠ 0` if and only if `d ∣ P` and
`d.primeFactors` is Brun-admissible. -/
theorem brunWeights_ne_zero_iff {P d : ℕ} (hP : Squarefree P) (y β : ℝ) (parity : ℕ) :
    brunWeights P y β parity d ≠ 0 ↔ d ∣ P ∧ IsBrunAdmissible y β parity d.primeFactors := by
  by_cases hd : d ∣ P
  · have hdmem : d ∈ P.divisors := Nat.mem_divisors.mpr ⟨hd, hP.ne_zero⟩
    have hμ0 : (μ d : ℝ) ≠ 0 := by
      exact_mod_cast moebius_ne_zero_iff_squarefree.mpr (hP.squarefree_of_dvd hd)
    rw [brunWeights_def]
    split_ifs with h
    · exact iff_of_true hμ0 ⟨hd, h.2⟩
    · exact iff_of_false (not_not.mpr rfl) fun h' ↦ h ⟨hdmem, h'.2⟩
  · have hdnot : d ∉ P.divisors := fun hm ↦ hd (Nat.dvd_of_mem_divisors hm)
    rw [brunWeights_eq_zero_of_notMem_divisors hdnot]
    exact iff_of_false (not_not.mpr rfl) fun h' ↦ hd h'.1

/-! ### Strict support of Brun weights -/

private theorem brunStepLt_iff_mul_rpow_lt {y β : ℝ} {l : List ℕ} {i : ℕ}
    (hp1 : ∀ p ∈ l, 1 ≤ p) (hy : 0 ≤ y) (hβ : 0 < β) (hi : i < l.length) :
    brunStepLt y β l i hi ↔
      (((l.take i).prod : ℕ) : ℝ) * ((l[i]'hi : ℕ) : ℝ) ^ (β + 1) < y := by
  have hp_pos : (0 : ℝ) < (l[i]'hi : ℕ) := Nat.cast_pos.mpr (hp1 _ (List.getElem_mem hi))
  have htake_pos : (0 : ℝ) < ((l.take i).prod : ℕ) :=
    Nat.cast_pos.mpr (List.prod_pos fun p hp ↦ hp1 p (List.mem_of_mem_take hp))
  have hprod_succ : (((l.take (i + 1)).prod : ℕ) : ℝ) =
      (((l.take i).prod : ℕ) : ℝ) * (l[i]'hi : ℕ) := by
    rw [List.prod_take_succ l i hi, Nat.cast_mul]
  have hprod_pos : (0 : ℝ) < ((l.take (i + 1)).prod : ℕ) := by rw [hprod_succ]; positivity
  rw [brunStepLt, one_div,
    lt_rpow_inv_iff_of_pos hp_pos.le (div_nonneg hy hprod_pos.le) hβ,
    lt_div_iff₀' hprod_pos, hprod_succ, mul_assoc,
    ← rpow_one_add' hp_pos.le (by positivity), add_comm 1 β]

private theorem list_prod_lt_of_admissible {l : List ℕ} {y β : ℝ} (parity : ℕ)
    (hsort : l.SortedGT) (hp2 : ∀ p ∈ l, 2 ≤ p) (hy : 1 < y) (hβ : 1 < β)
    (hpy : ∀ p ∈ l, (p : ℝ) < y)
    (hadm : ∀ (i : ℕ) (hi : i < l.length), (i + 1) % 2 = parity % 2 → brunStepLt y β l i hi) :
    ((l.prod : ℕ) : ℝ) < y := by
  have hy0 : 0 ≤ y := (zero_lt_one.trans hy).le
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hp1 : ∀ p ∈ l, 1 ≤ p := fun p hp ↦ by have := hp2 p hp; omega
  have hpos_prod (k : ℕ) : (0 : ℝ) < ((l.take k).prod : ℕ) :=
    Nat.cast_pos.mpr (List.prod_pos fun p hp ↦ hp1 p (List.mem_of_mem_take hp))
  rcases eq_or_ne l.length 0 with hlen0 | hlen
  · rw [List.length_eq_zero_iff.mp hlen0]; simpa using hy
  have hlen_pos : 0 < l.length := Nat.pos_of_ne_zero hlen
  have hj : l.length - 1 < l.length := Nat.sub_lt hlen_pos zero_lt_one
  have htake_full : l.prod = (l.take (l.length - 1)).prod * l[l.length - 1] := by
    have h := List.prod_take_succ l (l.length - 1) hj
    rwa [Nat.sub_add_cancel hlen_pos, List.take_length] at h
  by_cases hpar : l.length % 2 = parity % 2
  · have hstep := (brunStepLt_iff_mul_rpow_lt hp1 hy0 hβ0 hj).mp (hadm (l.length - 1) hj (by omega))
    have hge1 : (1 : ℝ) ≤ (l[l.length - 1] : ℕ) :=
      Nat.one_le_cast.mpr (hp1 _ (List.getElem_mem _))
    have hle_rpow : ((l[l.length - 1] : ℕ) : ℝ) ≤ ((l[l.length - 1] : ℕ) : ℝ) ^ (β + 1) := by
      simpa using rpow_le_rpow_of_exponent_le hge1 (by linarith : (1 : ℝ) ≤ β + 1)
    rw [htake_full, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hle_rpow (hpos_prod _).le).trans_lt hstep
  · rcases eq_or_ne l.length 1 with h1 | hgt1
    · obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h1
      simpa [hp] using hpy p (by simp [hp])
    · have hi : l.length - 2 < l.length := by omega
      have hstep := (brunStepLt_iff_mul_rpow_lt hp1 hy0 hβ0 hi).mp
        (hadm (l.length - 2) hi (by omega))
      have hlt_p : ((l[l.length - 1] : ℕ) : ℝ) < (l[l.length - 2] : ℕ) := by
        exact_mod_cast hsort.getElem_gt_getElem_of_lt (by omega : l.length - 2 < l.length - 1)
      have hpi1 : (1 : ℝ) < (l[l.length - 2] : ℕ) := by
        have := hp2 l[l.length - 2] (List.getElem_mem _); exact_mod_cast (by omega : 1 < _)
      have hp_rpow : ((l[l.length - 2] : ℕ) : ℝ) * (l[l.length - 1] : ℕ) <
          ((l[l.length - 2] : ℕ) : ℝ) ^ (β + 1) := by
        have hp_lt_β : ((l[l.length - 1] : ℕ) : ℝ) < ((l[l.length - 2] : ℕ) : ℝ) ^ β :=
          hlt_p.trans (by simpa using rpow_lt_rpow_of_exponent_lt hpi1 hβ)
        calc ((l[l.length - 2] : ℕ) : ℝ) * (l[l.length - 1] : ℕ)
            < ((l[l.length - 2] : ℕ) : ℝ) * ((l[l.length - 2] : ℕ) : ℝ) ^ β :=
              mul_lt_mul_of_pos_left hp_lt_β (zero_lt_one.trans hpi1)
          _ = ((l[l.length - 2] : ℕ) : ℝ) ^ (β + 1) := by
              rw [← rpow_one_add' (zero_lt_one.trans hpi1).le (by linarith), add_comm 1 β]
      have htake_two : l.prod =
          (l.take (l.length - 2)).prod * l[l.length - 2] * l[l.length - 1] := by
        have h2 := List.prod_take_succ l (l.length - 2) hi
        rw [show l.length - 2 + 1 = l.length - 1 by omega] at h2
        rw [htake_full, h2]
      rw [htake_two, Nat.cast_mul, Nat.cast_mul, mul_assoc]
      exact (mul_lt_mul_of_pos_left hp_rpow (hpos_prod _)).trans hstep

/-- **Strict support of Brun weights**: if `P` is squarefree, `1 < y`, `1 < β`, and every prime
factor of `P` is strictly below `y`, then `brunWeights P y β parity d ≠ 0` implies `(d : ℝ) < y`. -/
theorem lt_of_brunWeights_ne_zero {P d : ℕ} (hP : Squarefree P) {y β : ℝ} {parity : ℕ}
    (hy : 1 < y) (hβ : 1 < β) (hprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < y)
    (h : brunWeights P y β parity d ≠ 0) : (d : ℝ) < y := by
  obtain ⟨hd, hadm⟩ := (brunWeights_ne_zero_iff hP y β parity).mp h
  have hd_eq : (d.primeFactors.sort (· ≥ ·)).prod = d := by
    rw [(sort_perm_toList _ (· ≥ ·)).prod_eq, prod_toList,
      Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hd)]
  rw [← hd_eq]
  refine list_prod_lt_of_admissible parity (sortedGT_sort d.primeFactors)
    (fun p hp ↦ (Nat.prime_of_mem_primeFactors ((mem_sort _).mp hp)).two_le) hy hβ
    (fun p hp ↦ hprimes p (Nat.primeFactors_mono hd hP.ne_zero ((mem_sort _).mp hp))) hadm

/-! ### Kedlaya's first-failure partition (Lemma 12.1) -/

/-- Minimal-failing subsets `B`: nonempty, cardinality congruent to `parity` mod `2`, all strictly
shorter parity-selected prefixes pass, and the full set fails at its last element. -/
private def isBrunMinFailing (y β : ℝ) (parity : ℕ) (B : Finset ℕ) : Prop :=
  ∃ hlen : 0 < (B.sort (· ≥ ·)).length,
    (B.sort (· ≥ ·)).length % 2 = parity % 2 ∧
    (∀ (i : ℕ) (hi : i < (B.sort (· ≥ ·)).length), i + 1 < (B.sort (· ≥ ·)).length →
      (i + 1) % 2 = parity % 2 → brunStepLt y β (B.sort (· ≥ ·)) i hi) ∧
    ¬ brunStepLt y β (B.sort (· ≥ ·)) ((B.sort (· ≥ ·)).length - 1)
        (Nat.sub_lt hlen zero_lt_one)

private theorem brunStepLt_append_left {y β : ℝ} {l₁ l₂ : List ℕ} {i : ℕ} (hi : i < l₁.length) :
    brunStepLt y β (l₁ ++ l₂) i (Nat.lt_of_lt_of_le hi (by simp)) ↔
      brunStepLt y β l₁ i hi := by
  simp only [brunStepLt, List.getElem_append_left hi,
    List.take_append_of_le_length (Nat.succ_le_of_lt hi)]

private theorem brunStepLt_congr {y β : ℝ} {l₁ l₂ : List ℕ} (h : l₁ = l₂) {i : ℕ}
    (hi₁ : i < l₁.length) :
    brunStepLt y β l₁ i hi₁ ↔ brunStepLt y β l₂ i (h ▸ hi₁) := by
  subst h; rfl

private theorem disjoint_of_forall_lt {B C : Finset ℕ}
    (hBC : ∀ b ∈ B, ∀ c ∈ C, c < b) : Disjoint B C :=
  disjoint_left.mpr fun b hb hc ↦ (lt_irrefl b) (hBC b hb b hc)

private theorem forall_lt_of_mem_powerset_filter {S₀ B C : Finset ℕ}
    (hC : C ∈ (S₀.filter (fun q ↦ ∀ b ∈ B, q < b)).powerset) :
    ∀ b ∈ B, ∀ c ∈ C, c < b :=
  fun b hb _ hc ↦ (mem_filter.mp (mem_powerset.mp hC hc)).2 b hb

private theorem sort_union_eq_append_of_lt {B C : Finset ℕ}
    (hBC : ∀ b ∈ B, ∀ c ∈ C, c < b) :
    (B ∪ C).sort (· ≥ ·) = B.sort (· ≥ ·) ++ C.sort (· ≥ ·) := by
  rw [Finset.sort, union_val,
    ← Multiset.add_eq_union_iff_disjoint.mpr (disjoint_val.mpr (disjoint_of_forall_lt hBC)),
    Multiset.sort_add (· ≥ ·) (fun b hb c hc ↦ (hBC b hb c hc).le), sort_val, sort_val]

private theorem union_not_admissible_of_minFailing {y β : ℝ} {parity : ℕ} {B C : Finset ℕ}
    (hB : isBrunMinFailing y β parity B) (hBC : ∀ b ∈ B, ∀ c ∈ C, c < b) :
    ¬ IsBrunAdmissible y β parity (B ∪ C) := by
  obtain ⟨hlen, hpar, _, hfail⟩ := hB
  intro hadm
  have happ := sort_union_eq_append_of_lt hBC
  have hiB : (B.sort (· ≥ ·)).length - 1 < (B.sort (· ≥ ·)).length := Nat.sub_lt hlen zero_lt_one
  have hiU : (B.sort (· ≥ ·)).length - 1 < ((B ∪ C).sort (· ≥ ·)).length := by
    rw [happ, List.length_append]; omega
  have hstep : brunStepLt y β ((B ∪ C).sort (· ≥ ·)) ((B.sort (· ≥ ·)).length - 1) hiU :=
    hadm ((B.sort (· ≥ ·)).length - 1) hiU (by omega)
  rw [brunStepLt_congr happ hiU, brunStepLt_append_left hiB] at hstep
  exact hfail hstep

private theorem not_minFailing_lt_length {y β : ℝ} {parity : ℕ} {B₁ B₂ : Finset ℕ}
    (hB₁ : isBrunMinFailing y β parity B₁) (hB₂ : isBrunMinFailing y β parity B₂)
    (hlt : (B₁.sort (· ≥ ·)).length < (B₂.sort (· ≥ ·)).length)
    (hpref : B₁.sort (· ≥ ·) = (B₂.sort (· ≥ ·)).take (B₁.sort (· ≥ ·)).length) : False := by
  obtain ⟨hlen₁, hpar₁, _, hfail₁⟩ := hB₁
  obtain ⟨_, _, hpass₂, _⟩ := hB₂
  have hj : (B₁.sort (· ≥ ·)).length - 1 < (B₂.sort (· ≥ ·)).length := by omega
  have hjpass := hpass₂ ((B₁.sort (· ≥ ·)).length - 1) hj (by omega) (by omega)
  have hdrop : B₂.sort (· ≥ ·) =
      B₁.sort (· ≥ ·) ++ (B₂.sort (· ≥ ·)).drop (B₁.sort (· ≥ ·)).length := by
    conv_lhs => rw [← List.take_append_drop (B₁.sort (· ≥ ·)).length (B₂.sort (· ≥ ·))]
    rw [← hpref]
  have hi₁ : (B₁.sort (· ≥ ·)).length - 1 < (B₁.sort (· ≥ ·)).length := Nat.sub_lt hlen₁ zero_lt_one
  rw [brunStepLt_congr hdrop hj, brunStepLt_append_left hi₁] at hjpass
  exact hfail₁ hjpass

private theorem minFailing_eq_of_union_eq {y β : ℝ} {parity : ℕ} {B₁ C₁ B₂ C₂ : Finset ℕ}
    (hB₁ : isBrunMinFailing y β parity B₁) (hC₁ : ∀ b ∈ B₁, ∀ c ∈ C₁, c < b)
    (hB₂ : isBrunMinFailing y β parity B₂) (hC₂ : ∀ b ∈ B₂, ∀ c ∈ C₂, c < b)
    (heq : B₁ ∪ C₁ = B₂ ∪ C₂) : B₁ = B₂ := by
  have happ : B₁.sort (· ≥ ·) ++ C₁.sort (· ≥ ·) = B₂.sort (· ≥ ·) ++ C₂.sort (· ≥ ·) := by
    rw [← sort_union_eq_append_of_lt hC₁, heq, sort_union_eq_append_of_lt hC₂]
  rcases lt_trichotomy (B₁.sort (· ≥ ·)).length (B₂.sort (· ≥ ·)).length with hlt | heql | hgt
  · have hpref : B₁.sort (· ≥ ·) = (B₂.sort (· ≥ ·)).take (B₁.sort (· ≥ ·)).length := by
      have h1 := congrArg (List.take (B₁.sort (· ≥ ·)).length) happ
      rwa [List.take_left, List.take_append_of_le_length hlt.le] at h1
    exact False.elim (not_minFailing_lt_length hB₁ hB₂ hlt hpref)
  · have hsort_eq : B₁.sort (· ≥ ·) = B₂.sort (· ≥ ·) := by
      have h1 := congrArg (List.take (B₁.sort (· ≥ ·)).length) happ
      rwa [List.take_left, heql, List.take_left] at h1
    rw [← sort_toFinset B₁ (· ≥ ·), hsort_eq, sort_toFinset]
  · have hpref : B₂.sort (· ≥ ·) = (B₁.sort (· ≥ ·)).take (B₂.sort (· ≥ ·)).length := by
      have h1 := congrArg (List.take (B₂.sort (· ≥ ·)).length) happ.symm
      rwa [List.take_left, List.take_append_of_le_length hgt.le] at h1
    exact False.elim (not_minFailing_lt_length hB₂ hB₁ hgt hpref)

private theorem exists_minFailing_decomp_of_not_admissible {S₀ A : Finset ℕ} {y β : ℝ} {parity : ℕ}
    (hAS : A ⊆ S₀) (hna : ¬ IsBrunAdmissible y β parity A) :
    ∃ B ∈ S₀.powerset, isBrunMinFailing y β parity B ∧
      ∃ C ∈ (S₀.filter (fun q ↦ ∀ b ∈ B, q < b)).powerset, A = B ∪ C := by
  classical
  set l := A.sort (· ≥ ·) with hl
  let bad := (Finset.range l.length).filter (fun i ↦
    ∃ hi : i < l.length, (i + 1) % 2 = parity % 2 ∧ ¬ brunStepLt y β l i hi)
  have hbad : bad.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    refine hna fun i hi hpar ↦ by_contra fun hnf ↦ ?_
    have hm : i ∈ bad := mem_filter.mpr ⟨mem_range.mpr hi, hi, hpar, hnf⟩
    rw [hemp] at hm; exact notMem_empty i hm
  let i₀ := bad.min' hbad
  obtain ⟨_, hi₀_lt, hi₀_par, hi₀_fail⟩ := mem_filter.mp (min'_mem bad hbad)
  let B := (l.take (i₀ + 1)).toFinset
  let C := (l.drop (i₀ + 1)).toFinset
  have hBsort : B.sort (· ≥ ·) = l.take (i₀ + 1) :=
    (sortedGT_sort B).eq_of_mem_iff ((sortedGT_sort A).pairwise.take.sortedGT) (by simp [B])
  have hBC_lt : ∀ b ∈ B, ∀ c ∈ C, c < b := fun b hb c hc ↦
    (sortedGT_sort A).pairwise.rel_of_mem_take_of_mem_drop
      (List.mem_toFinset.mp hb) (List.mem_toFinset.mp hc)
  have hAB : A = B ∪ C := by
    rw [← sort_toFinset A (· ≥ ·), ← hl, ← List.take_append_drop (i₀ + 1) l, List.toFinset_append]
  have hBS : B ⊆ S₀ := fun b hb ↦ hAS (hAB ▸ mem_union_left C hb)
  have hCS : C ⊆ S₀.filter (fun q ↦ ∀ b ∈ B, q < b) := fun c hc ↦
    mem_filter.mpr ⟨hAS (hAB ▸ mem_union_right B hc), fun b hb ↦ hBC_lt b hb c hc⟩
  have hBlen : (B.sort (· ≥ ·)).length = i₀ + 1 := by
    rw [hBsort, List.length_take_of_le (Nat.succ_le_of_lt hi₀_lt)]
  have hdrop : l = B.sort (· ≥ ·) ++ l.drop (i₀ + 1) := by
    rw [hBsort, List.take_append_drop]
  refine ⟨B, mem_powerset.mpr hBS, ⟨by omega, by omega, ?_, ?_⟩, C, mem_powerset.mpr hCS, hAB⟩
  · intro j hjB hjlt hjpar
    have hj_lt_i₀ : j < i₀ := by omega
    have hj_l : j < l.length := by omega
    have hj_step : brunStepLt y β l j hj_l := by
      by_contra hnf
      exact not_lt_of_ge (min'_le bad j (mem_filter.mpr ⟨mem_range.mpr hj_l, hj_l, hjpar, hnf⟩))
        hj_lt_i₀
    rwa [brunStepLt_congr hdrop hj_l, brunStepLt_append_left hjB] at hj_step
  · intro hlast
    have hi₀B : i₀ < (B.sort (· ≥ ·)).length := by omega
    have hlast' : brunStepLt y β (B.sort (· ≥ ·)) i₀ hi₀B := by
      simpa only [show (B.sort (· ≥ ·)).length - 1 = i₀ by omega] using hlast
    have hstep : brunStepLt y β l i₀ hi₀_lt := by
      rw [brunStepLt_congr hdrop hi₀_lt, brunStepLt_append_left hi₀B]; exact hlast'
    exact hi₀_fail hstep

open Classical in
private theorem sum_fiber_minFailing {S₀ B : Finset ℕ} {y β : ℝ} {parity : ℕ} (g : ℕ → ℝ)
    (hBm : isBrunMinFailing y β parity B) :
    -(∑ A ∈ ((S₀.filter (fun q ↦ ∀ b ∈ B, q < b)).powerset).image (B ∪ ·),
        (-1 : ℝ) ^ A.card * ∏ p ∈ A, g p) =
      (-1 : ℝ) ^ (parity + 1) *
        ((∏ p ∈ B, g p) * ∏ q ∈ S₀.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - g q)) := by
  have hBpar : (-1 : ℝ) ^ B.card = (-1 : ℝ) ^ parity := by
    have hcard : B.card % 2 = parity % 2 := by
      simpa only [length_sort (· ≥ ·)] using hBm.choose_spec.1
    rcases Nat.mod_two_eq_zero_or_one B.card with h0 | h1
    · rw [(Nat.even_iff.mpr h0).neg_one_pow, (Nat.even_iff.mpr (hcard.symm.trans h0)).neg_one_pow]
    · rw [(Nat.odd_iff.mpr h1).neg_one_pow, (Nat.odd_iff.mpr (hcard.symm.trans h1)).neg_one_pow]
  have hinj : Set.InjOn (B ∪ ·)
      ((S₀.filter (fun q ↦ ∀ b ∈ B, q < b)).powerset : Set (Finset ℕ)) := by
    intro C₁ hC₁ C₂ hC₂ heq
    have hd₁ := disjoint_of_forall_lt (forall_lt_of_mem_powerset_filter hC₁)
    have hd₂ := disjoint_of_forall_lt (forall_lt_of_mem_powerset_filter hC₂)
    simpa only [union_sdiff_cancel_left hd₁, union_sdiff_cancel_left hd₂] using congrArg (· \ B) heq
  rw [sum_image hinj]
  have hsumC :
      ∑ C ∈ (S₀.filter (fun q ↦ ∀ b ∈ B, q < b)).powerset,
        (-1 : ℝ) ^ (B ∪ C).card * ∏ p ∈ B ∪ C, g p =
      ((-1 : ℝ) ^ parity * ∏ p ∈ B, g p) *
        ∏ q ∈ S₀.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - g q) := by
    rw [show ∏ q ∈ S₀.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - g q) =
        ∑ C ∈ (S₀.filter (fun q ↦ ∀ b ∈ B, q < b)).powerset, (-1 : ℝ) ^ C.card * ∏ q ∈ C, g q by
      simp [Finset.prod_sub], mul_sum]
    refine sum_congr rfl fun C hC ↦ ?_
    have hd := disjoint_of_forall_lt (forall_lt_of_mem_powerset_filter hC)
    rw [card_union_of_disjoint hd, pow_add, hBpar, prod_union hd]
    ring
  rw [hsumC, pow_succ]
  ring

open Classical in
/-- **Kedlaya Lemma 12.1**: exact first-failure identity for sums over Brun-admissible subsets of a
finite set `S₀ : Finset ℕ`. -/
private theorem sum_admissible_sub_prod_one_sub (S₀ : Finset ℕ) (g : ℕ → ℝ) (y β : ℝ)
    (parity : ℕ) :
    (∑ A ∈ S₀.powerset.filter (IsBrunAdmissible y β parity),
        (-1 : ℝ) ^ A.card * ∏ p ∈ A, g p) -
      ∏ p ∈ S₀, (1 - g p) =
      (-1 : ℝ) ^ (parity + 1) *
        ∑ B ∈ S₀.powerset.filter (isBrunMinFailing y β parity),
          (∏ p ∈ B, g p) * ∏ q ∈ S₀.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - g q) := by
  have hprod : ∏ p ∈ S₀, (1 - g p) =
      ∑ A ∈ S₀.powerset, (-1 : ℝ) ^ A.card * ∏ p ∈ A, g p := by simp [Finset.prod_sub]
  have hdiff :
      (∑ A ∈ S₀.powerset.filter (IsBrunAdmissible y β parity),
          (-1 : ℝ) ^ A.card * ∏ p ∈ A, g p) -
        ∑ A ∈ S₀.powerset, (-1 : ℝ) ^ A.card * ∏ p ∈ A, g p =
      -(∑ A ∈ S₀.powerset.filter (fun A ↦ ¬ IsBrunAdmissible y β parity A),
          (-1 : ℝ) ^ A.card * ∏ p ∈ A, g p) := by
    rw [← sum_filter_add_sum_filter_not S₀.powerset (IsBrunAdmissible y β parity)]; ring
  rw [hprod, hdiff]
  let M := S₀.powerset.filter (isBrunMinFailing y β parity)
  let fiber (B : Finset ℕ) := ((S₀.filter (fun q ↦ ∀ b ∈ B, q < b)).powerset).image (B ∪ ·)
  have hbiUnion : S₀.powerset.filter (fun A ↦ ¬ IsBrunAdmissible y β parity A) =
      M.biUnion fiber := by
    ext A
    simp only [mem_filter, mem_powerset, mem_biUnion, M, fiber, mem_image]
    refine ⟨fun ⟨hAS, hna⟩ ↦ ?_, fun ⟨B, ⟨hBS, hBm⟩, C, hCS, hEq⟩ ↦ ?_⟩
    · obtain ⟨B, hBS, hBm, C, hCS, rfl⟩ := exists_minFailing_decomp_of_not_admissible hAS hna
      exact ⟨B, ⟨mem_powerset.mp hBS, hBm⟩, C, mem_powerset.mp hCS, rfl⟩
    · subst hEq
      exact ⟨union_subset hBS (hCS.trans (filter_subset _ _)),
        union_not_admissible_of_minFailing hBm
          (forall_lt_of_mem_powerset_filter (mem_powerset.mpr hCS))⟩
  have hdisj : (M : Set (Finset ℕ)).PairwiseDisjoint fiber := by
    intro B₁ hB₁ B₂ hB₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro A hA₁ hA₂
    obtain ⟨C₁, hC₁, rfl⟩ := mem_image.mp hA₁
    obtain ⟨C₂, hC₂, heq⟩ := mem_image.mp hA₂
    exact hne (minFailing_eq_of_union_eq (mem_filter.mp hB₁).2
      (forall_lt_of_mem_powerset_filter hC₁) (mem_filter.mp hB₂).2
      (forall_lt_of_mem_powerset_filter hC₂) heq.symm)
  rw [hbiUnion, sum_biUnion hdisj, ← sum_neg_distrib, mul_sum]
  exact sum_congr rfl fun B hB ↦ sum_fiber_minFailing g (mem_filter.mp hB).2

/-! ### Divisor-sum brackets and `BoundingSieve` consequences -/

/-- For squarefree `r`, summing over `r.divisors` is equivalent via `A ↦ ∏ p ∈ A, p` to summing
over subsets `A` of `r.primeFactors`. -/
private theorem sum_divisors_eq_sum_powerset_primeFactors {M : Type*} [AddCommMonoid M] {r : ℕ}
    (hr : Squarefree r) (g : ℕ → M) :
    ∑ d ∈ r.divisors, g d = ∑ A ∈ r.primeFactors.powerset, g (∏ p ∈ A, p) := by
  refine (Finset.sum_bij (fun A _ ↦ ∏ p ∈ A, p) ?_ ?_ ?_ fun _ _ ↦ rfl).symm
  · intro A hA
    refine Nat.mem_divisors.mpr ⟨?_, hr.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hr]
    exact prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp hA)
  · intro A₁ hA₁ A₂ hA₂ heq
    rw [← Nat.primeFactors_prod (fun p hp ↦ Nat.prime_of_mem_primeFactors (mem_powerset.mp hA₁ hp)),
      heq,
      Nat.primeFactors_prod (fun p hp ↦ Nat.prime_of_mem_primeFactors (mem_powerset.mp hA₂ hp))]
  · intro d hd
    exact ⟨d.primeFactors,
      mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hr.ne_zero),
      Nat.prod_primeFactors_of_squarefree (hr.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))⟩

/-- The Möbius value at a product of distinct primes `A` is `(-1) ^ A.card`. -/
private theorem moebius_prod_primes {A : Finset ℕ} (hpA : ∀ p ∈ A, p.Prime) :
    μ (∏ p ∈ A, p) = (-1 : ℤ) ^ A.card := by
  have hcop : (A : Set ℕ).Pairwise Nat.Coprime := fun p hp q hq ↦
    (Nat.coprime_primes (hpA p hp) (hpA q hq)).mpr
  rw [ArithmeticFunction.IsMultiplicative.map_prod (fun p ↦ p) isMultiplicative_moebius A hcop,
    ← prod_const]
  exact prod_congr rfl fun p hp ↦ moebius_apply_prime (hpA p hp)

open Classical in
/-- Reindexing a weighted sum over `r.divisors` for `r ∣ P` (`Squarefree P`) as a sum over
Brun-admissible subsets of `r.primeFactors`. -/
private theorem sum_divisors_brunWeights_mul_eq_sum_admissible {P r : ℕ} (hP : Squarefree P)
    (hr : r ∣ P) (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) (y β : ℝ) (parity : ℕ) :
    ∑ d ∈ r.divisors, brunWeights P y β parity d * f d =
      ∑ A ∈ r.primeFactors.powerset.filter (IsBrunAdmissible y β parity),
        (-1 : ℝ) ^ A.card * ∏ p ∈ A, f p := by
  have hrsq : Squarefree r := hP.squarefree_of_dvd hr
  -- Reindex divisors `d ∣ r` by prime-factor subsets `A ⊆ r.primeFactors`, then factor `μ` and `f`.
  rw [sum_divisors_eq_sum_powerset_primeFactors hrsq, sum_filter]
  refine sum_congr rfl fun A hA ↦ ?_
  have hAsub : A ⊆ r.primeFactors := mem_powerset.mp hA
  have hpA : ∀ p ∈ A, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors (hAsub hp)
  have hd_dvd_r : (∏ p ∈ A, p) ∣ r := by
    rw [← Nat.prod_primeFactors_of_squarefree hrsq]
    exact prod_dvd_prod_of_subset _ _ _ hAsub
  have hd_mem_P : (∏ p ∈ A, p) ∈ P.divisors :=
    Nat.mem_divisors.mpr ⟨hd_dvd_r.trans hr, hP.ne_zero⟩
  rw [brunWeights_def, Nat.primeFactors_prod hpA]
  split_ifs with h₁ h₂ h₂
  · have hcop : (A : Set ℕ).Pairwise Nat.Coprime := fun p hp q hq ↦
      (Nat.coprime_primes (hpA p hp) (hpA q hq)).mpr
    have hμ : (μ (∏ p ∈ A, p) : ℝ) = (-1 : ℝ) ^ A.card := by exact_mod_cast moebius_prod_primes hpA
    rw [hμ, ArithmeticFunction.IsMultiplicative.map_prod (fun p ↦ p) hf A hcop]
  · exact False.elim (h₂ h₁.2)
  · exact False.elim (h₁ ⟨hd_mem_P, h₂⟩)
  · simp

open Classical in
private theorem sum_divisors_brunWeights_sub_ite_eq {P r : ℕ} (hP : Squarefree P) (hr : r ∣ P)
    (y β : ℝ) (parity : ℕ) :
    (∑ d ∈ r.divisors, brunWeights P y β parity d) - (if r = 1 then 1 else 0) =
      (-1 : ℝ) ^ (parity + 1) *
        ∑ B ∈ r.primeFactors.powerset.filter (isBrunMinFailing y β parity),
          (∏ _ ∈ B, (1 : ℝ)) *
            ∏ q ∈ r.primeFactors.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - (1 : ℝ)) := by
  have hlhs : ∑ d ∈ r.divisors, brunWeights P y β parity d =
      ∑ d ∈ r.divisors, brunWeights P y β parity d * (ζ : ArithmeticFunction ℝ) d :=
    sum_congr rfl fun d hd ↦ by simp [natCoe_apply, zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne']
  rw [hlhs,
    sum_divisors_brunWeights_mul_eq_sum_admissible hP hr (ζ : ArithmeticFunction ℝ)
      isMultiplicative_zeta.natCast]
  have h1 : ∀ A ∈ r.primeFactors.powerset.filter (IsBrunAdmissible y β parity),
      (-1 : ℝ) ^ A.card * (∏ p ∈ A, (ζ : ArithmeticFunction ℝ) p) =
        (-1 : ℝ) ^ A.card * ∏ _ ∈ A, (1 : ℝ) := fun A hA ↦
    congrArg _ (prod_congr rfl fun p hp ↦ by
      simp [natCoe_apply, zeta_apply_ne
        (Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_filter.mp hA).1 hp)).ne_zero])
  rw [sum_congr rfl h1]
  have hprod0 : (∏ _ ∈ r.primeFactors, (1 - (1 : ℝ))) = if r = 1 then 1 else 0 := by
    have hrsq : Squarefree r := hP.squarefree_of_dvd hr
    split_ifs with hr1
    · simp [hr1]
    · obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hrsq.ne_zero, hr1⟩)
      exact prod_eq_zero hp (by ring)
  rw [← hprod0]
  exact sum_admissible_sub_prod_one_sub r.primeFactors (fun _ ↦ (1 : ℝ)) y β parity

open Classical in
private theorem sum_minFailing_one_nonneg (S₀ : Finset ℕ) (y β : ℝ) (parity : ℕ) :
    (0 : ℝ) ≤ ∑ B ∈ S₀.powerset.filter (isBrunMinFailing y β parity),
      (∏ _ ∈ B, (1 : ℝ)) * ∏ q ∈ S₀.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - (1 : ℝ)) := by
  refine sum_nonneg fun B _ ↦ ?_
  rw [sub_self, prod_const_one, one_mul]
  by_cases hemp : (S₀.filter (fun q ↦ ∀ b ∈ B, q < b)) = ∅
  · simp [hemp]
  · obtain ⟨q, hq⟩ := nonempty_iff_ne_empty.mpr hemp
    rw [prod_eq_zero hq rfl]

/-- **Brun lower divisor bracket**: for squarefree `P` and every `r ∣ P`,
`∑ d ∈ r.divisors, brunWeights P y β 0 d ≤ if r = 1 then 1 else 0`. -/
theorem sum_divisors_brunWeights_zero_le {P r : ℕ} (hP : Squarefree P) (hr : r ∣ P) (y β : ℝ) :
    ∑ d ∈ r.divisors, brunWeights P y β 0 d ≤ if r = 1 then 1 else 0 := by
  have hid := sum_divisors_brunWeights_sub_ite_eq hP hr y β 0
  have hnn := sum_minFailing_one_nonneg r.primeFactors y β 0
  rw [zero_add, pow_one, neg_one_mul] at hid
  linarith

/-- **Brun upper divisor bracket**: for squarefree `P` and every `r ∣ P`,
`(if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, brunWeights P y β 1 d`. -/
theorem le_sum_divisors_brunWeights_one {P r : ℕ} (hP : Squarefree P) (hr : r ∣ P) (y β : ℝ) :
    (if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, brunWeights P y β 1 d := by
  have hid := sum_divisors_brunWeights_sub_ite_eq hP hr y β 1
  have hnn := sum_minFailing_one_nonneg r.primeFactors y β 1
  rw [show (1 + 1 : ℕ) = 2 from rfl, neg_one_sq, one_mul] at hid
  linarith

/-! ### Prefix induction for minimal-failing prime sets -/

private theorem two_step_rpow_le {A p y β : ℝ} {m' : ℕ} (hA0 : 0 < A) (hp0 : 0 < p)
    (hy : 1 < y) (hβ : 1 < β)
    (hA : A ≤ y ^ (1 - (β + 1) / β * (1 - β⁻¹) ^ m'))
    (hstep : A * p ^ (β + 1) < y) :
    A * p ^ 2 ≤ y ^ (1 - (β + 1) / β * (1 - β⁻¹) ^ (m' + 2)) := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hβ1 : 0 < β + 1 := by linarith
  set θ : ℝ := (β + 1) / β * (1 - β⁻¹) ^ m'
  have hθ_pos : 0 < θ := by
    have : 0 < 1 - β⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hβ)
    positivity
  have hrpow : (A * p ^ 2) ^ (β + 1) ≤ y ^ ((β + 1) - θ * (β - 1)) := by
    have hident : (A * p ^ 2) ^ (β + 1) = A ^ (β - 1) * (A * p ^ (β + 1)) ^ 2 := by
      rw [mul_rpow hA0.le (sq_nonneg _), ← rpow_natCast p 2, ← rpow_mul hp0.le, mul_pow,
        ← rpow_natCast A 2, ← mul_assoc, ← rpow_add hA0,
        ← rpow_natCast (p ^ (β + 1)) 2, ← rpow_mul hp0.le,
        show β - 1 + (2 : ℕ) = β + 1 by push_cast; ring,
        show ((2 : ℕ) : ℝ) * (β + 1) = (β + 1) * (2 : ℕ) by ring]
    rw [hident]
    calc A ^ (β - 1) * (A * p ^ (β + 1)) ^ 2
        ≤ (y ^ (1 - θ)) ^ (β - 1) * y ^ 2 :=
          mul_le_mul (rpow_le_rpow hA0.le hA (by linarith))
            (pow_le_pow_left₀ (by positivity) hstep.le 2) (by positivity) (by positivity)
      _ = y ^ ((β + 1) - θ * (β - 1)) := by
          rw [← rpow_mul hy0.le, ← rpow_natCast y 2, ← rpow_add hy0]
          congr 1; push_cast; ring
  have hAp2 : A * p ^ 2 ≤ y ^ (1 - θ * ((β - 1) / (β + 1))) := by
    have hbase : 0 ≤ A * p ^ 2 := by positivity
    have h1 := rpow_le_rpow (rpow_nonneg hbase _) hrpow (one_div_nonneg.mpr hβ1.le)
    rw [← rpow_mul hbase, mul_one_div_cancel hβ1.ne', rpow_one, ← rpow_mul hy0.le,
      show ((β + 1) - θ * (β - 1)) * (1 / (β + 1)) = 1 - θ * ((β - 1) / (β + 1)) by
        field_simp] at h1
    exact h1
  have hexp : 1 - θ * ((β - 1) / (β + 1)) ≤ 1 - (β + 1) / β * (1 - β⁻¹) ^ (m' + 2) := by
    have hcmp : (1 - β⁻¹) ^ 2 ≤ (β - 1) / (β + 1) := by
      have : (β - 1) / (β + 1) - (1 - β⁻¹) ^ 2 = (β - 1) / (β ^ 2 * (β + 1)) := by
        field_simp; ring
      have hpos : 0 < (β - 1) / (β ^ 2 * (β + 1)) := div_pos (by linarith) (by positivity)
      linarith
    rw [pow_add, show (β + 1) / β * ((1 - β⁻¹) ^ m' * (1 - β⁻¹) ^ 2) = θ * (1 - β⁻¹) ^ 2 by ring]
    nlinarith [mul_le_mul_of_nonneg_left hcmp hθ_pos.le]
  exact hAp2.trans (rpow_le_rpow_of_exponent_le hy.le hexp)

/-- Two-step prefix product upper bound for a minimal-failing sorted prime list. -/
private theorem take_prod_le_rpow_of_minFailing {l : List ℕ} {y β z : ℝ}
    (hsort : l.SortedGT) (hp1 : ∀ p ∈ l, 1 ≤ p)
    (hy : 1 < y) (hβ : 1 < β) (hzy : z ≤ y ^ (1 / β)) (hlz : ∀ p ∈ l, (p : ℝ) < z)
    (hpass : ∀ (i : ℕ) (hi : i < l.length), i + 1 < l.length →
      (i + 1) % 2 = l.length % 2 → brunStepLt y β l i hi) :
    ∀ m : ℕ, 1 ≤ m → m ≤ l.length → m % 2 = l.length % 2 →
      (((l.take (m - 1)).prod : ℕ) : ℝ) ≤ y ^ (1 - ((β + 1) / β) * (1 - β⁻¹) ^ m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm1 hmlen hmpar
    rcases eq_or_ne m 1 with rfl | hm_ne1
    · simp only [Nat.sub_self, List.take_zero, List.prod_nil, Nat.cast_one]
      have h1 : (β + 1) / β * (1 - β⁻¹) ^ 1 = 1 - 1 / β ^ 2 := by field_simp; ring
      exact one_le_rpow hy.le (by rw [h1]; linarith [show 0 ≤ 1 / β ^ 2 by positivity])
    rcases eq_or_ne m 2 with rfl | hm_ne2
    · rcases l with _ | ⟨p₀, tl⟩
      · simp at hmlen
      · simp only [Nat.add_one_sub_one, List.take_succ_cons, List.take_zero, List.prod_singleton]
        have hexp : 1 / β ≤ 1 - (β + 1) / β * (1 - β⁻¹) ^ 2 := by
          have : 1 - (β + 1) / β * (1 - β⁻¹) ^ 2 - 1 / β = (β - 1) / β ^ 3 := by field_simp; ring
          linarith [show 0 < (β - 1) / β ^ 3 from div_pos (by linarith) (by positivity)]
        exact ((hlz p₀ List.mem_cons_self).le.trans hzy).trans
          (rpow_le_rpow_of_exponent_le hy.le hexp)
    · let m' := m - 2
      have hm'_eq : m = m' + 2 := by omega
      have hm'1 : 1 ≤ m' := by omega
      have hm'_len : m' < l.length := by omega
      have hidx : m' - 1 < l.length := by omega
      have ihm := ih m' (by omega) hm'1 hm'_len.le (by omega)
      set A : ℝ := (((l.take (m' - 1)).prod : ℕ) : ℝ)
      have hA_pos : 0 < A :=
        Nat.cast_pos.mpr (List.prod_pos fun p hp ↦ hp1 p (List.mem_of_mem_take hp))
      have hp_pos : (0 : ℝ) < (l[m' - 1] : ℕ) := Nat.cast_pos.mpr (hp1 _ (List.getElem_mem _))
      have hprod_m' : (((l.take m').prod : ℕ) : ℝ) = A * (l[m' - 1] : ℕ) := by
        conv_lhs => rw [← Nat.sub_add_cancel hm'1, List.prod_take_succ l (m' - 1) hidx]
        exact Nat.cast_mul _ _
      have hstep := (brunStepLt_iff_mul_rpow_lt hp1 (zero_lt_one.trans hy).le
        (zero_lt_one.trans hβ) hidx).mp (hpass (m' - 1) hidx (by omega) (by omega))
      have hlt_next : ((l[m'] : ℕ) : ℝ) ≤ (l[m' - 1] : ℕ) := by
        exact_mod_cast (hsort.getElem_gt_getElem_of_lt (by omega : m' - 1 < m')).le
      have htake_m : (((l.take (m - 1)).prod : ℕ) : ℝ) ≤ A * ((l[m' - 1] : ℕ) : ℝ) ^ 2 := by
        rw [show m - 1 = m' + 1 by omega, List.prod_take_succ l m' hm'_len, Nat.cast_mul, hprod_m']
        nlinarith [mul_le_mul_of_nonneg_left hlt_next (mul_nonneg hA_pos.le hp_pos.le)]
      exact htake_m.trans (hm'_eq ▸ two_step_rpow_le hA_pos hp_pos hy hβ ihm hstep)

private theorem minFailing_last_fail {B : Finset ℕ} {y β : ℝ} {parity : ℕ}
    (hB : isBrunMinFailing y β parity B) (hpB : ∀ b ∈ B, b.Prime) (hy : 1 < y) (hβ : 1 < β) :
    y ≤ ((((B.sort (· ≥ ·)).take ((B.sort (· ≥ ·)).length - 1)).prod : ℕ) : ℝ) *
      (((B.sort (· ≥ ·))[(B.sort (· ≥ ·)).length - 1]'(Nat.sub_lt hB.choose zero_lt_one) : ℕ) : ℝ) ^
        (β + 1) := by
  obtain ⟨hlen, _, _, hfail⟩ := hB
  have hp1 : ∀ p ∈ B.sort (· ≥ ·), 1 ≤ p := fun p hp ↦ (hpB p ((mem_sort _).mp hp)).one_le
  exact not_lt.mp ((brunStepLt_iff_mul_rpow_lt hp1 (zero_lt_one.trans hy).le
    (zero_lt_one.trans hβ) (Nat.sub_lt hlen zero_lt_one)).not.mp hfail)

private theorem lt_rpow_card_add_of_minFailing {B : Finset ℕ} {y β z : ℝ} {parity : ℕ}
    (hB : isBrunMinFailing y β parity B) (hpB : ∀ b ∈ B, b.Prime)
    (hy : 1 < y) (hβ : 1 < β) (hz1 : 1 < z) (hBz : ∀ b ∈ B, (b : ℝ) < z) :
    y < z ^ ((B.card : ℝ) + β) := by
  let l := B.sort (· ≥ ·)
  have hlen : 0 < l.length := hB.choose
  have hz0 : 0 < z := zero_lt_one.trans hz1
  have hlz : ∀ p ∈ l, (p : ℝ) < z := fun p hp ↦ hBz p ((mem_sort _).mp hp)
  have hA_pos : (0 : ℝ) < (((l.take (l.length - 1)).prod : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (List.prod_pos fun p hp ↦
      (hpB p ((mem_sort _).mp (List.mem_of_mem_take hp))).one_le)
  have htake_le : (((l.take (l.length - 1)).prod : ℕ) : ℝ) ≤ z ^ (l.length - 1) := by
    have h := List.prod_map_le_pow_length₀ (f := Nat.castRingHom ℝ) (t := l.take (l.length - 1))
      (fun p _ ↦ by simp) (fun p hp ↦ by simpa using (hlz p (List.mem_of_mem_take hp)).le)
    simpa [Nat.cast_list_prod, List.length_take_of_le (Nat.sub_le l.length 1)] using h
  have hlast_lt : ((l[l.length - 1]'(Nat.sub_lt hlen zero_lt_one) : ℕ) : ℝ) ^ (β + 1) <
      z ^ (β + 1) :=
    rpow_lt_rpow (Nat.cast_nonneg _) (hlz _ (List.getElem_mem _)) (by linarith)
  have hmul_lt : (((l.take (l.length - 1)).prod : ℕ) : ℝ) *
      ((l[l.length - 1]'(Nat.sub_lt hlen zero_lt_one) : ℕ) : ℝ) ^ (β + 1) <
      z ^ (l.length - 1) * z ^ (β + 1) :=
    (mul_lt_mul_of_pos_left hlast_lt hA_pos).trans_le
      (mul_le_mul_of_nonneg_right htake_le (rpow_nonneg hz0.le _))
  rw [← rpow_natCast z (l.length - 1), ← rpow_add hz0,
    show ((l.length - 1 : ℕ) : ℝ) + (β + 1) = (B.card : ℝ) + β by
      rw [Nat.cast_sub hlen, show l.length = B.card from length_sort (· ≥ ·)]; ring] at hmul_lt
  exact (minFailing_last_fail hB hpB hy hβ).trans_lt hmul_lt

private theorem rpow_le_of_mem_minFailing {B : Finset ℕ} {y β z : ℝ} {parity : ℕ}
    (hB : isBrunMinFailing y β parity B) (hpB : ∀ b ∈ B, b.Prime)
    (hy : 1 < y) (hβ : 1 < β) (hz1 : 1 < z) (hzy : z ≤ y ^ (1 / β))
    (hBz : ∀ b ∈ B, (b : ℝ) < z) :
    ∀ b ∈ B, z ^ ((1 - β⁻¹) ^ B.card) ≤ (b : ℝ) := by
  have hfail_ge := minFailing_last_fail hB hpB hy hβ
  obtain ⟨hlen, hpar, hpass, _⟩ := hB
  let l := B.sort (· ≥ ·)
  have hn_eq : l.length = B.card := length_sort (· ≥ ·)
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hz0 : 0 < z := zero_lt_one.trans hz1
  have hp1 : ∀ p ∈ l, 1 ≤ p := fun p hp ↦ (hpB p ((mem_sort _).mp hp)).one_le
  have hlz : ∀ p ∈ l, (p : ℝ) < z := fun p hp ↦ hBz p ((mem_sort _).mp hp)
  have hpref := take_prod_le_rpow_of_minFailing (sortedGT_sort B) hp1 hy hβ hzy hlz
    (fun i hi hlt hmod ↦ hpass i hi hlt (hmod.trans hpar)) l.length hlen le_rfl rfl
  set θ : ℝ := (β + 1) / β * (1 - β⁻¹) ^ l.length
  have hlast_rpow : y ^ θ ≤
      ((l[l.length - 1]'(Nat.sub_lt hlen zero_lt_one) : ℕ) : ℝ) ^ (β + 1) := by
    refine le_of_mul_le_mul_left ?_ (rpow_pos_of_pos hy0 (1 - θ))
    rw [← rpow_add hy0, sub_add_cancel, rpow_one]
    exact hfail_ge.trans (mul_le_mul_of_nonneg_right hpref (rpow_nonneg (Nat.cast_nonneg _) _))
  have hlast_ge : z ^ ((1 - β⁻¹) ^ l.length) ≤
      ((l[l.length - 1]'(Nat.sub_lt hlen zero_lt_one) : ℕ) : ℝ) := by
    have h2 := rpow_le_rpow (rpow_nonneg hy0.le _) hlast_rpow
      (one_div_nonneg.mpr (by linarith : (0 : ℝ) ≤ β + 1))
    rw [← rpow_mul hy0.le, ← rpow_mul (Nat.cast_nonneg _),
      mul_one_div_cancel (by linarith : β + 1 ≠ 0), rpow_one,
      show θ * (1 / (β + 1)) = (1 / β) * (1 - β⁻¹) ^ l.length by dsimp [θ]; field_simp,
      rpow_mul hy0.le] at h2
    exact (rpow_le_rpow hz0.le hzy
      (pow_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hβ.le)) l.length)).trans h2
  intro b hb
  obtain ⟨k, hk_lt, rfl⟩ := List.getElem_of_mem ((mem_sort (· ≥ ·)).mpr hb)
  have hge_last : (l[l.length - 1]'(Nat.sub_lt hlen zero_lt_one) : ℕ) ≤ l[k] := by
    rcases (Nat.le_sub_one_of_lt hk_lt).eq_or_lt with heq | hlt
    · subst heq; exact le_rfl
    · exact ((sortedGT_sort B).getElem_gt_getElem_of_lt hlt).le
  rw [← hn_eq]
  exact hlast_ge.trans (by exact_mod_cast hge_last)

/-- Every minimal-failing subset `B` of primes `< z` satisfies `y < z ^ (B.card + β)` and
`z ^ ((1 - β⁻¹) ^ B.card) ≤ b` for every `b ∈ B`. -/
private theorem minFailing_bounds {B : Finset ℕ} {y β z : ℝ} {parity : ℕ}
    (hB : isBrunMinFailing y β parity B)
    (hpB : ∀ b ∈ B, b.Prime) (hy : 1 < y) (hβ : 1 < β) (hz1 : 1 < z) (hzy : z ≤ y ^ (1 / β))
    (hBz : ∀ b ∈ B, (b : ℝ) < z) :
    y < z ^ ((B.card : ℝ) + β) ∧ ∀ b ∈ B, z ^ ((1 - β⁻¹) ^ B.card) ≤ (b : ℝ) :=
  ⟨lt_rpow_card_add_of_minFailing hB hpB hy hβ hz1 hBz,
    rpow_le_of_mem_minFailing hB hpB hy hβ hz1 hzy hBz⟩

end TauCeti

namespace BoundingSieve

/-- **Brun lower sifted-sum bracket**: `∑ d ∣ P, λ⁻(d) * s.multSum d ≤ s.siftedSum`. -/
theorem sum_brunWeights_zero_le_siftedSum (s : BoundingSieve) (y β : ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, TauCeti.brunWeights s.prodPrimes y β 0 d * s.multSum d ≤
      s.siftedSum :=
  s.sum_le_siftedSum_of_dvd _ fun _ hr ↦
    TauCeti.sum_divisors_brunWeights_zero_le s.prodPrimes_squarefree hr y β

/-- **Brun upper sifted-sum bracket**: `s.siftedSum ≤ ∑ d ∣ P, λ⁺(d) * s.multSum d`. -/
theorem siftedSum_le_sum_brunWeights_one (s : BoundingSieve) (y β : ℝ) :
    s.siftedSum ≤
      ∑ d ∈ s.prodPrimes.divisors, TauCeti.brunWeights s.prodPrimes y β 1 d * s.multSum d :=
  s.siftedSum_le_sum_of_dvd _ fun _ hr ↦
    TauCeti.le_sum_divisors_brunWeights_one s.prodPrimes_squarefree hr y β

open Classical in
/-- Exact first-failure formula for `s.mainSum (brunWeights s.prodPrimes y β parity) - V`. -/
private theorem mainSum_brunWeights_sub_prod_eq (s : BoundingSieve) (y β : ℝ) (parity : ℕ) :
    s.mainSum (TauCeti.brunWeights s.prodPrimes y β parity) -
        ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) =
      (-1 : ℝ) ^ (parity + 1) *
        ∑ B ∈ s.prodPrimes.primeFactors.powerset.filter (TauCeti.isBrunMinFailing y β parity),
          (∏ p ∈ B, s.nu p) *
            ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - s.nu q) := by
  rw [mainSum, TauCeti.sum_divisors_brunWeights_mul_eq_sum_admissible
    s.prodPrimes_squarefree dvd_rfl s.nu s.nu_mult y β parity]
  exact TauCeti.sum_admissible_sub_prod_one_sub s.prodPrimes.primeFactors s.nu y β parity

open Classical in
private theorem sum_minFailing_nu_nonneg (s : BoundingSieve) (y β : ℝ) (parity : ℕ) :
    (0 : ℝ) ≤ ∑ B ∈ s.prodPrimes.primeFactors.powerset.filter (TauCeti.isBrunMinFailing y β parity),
      (∏ p ∈ B, s.nu p) *
        ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - s.nu q) :=
  sum_nonneg fun _ hB ↦ mul_nonneg
    (prod_nonneg fun _ hp ↦
      (s.nu_pos_of_mem_primeFactors (mem_powerset.mp (mem_filter.mp hB).1 hp)).le)
    (prod_nonneg fun _ hq ↦ (s.one_sub_nu_pos_of_mem_primeFactors (mem_filter.mp hq).1).le)

/-- The lower Brun main sum never exceeds the Euler product `∏ p ∈ P.primeFactors, (1 - s.nu p)`. -/
theorem mainSum_brunWeights_zero_le (s : BoundingSieve) (y β : ℝ) :
    s.mainSum (TauCeti.brunWeights s.prodPrimes y β 0) ≤
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  classical
  have hid := s.mainSum_brunWeights_sub_prod_eq y β 0
  have hnn := s.sum_minFailing_nu_nonneg y β 0
  norm_num at hid
  linarith

/-- The upper Brun main sum is at least the Euler product `∏ p ∈ P.primeFactors, (1 - s.nu p)`. -/
theorem le_mainSum_brunWeights_one (s : BoundingSieve) (y β : ℝ) :
    ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ≤
      s.mainSum (TauCeti.brunWeights s.prodPrimes y β 1) := by
  classical
  have hid := s.mainSum_brunWeights_sub_prod_eq y β 1
  have hnn := s.sum_minFailing_nu_nonneg y β 1
  norm_num at hid
  linarith

/-- Removing a subset `S ⊆ s.prodPrimes.primeFactors` from the Euler product divides by the
corresponding subproduct. -/
private theorem prod_sdiff_one_sub_nu_eq (s : BoundingSieve) {S : Finset ℕ}
    (hS : S ⊆ s.prodPrimes.primeFactors) :
    ∏ q ∈ s.prodPrimes.primeFactors \ S, (1 - s.nu q) =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * ∏ p ∈ S, (1 - s.nu p)⁻¹ := by
  have hmul := prod_sdiff (f := fun p ↦ 1 - s.nu p) hS
  have hinv : (∏ p ∈ S, (1 - s.nu p)) * (∏ p ∈ S, (1 - s.nu p)⁻¹) = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun p hp ↦ mul_inv_cancel₀ (s.one_sub_nu_pos_of_mem_primeFactors (hS hp)).ne'
  rw [← hmul, mul_assoc, hinv, mul_one]

open Classical in
private theorem sum_minFailing_card_le (s : BoundingSieve) {y β z : ℝ} {parity n : ℕ}
    (hy : 1 < y) (hβ : 1 < β) (hz1 : 1 < z) (hzy : z ≤ y ^ (1 / β))
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
    let w := max 2 (z ^ ((1 - β⁻¹) ^ n))
    let S := s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
    let Mn := (s.prodPrimes.primeFactors.powerset.filter
      (TauCeti.isBrunMinFailing y β parity)).filter (fun B ↦ B.card = n)
    ∑ B ∈ Mn, (∏ p ∈ B, s.nu p) *
        (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - s.nu q)) ≤
      V * ((∏ p ∈ S, (1 - s.nu p)⁻¹) * ∑ B ∈ S.powersetCard n, ∏ p ∈ B, s.nu p) := by
  intro V w S Mn
  let P' := s.prodPrimes.primeFactors
  -- Step 1: every minimal-failing `B` of size `n` has all elements in `S = P' ∩ [w, z)`.
  have hsub_pow : Mn ⊆ S.powersetCard n := by
    intro B hB
    obtain ⟨⟨hBP, hBm⟩, hcard⟩ := by simpa only [mem_filter, mem_powerset, Mn] using hB
    have hbds := TauCeti.minFailing_bounds hBm
      (fun b hb ↦ Nat.prime_of_mem_primeFactors (hBP hb)) hy hβ hz1 hzy
      (fun b hb ↦ hprimes b (hBP hb))
    refine mem_powersetCard.mpr ⟨fun b hb ↦ mem_filter.mpr ⟨hBP hb, ?_, hprimes b (hBP hb)⟩, hcard⟩
    exact max_le_iff.mpr ⟨by exact_mod_cast (Nat.prime_of_mem_primeFactors (hBP hb)).two_le,
      hcard ▸ hbds.2 b hb⟩
  -- Step 2: bound the tail Euler product over `{q < min B}` above by `P' \ S`, then enlarge `Mn`.
  calc ∑ B ∈ Mn, (∏ p ∈ B, s.nu p) *
          (∏ q ∈ P'.filter (fun q ↦ ∀ b ∈ B, q < b), (1 - s.nu q))
      ≤ ∑ B ∈ Mn, (∏ p ∈ B, s.nu p) * (V * ∏ p ∈ S, (1 - s.nu p)⁻¹) := by
        refine sum_le_sum fun B hB ↦ mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun p hp ↦
          (s.nu_pos_of_mem_primeFactors
            (filter_subset _ _ ((mem_powersetCard.mp (hsub_pow hB)).1 hp))).le)
        rw [← s.prod_sdiff_one_sub_nu_eq (filter_subset _ _)]
        refine prod_le_prod_of_subset_of_le_one₀ ?_
          (fun q hq ↦ (s.one_sub_nu_pos_of_mem_primeFactors (filter_subset _ _ hq)).le)
          (fun q hq _ ↦ sub_le_self 1
            (s.nu_pos_of_mem_primeFactors (filter_subset _ _ hq)).le)
        intro q hq
        obtain ⟨hqP, hqnotS⟩ := mem_sdiff.mp hq
        have hqw : (q : ℝ) < w := by
          by_contra hge; exact hqnotS (mem_filter.mpr ⟨hqP, le_of_not_gt hge, hprimes q hqP⟩)
        exact mem_filter.mpr ⟨hqP, fun b hb ↦ by
          have hbS := (mem_powersetCard.mp (hsub_pow hB)).1 hb
          exact_mod_cast hqw.trans_le (mem_filter.mp hbS).2.1⟩
    _ ≤ ∑ B ∈ S.powersetCard n, (∏ p ∈ B, s.nu p) * (V * ∏ p ∈ S, (1 - s.nu p)⁻¹) :=
        sum_le_sum_of_subset_of_nonneg hsub_pow fun B hB _ ↦ mul_nonneg
          (prod_nonneg fun p hp ↦ (s.nu_pos_of_mem_primeFactors
            (filter_subset _ _ ((mem_powersetCard.mp hB).1 hp))).le)
          (mul_nonneg (prod_nonneg fun p hp ↦ (s.one_sub_nu_pos_of_mem_primeFactors hp).le)
            (prod_nonneg fun p hp ↦ inv_nonneg.mpr
              (s.one_sub_nu_pos_of_mem_primeFactors (filter_subset _ _ hp)).le))
    _ = V * ((∏ p ∈ S, (1 - s.nu p)⁻¹) * ∑ B ∈ S.powersetCard n, ∏ p ∈ B, s.nu p) := by
        rw [← sum_mul, mul_comm, mul_assoc]

/-- **Combinatorial main-sum defect bound**: when `1 < y`, `1 < β`, `1 < z ≤ y ^ (1 / β)`, and all
primes of `s.prodPrimes` lie strictly below `z`, the signed Brun main-sum defect is bounded by `V`
times a sum over failure lengths `n` with `y < z ^ (n + β)` of Euler-product ratios and elementary
symmetric sums on `[max 2 (z ^ ((1 - β⁻¹) ^ n)), z)`. -/
theorem brun_mainSum_defect_le (s : BoundingSieve) {y β z : ℝ} (parity : ℕ)
    (hy : 1 < y) (hβ : 1 < β) (hz1 : 1 < z) (hzy : z ≤ y ^ (1 / β))
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
    let w : ℕ → ℝ := fun n ↦ max 2 (z ^ ((1 - β⁻¹) ^ n))
    let S : ℕ → Finset ℕ := fun n ↦
      s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w n ≤ (p : ℝ) ∧ (p : ℝ) < z)
    (-1 : ℝ) ^ (parity + 1) *
        (s.mainSum (TauCeti.brunWeights s.prodPrimes y β parity) - V) ≤
      V * ∑ n ∈ (Icc 1 s.prodPrimes.primeFactors.card).filter
          (fun n : ℕ ↦ y < z ^ ((n : ℝ) + β)),
        (∏ p ∈ S n, (1 - s.nu p)⁻¹) * ∑ B ∈ (S n).powersetCard n, ∏ p ∈ B, s.nu p := by
  classical
  intro V w S
  have hid := congrArg ((-1 : ℝ) ^ (parity + 1) * ·) (s.mainSum_brunWeights_sub_prod_eq y β parity)
  set P' := s.prodPrimes.primeFactors
  set M := P'.powerset.filter (TauCeti.isBrunMinFailing y β parity)
  have hsign : (-1 : ℝ) ^ (parity + 1) * (-1 : ℝ) ^ (parity + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [← mul_assoc, hsign, one_mul] at hid
  let Nset := (Icc 1 P'.card).filter (fun n : ℕ ↦ y < z ^ ((n : ℝ) + β))
  have hpart : M = Nset.biUnion (fun n ↦ M.filter (fun B ↦ B.card = n)) := by
    ext B
    simp only [mem_biUnion, mem_filter, mem_Icc, M, Nset, mem_powerset]
    refine ⟨fun ⟨hBP, hBm⟩ ↦ ?_, fun ⟨_, _, hBM, rfl⟩ ↦ hBM⟩
    have hbds := TauCeti.minFailing_bounds hBm
      (fun b hb ↦ Nat.prime_of_mem_primeFactors (hBP hb)) hy hβ hz1 hzy
      (fun b hb ↦ hprimes b (hBP hb))
    have hpos : 0 < B.card := by simpa only [length_sort (· ≥ ·)] using hBm.choose
    exact ⟨B.card, ⟨⟨Nat.succ_le_of_lt hpos, card_le_card hBP⟩, hbds.1⟩, ⟨hBP, hBm⟩, rfl⟩
  have hdisj : (Nset : Set ℕ).PairwiseDisjoint (fun n ↦ M.filter (fun B ↦ B.card = n)) := by
    intro n₁ _ n₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    exact fun B h₁ h₂ ↦ hne ((mem_filter.mp h₁).2.symm.trans (mem_filter.mp h₂).2)
  rw [hid, hpart, sum_biUnion hdisj, mul_sum]
  exact sum_le_sum fun n _ ↦ s.sum_minFailing_card_le hy hβ hz1 hzy hprimes

end BoundingSieve
