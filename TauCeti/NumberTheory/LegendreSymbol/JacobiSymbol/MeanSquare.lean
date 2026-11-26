/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.ResidueClass
import TauCeti.Algebra.Order.BigOperators.Sum.Union
import TauCeti.Data.Nat.Prime.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Algebraic mean-square inequality for quadratic twists of prime-power sums

Let `8 ∣ m₀`, let `a₀` be odd, and let `P` be a finite set of natural numbers congruent to `a₀`
modulo `m₀` and coprime to every `n ≤ N` in the support of `c`. For nonnegative weights `c`
supported on prime powers up to `N`, coefficients `κ : ℕ → ℂ` with `‖κ n‖ ≤ 1`, a constant
`η ≥ 0`, and a uniform bound `|(∑ q ∈ P, J(q | s) : ℝ)| ≤ η * P.card` on
every odd squarefree `1 < s ≤ N ^ 2` coprime to `m₀` other than one exceptional modulus `sStar`,
expanding the square and applying reciprocity on the residue class
(`exists_jacobiSym_eq_mul_jacobiSym_oddExpPart`) bounds the mean square
`∑ q ∈ P, ‖∑ n ∈ Finset.Icc 1 N, c n * κ n * J(n | q)‖ ^ 2` by
`P.card * (∑ p, sP(p) ^ 2 + RR ^ 2 + 2 * B ^ 2 + 2 * B * RR + η * (∑ n, c n) ^ 2)`, where
`sP(p)` is the total weight on powers of `p`, `B` bounds every `sP(p)`, and `RR` is the total
weight on prime powers with even exponent or base dividing `m₀`.

## Main statements

* `TauCeti.sum_norm_sq_jacobiSym_le_sum_sum_mul_abs`: expanding the square of a twisted sum of
  Jacobi symbols over a finite set `P`.
* `TauCeti.sum_norm_sq_jacobiSym_le`: the algebraic mean-square inequality for quadratic twists of
  prime-power sums over a residue class modulo a multiple of `8`.

## References

* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>.
-/

public section

namespace TauCeti

open Nat (oddExpPart)

/-- Expanding the square: for nonnegative weights `c` and coefficients `‖κ n‖ ≤ 1` on a finite set
`S`, the mean square over a finite set `P` of the twisted sums `∑ n ∈ S, c n * κ n * J(n | q)` is
at most `∑ n ∈ S, ∑ n' ∈ S, c n * c n' * |∑ q ∈ P, J(n * n' | q)|`. -/
theorem sum_norm_sq_jacobiSym_le_sum_sum_mul_abs {P S : Finset ℕ} {c : ℕ → ℝ} {κ : ℕ → ℂ}
    (hc : ∀ n ∈ S, 0 ≤ c n) (hκ : ∀ n ∈ S, ‖κ n‖ ≤ 1) :
    ∑ q ∈ P, ‖∑ n ∈ S, (c n : ℂ) * κ n * (jacobiSym n q : ℂ)‖ ^ 2 ≤
      ∑ n ∈ S, ∑ n' ∈ S, c n * c n' * |(∑ q ∈ P, (jacobiSym (n * n') q : ℝ))| := by
  have h1 : ∀ q ∈ P, ‖∑ n ∈ S, (c n : ℂ) * κ n * (jacobiSym n q : ℂ)‖ ^ 2 =
      (∑ n ∈ S, ∑ n' ∈ S,
        ((c n * c n' : ℝ) : ℂ) * (κ n * star (κ n')) * (jacobiSym (n * n') q : ℂ)).re := by
    intro q _
    rw [← Complex.normSq_eq_norm_sq]
    have hre := congrArg Complex.re
      (Complex.normSq_eq_conj_mul_self (z := ∑ n ∈ S, (c n : ℂ) * κ n * (jacobiSym n q : ℂ)))
    rw [Complex.ofReal_re] at hre
    rw [hre, map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
    have hconj : starRingEnd ℂ (jacobiSym n' q : ℂ) = (jacobiSym n' q : ℂ) := by simp
    have hc' : starRingEnd ℂ (c n' : ℂ) = (c n' : ℂ) := Complex.conj_ofReal _
    congr 1
    simp only [map_mul, hc', hconj, jacobiSym.mul_left, Int.cast_mul, Complex.ofReal_mul,
      Complex.star_def]
    ring
  rw [Finset.sum_congr rfl h1, ← Complex.re_sum, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := P) (t := S)]
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun n' hn' => ?_
  have hsumC : (∑ q ∈ P, (jacobiSym (n * n') q : ℂ)) =
      Complex.ofReal (∑ q ∈ P, (jacobiSym (n * n') q : ℝ)) := by simp
  have hκ' : ‖κ n‖ * ‖κ n'‖ ≤ 1 := by
    calc ‖κ n‖ * ‖κ n'‖ ≤ 1 * 1 :=
          mul_le_mul (hκ n hn) (hκ n' hn') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc (∑ q ∈ P, ((c n * c n' : ℝ) : ℂ) * (κ n * star (κ n')) * (jacobiSym (n * n') q : ℂ)).re
      ≤ ‖∑ q ∈ P, ((c n * c n' : ℝ) : ℂ) * (κ n * star (κ n')) * (jacobiSym (n * n') q : ℂ)‖ :=
        Complex.re_le_norm _
    _ = c n * c n' * (‖κ n‖ * ‖κ n'‖) * |(∑ q ∈ P, (jacobiSym (n * n') q : ℝ))| := by
        rw [← Finset.mul_sum, hsumC]
        simp only [norm_mul, Complex.norm_real, norm_star, Real.norm_eq_abs,
          abs_of_nonneg (hc n hn), abs_of_nonneg (hc n' hn')]
    _ ≤ c n * c n' * 1 * |(∑ q ∈ P, (jacobiSym (n * n') q : ℝ))| := by
        gcongr; exact mul_nonneg (hc n hn) (hc n' hn')
    _ = c n * c n' * |(∑ q ∈ P, (jacobiSym (n * n') q : ℝ))| := by ring

private lemma special_pairs_subset {m₀ sStar : ℕ} {S R A : Finset ℕ}
    (hS : ∀ n ∈ S, IsPrimePow n) (hR : R = S.filter fun n => oddExpPart m₀ n = 1)
    (hA : A = S.filter fun n => oddExpPart m₀ n ≠ 1) :
    (S ×ˢ S).filter (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨
        oddExpPart m₀ (x.1 * x.2) = sStar) ⊆
      (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac) ∪
      (R ×ˢ R) ∪
      ((A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧ x.1.minFac * x.2.minFac = sStar)) ∪
      ((R ×ˢ A).filter (fun x => x.2.minFac = sStar)) ∪
      ((A ×ˢ R).filter (fun x => x.1.minFac = sStar)) := by
  classical
  subst hR hA
  intro ⟨n, n'⟩ hx
  obtain ⟨hmem, hor⟩ := Finset.mem_filter.mp hx
  obtain ⟨hnS, hn'S⟩ := Finset.mem_product.mp hmem
  have hpp := hS n hnS
  have hpp' := hS n' hn'S
  have hmul := Nat.oddExpPart_mul_of_isPrimePow (m := m₀) hpp hpp'
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, ne_eq]
  by_cases h1 : oddExpPart m₀ n = 1 <;> by_cases h2 : oddExpPart m₀ n' = 1
  · simp [hnS, hn'S, h1, h2]
  · have hv := Nat.oddExpPart_eq_minFac_of_isPrimePow hpp' h2
    rw [ite_eq_left h1, hv] at hmul
    have hss : n'.minFac = sStar := hmul.symm.trans (hor.resolve_left (hmul ▸ hv ▸ h2))
    simp [hnS, hn'S, h1, h2, hss]
  · have hv := Nat.oddExpPart_eq_minFac_of_isPrimePow hpp h1
    rw [ite_eq_right h1, ite_eq_left h2, hv] at hmul
    have hss : n.minFac = sStar := hmul.symm.trans (hor.resolve_left (hmul ▸ hv ▸ h1))
    simp [hnS, hn'S, h1, h2, hss]
  · rw [ite_eq_right h1, ite_eq_right h2] at hmul
    by_cases heq : n.minFac = n'.minFac
    · simp [hnS, hn'S, h1, h2, heq]
    · rw [ite_eq_right heq] at hmul
      have hne1 : n.minFac * n'.minFac ≠ 1 := by
        have hp1 := (Nat.minFac_prime hpp.ne_one).one_lt
        have hp2 := (Nat.minFac_prime hpp'.ne_one).one_lt
        nlinarith
      have hss : n.minFac * n'.minFac = sStar := hmul.symm.trans (hor.resolve_left (hmul ▸ hne1))
      simp [hnS, hn'S, h1, h2, heq, hss]

/-- `Nat.minFac_mem_filter_prime_Icc` for a prime power in `[1, N]`. -/
private lemma minFac_mem_of_mem_primePows {N n : ℕ}
    (hn : n ∈ (Finset.Icc 1 N).filter IsPrimePow) : n.minFac ∈ (Finset.Icc 1 N).filter Nat.Prime :=
  Nat.minFac_mem_filter_prime_Icc (Finset.mem_filter.mp hn).2.one_lt
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2

/-- For weights nonnegative on `S` and `A ⊆ S`, the weight on the members of `A` with least prime
factor `p` is nonnegative. -/
private lemma sum_fiber_nonneg {S A : Finset ℕ} {c : ℕ → ℝ} (hAS : A ⊆ S)
    (hc : ∀ n ∈ S, 0 ≤ c n) (p : ℕ) : 0 ≤ ∑ n ∈ A.filter (fun n => n.minFac = p), c n :=
  Finset.sum_nonneg fun n hn => hc n (hAS (Finset.mem_filter.mp hn).1)

/-- For weights nonnegative on `S` and `A ⊆ S`, the weight on the members of `A` with least prime
factor `p` is at most the weight on the members of `S` with least prime factor `p`. -/
private lemma sum_fiber_le_of_subset {S A : Finset ℕ} {c : ℕ → ℝ} (hAS : A ⊆ S)
    (hc : ∀ n ∈ S, 0 ≤ c n) (p : ℕ) :
    ∑ n ∈ A.filter (fun n => n.minFac = p), c n ≤ ∑ n ∈ S.filter (fun n => n.minFac = p), c n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hAS)
    fun n hn _ => hc n (Finset.mem_filter.mp hn).1

private lemma sum_diag_active_le {N : ℕ} {S A : Finset ℕ} {c : ℕ → ℝ}
    (hS : S = (Finset.Icc 1 N).filter IsPrimePow) (hAS : A ⊆ S) (hc : ∀ n ∈ S, 0 ≤ c n) :
    ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac), c x.1 * c x.2 ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ^ 2 := by
  classical
  subst hS
  have hfib : ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac), c x.1 * c x.2 =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (∑ n ∈ A.filter (fun n => n.minFac = p), c n) ^ 2 := by
    simp_rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ⟨n, n'⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨hn, hn'⟩, heq⟩ => ⟨n.minFac,
          Finset.mem_filter.mp (minFac_mem_of_mem_primePows (hAS hn)), ⟨hn, rfl⟩, ⟨hn', heq.symm⟩⟩,
        fun ⟨_, _, ⟨hn, hp1⟩, ⟨hn', hp2⟩⟩ => ⟨⟨hn, hn'⟩, hp1.trans hp2.symm⟩⟩
    · intro p _ q _ hpq
      rw [Function.onFun, Finset.disjoint_left]
      intro ⟨n, _⟩ h1 h2
      exact hpq ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2)
  rw [hfib]
  exact Finset.sum_le_sum fun p _ =>
    pow_le_pow_left₀ (sum_fiber_nonneg hAS hc p) (sum_fiber_le_of_subset hAS hc p) 2

private lemma sum_offDiag_eq_sum_pairs {N sStar : ℕ} {A : Finset ℕ} {Q : Finset (ℕ × ℕ)}
    {c : ℕ → ℝ} (hA : A ⊆ (Finset.Icc 1 N).filter IsPrimePow)
    (hQ : Q = ((Finset.Icc 1 N).filter Nat.Prime ×ˢ (Finset.Icc 1 N).filter Nat.Prime).filter
      fun q => q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧ q.1 * q.2 = sStar) :
    ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧
        x.1.minFac * x.2.minFac = sStar), c x.1 * c x.2 =
      ∑ q ∈ Q, (∑ n ∈ A.filter (fun n => n.minFac = q.1), c n) *
        (∑ n' ∈ A.filter (fun n' => n'.minFac = q.2), c n') := by
  classical
  subst hQ
  simp_rw [Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ⟨n, n'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨hn, hn'⟩, hne, hmul⟩
      have h1 := minFac_mem_of_mem_primePows (hA hn)
      have h2 := minFac_mem_of_mem_primePows (hA hn')
      exact ⟨(n.minFac, n'.minFac), ⟨⟨Finset.mem_filter.mp h1, Finset.mem_filter.mp h2⟩,
        (Finset.mem_filter.mp h1).2,
        (Finset.mem_filter.mp h2).2, hne, hmul⟩, ⟨hn, rfl⟩, ⟨hn', rfl⟩⟩
    · rintro ⟨⟨p, q⟩, ⟨-, -, -, hne, hmul⟩, ⟨hn, rfl⟩, ⟨hn', rfl⟩⟩
      exact ⟨⟨hn, hn'⟩, hne, hmul⟩
  · intro q₁ _ q₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ⟨n, n'⟩ h1 h2
    exact hne (Prod.ext
      ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2)
      ((Finset.mem_filter.mp (Finset.mem_product.mp h1).2).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp h2).2).2))

private lemma sum_offDiag_active_le {N sStar : ℕ} {S A : Finset ℕ} {c : ℕ → ℝ} {B : ℝ}
    (hS : S = (Finset.Icc 1 N).filter IsPrimePow) (hAS : A ⊆ S) (hc : ∀ n ∈ S, 0 ≤ c n)
    (hB : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ≤ B) :
    ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧ x.1.minFac * x.2.minFac = sStar),
      c x.1 * c x.2 ≤ 2 * B ^ 2 := by
  classical
  subst hS
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset (ℕ × ℕ), Q = ((Finset.Icc 1 N).filter Nat.Prime ×ˢ
      (Finset.Icc 1 N).filter Nat.Prime).filter
        fun q => q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧ q.1 * q.2 = sStar := ⟨_, rfl⟩
  have hA_le_B : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ A.filter (fun n => n.minFac = p), c n) ≤ B := fun p hp =>
    (sum_fiber_le_of_subset hAS hc p).trans (hB p hp)
  have hQ2 : Q.card ≤ 2 := Nat.card_le_two_of_forall_prime_mul_eq fun q hq => by
    rw [hQ] at hq
    obtain ⟨-, h1, h2, -, h3⟩ := Finset.mem_filter.mp hq
    exact ⟨h1, h2, h3⟩
  rw [sum_offDiag_eq_sum_pairs hAS hQ]
  calc ∑ q ∈ Q, (∑ n ∈ A.filter (fun n => n.minFac = q.1), c n) *
        (∑ n' ∈ A.filter (fun n' => n'.minFac = q.2), c n')
      ≤ ∑ _q ∈ Q, B ^ 2 := Finset.sum_le_sum fun q hq => by
        rw [hQ] at hq
        have hqP := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
        rw [sq]
        exact mul_le_mul (hA_le_B q.1 hqP.1) (hA_le_B q.2 hqP.2) (sum_fiber_nonneg hAS hc q.2)
          ((sum_fiber_nonneg hAS hc q.1).trans (hA_le_B q.1 hqP.1))
    _ = (Q.card : ℝ) * B ^ 2 := by simp
    _ ≤ 2 * B ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hQ2) (sq_nonneg B)

private lemma sum_cross_active_le {N sStar : ℕ} {S R A : Finset ℕ} {c : ℕ → ℝ} {B : ℝ}
    (hS : S = (Finset.Icc 1 N).filter IsPrimePow) (hRS : R ⊆ S) (hAS : A ⊆ S)
    (hc : ∀ n ∈ S, 0 ≤ c n)
    (hB : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ≤ B) :
    (∑ n ∈ A.filter (fun n => n.minFac = sStar), c n) * (∑ n ∈ R, c n) ≤
      B * (∑ n ∈ R, c n) := by
  classical
  subst hS
  have hRR_nonneg : 0 ≤ ∑ n ∈ R, c n := Finset.sum_nonneg fun n hn => hc n (hRS hn)
  by_cases hsP : sStar ∈ (Finset.Icc 1 N).filter Nat.Prime
  · exact mul_le_mul_of_nonneg_right ((sum_fiber_le_of_subset hAS hc sStar).trans (hB sStar hsP))
      hRR_nonneg
  · have hempty : A.filter (fun n => n.minFac = sStar) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn heq
      exact hsP (heq ▸ minFac_mem_of_mem_primePows (hAS hn))
    rw [hempty, Finset.sum_empty, zero_mul]
    rcases R.eq_empty_or_nonempty with hR | ⟨n₀, hn₀⟩
    · simp [hR]
    · have hp0 := minFac_mem_of_mem_primePows (hRS hn₀)
      have hB0 : 0 ≤ B :=
        (sum_fiber_nonneg (Finset.Subset.refl _) hc n₀.minFac).trans (hB n₀.minFac hp0)
      exact mul_nonneg hB0 hRR_nonneg

private lemma sum_special_pairs_le {m₀ N sStar : ℕ} {S R : Finset ℕ} {c : ℕ → ℝ} {B : ℝ}
    (hS : S = (Finset.Icc 1 N).filter IsPrimePow)
    (hR : R = S.filter fun n => oddExpPart m₀ n = 1)
    (hc : ∀ n ∈ S, 0 ≤ c n)
    (hB : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ≤ B) :
    ∑ x ∈ (S ×ˢ S).filter (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨
        oddExpPart m₀ (x.1 * x.2) = sStar), c x.1 * c x.2 ≤
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ^ 2) +
        (∑ n ∈ R, c n) ^ 2 + 2 * B ^ 2 + 2 * B * (∑ n ∈ R, c n) := by
  classical
  set A := S.filter (fun n => oddExpPart m₀ n ≠ 1) with hA
  have hRS : R ⊆ S := by rw [hR]; exact Finset.filter_subset _ _
  have hAS : A ⊆ S := by rw [hA]; exact Finset.filter_subset _ _
  have hpp : ∀ n ∈ S, IsPrimePow n := fun n hn => by
    rw [hS] at hn; exact (Finset.mem_filter.mp hn).2
  have hsub := special_pairs_subset (sStar := sStar) hpp hR hA
  have h1 := sum_diag_active_le hS hAS hc
  have h3 := sum_offDiag_active_le (sStar := sStar) hS hAS hc hB
  set U1 := (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac) with hU1
  set U2 := R ×ˢ R with hU2
  set U3 := (A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧
    x.1.minFac * x.2.minFac = sStar) with hU3
  set U4 := (R ×ˢ A).filter (fun x => x.2.minFac = sStar) with hU4
  set U5 := (A ×ˢ R).filter (fun x => x.1.minFac = sStar) with hU5
  have hU_nonneg : ∀ x ∈ U1 ∪ U2 ∪ U3 ∪ U4 ∪ U5, 0 ≤ c x.1 * c x.2 := by
    intro x hx
    simp only [hU1, hU2, hU3, hU4, hU5, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product] at hx
    have key : x.1 ∈ S ∧ x.2 ∈ S := by
      rcases hx with ((((⟨⟨h, h'⟩, -⟩ | ⟨h, h'⟩) | ⟨⟨h, h'⟩, -⟩) | ⟨⟨h, h'⟩, -⟩) | ⟨⟨h, h'⟩, -⟩) <;>
        exact ⟨by first | exact hAS h | exact hRS h, by first | exact hAS h' | exact hRS h'⟩
    exact mul_nonneg (hc x.1 key.1) (hc x.2 key.2)
  have hle1 := Finset.sum_le_sum_of_subset_of_nonneg hsub fun x hx _ => hU_nonneg x hx
  have hU2_eq : ∑ x ∈ U2, c x.1 * c x.2 = (∑ n ∈ R, c n) ^ 2 := by
    rw [hU2, sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hU4_le : ∑ x ∈ U4, c x.1 * c x.2 ≤ B * ∑ n ∈ R, c n := by
    have hfilt : U4 = R ×ˢ (A.filter (fun n => n.minFac = sStar)) := by
      ext ⟨n, n'⟩; simp only [hU4, Finset.mem_filter, Finset.mem_product]; tauto
    rw [hfilt, Finset.sum_product, ← Finset.sum_mul_sum, mul_comm]
    exact sum_cross_active_le hS hRS hAS hc hB
  have hU5_le : ∑ x ∈ U5, c x.1 * c x.2 ≤ B * ∑ n ∈ R, c n := by
    have hfilt : U5 = (A.filter (fun n => n.minFac = sStar)) ×ˢ R := by
      ext ⟨n, n'⟩; simp only [hU5, Finset.mem_filter, Finset.mem_product]; tauto
    rw [hfilt, Finset.sum_product, ← Finset.sum_mul_sum]
    exact sum_cross_active_le hS hRS hAS hc hB
  have hu : ∀ {T T' : Finset (ℕ × ℕ)}, (∀ x ∈ T ∩ T', 0 ≤ c x.1 * c x.2) →
      ∑ x ∈ T ∪ T', c x.1 * c x.2 ≤ ∑ x ∈ T, c x.1 * c x.2 + ∑ x ∈ T', c x.1 * c x.2 :=
    fun h => Finset.sum_union_le h
  have hu5 := hu (T := U1 ∪ U2 ∪ U3 ∪ U4) (T' := U5) fun x hx =>
    hU_nonneg x (by simp [(Finset.mem_inter.mp hx).2])
  have hu4 := hu (T := U1 ∪ U2 ∪ U3) (T' := U4) fun x hx =>
    hU_nonneg x (by simp [(Finset.mem_inter.mp hx).2])
  have hu3 := hu (T := U1 ∪ U2) (T' := U3) fun x hx =>
    hU_nonneg x (by simp [(Finset.mem_inter.mp hx).2])
  have hu2 := hu (T := U1) (T' := U2) fun x hx =>
    hU_nonneg x (by simp [(Finset.mem_inter.mp hx).2])
  linarith

private lemma abs_sum_jacobiSym_mul_le_eta {m₀ a₀ N sStar n₁ n₂ : ℕ} {P : Finset ℕ} {η : ℝ}
    (h8 : 8 ∣ m₀) (ha₀ : Odd a₀)
    (hP_mod : ∀ q ∈ P, q ≡ a₀ [MOD m₀])
    (hcop1 : ∀ q ∈ P, n₁.Coprime q) (hcop2 : ∀ q ∈ P, n₂.Coprime q)
    (hn1 : n₁ ∈ Finset.Icc 1 N) (hn2 : n₂ ∈ Finset.Icc 1 N)
    (hne1 : oddExpPart m₀ (n₁ * n₂) ≠ 1) (hneS : oddExpPart m₀ (n₁ * n₂) ≠ sStar)
    (hchar : ∀ s : ℕ, 1 < s → s ≤ N ^ 2 → Odd s → Squarefree s → s.Coprime m₀ → s ≠ sStar →
      |(∑ q ∈ P, (jacobiSym q s : ℝ))| ≤ η * P.card) :
    |(∑ q ∈ P, (jacobiSym (n₁ * n₂) q : ℝ))| ≤ η * P.card := by
  obtain ⟨ε, hε, hrec⟩ := exists_jacobiSym_eq_mul_jacobiSym_oddExpPart (n := n₁ * n₂) h8 ha₀
  have hcongr : ∑ q ∈ P, (jacobiSym (n₁ * n₂) q : ℝ) =
      (ε : ℝ) * ∑ q ∈ P, (jacobiSym q (oddExpPart m₀ (n₁ * n₂)) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    exact_mod_cast hrec q (hP_mod q hq) ((hcop1 q hq).mul_left (hcop2 q hq))
  have hrecP : |(∑ q ∈ P, (jacobiSym (n₁ * n₂) q : ℝ))| =
      |(∑ q ∈ P, (jacobiSym q (oddExpPart m₀ (n₁ * n₂)) : ℝ))| := by
    rw [hcongr, abs_mul]; rcases hε with rfl | rfl <;> simp
  have hodd : Odd (oddExpPart m₀ (n₁ * n₂)) := Nat.odd_oddExpPart _ (dvd_trans (by norm_num) h8)
  have hgt1 : 1 < oddExpPart m₀ (n₁ * n₂) := by have := hodd.pos; omega
  have hleN2 : oddExpPart m₀ (n₁ * n₂) ≤ N ^ 2 := by
    have h1I := Finset.mem_Icc.mp hn1
    have h2I := Finset.mem_Icc.mp hn2
    exact (Nat.oddExpPart_le (by nlinarith)).trans (by rw [sq]; exact Nat.mul_le_mul h1I.2 h2I.2)
  rw [hrecP]
  exact hchar _ hgt1 hleN2 hodd (Nat.squarefree_oddExpPart m₀ _)
    (Nat.coprime_oddExpPart m₀ _) hneS

private lemma sum_jacobiSym_split_le {m₀ a₀ N sStar : ℕ} {P S : Finset ℕ} {c : ℕ → ℝ} {η : ℝ}
    (h8 : 8 ∣ m₀) (ha₀ : Odd a₀)
    (hP_mod : ∀ q ∈ P, q ≡ a₀ [MOD m₀])
    (hP_cop : ∀ q ∈ P, ∀ n ∈ Finset.Icc 1 N, c n ≠ 0 → n.Coprime q)
    (hS : S ⊆ Finset.Icc 1 N) (hc : ∀ n ∈ S, 0 ≤ c n)
    (hη : 0 ≤ η)
    (hchar : ∀ s : ℕ, 1 < s → s ≤ N ^ 2 → Odd s → Squarefree s → s.Coprime m₀ → s ≠ sStar →
      |(∑ q ∈ P, (jacobiSym q s : ℝ))| ≤ η * P.card) :
    ∑ x ∈ S ×ˢ S, c x.1 * c x.2 * |(∑ q ∈ P, (jacobiSym (x.1 * x.2) q : ℝ))| ≤
      (P.card : ℝ) * (∑ x ∈ (S ×ˢ S).filter (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨
        oddExpPart m₀ (x.1 * x.2) = sStar), c x.1 * c x.2) +
      (η * P.card) * (∑ x ∈ S ×ˢ S, c x.1 * c x.2) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (S ×ˢ S)
    (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨ oddExpPart m₀ (x.1 * x.2) = sStar)]
  refine add_le_add ?_ ?_
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hxS := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    have habs : |(∑ q ∈ P, (jacobiSym (x.1 * x.2) q : ℝ))| ≤ P.card := by
      calc |(∑ q ∈ P, (jacobiSym (x.1 * x.2) q : ℝ))|
          ≤ ∑ q ∈ P, |(jacobiSym (x.1 * x.2) q : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _q ∈ P, (1 : ℝ) := Finset.sum_le_sum fun q _ => by
            rcases jacobiSym.trichotomy (x.1 * x.2) q with h | h | h <;> simp [h]
        _ = P.card := by simp
    rw [mul_comm (P.card : ℝ)]
    exact mul_le_mul_of_nonneg_left habs (mul_nonneg (hc x.1 hxS.1) (hc x.2 hxS.2))
  · calc _ ≤ ∑ x ∈ (S ×ˢ S).filter (fun x => ¬ (oddExpPart m₀ (x.1 * x.2) = 1 ∨
            oddExpPart m₀ (x.1 * x.2) = sStar)), c x.1 * c x.2 * (η * P.card) := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨hxP, hnot⟩ := Finset.mem_filter.mp hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hxP
          by_cases hc0 : c x.1 = 0 ∨ c x.2 = 0
          · rcases hc0 with h | h <;> simp [h]
          push Not at hc0
          exact mul_le_mul_of_nonneg_left
            (abs_sum_jacobiSym_mul_le_eta h8 ha₀ hP_mod
              (fun q hq => hP_cop q hq x.1 (hS hx1) hc0.1)
              (fun q hq => hP_cop q hq x.2 (hS hx2) hc0.2)
              (hS hx1) (hS hx2)
              (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h)) hchar)
            (mul_nonneg (hc x.1 hx1) (hc x.2 hx2))
      _ ≤ ∑ x ∈ S ×ˢ S, c x.1 * c x.2 * (η * P.card) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x hx _ => by
            have hxP := Finset.mem_product.mp hx
            exact mul_nonneg (mul_nonneg (hc x.1 hxP.1) (hc x.2 hxP.2))
              (mul_nonneg hη (Nat.cast_nonneg _))
      _ = (η * P.card) * ∑ x ∈ S ×ˢ S, c x.1 * c x.2 := by rw [← Finset.sum_mul, mul_comm]

/-- The prime powers in `[1, N]` with odd-exponent part `1` away from `m₀` are those whose base
divides `m₀` or whose exponent is even. -/
private lemma filter_oddExpPart_eq_one (m₀ N : ℕ) :
    ((Finset.Icc 1 N).filter IsPrimePow).filter (fun n => oddExpPart m₀ n = 1) =
      (Finset.Icc 1 N).filter
        (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)) := by
  rw [Finset.filter_filter]
  exact Finset.filter_congr fun n _ =>
    and_congr_right fun hn => (Nat.oddExpPart_eq_one_iff_of_isPrimePow hn).trans or_comm

/-- **Algebraic mean-square inequality for quadratic twists of prime-power sums.**
Let `8 ∣ m₀`, let `a₀` be odd, and let `P` be a finite set of natural numbers congruent to `a₀`
modulo `m₀` that are coprime to every `n ≤ N` in the support of `c`. Suppose `c : ℕ → ℝ` is
nonnegative and supported on prime powers in `[1, N]`, `‖κ n‖ ≤ 1`, `η ≥ 0`, and
`|(∑ q ∈ P, J(q | s) : ℝ)| ≤ η * P.card` for every odd squarefree `1 < s ≤ N ^ 2` coprime to `m₀`
other than one exceptional modulus `sStar`. Then the mean square of the twisted sums
`∑ n ∈ Finset.Icc 1 N, c n * κ n * J(n | q)` over `q ∈ P` is bounded by
`P.card * (∑ p, sP(p) ^ 2 + RR ^ 2 + 2 * B ^ 2 + 2 * B * RR + η * (∑ n, c n) ^ 2)`, where
`sP(p)` is the total weight on powers of `p`, `B` bounds every `sP(p)`, and `RR` is the total
weight on prime powers with even exponent or base dividing `m₀`. -/
theorem sum_norm_sq_jacobiSym_le {m₀ a₀ N sStar : ℕ} {P : Finset ℕ}
    {c : ℕ → ℝ} {κ : ℕ → ℂ} {B η : ℝ}
    (h8 : 8 ∣ m₀) (ha₀ : Odd a₀)
    (hP_mod : ∀ q ∈ P, q ≡ a₀ [MOD m₀])
    (hP_cop : ∀ q ∈ P, ∀ n ∈ Finset.Icc 1 N, c n ≠ 0 → n.Coprime q)
    (hc_nonneg : ∀ n ∈ Finset.Icc 1 N, 0 ≤ c n)
    (hc_supp : ∀ n ∈ Finset.Icc 1 N, c n ≠ 0 → IsPrimePow n)
    (hκ : ∀ n ∈ Finset.Icc 1 N, ‖κ n‖ ≤ 1)
    (hη : 0 ≤ η)
    (hchar : ∀ s : ℕ, 1 < s → s ≤ N ^ 2 → Odd s → Squarefree s → s.Coprime m₀ → s ≠ sStar →
      |(∑ q ∈ P, (jacobiSym q s : ℝ))| ≤ η * P.card)
    (hB : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n) ≤ B) :
    ∑ q ∈ P, ‖∑ n ∈ Finset.Icc 1 N, (c n : ℂ) * κ n * (jacobiSym n q : ℂ)‖ ^ 2 ≤
      P.card *
        ((∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n) ^ 2) +
          (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n)
            ^ 2 +
          2 * B ^ 2 +
          2 * B * (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n) +
          η * (∑ n ∈ Finset.Icc 1 N, c n) ^ 2) := by
  classical
  set S := (Finset.Icc 1 N).filter IsPrimePow with hS
  set R := S.filter (fun n => oddExpPart m₀ n = 1) with hR
  have hSI : S ⊆ Finset.Icc 1 N := by rw [hS]; exact Finset.filter_subset _ _
  have hcS : ∀ n ∈ S, 0 ≤ c n := fun n hn => hc_nonneg n (hSI hn)
  have hsum_eq : ∀ q : ℕ,
      ∑ n ∈ Finset.Icc 1 N, (c n : ℂ) * κ n * (jacobiSym n q : ℂ) =
      ∑ n ∈ S, (c n : ℂ) * κ n * (jacobiSym n q : ℂ) := fun q => by
    rw [hS]
    exact (Finset.sum_filter_of_ne fun n hn hne => hc_supp n hn fun h0 => hne (by simp [h0])).symm
  simp_rw [hsum_eq]
  have hexp := sum_norm_sq_jacobiSym_le_sum_sum_mul_abs (P := P) (S := S) hcS
    (fun n hn => hκ n (hSI hn))
  rw [← Finset.sum_product'] at hexp
  have hsplit := sum_jacobiSym_split_le (sStar := sStar) h8 ha₀ hP_mod hP_cop hSI hcS hη hchar
  have htot : ∑ x ∈ S ×ˢ S, c x.1 * c x.2 = (∑ n ∈ Finset.Icc 1 N, c n) ^ 2 := by
    rw [Finset.sum_product, ← Finset.sum_mul_sum, ← sq, hS, Finset.sum_filter_of_ne hc_supp]
  have hsP_eq : ∀ p, ∑ n ∈ S.filter (fun n => n.minFac = p), c n =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n := fun p => by
    rw [hS, Finset.filter_filter]
  have hR_eq : R = (Finset.Icc 1 N).filter
      (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)) := by
    rw [hR, hS, filter_oddExpPart_eq_one]
  have hB' : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ≤ B := fun p hp => by
    rw [hsP_eq p]; exact hB p hp
  have hspec := sum_special_pairs_le (sStar := sStar) hS hR hcS hB'
  rw [hR_eq] at hspec
  simp only [hsP_eq] at hspec
  have h1 := hexp.trans hsplit
  rw [htot] at h1
  have h2 := mul_le_mul_of_nonneg_left hspec (Nat.cast_nonneg (α := ℝ) P.card)
  linarith

end TauCeti
