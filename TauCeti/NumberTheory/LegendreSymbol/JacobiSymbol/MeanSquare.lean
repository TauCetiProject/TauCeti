/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Nat.Factorization.PrimePow
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.ResidueClass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-!
# Algebraic mean-square inequality for quadratic twists of prime-power sums

Let `8 ∣ m₀`, let `a₀` be odd, and let `P` be a finite set of natural numbers congruent to `a₀`
modulo `m₀`. For nonnegative weights `c` supported on prime powers up to `N`, coefficients
`κ : ℕ → ℂ` with `‖κ n‖ ≤ 1`, and a uniform bound `|(∑ q ∈ P, J(q | s) : ℝ)| ≤ η * P.card` on
every odd squarefree `1 < s ≤ N ^ 2` coprime to `m₀` other than one exceptional modulus `sStar`,
expanding the square and applying reciprocity on the residue class
(`exists_jacobiSym_eq_mul_jacobiSym_prod`) bounds the mean square
`∑ q ∈ P, ‖∑ n ∈ Finset.Icc 1 N, c n * κ n * J(n | q)‖ ^ 2` by
`P.card * (∑ p, sP(p) ^ 2 + RR ^ 2 + 2 * B ^ 2 + 2 * B * RR + η * (∑ n, c n) ^ 2)`, where
`sP(p)` is the total weight on powers of `p`, `B` bounds every `sP(p)`, and `RR` is the total
weight on prime powers with even exponent or base dividing `m₀`.

## Main statements

* `TauCeti.sum_norm_sq_jacobiSym_le`: the algebraic mean-square inequality for quadratic twists of
  prime-power sums over a residue class modulo a multiple of `8`.

## References

* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>.
-/

public section

namespace TauCeti

private def oddExpPart (m₀ n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with ¬ p ∣ m₀ ∧ Odd (n.factorization p), p

private lemma minFac_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : (p ^ k).minFac = p := by
  have hne1 : p ^ k ≠ 1 := fun h => hp.ne_one ((Nat.pow_eq_one.mp h).resolve_right hk)
  exact (Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hne1) hp).mp
    ((Nat.minFac_prime hne1).dvd_of_dvd_pow (Nat.minFac_dvd (p ^ k)))

private lemma oddExpPart_le {m₀ n : ℕ} (hn : n ≠ 0) : oddExpPart m₀ n ≤ n := by
  obtain ⟨t, A, h, -⟩ := Nat.exists_eq_prod_mul_sq_mul m₀ n
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨t ^ 2 * A, by rw [← mul_assoc]; exact h⟩

private lemma odd_oddExpPart {m₀ n : ℕ} (h2 : 2 ∣ m₀) : Odd (oddExpPart m₀ n) := by
  unfold oddExpPart
  refine Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rcases (Nat.prime_of_mem_primeFactors hp.1).eq_two_or_odd' with rfl | hodd
  · exact (hp.2.1 h2).elim
  · exact hodd

private lemma squarefree_oddExpPart (m₀ n : ℕ) : Squarefree (oddExpPart m₀ n) := by
  unfold oddExpPart
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hdvd
  have hmem : ∀ q ∈ n.primeFactors.filter (fun q => ¬ q ∣ m₀ ∧ Odd (n.factorization q)),
      q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hp_mem : p ∈ n.primeFactors.filter (fun q => ¬ q ∣ m₀ ∧ Odd (n.factorization q)) := by
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp (dvd_of_mul_right_dvd hdvd)
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hmem q hq)).mp hpq]
  rw [← Finset.mul_prod_erase _ _ hp_mem] at hdvd
  have hp_dvd : p ∣ ∏ q ∈ (n.primeFactors.filter _).erase p, q :=
    (mul_dvd_mul_iff_left hp.ne_zero).mp hdvd
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hp_dvd
  have hne : q ≠ p := (Finset.mem_erase.mp hq).1
  have hqp := (Nat.prime_dvd_prime_iff_eq hp (hmem q (Finset.mem_erase.mp hq).2)).mp hpq
  exact hne hqp.symm

private lemma coprime_oddExpPart (m₀ n : ℕ) : (oddExpPart m₀ n).Coprime m₀ := by
  unfold oddExpPart
  refine Nat.coprime_prod_left_iff.mpr fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact ((Nat.prime_of_mem_primeFactors hp.1).coprime_iff_not_dvd).mpr hp.2.1

private lemma oddExpPart_primePow {m₀ n : ℕ} (hn : IsPrimePow n) :
    oddExpPart m₀ n =
      if ¬ n.minFac ∣ m₀ ∧ Odd (n.factorization n.minFac) then n.minFac else 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  have hpf : (p ^ k).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p hk.ne', hp.nat_prime.primeFactors]
  have hmin : (p ^ k).minFac = p := minFac_prime_pow hp.nat_prime hk.ne'
  unfold oddExpPart
  rw [hpf, hmin, Finset.filter_singleton]
  split_ifs <;> simp

private lemma oddExpPart_mul_of_primePow_eq {m₀ p k l : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hl : 0 < l) :
    oddExpPart m₀ (p ^ k * p ^ l) =
      if oddExpPart m₀ (p ^ k) = 1 then oddExpPart m₀ (p ^ l)
      else if oddExpPart m₀ (p ^ l) = 1 then oddExpPart m₀ (p ^ k) else 1 := by
  have hmul : p ^ k * p ^ l = p ^ (k + l) := (pow_add p k l).symm
  have hkl : 0 < k + l := Nat.add_pos_left hk l
  have hon := oddExpPart_primePow (m₀ := m₀) ⟨p, k, hp.prime, hk, rfl⟩
  have hon' := oddExpPart_primePow (m₀ := m₀) ⟨p, l, hp.prime, hl, rfl⟩
  have hom := oddExpPart_primePow (m₀ := m₀) ⟨p, k + l, hp.prime, hkl, rfl⟩
  rw [minFac_prime_pow hp hk.ne', hp.factorization_pow, Finsupp.single_eq_same] at hon
  rw [minFac_prime_pow hp hl.ne', hp.factorization_pow, Finsupp.single_eq_same] at hon'
  rw [minFac_prime_pow hp hkl.ne', hp.factorization_pow, Finsupp.single_eq_same] at hom
  rw [hmul, hom, hon, hon']
  by_cases hdiv : p ∣ m₀
  · simp [hdiv]
  · rcases Nat.even_or_odd k with hk_ev | hk_od <;> rcases Nat.even_or_odd l with hl_ev | hl_od
    · simp [hdiv, Nat.not_odd_iff_even.mpr hk_ev, Nat.not_odd_iff_even.mpr hl_ev,
        Nat.not_odd_iff_even.mpr (hk_ev.add hl_ev)]
    · simp [hdiv, Nat.not_odd_iff_even.mpr hk_ev, hl_od, hk_ev.add_odd hl_od]
    · simp [hdiv, hk_od, Nat.not_odd_iff_even.mpr hl_ev, hk_od.add_even hl_ev, hp.ne_one]
    · simp [hdiv, hk_od, hl_od, Nat.not_odd_iff_even.mpr (hk_od.add_odd hl_od), hp.ne_one]

private lemma oddExpPart_mul_of_primePow {m₀ n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n') :
    oddExpPart m₀ (n * n') =
      if oddExpPart m₀ n = 1 then oddExpPart m₀ n'
      else if oddExpPart m₀ n' = 1 then oddExpPart m₀ n
      else if n.minFac = n'.minFac then 1
      else n.minFac * n'.minFac := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  obtain ⟨q, l, hq, hl, rfl⟩ := hn'
  have hp' := hp.nat_prime
  have hq' := hq.nat_prime
  have hmin_p : (p ^ k).minFac = p := minFac_prime_pow hp' hk.ne'
  have hmin_q : (q ^ l).minFac = q := minFac_prime_pow hq' hl.ne'
  by_cases hpq : p = q
  · subst hpq
    rw [hmin_p, hmin_q, ite_eq_left rfl]
    exact oddExpPart_mul_of_primePow_eq hp' hk hl
  · have hon := oddExpPart_primePow (m₀ := m₀) ⟨p, k, hp, hk, rfl⟩
    have hon' := oddExpPart_primePow (m₀ := m₀) ⟨q, l, hq, hl, rfl⟩
    rw [hmin_p, hp'.factorization_pow, Finsupp.single_eq_same] at hon
    rw [hmin_q, hq'.factorization_pow, Finsupp.single_eq_same] at hon'
    have hpf : (p ^ k * q ^ l).primeFactors = {p, q} := by
      rw [Nat.primeFactors_mul (pow_ne_zero k hp'.ne_zero) (pow_ne_zero l hq'.ne_zero),
        Nat.primeFactors_pow p hk.ne', Nat.primeFactors_pow q hl.ne',
        hp'.primeFactors, hq'.primeFactors]
      rfl
    have hfac_p : (p ^ k * q ^ l).factorization p = k := by
      rw [Nat.factorization_mul (pow_ne_zero k hp'.ne_zero) (pow_ne_zero l hq'.ne_zero),
        Finsupp.add_apply, hp'.factorization_pow, hq'.factorization_pow,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hpq, add_zero]
    have hfac_q : (p ^ k * q ^ l).factorization q = l := by
      rw [Nat.factorization_mul (pow_ne_zero k hp'.ne_zero) (pow_ne_zero l hq'.ne_zero),
        Finsupp.add_apply, hp'.factorization_pow, hq'.factorization_pow,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hpq), zero_add]
    rw [hon, hon', hmin_p, hmin_q]
    unfold oddExpPart
    rw [hpf, Finset.filter_insert, Finset.filter_singleton, hfac_p, hfac_q]
    by_cases h1 : ¬ p ∣ m₀ ∧ Odd k <;> by_cases h2 : ¬ q ∣ m₀ ∧ Odd l <;>
      simp [h1, h2, hpq, hp'.ne_one, hq'.ne_one]

private lemma card_prime_mul_eq_le_two (S : Finset ℕ) (s : ℕ) :
    ((S ×ˢ S).filter fun x => x.1.Prime ∧ x.2.Prime ∧ x.1 ≠ x.2 ∧ x.1 * x.2 = s).card ≤ 2 := by
  classical
  set T := (S ×ˢ S).filter fun x => x.1.Prime ∧ x.2.Prime ∧ x.1 ≠ x.2 ∧ x.1 * x.2 = s
  rcases T.eq_empty_or_nonempty with hT | ⟨⟨p₁, p₂⟩, h12⟩
  · simp [hT]
  obtain ⟨-, hp₁, hp₂, -, hmul⟩ := Finset.mem_filter.mp h12
  dsimp only at hp₁ hp₂ hmul
  have hsub : T ⊆ {(p₁, p₂), (p₂, p₁)} := by
    intro ⟨p, q⟩ hpq
    obtain ⟨-, hp, hq, -, hmul'⟩ := Finset.mem_filter.mp hpq
    dsimp only at hp hq hmul'
    have hdvd : p ∣ p₁ * p₂ := ⟨q, hmul.trans hmul'.symm⟩
    rcases hp.dvd_mul.mp hdvd with h | h
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hp₁).mp h
      have hq2 : q = p₂ := mul_left_cancel₀ hp.ne_zero (hmul'.trans hmul.symm)
      simp [hq2]
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hp₂).mp h
      have hq1 : q = p₁ :=
        mul_left_cancel₀ hp.ne_zero (hmul'.trans (hmul.symm.trans (mul_comm _ _)))
      simp [hq1]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

private lemma sum_norm_sq_jacobiSym_le_expand {P S : Finset ℕ} {c : ℕ → ℝ} {κ : ℕ → ℂ}
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

private lemma special_pairs_subset (m₀ N sStar : ℕ) :
    let S := (Finset.Icc 1 N).filter IsPrimePow
    let R := S.filter (fun n => oddExpPart m₀ n = 1)
    let A := S.filter (fun n => oddExpPart m₀ n ≠ 1)
    (S ×ˢ S).filter (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨
        oddExpPart m₀ (x.1 * x.2) = sStar) ⊆
      (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac) ∪
      (R ×ˢ R) ∪
      ((A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧ x.1.minFac * x.2.minFac = sStar)) ∪
      ((R ×ˢ A).filter (fun x => x.2.minFac = sStar)) ∪
      ((A ×ˢ R).filter (fun x => x.1.minFac = sStar)) := by
  classical
  intro S R A ⟨n, n'⟩ hx
  obtain ⟨hmem, hor⟩ := Finset.mem_filter.mp hx
  obtain ⟨hnS, hn'S⟩ := Finset.mem_product.mp hmem
  have hpp := (Finset.mem_filter.mp hnS).2
  have hpp' := (Finset.mem_filter.mp hn'S).2
  have hmul := oddExpPart_mul_of_primePow (m₀ := m₀) hpp hpp'
  have hact : ∀ {k : ℕ}, IsPrimePow k → oddExpPart m₀ k ≠ 1 → oddExpPart m₀ k = k.minFac := by
    intro k hk hne
    rw [oddExpPart_primePow hk] at hne ⊢
    split_ifs at hne ⊢ with h
    · rfl
    · exact (hne rfl).elim
  by_cases h1 : oddExpPart m₀ n = 1 <;> by_cases h2 : oddExpPart m₀ n' = 1
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hnS, h1⟩, Finset.mem_filter.mpr ⟨hn'S, h2⟩⟩))))
  · have hv := hact hpp' h2
    rw [ite_eq_left h1, hv] at hmul
    have hss : n'.minFac = sStar := hmul.symm.trans (hor.resolve_left (hmul ▸ hv ▸ h2))
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hnS, h1⟩, Finset.mem_filter.mpr ⟨hn'S, h2⟩⟩,
        hss⟩))
  · have hv := hact hpp h1
    rw [ite_eq_right h1, ite_eq_left h2, hv] at hmul
    have hss : n.minFac = sStar := hmul.symm.trans (hor.resolve_left (hmul ▸ hv ▸ h1))
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hnS, h1⟩, Finset.mem_filter.mpr ⟨hn'S, h2⟩⟩,
        hss⟩)
  · rw [ite_eq_right h1, ite_eq_right h2] at hmul
    by_cases heq : n.minFac = n'.minFac
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨hnS, h1⟩, Finset.mem_filter.mpr ⟨hn'S, h2⟩⟩, heq⟩))))
    · rw [ite_eq_right heq] at hmul
      have hne1 : n.minFac * n'.minFac ≠ 1 := by
        have hp1 := (Nat.minFac_prime hpp.ne_one).one_lt
        have hp2 := (Nat.minFac_prime hpp'.ne_one).one_lt
        nlinarith
      have hss : n.minFac * n'.minFac = sStar := hmul.symm.trans (hor.resolve_left (hmul ▸ hne1))
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨hnS, h1⟩, Finset.mem_filter.mpr ⟨hn'S, h2⟩⟩,
            ⟨heq, hss⟩⟩)))

private lemma minFac_mem_primes {N n : ℕ} (hn : n ∈ (Finset.Icc 1 N).filter IsPrimePow) :
    n.minFac ∈ (Finset.Icc 1 N).filter Nat.Prime := by
  have ⟨hnI, hpp⟩ := Finset.mem_filter.mp hn
  have hp := Nat.minFac_prime hpp.ne_one
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hp.one_le, (Nat.minFac_le (Finset.mem_Icc.mp hnI).1).trans (Finset.mem_Icc.mp hnI).2⟩, hp⟩

private lemma sum_diag_active_le {m₀ N : ℕ} {c : ℕ → ℝ}
    (hc : ∀ n ∈ Finset.Icc 1 N, 0 ≤ c n) :
    let S := (Finset.Icc 1 N).filter IsPrimePow
    let A := S.filter (fun n => oddExpPart m₀ n ≠ 1)
    ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac), c x.1 * c x.2 ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ^ 2 := by
  classical
  intro S A
  set Pset := (Finset.Icc 1 N).filter Nat.Prime
  have hcS : ∀ n ∈ S, 0 ≤ c n := fun n hn => hc n (Finset.mem_filter.mp hn).1
  have hfib : ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac), c x.1 * c x.2 =
      ∑ p ∈ Pset, (∑ n ∈ A.filter (fun n => n.minFac = p), c n) ^ 2 := by
    simp_rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ⟨n, n'⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨hn, hn'⟩, heq⟩ =>
          ⟨n.minFac, minFac_mem_primes (Finset.mem_filter.mp hn).1, ⟨hn, rfl⟩, ⟨hn', heq.symm⟩⟩,
        fun ⟨_, _, ⟨hn, hp1⟩, ⟨hn', hp2⟩⟩ => ⟨⟨hn, hn'⟩, hp1.trans hp2.symm⟩⟩
    · intro p _ q _ hpq
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro ⟨n, _⟩ h1 h2
      exact hpq ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2)
  rw [hfib]
  refine Finset.sum_le_sum fun p _ => pow_le_pow_left₀
    (Finset.sum_nonneg fun n hn => hcS n (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      fun n hn _ => hcS n (Finset.mem_filter.mp hn).1) 2

private lemma sum_offDiag_eq_sum_pairs {m₀ N sStar : ℕ} {c : ℕ → ℝ} :
    let S := (Finset.Icc 1 N).filter IsPrimePow
    let A := S.filter (fun n => oddExpPart m₀ n ≠ 1)
    let Pset := (Finset.Icc 1 N).filter Nat.Prime
    let Q := (Pset ×ˢ Pset).filter fun q =>
      q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧ q.1 * q.2 = sStar
    ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧
        x.1.minFac * x.2.minFac = sStar), c x.1 * c x.2 =
      ∑ q ∈ Q, (∑ n ∈ A.filter (fun n => n.minFac = q.1), c n) *
        (∑ n' ∈ A.filter (fun n' => n'.minFac = q.2), c n') := by
  classical
  intro S A Pset Q
  simp_rw [Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ⟨n, n'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Q]
    constructor
    · rintro ⟨⟨hn, hn'⟩, hne, hmul⟩
      have h1 := minFac_mem_primes (Finset.mem_filter.mp hn).1
      have h2 := minFac_mem_primes (Finset.mem_filter.mp hn').1
      exact ⟨(n.minFac, n'.minFac), ⟨⟨h1, h2⟩, (Finset.mem_filter.mp h1).2,
        (Finset.mem_filter.mp h2).2, hne, hmul⟩, ⟨hn, rfl⟩, ⟨hn', rfl⟩⟩
    · rintro ⟨⟨p, q⟩, ⟨-, -, -, hne, hmul⟩, ⟨hn, rfl⟩, ⟨hn', rfl⟩⟩
      exact ⟨⟨hn, hn'⟩, hne, hmul⟩
  · intro q₁ _ q₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro ⟨n, n'⟩ h1 h2
    exact hne (Prod.ext
      ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2)
      ((Finset.mem_filter.mp (Finset.mem_product.mp h1).2).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp h2).2).2))

private lemma sum_offDiag_active_le {m₀ N sStar : ℕ} {c : ℕ → ℝ} {B : ℝ}
    (hc : ∀ n ∈ Finset.Icc 1 N, 0 ≤ c n)
    (hB : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ ((Finset.Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p), c n) ≤ B) :
    let S := (Finset.Icc 1 N).filter IsPrimePow
    let A := S.filter (fun n => oddExpPart m₀ n ≠ 1)
    ∑ x ∈ (A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧ x.1.minFac * x.2.minFac = sStar),
      c x.1 * c x.2 ≤ 2 * B ^ 2 := by
  classical
  intro S A
  set Pset := (Finset.Icc 1 N).filter Nat.Prime
  set Q := (Pset ×ˢ Pset).filter fun q => q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧ q.1 * q.2 = sStar
  have hcS : ∀ n ∈ S, 0 ≤ c n := fun n hn => hc n (Finset.mem_filter.mp hn).1
  have hA_le_B : ∀ p ∈ Pset, (∑ n ∈ A.filter (fun n => n.minFac = p), c n) ≤ B := fun p hp =>
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      fun n hn _ => hcS n (Finset.mem_filter.mp hn).1).trans (hB p hp)
  rw [sum_offDiag_eq_sum_pairs (m₀ := m₀) (N := N) (sStar := sStar) (c := c)]
  calc ∑ q ∈ Q, (∑ n ∈ A.filter (fun n => n.minFac = q.1), c n) *
        (∑ n' ∈ A.filter (fun n' => n'.minFac = q.2), c n')
      ≤ ∑ _q ∈ Q, B ^ 2 := Finset.sum_le_sum fun q hq => by
        have hqP := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
        have h01 : 0 ≤ ∑ n ∈ A.filter (fun n => n.minFac = q.1), c n :=
          Finset.sum_nonneg fun n hn => hcS n (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
        have h02 : 0 ≤ ∑ n' ∈ A.filter (fun n' => n'.minFac = q.2), c n' :=
          Finset.sum_nonneg fun n hn => hcS n (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
        rw [sq]
        exact mul_le_mul (hA_le_B q.1 hqP.1) (hA_le_B q.2 hqP.2) h02
          (h01.trans (hA_le_B q.1 hqP.1))
    _ = (Q.card : ℝ) * B ^ 2 := by simp
    _ ≤ 2 * B ^ 2 := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_prime_mul_eq_le_two Pset sStar) (sq_nonneg B)

private lemma sum_cross_active_le {m₀ N sStar : ℕ} {c : ℕ → ℝ} {B : ℝ}
    (hc : ∀ n ∈ Finset.Icc 1 N, 0 ≤ c n)
    (hB : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ ((Finset.Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p), c n) ≤ B) :
    let S := (Finset.Icc 1 N).filter IsPrimePow
    let R := S.filter (fun n => oddExpPart m₀ n = 1)
    let A := S.filter (fun n => oddExpPart m₀ n ≠ 1)
    (∑ n ∈ A.filter (fun n => n.minFac = sStar), c n) * (∑ n ∈ R, c n) ≤
      B * (∑ n ∈ R, c n) := by
  classical
  intro S R A
  set Pset := (Finset.Icc 1 N).filter Nat.Prime
  have hcS : ∀ n ∈ S, 0 ≤ c n := fun n hn => hc n (Finset.mem_filter.mp hn).1
  have hRR_nonneg : 0 ≤ ∑ n ∈ R, c n := Finset.sum_nonneg fun n hn =>
    hcS n (Finset.mem_filter.mp hn).1
  by_cases hsP : sStar ∈ Pset
  · refine mul_le_mul_of_nonneg_right ?_ hRR_nonneg
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      fun n hn _ => hcS n (Finset.mem_filter.mp hn).1).trans (hB sStar hsP)
  · have hempty : A.filter (fun n => n.minFac = sStar) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn heq
      exact hsP (heq ▸ minFac_mem_primes (Finset.mem_filter.mp hn).1)
    rw [hempty, Finset.sum_empty, zero_mul]
    rcases R.eq_empty_or_nonempty with hR | ⟨n₀, hn₀⟩
    · simp [hR]
    · have hp0 := minFac_mem_primes (Finset.mem_filter.mp hn₀).1
      have hB0 : 0 ≤ B := (Finset.sum_nonneg fun n hn =>
        hcS n (Finset.mem_filter.mp hn).1).trans (hB n₀.minFac hp0)
      exact mul_nonneg hB0 hRR_nonneg

private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {f : α → ℝ} {U V : Finset α}
    (hUV : ∀ x ∈ U ∪ V, 0 ≤ f x) :
    ∑ x ∈ U ∪ V, f x ≤ ∑ x ∈ U, f x + ∑ x ∈ V, f x := by
  have hint : 0 ≤ ∑ x ∈ U ∩ V, f x :=
    Finset.sum_nonneg fun x hx => hUV x (Finset.mem_union_left V (Finset.mem_inter.mp hx).1)
  linarith [Finset.sum_union_inter (s₁ := U) (s₂ := V) (f := f)]

private lemma sum_special_pairs_le {m₀ N sStar : ℕ} {c : ℕ → ℝ} {B : ℝ}
    (hc : ∀ n ∈ Finset.Icc 1 N, 0 ≤ c n)
    (hB : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ ((Finset.Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p), c n) ≤ B) :
    let S := (Finset.Icc 1 N).filter IsPrimePow
    let RR := ∑ n ∈ S.filter (fun n => oddExpPart m₀ n = 1), c n
    ∑ x ∈ (S ×ˢ S).filter (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨
        oddExpPart m₀ (x.1 * x.2) = sStar), c x.1 * c x.2 ≤
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ^ 2) +
        RR ^ 2 + 2 * B ^ 2 + 2 * B * RR := by
  classical
  intro S RR
  set R := S.filter (fun n => oddExpPart m₀ n = 1)
  set A := S.filter (fun n => oddExpPart m₀ n ≠ 1)
  have hcS : ∀ n ∈ S, 0 ≤ c n := fun n hn => hc n (Finset.mem_filter.mp hn).1
  have hnn : ∀ (T : Finset (ℕ × ℕ)), T ⊆ S ×ˢ S → ∀ x ∈ T, 0 ≤ c x.1 * c x.2 := fun T hT x hx =>
    mul_nonneg (hcS x.1 (Finset.mem_product.mp (hT hx)).1)
      (hcS x.2 (Finset.mem_product.mp (hT hx)).2)
  set U1 := (A ×ˢ A).filter (fun x => x.1.minFac = x.2.minFac)
  set U2 := R ×ˢ R
  set U3 := (A ×ˢ A).filter (fun x => x.1.minFac ≠ x.2.minFac ∧ x.1.minFac * x.2.minFac = sStar)
  set U4 := (R ×ˢ A).filter (fun x => x.2.minFac = sStar)
  set U5 := (A ×ˢ R).filter (fun x => x.1.minFac = sStar)
  have hU_sub : U1 ∪ U2 ∪ U3 ∪ U4 ∪ U5 ⊆ S ×ˢ S :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.union_subset
      ((Finset.filter_subset _ _).trans
        (Finset.product_subset_product (Finset.filter_subset _ _) (Finset.filter_subset _ _)))
      (Finset.product_subset_product (Finset.filter_subset _ _) (Finset.filter_subset _ _)))
      ((Finset.filter_subset _ _).trans
        (Finset.product_subset_product (Finset.filter_subset _ _) (Finset.filter_subset _ _))))
      ((Finset.filter_subset _ _).trans
        (Finset.product_subset_product (Finset.filter_subset _ _) (Finset.filter_subset _ _))))
      ((Finset.filter_subset _ _).trans
        (Finset.product_subset_product (Finset.filter_subset _ _) (Finset.filter_subset _ _)))
  have hle1 := Finset.sum_le_sum_of_subset_of_nonneg (special_pairs_subset m₀ N sStar)
    fun x hx _ => hnn _ hU_sub x hx
  have hU2 : ∑ x ∈ U2, c x.1 * c x.2 = RR ^ 2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hU4 : ∑ x ∈ U4, c x.1 * c x.2 ≤ B * RR := by
    have hfilt : U4 = R ×ˢ (A.filter (fun n => n.minFac = sStar)) := by
      ext ⟨n, n'⟩; simp only [U4, Finset.mem_filter, Finset.mem_product]; tauto
    rw [hfilt, Finset.sum_product, ← Finset.sum_mul_sum, mul_comm]
    exact sum_cross_active_le (m₀ := m₀) (sStar := sStar) hc hB
  have hU5 : ∑ x ∈ U5, c x.1 * c x.2 ≤ B * RR := by
    have hfilt : U5 = (A.filter (fun n => n.minFac = sStar)) ×ˢ R := by
      ext ⟨n, n'⟩; simp only [U5, Finset.mem_filter, Finset.mem_product]; tauto
    rw [hfilt, Finset.sum_product, ← Finset.sum_mul_sum]
    exact sum_cross_active_le (m₀ := m₀) (sStar := sStar) hc hB
  have h1 := sum_diag_active_le (m₀ := m₀) hc
  have h3 := sum_offDiag_active_le (m₀ := m₀) (sStar := sStar) hc hB
  have hu5 := sum_union_le_of_nonneg (hnn _ hU_sub)
  have hu4 := sum_union_le_of_nonneg (hnn _ (Finset.subset_union_left.trans hU_sub))
  have hu3 := sum_union_le_of_nonneg
    (hnn _ (Finset.subset_union_left.trans (Finset.subset_union_left.trans hU_sub)))
  have hu2 := sum_union_le_of_nonneg (hnn _ (Finset.subset_union_left.trans
    (Finset.subset_union_left.trans (Finset.subset_union_left.trans hU_sub))))
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
  obtain ⟨ε, hε, hrec⟩ := exists_jacobiSym_eq_mul_jacobiSym_prod (n := n₁ * n₂) h8 ha₀
  have hcongr : ∑ q ∈ P, (jacobiSym (n₁ * n₂) q : ℝ) =
      (ε : ℝ) * ∑ q ∈ P, (jacobiSym q (oddExpPart m₀ (n₁ * n₂)) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    exact_mod_cast hrec q (hP_mod q hq) ((hcop1 q hq).mul_left (hcop2 q hq))
  have hrecP : |(∑ q ∈ P, (jacobiSym (n₁ * n₂) q : ℝ))| =
      |(∑ q ∈ P, (jacobiSym q (oddExpPart m₀ (n₁ * n₂)) : ℝ))| := by
    rw [hcongr, abs_mul]; rcases hε with rfl | rfl <;> simp
  have hodd : Odd (oddExpPart m₀ (n₁ * n₂)) := odd_oddExpPart (dvd_trans (by norm_num) h8)
  have hgt1 : 1 < oddExpPart m₀ (n₁ * n₂) := by have := hodd.pos; omega
  have hleN2 : oddExpPart m₀ (n₁ * n₂) ≤ N ^ 2 := by
    have h1I := Finset.mem_Icc.mp hn1
    have h2I := Finset.mem_Icc.mp hn2
    exact (oddExpPart_le (by nlinarith)).trans (by rw [sq]; exact Nat.mul_le_mul h1I.2 h2I.2)
  rw [hrecP]
  exact hchar _ hgt1 hleN2 hodd (squarefree_oddExpPart m₀ _) (coprime_oddExpPart m₀ _) hneS

private lemma sum_jacobiSym_split_le {m₀ a₀ N sStar : ℕ} {P : Finset ℕ} {c : ℕ → ℝ} {η : ℝ}
    (h8 : 8 ∣ m₀) (ha₀ : Odd a₀)
    (hP_mod : ∀ q ∈ P, q ≡ a₀ [MOD m₀])
    (hP_cop : ∀ q ∈ P, ∀ n ∈ Finset.Icc 1 N, c n ≠ 0 → n.Coprime q)
    (hc : ∀ n ∈ Finset.Icc 1 N, 0 ≤ c n)
    (hη : 0 ≤ η)
    (hchar : ∀ s : ℕ, 1 < s → s ≤ N ^ 2 → Odd s → Squarefree s → s.Coprime m₀ → s ≠ sStar →
      |(∑ q ∈ P, (jacobiSym q s : ℝ))| ≤ η * P.card) :
    let S := (Finset.Icc 1 N).filter IsPrimePow
    ∑ x ∈ S ×ˢ S, c x.1 * c x.2 * |(∑ q ∈ P, (jacobiSym (x.1 * x.2) q : ℝ))| ≤
      (P.card : ℝ) * (∑ x ∈ (S ×ˢ S).filter (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨
        oddExpPart m₀ (x.1 * x.2) = sStar), c x.1 * c x.2) +
      (η * P.card) * (∑ x ∈ S ×ˢ S, c x.1 * c x.2) := by
  classical
  intro S
  have hcS : ∀ n ∈ S, 0 ≤ c n := fun n hn => hc n (Finset.mem_filter.mp hn).1
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
    exact mul_le_mul_of_nonneg_left habs (mul_nonneg (hcS x.1 hxS.1) (hcS x.2 hxS.2))
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
              (fun q hq => hP_cop q hq x.1 (Finset.mem_filter.mp hx1).1 hc0.1)
              (fun q hq => hP_cop q hq x.2 (Finset.mem_filter.mp hx2).1 hc0.2)
              (Finset.mem_filter.mp hx1).1 (Finset.mem_filter.mp hx2).1
              (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h)) hchar)
            (mul_nonneg (hcS x.1 hx1) (hcS x.2 hx2))
      _ ≤ ∑ x ∈ S ×ˢ S, c x.1 * c x.2 * (η * P.card) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x hx _ => by
            have hxP := Finset.mem_product.mp hx
            exact mul_nonneg (mul_nonneg (hcS x.1 hxP.1) (hcS x.2 hxP.2))
              (mul_nonneg hη (Nat.cast_nonneg _))
      _ = (η * P.card) * ∑ x ∈ S ×ˢ S, c x.1 * c x.2 := by rw [← Finset.sum_mul, mul_comm]

private lemma sum_oddExpPart_eq_one_eq (m₀ N : ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ ((Finset.Icc 1 N).filter IsPrimePow).filter (fun n => oddExpPart m₀ n = 1), c n =
      ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n := by
  classical
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun hpp => ?_
  rw [oddExpPart_primePow hpp]
  have hne1 := (Nat.minFac_prime hpp.ne_one).ne_one
  by_cases hdiv : n.minFac ∣ m₀ <;> by_cases hodd : Odd (n.factorization n.minFac)
  · simp [hdiv, hodd]
  · simp [hdiv, hodd]
  · simp [hdiv, hodd, hne1, Nat.not_even_iff_odd.mpr hodd]
  · simp [hdiv, hodd, Nat.not_odd_iff_even.mp hodd]

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
  set S := (Finset.Icc 1 N).filter IsPrimePow
  have hsum_eq : ∀ q : ℕ,
      ∑ n ∈ Finset.Icc 1 N, (c n : ℂ) * κ n * (jacobiSym n q : ℂ) =
      ∑ n ∈ S, (c n : ℂ) * κ n * (jacobiSym n q : ℂ) := fun q =>
    (Finset.sum_subset (Finset.filter_subset IsPrimePow (Finset.Icc 1 N)) fun n hn hnot => by
      have hc0 : c n = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨hn, hc_supp n hn hne⟩)
      simp [hc0]).symm
  simp_rw [hsum_eq]
  have hexp := sum_norm_sq_jacobiSym_le_expand (P := P) (S := S)
    (fun n hn => hc_nonneg n (Finset.mem_filter.mp hn).1)
    (fun n hn => hκ n (Finset.mem_filter.mp hn).1)
  rw [← Finset.sum_product'] at hexp
  have hsplit := sum_jacobiSym_split_le (P := P) (sStar := sStar) h8 ha₀ hP_mod hP_cop hc_nonneg
    hη hchar
  have htot : ∑ x ∈ S ×ˢ S, c x.1 * c x.2 = (∑ n ∈ Finset.Icc 1 N, c n) ^ 2 := by
    rw [Finset.sum_product, ← Finset.sum_mul_sum, ← sq]
    congr 1
    exact Finset.sum_subset (Finset.filter_subset IsPrimePow (Finset.Icc 1 N)) fun n hn hnot => by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hn, hc_supp n hn hne⟩)
  have hsP_eq : ∀ p, ∑ n ∈ ((Finset.Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p),
      c n = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n := fun p =>
    Finset.sum_congr (by ext n; simp [and_assoc]) fun _ _ => rfl
  have hB' : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (∑ n ∈ S.filter (fun n => n.minFac = p), c n) ≤ B := fun p hp => by
    rw [hsP_eq p]; exact hB p hp
  have hspec := sum_special_pairs_le (m₀ := m₀) (sStar := sStar) hc_nonneg hB'
  have hspec' : ∑ x ∈ (S ×ˢ S).filter (fun x => oddExpPart m₀ (x.1 * x.2) = 1 ∨
        oddExpPart m₀ (x.1 * x.2) = sStar), c x.1 * c x.2 ≤
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n) ^ 2) +
      (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n) ^ 2 +
      2 * B ^ 2 +
      2 * B * (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n) := by
    simpa only [hsP_eq, sum_oddExpPart_eq_one_eq] using hspec
  have h1 := hexp.trans hsplit
  rw [htot] at h1
  nlinarith [Nat.cast_nonneg (α := ℝ) P.card]

end TauCeti
