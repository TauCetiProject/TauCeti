/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import TauCeti.RingTheory.AdicCompletion.Pi
import Mathlib.Tactic.LinearCombination

/-!
# Surjectivity of Frobenius in a `π`-adically complete ring

Let `p` be a prime and `A` a commutative ring that is `π`-adically complete and separated for an
element `π` with `π ^ p ∣ p`. Then the following are equivalent (Bhatt–Morrow–Scholze, *Integral
p-adic Hodge theory*, Lemma 3.9):

1. the relative Frobenius `A ⧸ π → A ⧸ π ^ p`, `[x] ↦ [x ^ p]`, is surjective, that is, every
   element of `A` is a `p`-th power modulo `π ^ p`;
2. Frobenius on `A ⧸ p` is surjective;
3. every element of `A ⧸ π p` is a `p`-th power.

The implications `3 → 2 → 1` only use `π ^ p ∣ p`. The implication `1 → 3` is a successive
approximation which does not use this divisibility: writing `x = y₀ ^ p + π ^ p z₁`,
`z₁ = y₁ ^ p + π ^ p z₂`, and so on, the partial sums `sₙ = y₀ + π y₁ + ⋯ + π ^ (n - 1) yₙ₋₁`
satisfy `x = sₙ ^ p + p bₙ + π ^ (p n) zₙ`, where `p bₙ` collects the cross terms of the binomial
expansions. These cross terms are divisible by `p π`, so `π ∣ bₙ`, and both `sₙ` and `bₙ`
converge `π`-adically. In the limit `x = s ^ p + p b` with `π ∣ b`.

For a perfectoid Tate ring `R` this applies to `A = R°` and a pseudouniformiser `ϖ ∈ R°` with
`ϖ ^ p ∣ p`, where `R°` is `ϖ`-adically complete; it shows that the perfectoid condition can be
tested modulo `p` and that it does not depend on the choice of `ϖ`. Condition 2 is the hypothesis
of Mathlib's `WittVector.surjective_fontaineTheta`, in the form of
`TauCeti.surjective_frobenius_modP_iff` (in `TauCeti.RingTheory.Ideal.Quotient.Frobenius`).

## Main results

* `TauCeti.exists_mul_dvd_sub_pow`: in a `π`-adically complete ring in which every element is a
  `p`-th power modulo `π ^ p`, every element is a `p`-th power modulo `π p`.
* `TauCeti.tfae_forall_exists_dvd_sub_pow`: the equivalence of the three conditions above.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.9.
* P. Scholze, *Étale cohomology of diamonds*, Remark 3.2.
-/

public section

namespace TauCeti

variable {A : Type*} [CommRing A] {π : A} {p : ℕ} [Fact p.Prime]

/-- **Successive approximation of `p`-th roots.** If every element is a `p`-th power modulo
`π ^ p`, then every `x` is `s n ^ p + p * b n` modulo `π ^ (p n)`, where consecutive terms of `s`
and of `b` are congruent modulo `π ^ n` and every `b n` is divisible by `π`. -/
private theorem exists_seq_pow_add_mul (h : ∀ x : A, ∃ y, π ^ p ∣ x - y ^ p) (x : A) :
    ∃ s b : ℕ → A, (∀ n, π ^ n ∣ s (n + 1) - s n) ∧ (∀ n, π ^ n ∣ b (n + 1) - b n) ∧
      (∀ n, π ∣ b n) ∧ ∀ n, (π ^ p) ^ n ∣ x - s n ^ p - p * b n := by
  have hp : p.Prime := Fact.out
  -- every `z` is `Y z ^ p + π ^ p * W z`
  have step (z : A) : ∃ y w, z = y ^ p + π ^ p * w :=
    let ⟨y, w, hw⟩ := h z
    ⟨y, w, by rw [← hw, add_sub_cancel]⟩
  choose Y W hYW using step
  -- the cross terms of `(a + c) ^ p`
  choose r hr using fun a c : A ↦ exists_add_pow_prime_eq hp a c
  -- the remainders `z n`, the partial sums `s n` and the cross-term sums `b n`
  set z : ℕ → A := fun n ↦ W^[n] x
  set t : ℕ → A := fun k ↦ π ^ k * Y (z k)
  set s : ℕ → A := fun n ↦ ∑ k ∈ Finset.range n, t k
  set c : ℕ → A := fun k ↦ s k * t k * r (s k) (t k)
  set b : ℕ → A := fun n ↦ -∑ k ∈ Finset.range n, c k
  have hsn (n : ℕ) : s (n + 1) = s n + t n := Finset.sum_range_succ _ n
  have hbn (n : ℕ) : b (n + 1) = b n - c n := by
    simp only [b, Finset.sum_range_succ]
    ring
  have hrem (n : ℕ) : x = s n ^ p + p * b n + (π ^ p) ^ n * z n := by
    induction n with
    | zero => simp [s, b, z, zero_pow hp.ne_zero]
    | succ n ih =>
      have hz : z (n + 1) = W (z n) := Function.iterate_succ_apply' W n x
      rw [hsn, hbn, hz, hr]
      linear_combination ih + (π ^ p) ^ n * hYW (z n)
  refine ⟨s, b, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ⟨z n, ?_⟩⟩
  · simp [hsn, t]
  · simpa [hbn, c, t] using ((dvd_mul_right (π ^ n) (Y (z n))).mul_left (s n)).mul_right _
  · -- every cross term is divisible by `π`, as `s 0 = 0`
    refine (Finset.dvd_sum fun k _ ↦ ?_).neg_right
    rcases k with _ | k
    · simp [c, s]
    · exact ((dvd_pow_self π k.succ_ne_zero).mul_right _ |>.mul_left _).mul_right _
  · linear_combination hrem n

/-- **Roots modulo `π ^ p` give roots modulo `π p`.** In a `π`-adically complete and separated
ring in which every element is a `p`-th power modulo `π ^ p`, every element is a `p`-th power
modulo `π p` (Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*, Lemma 3.9). -/
theorem exists_mul_dvd_sub_pow [IsHausdorff (Ideal.span {π}) A]
    [IsPrecomplete (Ideal.span {π}) A] (h : ∀ x : A, ∃ y, π ^ p ∣ x - y ^ p) (x : A) :
    ∃ y, π * p ∣ x - y ^ p := by
  obtain ⟨s, b, hs, hb, hbπ, hx⟩ := exists_seq_pow_add_mul h x
  -- the pairs `(s (m + 1), b (m + 1))` converge `π`-adically, to `(L 0, L 1)`
  obtain ⟨L, hL⟩ := exists_forall_pow_dvd_sub π (fun m ↦ ![s (m + 1), b (m + 1)]) fun m i ↦ by
    fin_cases i
    · simpa using hs (m + 1)
    · simpa using hb (m + 1)
  have hLs (m : ℕ) : π ^ m ∣ L 0 - s (m + 1) := by simpa using hL m 0
  have hLb (m : ℕ) : π ^ m ∣ L 1 - b (m + 1) := by simpa using hL m 1
  -- in the limit, `x = L 0 ^ p + p * L 1`
  have hlim : x - L 0 ^ p - p * L 1 = 0 := by
    refine congrFun (eq_zero_of_forall_pow_dvd (ι := Unit) π
      (x := fun _ ↦ x - L 0 ^ p - p * L 1) fun m _ ↦ ?_) ()
    have h1 : π ^ m ∣ s (m + 1) ^ p - L 0 ^ p :=
      (dvd_sub_comm.mp (hLs m)).trans (sub_dvd_pow_sub_pow _ _ p)
    have h2 : π ^ m ∣ (π ^ p) ^ (m + 1) := by
      rw [← pow_mul]
      exact pow_dvd_pow π (by nlinarith [(Fact.out : p.Prime).one_lt])
    have h3 : x - L 0 ^ p - p * L 1 = (x - s (m + 1) ^ p - p * b (m + 1)) +
        (s (m + 1) ^ p - L 0 ^ p) - p * (L 1 - b (m + 1)) := by ring
    rw [h3]
    exact dvd_sub (dvd_add (h2.trans (hx (m + 1))) h1) ((hLb m).mul_left _)
  -- and `π ∣ L 1`, since `π ∣ b 2`
  obtain ⟨d, hd⟩ : π ∣ L 1 := by
    have h1 : π ∣ L 1 - b 2 := by simpa using hLb 1
    have h2 := dvd_add h1 (hbπ 2)
    rwa [sub_add_cancel] at h2
  exact ⟨L 0, d, by linear_combination hlim + (p : A) * hd⟩

variable (π) in
/-- **The Frobenius surjectivity criterion** (Bhatt–Morrow–Scholze, *Integral p-adic Hodge
theory*, Lemma 3.9). In a `π`-adically complete and separated ring `A` with `π ^ p ∣ p`, the
following are equivalent: every element of `A` is a `p`-th power modulo `π ^ p`, modulo `p`, and
modulo `π p`. -/
theorem tfae_forall_exists_dvd_sub_pow [IsHausdorff (Ideal.span {π}) A]
    [IsPrecomplete (Ideal.span {π}) A] (h : π ^ p ∣ (p : A)) :
    [∀ x : A, ∃ y, π ^ p ∣ x - y ^ p, ∀ x : A, ∃ y, (p : A) ∣ x - y ^ p,
      ∀ x : A, ∃ y, π * p ∣ x - y ^ p].TFAE := by
  tfae_have 1 → 3 := exists_mul_dvd_sub_pow
  tfae_have 3 → 2 := fun h3 x ↦ (h3 x).imp fun _ ↦ (dvd_mul_left _ _).trans
  tfae_have 2 → 1 := fun h2 x ↦ (h2 x).imp fun _ ↦ h.trans
  tfae_finish

end TauCeti
