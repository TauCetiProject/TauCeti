/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Recovering exponents from products of powers of polynomials

Let `P i γ` be nonzero polynomials over a field `k`, indexed by a finite type `ι` and a parameter
`γ`. Suppose the products `∏ i, P i γ ^ c i` for all `γ` determine an exponent vector
`c : ι → ℕ` after casting into `k`. This file shows that they then determine `c` itself
(`Polynomial.eq_of_forall_prod_pow_eq`). In characteristic `p` the cast forgets multiples of `p`;
the missing information is recovered by extracting `p`-th roots, using that Frobenius is
injective on `k[X]`.

This is the step of the Brauer–Nesbitt theorem that passes from traces to characteristic
polynomials, with `P i γ` the characteristic polynomials of the simple modules.

## Main results

* `Polynomial.eq_of_forall_prod_pow_eq`: exponent vectors giving the same products of powers of
  nonzero polynomials agree, given that they agree after casting into `k`.
-/

public section

namespace Polynomial

variable {k ι Γ : Type*} [Field k] [Fintype ι] (P : ι → Γ → k[X]) (hP : ∀ i γ, P i γ ≠ 0)
variable (hsep : ∀ c d : ι → ℕ, (∀ γ, ∏ i, P i γ ^ c i = ∏ i, P i γ ^ d i) → ∀ i, (c i : k) = d i)
include hsep

/-- **Exponent vectors with disjoint supports.** Let `P i γ` be polynomials over a field `k` such
that exponent vectors `c, d` giving the same products `∏ i, P i γ ^ c i` for every `γ` agree after
casting into `k`. If such `c, d` have disjoint supports, they vanish. Their entries vanish in `k`,
so in characteristic `p` they are divisible by `p`; since Frobenius is injective on `k[X]`, the
quotients by `p` again give equal products, and induction on the total exponent applies. -/
private theorem eq_zero_of_forall_prod_pow_eq :
    ∀ c d : ι → ℕ, (∀ i, c i = 0 ∨ d i = 0) → (∀ γ, ∏ i, P i γ ^ c i = ∏ i, P i γ ^ d i) →
      c = 0 ∧ d = 0 := by
  intro c d
  induction hn : ∑ i, (c i + d i) using Nat.strong_induction_on generalizing c d with
  | _ n ih =>
  intro hdisj h
  have hcast (i : ι) : (c i : k) = 0 ∧ (d i : k) = 0 := by
    have := hsep c d h i
    rcases hdisj i with hi | hi <;> simp_all
  by_contra h0
  obtain ⟨p, hchar⟩ := CharP.exists k
  have hdvd (i : ι) : p ∣ c i ∧ p ∣ d i :=
    ⟨(CharP.cast_eq_zero_iff k p _).mp (hcast i).1, (CharP.cast_eq_zero_iff k p _).mp (hcast i).2⟩
  rcases CharP.char_is_prime_or_zero k p with hp | rfl
  swap
  · exact h0 ⟨funext fun i => Nat.eq_zero_of_zero_dvd (hdvd i).1,
      funext fun i => Nat.eq_zero_of_zero_dvd (hdvd i).2⟩
  have := Fact.mk hp
  choose u hu using fun i => (hdvd i).1
  choose v hv using fun i => (hdvd i).2
  have hpow (e : ι → ℕ) (γ : Γ) : ∏ i, P i γ ^ (p * e i) = (∏ i, P i γ ^ e i) ^ p := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
  have h2 := hp.two_le
  obtain ⟨hu0, hv0⟩ : u = 0 ∧ v = 0 := by
    refine ih (∑ i, (u i + v i)) ?_ u v rfl (fun i => ?_) fun γ => frobenius_inj k[X] p ?_
    · rw [← hn]
      obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 ∨ v i ≠ 0 := by
        by_contra! hall
        exact h0 ⟨funext fun i => by simp [hu i, (hall i).1],
          funext fun i => by simp [hv i, (hall i).2]⟩
      refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · nlinarith [hu i, hv i]
      · rcases hi with hi | hi <;> nlinarith [hu i, hv i, Nat.pos_of_ne_zero hi]
    · rcases hdisj i with hi | hi
      · exact Or.inl (by simpa [hu i, hp.ne_zero] using hi)
      · exact Or.inr (by simpa [hv i, hp.ne_zero] using hi)
    · simp only [frobenius_def, ← hpow]
      simpa only [← hu, ← hv] using h γ
  exact h0 ⟨funext fun i => by simp [hu i, hu0], funext fun i => by simp [hv i, hv0]⟩

include hP in
/-- **Cancelling exponents against a separating family.** Let `P i γ` be nonzero polynomials over
a field `k` such that exponent vectors `c, d` giving the same products `∏ i, P i γ ^ c i` for every
`γ` agree after casting into `k`. Then such exponent vectors agree. -/
theorem eq_of_forall_prod_pow_eq (c d : ι → ℕ)
    (h : ∀ γ, ∏ i, P i γ ^ c i = ∏ i, P i γ ^ d i) : c = d := by
  -- Cancelling the common part `min (c i) (d i)` leaves exponent vectors with disjoint supports,
  -- which vanish by the disjoint-support case above.
  have key (e : ι → ℕ) (he : ∀ i, min (c i) (d i) ≤ e i) (γ : Γ) : ∏ i, P i γ ^ e i =
      (∏ i, P i γ ^ min (c i) (d i)) * ∏ i, P i γ ^ (e i - min (c i) (d i)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_add, Nat.add_sub_cancel' (he i)]
  obtain ⟨hc, hd⟩ := eq_zero_of_forall_prod_pow_eq P hsep (fun i => c i - min (c i) (d i))
    (fun i => d i - min (c i) (d i)) (fun i => by omega) fun γ => by
      have := h γ
      rw [key c (fun i => min_le_left _ _), key d (fun i => min_le_right _ _)] at this
      exact mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hP i γ)) this
  funext i
  have := congrFun hc i
  have := congrFun hd i
  simp only [Pi.zero_apply] at *
  omega

end Polynomial
