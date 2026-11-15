/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Ring.GeomSum

/-!
# Elements of finite order congruent to `1` modulo `p ^ k`

Let `p` be a prime and `A` a ring, not necessarily commutative, with no `p`-torsion and with
`⋂ⱼ pʲ A = 0`. This file proves **Serre's lemma**: an element of finite order of `A` that is
congruent to `1` modulo `p ^ k`, with `p ^ k ≥ 3`, is equal to `1`. Minkowski proved the case
`A = Mₙ(ℤ)`. The bound is sharp: `-1` has order `2` and is congruent to `1` modulo `2`.

The typical ring is the endomorphism ring of a Tate module `T_ℓ E`. Then the lemma says that an
automorphism of `T_ℓ E` of finite order acting trivially on `E[ℓ ^ k]`, with `ℓ ^ k ≥ 3`, is the
identity. In the criterion of Néron, Ogg and Shafarevich, this lets one pass from unramified
torsion `E[ℓ ^ k]` to an unramified Tate module once inertia is known to act through a finite
quotient.

## Main results

* `TauCeti.eq_one_of_isOfFinOrder_of_pow_dvd_sub_one`: an element of finite order congruent to
  `1` modulo `p ^ k`, with `p ^ k ≥ 3`, is `1`.

## Implementation notes

The proof reduces to an element `b` of prime order `r`. Write `b - 1 = pʲ c` with `c` not divisible
by `p`, where `j ≥ k`. Then `0 = bʳ - 1 = (b - 1) ∑_{i < r} bⁱ`, and
`∑_{i < r} bⁱ = r + C(r, 2) (b - 1) + (b - 1)² w`. Cancelling `pʲ` gives
`r c + C(r, 2) pʲ c² + p²ʲ c³ w = 0`. If `r ≠ p`, then `p` divides `r c`, hence `c`. If `r = p`,
then `p²` divides `C(p, 2) pʲ`, as `p ∣ C(p, 2)` for odd `p` and `j ≥ 2` for `p = 2`. So `p²`
divides `p c`, and `p` divides `c`. Both cases contradict the choice of `j`. The integer `p` is
central in `A`, which is all the noncommutative manipulations need.

## References

* J.-P. Serre, *Rigidité du foncteur de Jacobi d'échelon n ≥ 3*, appendix to exposé 17 of
  *Séminaire Henri Cartan* 13 (1960/61).
* J.-P. Serre and J. Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968),
  492–517.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A]

/-- If `bʳ = 1` and `b - 1 = pʲ c`, then `r c + C(r, 2) pʲ c² + p²ʲ c³ w = 0` for some `w`: expand
`0 = bʳ - 1 = (b - 1) ∑_{i < r} bⁱ` and cancel `pʲ`. -/
private theorem exists_mul_add_eq_zero_of_pow_eq_one {p : ℕ} (hreg : IsLeftRegular (p : A))
    {r : ℕ} {b : A} (hb : b ^ r = 1) {j : ℕ} {c : A} (hc : b - 1 = (p : A) ^ j * c) :
    ∃ w : A, (r : A) * c + ((r.choose 2 * p ^ j : ℕ) : A) * (c * c) +
      ((p ^ j * p ^ j : ℕ) : A) * (c * c * c * w) = 0 := by
  obtain ⟨v, w, -, hw⟩ := exists_one_add_pow_eq_and_geom_sum_eq (b - 1) r
  have hbS : (b - 1) * ∑ i ∈ Finset.range r, (1 + (b - 1)) ^ i = 0 := by
    rw [add_sub_cancel, mul_geom_sum, hb, sub_self]
  rw [hw, hc, mul_assoc] at hbS
  refine ⟨w, Eq.trans ?_ ((hreg.pow j) (hbS.trans (mul_zero _).symm))⟩
  -- `p` is central, so the casts move past `c`.
  have h₁ (n : ℕ) : c * (n : A) = n * c := (Nat.cast_comm n c).symm
  have h₂ (n : ℕ) (z : A) : c * ((n : A) * z) = n * (c * z) :=
    (Nat.cast_commute n c).symm.left_comm z
  rw [← Nat.cast_pow]
  simp only [mul_add, sq, Nat.cast_mul, mul_assoc, h₁, h₂]

/-- The case of prime order of `eq_one_of_isOfFinOrder_of_pow_dvd_sub_one`. -/
private theorem eq_one_of_pow_prime_eq_one_of_pow_dvd_sub_one {p : ℕ} (hp : p.Prime)
    (hreg : IsLeftRegular (p : A)) (hsep : ∀ x : A, (∀ j, (p : A) ^ j ∣ x) → x = 0) {k : ℕ}
    (hk : 3 ≤ p ^ k) {r : ℕ} (hr : r.Prime) {b : A} (hb : b ^ r = 1)
    (hdvd : (p : A) ^ k ∣ b - 1) : b = 1 := by
  by_contra hne
  -- Write `b - 1 = p ^ j * c` with `j` the multiplicity of `p` in `b - 1`.
  have hfin : FiniteMultiplicity (p : A) (b - 1) := by
    by_contra h
    exact sub_ne_zero.mpr hne (hsep _ (FiniteMultiplicity.not_iff_forall.mp h))
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hjk := hfin.le_multiplicity_of_pow_dvd hdvd
  set j := multiplicity (p : A) (b - 1)
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h ↦ by simp [h] at hk
  have hj0 : j ≠ 0 := by omega
  obtain ⟨w, hcS⟩ := exists_mul_add_eq_zero_of_pow_eq_one hreg hb hc
  rcases eq_or_ne r p with rfl | hrp
  · -- `r = p`: `p ^ 2` divides the last two terms, so `p c ∈ p ^ 2 A`.
    have hC : r ^ 2 ∣ r.choose 2 * r ^ j := by
      rcases hr.eq_two_or_odd' with rfl | hodd
      · have hk2 : 2 ≤ k := by
          by_contra h
          interval_cases k
          simp at hk
        rw [Nat.choose_self, one_mul]
        exact pow_dvd_pow 2 (hjk.trans' hk2)
      · rw [sq]
        refine mul_dvd_mul (hr.dvd_choose_self two_ne_zero ?_) (dvd_pow_self r hj0)
        exact lt_of_le_of_ne hr.two_le fun h ↦ absurd (h ▸ hodd) (by decide)
    obtain ⟨e₁, he₁⟩ := hC
    obtain ⟨e₂, he₂⟩ : r ^ 2 ∣ r ^ j * r ^ j := by
      rw [← pow_add]
      exact pow_dvd_pow r (by omega)
    refine hpc ⟨-((e₁ : A) * (c * c) + (e₂ : A) * (c * c * c * w)), hreg ?_⟩
    rw [he₁, he₂, add_assoc] at hcS
    push_cast at hcS
    -- Beta-reduce the goal `(fun y ↦ p * y) c = (fun y ↦ p * y) (p * _)` left by `hreg`.
    dsimp only
    rw [eq_neg_of_add_eq_zero_left hcS]
    noncomm_ring
  · -- `r ≠ p`: `p` divides `r c`, and `r` is invertible modulo `p`.
    obtain ⟨e₁, he₁⟩ : p ∣ r.choose 2 * p ^ j := dvd_mul_of_dvd_right (dvd_pow_self p hj0) _
    obtain ⟨e₂, he₂⟩ : p ∣ p ^ j * p ^ j := dvd_mul_of_dvd_right (dvd_pow_self p hj0) _
    have hrc : (r : A) * c = p * -((e₁ : A) * (c * c) + (e₂ : A) * (c * c * c * w)) := by
      rw [he₁, he₂, add_assoc] at hcS
      push_cast at hcS
      rw [eq_neg_of_add_eq_zero_left hcS]
      noncomm_ring
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hr hp).mpr hrp)
    have huv' : (u : A) * r + v * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    refine hpc ⟨u * -((e₁ : A) * (c * c) + (e₂ : A) * (c * c * c * w)) + v * c, ?_⟩
    calc c = ((u : A) * r + v * p) * c := by rw [huv', one_mul]
      _ = u * (r * c) + v * (p * c) := by rw [add_mul, mul_assoc, mul_assoc]
      _ = _ := by
        rw [hrc, mul_add, (Int.cast_commute u (p : A)).left_comm,
          (Int.cast_commute v (p : A)).left_comm]

/-- **Serre's lemma.** Let `p` be a prime and `A` a ring with no `p`-torsion in which only `0` is
divisible by every power of `p`. An element of finite order of `A` that is congruent to `1` modulo
`p ^ k`, with `p ^ k ≥ 3`, is equal to `1`. -/
theorem eq_one_of_isOfFinOrder_of_pow_dvd_sub_one {p : ℕ} (hp : p.Prime)
    (hreg : IsLeftRegular (p : A)) (hsep : ∀ x : A, (∀ j, (p : A) ^ j ∣ x) → x = 0) {k : ℕ}
    (hk : 3 ≤ p ^ k) {a : A} (ha : IsOfFinOrder a) (hdvd : (p : A) ^ k ∣ a - 1) : a = 1 := by
  by_contra hne
  -- Some power `b` of `a` has prime order `r`, and `b - 1` is still divisible by `p ^ k`.
  obtain ⟨r, hr, hra⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.mp hne)
  have hb := orderOf_pow_orderOf_div ha.orderOf_pos.ne' hra
  have hb1 := eq_one_of_pow_prime_eq_one_of_pow_dvd_sub_one hp hreg hsep hk hr
    (hb ▸ pow_orderOf_eq_one _) (hdvd.trans (sub_one_dvd_pow_sub_one a _))
  exact hr.one_lt.ne' (by rw [← hb, hb1, orderOf_one])

end TauCeti
