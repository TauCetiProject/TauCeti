/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import TauCeti.Algebra.Algebra.NatCast
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Multiset.Fintype
import Mathlib.Tactic.Ring
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# Newton's identities for a multiset and the variation of Newton coefficients

Mathlib states Newton's identities, `MvPolynomial.mul_esymm_eq_sum`, for the elementary symmetric
and power-sum polynomials in a finite type of variables. This file evaluates them at the elements
of a multiset, which is the form in which they apply to the roots of a polynomial: the elementary
symmetric functions `Multiset.esymm` of a multiset are recovered recursively from its power sums
`(s.map (· ^ j)).sum`, in any commutative ring in which the relevant integers can be inverted.

Consequently, if `(card s)!` is invertible in the scalars, any subalgebra containing the first
`card s` power sums of `s` contains every elementary symmetric function and every power sum of `s`.
This is how a statement about boundedly many power sums of the translates of an element under a
finite group, as in Noether's bound on the degrees of generating invariants, controls all of them.

Newton's recursion `j b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} M_k` defines numbers `b₀ = 1, b₁, …`
from any sequence `M₁, M₂, …`, its *Newton coefficients*; for the power sums of a multiset they
are its elementary symmetric functions. The last section computes how they vary with the `M_k`.
Writing `δ` for a variation, for instance a derivative or a `\bar∂`-operator obeying the Leibniz
rule, the generating function identity `∑ (-1)ʲ b_j tʲ = exp (-∑ M_k tᵏ / k)` predicts

`δ b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} δM_k / k`.

`TauCeti.newton_variation_eq_sum` proves this without power series or exponentials: if `c_j`
satisfies the recursion obtained by applying the Leibniz rule to Newton's recursion, with
`δM_k = k e_k`, then `c_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} e_k`. The variations live in a
module in which division by positive integers is unique, as derivatives of scalar functions
over a field of characteristic zero do. The same
recursion shows that the Newton coefficients are homogeneous: rescaling `M_k ↦ gᵏ M_k`, as a
change of frame `W ↦ g W` does to the moments `M_k = ∫ Wᵏ`, rescales `b_j ↦ gʲ b_j`
(`TauCeti.newton_eq_pow_mul`). These identities are the algebra behind the equation satisfied by
the Newton coefficients of the moments of a family of measures in Taubes's analysis of
Seiberg–Witten solutions near a pseudoholomorphic curve.

## Main results

* `Multiset.mul_esymm_eq_sum`: **Newton's identities** for the elements of a multiset.
* `Multiset.sum_map_pow_one_eq_esymm`, `Multiset.sum_map_pow_two_eq_esymm`,
  `Multiset.sum_map_pow_three_eq_esymm`: the power sums `p₁ = e₁`, `p₂ = e₁² - 2e₂` and
  `p₃ = e₁³ - 3e₁e₂ + 3e₃` of a multiset.
* `Multiset.esymm_mem_of_sum_map_pow_mem`: the elementary symmetric functions of `s` lie in every
  subalgebra containing its first `card s` power sums.
* `Multiset.sum_map_pow_mem_of_sum_map_pow_mem`: so do all the power sums of `s`.
* `TauCeti.newton_variation_eq_sum`: the variation of the Newton coefficients of a sequence.
* `TauCeti.newton_eq_pow_mul`: homogeneity of the Newton coefficients.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Finset

namespace TauCeti

/-- **Newton's identities** for a multiset: `k` times the `k`-th elementary symmetric function of
the elements of `s` is an explicit combination of the lower elementary symmetric functions and
the power sums `(s.map (· ^ j)).sum`. This is `MvPolynomial.mul_esymm_eq_sum` evaluated at the
elements of `s`. -/
theorem _root_.Multiset.mul_esymm_eq_sum {R : Type*} [CommRing R] (s : Multiset R) (k : ℕ) :
    k * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval fun x : s.ToType => (x : R))
    (MvPolynomial.mul_esymm_eq_sum s.ToType R k)
  have hpsum (j : ℕ) : MvPolynomial.aeval (fun x : s.ToType => (x : R))
      (MvPolynomial.psum s.ToType R j) = (s.map (· ^ j)).sum := by
    rw [← Multiset.map_univ_comp_coe, Finset.sum_map_val]
    simp [MvPolynomial.psum]
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, hpsum] at h
  exact h

/-- The first power sum of a multiset is its first elementary symmetric function: `p₁ = e₁`. -/
theorem _root_.Multiset.sum_map_pow_one_eq_esymm {R : Type*} [CommSemiring R] (s : Multiset R) :
    (s.map (· ^ 1)).sum = s.esymm 1 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.esymm_cons, Multiset.esymm_zero, ih]
    ring

/-- The second power sum of a multiset in terms of its elementary symmetric functions:
`p₂ = e₁² - 2e₂`. -/
theorem _root_.Multiset.sum_map_pow_two_eq_esymm {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map (· ^ 2)).sum = s.esymm 1 ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.esymm_cons, Multiset.esymm_zero, ih]
    ring

/-- The third power sum of a multiset in terms of its elementary symmetric functions:
`p₃ = e₁³ - 3e₁e₂ + 3e₃`. -/
theorem _root_.Multiset.sum_map_pow_three_eq_esymm {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map (· ^ 3)).sum = s.esymm 1 ^ 3 - 3 * s.esymm 1 * s.esymm 2 + 3 * s.esymm 3 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.esymm_cons, Multiset.esymm_zero, ih]
    ring

section Subalgebra

variable {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {T : Subalgebra K S}

/-- If `(card s)!` is invertible in `K`, then the elementary symmetric functions of a multiset `s`
lie in every `K`-subalgebra containing its power sums `(s.map (· ^ j)).sum` for
`1 ≤ j ≤ card s`. -/
theorem _root_.Multiset.esymm_mem_of_sum_map_pow_mem (s : Multiset S)
    (hs : IsUnit ((Multiset.card s).factorial : K))
    (hT : ∀ j, 0 < j → j ≤ Multiset.card s → (s.map (· ^ j)).sum ∈ T) (k : ℕ) :
    s.esymm k ∈ T := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases lt_or_ge (Multiset.card s) k with hk | hk
  · rw [Multiset.esymm_of_card_lt hk]
    exact zero_mem T
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  -- Newton's identity expresses `k * e_k` through lower `e_i` and the power sums `p_j`, `j ≤ k`.
  have hu : IsUnit (k : K) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.dvd_factorial hk0 hk)) hs
  rw [← T.natCast_mul_mem_iff hu, Multiset.mul_esymm_eq_sum]
  refine mul_mem (pow_mem (neg_mem (one_mem T)) _) (sum_mem fun a ha ↦ ?_)
  rw [mem_filter, mem_antidiagonal] at ha
  exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem T)) _) (ih _ ha.2))
    (hT _ (by omega) (by omega))

/-- If `(card s)!` is invertible in `K`, then every power sum `(s.map (· ^ k)).sum` of a multiset
`s` lies in every `K`-subalgebra containing those for `1 ≤ k ≤ card s`. -/
theorem _root_.Multiset.sum_map_pow_mem_of_sum_map_pow_mem (s : Multiset S)
    (hs : IsUnit ((Multiset.card s).factorial : K))
    (hT : ∀ j, 0 < j → j ≤ Multiset.card s → (s.map (· ^ j)).sum ∈ T) (k : ℕ) :
    (s.map (· ^ k)).sum ∈ T := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rcases le_or_gt k (Multiset.card s) with hk | hk
  · exact hT k hk0 hk
  -- Beyond `card s` we have `e_k = 0`, so Newton's identity at `k` writes `p_k` through the
  -- products `e_i * p_j` with `0 < i` and `j < k`.
  have h := s.mul_esymm_eq_sum k
  rw [Multiset.esymm_of_card_lt hk, mul_zero, eq_comm, neg_one_pow_mul_eq_zero_iff,
    ← add_sum_erase _ _ (by simp [hk0] : ((0, k) : ℕ × ℕ) ∈ {a ∈ antidiagonal k | a.1 < k})]
    at h
  simp only [pow_zero, Multiset.esymm_zero, one_mul] at h
  rw [eq_neg_of_add_eq_zero_left h]
  refine neg_mem (sum_mem fun a ha ↦ ?_)
  simp only [mem_erase, mem_filter, mem_antidiagonal, ne_eq, Prod.ext_iff, not_and] at ha
  exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem T)) _)
    (s.esymm_mem_of_sum_map_pow_mem hs hT _)) (ih _ (by omega))

end Subalgebra

section Variation

variable {A N : Type*} [CommRing A]

/-- **The variation of the Newton coefficients.** Let `b` satisfy Newton's recursion
`i b_i = ∑_{k=1}^{i} (-1)^(k-1) b_{i-k} M_k` for `i < j`, and let `c` satisfy the recursion
obtained from it by the Leibniz rule, `c₀ = 0` and

`i c_i = ∑_{k=1}^{i} (-1)^(k-1) (M_k c_{i-k} + b_{i-k} δM_k)`,  `δM_k = k e_k`,

for `i ≤ j`. Then `c_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} e_k`, that is
`δ b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} δM_k / k`. -/
theorem newton_variation_eq_sum [AddCommGroup N] [Module A N] [HasUniqueDiv N]
    {b M : ℕ → A} {c e : ℕ → N} {j : ℕ}
    (hb : ∀ i < j, (i : A) * b i = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) * M k)
    (hc₀ : c 0 = 0)
    (hc : ∀ i ≤ j, (i : A) • c i =
      ∑ k ∈ Icc 1 i, (-1 : A) ^ (k - 1) • (M k • c (i - k) + (k : A) • b (i - k) • e k)) :
    c j = ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * b (j - k)) • e k := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hc₀]
  -- The lower `c_i` are given by the claimed formula.
  have hlow : ∀ k ∈ Icc 1 j, c (j - k) =
      ∑ i ∈ Icc 1 (j - k), ((-1) ^ (i - 1) * b (j - k - i)) • e i := fun k hk ↦ by
    rw [mem_Icc] at hk
    exact ih _ (by omega) (fun i hi ↦ hb i (by omega)) (fun i hi ↦ hc i (by omega))
  -- Newton's recursion at `j - k` rewrites `(j - k) b_{j-k}` as a sum against the `M_i`.
  have hnewton : ∀ k ∈ Icc 1 j, ((j - k : ℕ) : A) * b (j - k) =
      ∑ i ∈ Icc 1 (j - k), (-1) ^ (i - 1) * b (j - k - i) * M i := fun k hk ↦ by
    rw [mem_Icc] at hk
    exact hb _ (by omega)
  -- Both double sums run over the pairs `(k, i)` with `1 ≤ k`, `1 ≤ i` and `k + i ≤ j`.
  have hswap : ∑ k ∈ Icc 1 j, (-1 : A) ^ (k - 1) • M k • c (j - k) =
      ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * (((j - k : ℕ) : A) * b (j - k))) • e k := by
    have hl : ∑ k ∈ Icc 1 j, (-1 : A) ^ (k - 1) • M k • c (j - k) = ∑ k ∈ Icc 1 j,
        (-1 : A) ^ (k - 1) • M k • ∑ i ∈ Icc 1 (j - k), ((-1) ^ (i - 1) * b (j - k - i)) • e i :=
      sum_congr rfl fun k hk ↦ by rw [hlow k hk]
    have hr : ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * (((j - k : ℕ) : A) * b (j - k))) • e k =
        ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) *
          ∑ i ∈ Icc 1 (j - k), (-1) ^ (i - 1) * b (j - k - i) * M i) • e k :=
      sum_congr rfl fun k hk ↦ by rw [hnewton k hk]
    rw [hl, hr]
    simp only [smul_sum, sum_smul, smul_smul, mul_sum]
    rw [sum_comm' (t' := Icc 1 j) (s' := fun i ↦ Icc 1 (j - i))
      (fun k i ↦ by simp only [mem_Icc]; omega)]
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun i _ ↦ ?_
    rw [Nat.sub_right_comm]
    congr 1
    ring
  refine nsmul_right_injective hj.ne' ?_
  simp only [← Nat.cast_smul_eq_nsmul A]
  simp only [smul_add, sum_add_distrib, hc j le_rfl, smul_sum]
  rw [hswap, ← sum_add_distrib]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_Icc] at hk
  rw [smul_smul, smul_smul, smul_smul, ← add_smul, Nat.cast_sub hk.2]
  congr 1
  ring

/-- **Homogeneity of the Newton coefficients.** If `b` and `b'` both start at `1` and satisfy
Newton's recursion for `M` and for the rescaled sequence `k ↦ gᵏ M_k` respectively, up to `j`,
then `b'_j = gʲ b_j`. -/
theorem newton_eq_pow_mul [HasUniqueDiv A] {b b' M : ℕ → A} (g : A) {j : ℕ} (hb₀ : b 0 = 1)
    (hb'₀ : b' 0 = 1)
    (hb : ∀ i ≤ j, (i : A) * b i = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) * M k)
    (hb' : ∀ i ≤ j, (i : A) * b' i = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b' (i - k) * (g ^ k * M k)) :
    b' j = g ^ j * b j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hb₀, hb'₀]
  refine nsmul_right_injective hj.ne' ?_
  simp only [nsmul_eq_mul]
  rw [hb' j le_rfl, mul_left_comm, hb j le_rfl, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_Icc] at hk
  rw [ih (j - k) (by omega) (fun i hi ↦ hb i (by omega)) (fun i hi ↦ hb' i (by omega)),
    ← pow_sub_mul_pow g hk.2]
  ring

end Variation

end TauCeti
