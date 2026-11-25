/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Order.BigOperators.Ring.Multiset
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Newton's inequalities for a multiset of real numbers

For a multiset `s` of real numbers with `n` elements write `S_k = e_k(s) / binom(n, k)` for its
normalized elementary symmetric functions, where `e_k(s)` is `Multiset.esymm s k`.

## Main results

* `Multiset.esymm_div_choose_mul_esymm_div_choose_le_sq`: **Newton's inequalities**
  `S_k S_{k+2} ≤ S_{k+1}²` for every `k`.
* `Multiset.eq_of_esymm_div_choose_mul_esymm_div_choose_eq_sq`: if `e_{k+2}(s) ≠ 0` and
  `S_k S_{k+2} = S_{k+1}²`, then all elements of `s` are equal.
* `Multiset.exists_esymm_div_choose_eq_of_card_eq_succ`: if `n ≥ 1`, there is a multiset `r` of
  `n - 1` real numbers with the same `S_0, …, S_{n-1}` as `s`.

## Implementation notes

The last result is Rolle's theorem (`Polynomial.card_roots_le_derivative`): its proof takes for
`r` the roots of the derivative of `∏_{a ∈ s} (X - a)`. It lowers `n` to `k + 2` in Newton's
inequality. Replacing `s` by the inverses of its elements reverses the
sequence `S_0, …, S_{k+2}` up to the factor `S_{k+2}`, which reduces the inequality to
`S_0 S_2 ≤ S_1²`, the inequality between the arithmetic and the quadratic mean.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, Global
  theory of minimal surfaces, Clay Math. Proc. 2 (2005), Lemma 2.6.
-/

public section

namespace Multiset

/-- The normalized elementary symmetric function `e_k(s) / binom(card s, k)` of a multiset. -/
private noncomputable def mNorm (s : Multiset ℝ) (k : ℕ) : ℝ :=
  s.esymm k / (card s).choose k

private theorem mNorm_card (s : Multiset ℝ) : mNorm s (card s) = s.prod := by
  rw [mNorm, Multiset.esymm_card_eq_prod, Nat.choose_self, Nat.cast_one, div_one]

private theorem mNorm_of_card_lt {s : Multiset ℝ} {k : ℕ} (h : card s < k) :
    mNorm s k = 0 := by
  rw [mNorm, Multiset.esymm_of_card_lt h, zero_div]

private theorem mNorm_map_inv_mul_prod (s : Multiset ℝ) (hs : (0 : ℝ) ∉ s) {j : ℕ}
    (hj : j ≤ card s) :
    mNorm (s.map (·⁻¹)) j * s.prod = mNorm s (card s - j) := by
  rw [mNorm, mNorm, card_map, ← Nat.choose_symm hj, div_mul_eq_mul_div,
    Multiset.esymm_map_inv_mul_prod s hs hj]

/-- For `card s = k + 2` and `0 ∉ s`, inverting the elements of `s` expresses `S_{k+2}`, `S_{k+1}`
and `S_k` through `∏ s` and `S_0`, `S_1`, `S_2` of the inverses. -/
private theorem mNorm_eq_mul_prod_of_card_eq {s : Multiset ℝ} {k : ℕ} (hcard : card s = k + 2)
    (h0 : (0 : ℝ) ∉ s) :
    mNorm s (k + 2) = s.prod ∧ mNorm s (k + 1) = mNorm (s.map (·⁻¹)) 1 * s.prod ∧
      mNorm s k = mNorm (s.map (·⁻¹)) 2 * s.prod := by
  have h1 := mNorm_map_inv_mul_prod s h0 (j := 1) (by omega)
  have h2 := mNorm_map_inv_mul_prod s h0 (j := 2) (by omega)
  rw [hcard, show k + 2 - 1 = k + 1 by omega] at h1
  rw [hcard, show k + 2 - 2 = k by omega] at h2
  exact ⟨by rw [← hcard, mNorm_card], h1.symm, h2.symm⟩

open Polynomial in
/-- Rolle's theorem: the roots `r` of the derivative of `∏_{a ∈ s} (X - a)` are real, and they
have the same normalized elementary symmetric functions as `s` up to degree `card r`. -/
private theorem exists_mNorm_eq (s : Multiset ℝ) {m : ℕ} (hs : card s = m + 1) :
    ∃ r : Multiset ℝ, card r = m ∧ ∀ j ≤ m, mNorm s j = mNorm r j := by
  set p : ℝ[X] := (s.map fun a ↦ Polynomial.X - Polynomial.C a).prod with hp
  have hroots : p.roots = s := roots_multiset_prod_X_sub_C s
  have hmonic : p.Monic := monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a
  have hdeg : p.natDegree = m + 1 := by
    rw [hp, natDegree_multiset_prod_X_sub_C_eq_card, hs]
  have hcardp : card p.roots = p.natDegree := by rw [hroots, hdeg, hs]
  have hlead : p.coeff (m + 1) = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  obtain ⟨q, hqdef⟩ : ∃ q, q = derivative p := ⟨_, rfl⟩
  have hqm : q.coeff m = m + 1 := by
    rw [hqdef, coeff_derivative, hlead, one_mul]
  have hqdeg : q.natDegree = m := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hqm]; positivity))
    have := natDegree_derivative_le p
    rw [← hqdef, hdeg] at this
    omega
  have hcardq : card q.roots = q.natDegree := by
    refine le_antisymm (card_roots' q) ?_
    have := card_roots_le_derivative p
    rw [← hqdef, hcardp, hdeg] at this
    omega
  refine ⟨q.roots, by rw [hcardq, hqdeg], fun j hj ↦ ?_⟩
  have hq := coeff_eq_esymm_roots_of_card hcardq (k := m - j) (by omega)
  have hpc := coeff_eq_esymm_roots_of_card hcardp (k := m - j + 1) (by omega)
  rw [hqdeg, show m - (m - j) = j by omega, leadingCoeff, hqdeg, hqm, hqdef, coeff_derivative,
    ← hqdef] at hq
  rw [hdeg, show m + 1 - (m - j + 1) = j by omega, hmonic.leadingCoeff, hroots] at hpc
  rw [hpc] at hq
  have E : (m + 1 : ℝ) * q.roots.esymm j = s.esymm j * ((m - j : ℕ) + 1 : ℝ) := by
    have h1 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    push_cast [Nat.cast_sub hj] at hq ⊢
    linear_combination (-1 : ℝ) ^ j * hq.symm -
      ((m + 1 : ℝ) * q.roots.esymm j - s.esymm j * ((m : ℝ) - j + 1)) * h1
  have Ch : (m.choose j : ℝ) * (m + 1) = ((m + 1).choose j : ℝ) * ((m - j : ℕ) + 1 : ℝ) := by
    have := Nat.choose_mul_succ_eq m j
    rw [show m + 1 - j = m - j + 1 by omega] at this
    exact_mod_cast this
  rw [mNorm, mNorm, hs, hcardq, hqdeg, div_eq_div_iff (by exact_mod_cast (Nat.choose_pos
    (by omega)).ne') (by exact_mod_cast (Nat.choose_pos hj).ne')]
  refine mul_right_cancel₀ (show (m + 1 : ℝ) ≠ 0 by positivity) ?_
  linear_combination s.esymm j * Ch - ((m + 1).choose j : ℝ) * E

/-- The second normalized elementary symmetric function in terms of the first and the second
power sum. -/
private theorem mNorm_two_eq (s : Multiset ℝ) (hs : 2 ≤ card s) :
    mNorm s 2 = (s.sum ^ 2 - (s.map (· ^ 2)).sum) / (card s * (card s - 1)) := by
  have h := Multiset.sum_map_pow_two_eq_esymm s
  rw [Multiset.esymm_one] at h
  rw [mNorm, Nat.cast_choose_two, show s.esymm 2 = (s.sum ^ 2 - (s.map (· ^ 2)).sum) / 2 by
    linarith]
  have : (card s : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ card s := by exact_mod_cast hs
    linarith
  have : (card s : ℝ) ≠ 0 := by positivity
  field_simp

private theorem mNorm_one_eq (s : Multiset ℝ) : mNorm s 1 = s.sum / card s := by
  rw [mNorm, Multiset.esymm_one, Nat.choose_one_right]

/-- Newton's inequality at `k = 1`: `S₀ S₂ ≤ S₁²`, the inequality between the arithmetic and the
quadratic mean. -/
private theorem mNorm_two_le (s : Multiset ℝ) : mNorm s 2 ≤ mNorm s 1 ^ 2 := by
  rcases lt_or_ge (card s) 2 with hs | hs
  · rw [mNorm_of_card_lt hs]
    positivity
  have hn : (2 : ℝ) ≤ card s := by exact_mod_cast hs
  rw [mNorm_two_eq s hs, mNorm_one_eq, div_pow, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [Multiset.sq_sum_le_card_mul_sum_sq s, sq_nonneg s.sum]

private theorem eq_of_mNorm_two_eq (s : Multiset ℝ) (hs : 2 ≤ card s)
    (h : mNorm s 2 = mNorm s 1 ^ 2) : ∀ x ∈ s, ∀ y ∈ s, x = y := by
  have hn : (2 : ℝ) ≤ card s := by exact_mod_cast hs
  rw [mNorm_two_eq s hs, mNorm_one_eq, div_pow, div_eq_div_iff (by nlinarith) (by positivity)] at h
  refine Multiset.eq_of_sq_sum_eq_card_mul_sum_sq s ?_
  have : (card s : ℝ) * (s.sum ^ 2 - card s * (s.map (· ^ 2)).sum) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · linarith
  · linarith

private theorem mNorm_replicate (n : ℕ) (hn : 2 ≤ n) (c : ℝ) :
    mNorm (Multiset.replicate n c) 1 = c ∧ mNorm (Multiset.replicate n c) 2 = c ^ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum : (Multiset.replicate n c).sum = n * c := by simp
  have hsq : ((Multiset.replicate n c).map (· ^ 2)).sum = n * c ^ 2 := by simp
  refine ⟨?_, ?_⟩
  · rw [mNorm_one_eq, hsum, card_replicate]
    field_simp
  · rw [mNorm_two_eq _ (by simpa using hn), hsum, hsq, card_replicate,
      div_eq_iff (by nlinarith)]
    ring

/-- **Newton's inequality** for a multiset, `S_k S_{k+2} ≤ S_{k+1}²`. -/
private theorem mNorm_mul_le_sq (s : Multiset ℝ) (k : ℕ) :
    mNorm s k * mNorm s (k + 2) ≤ mNorm s (k + 1) ^ 2 := by
  rcases lt_or_ge (card s) (k + 2) with hlt | hge
  · rw [mNorm_of_card_lt hlt, mul_zero]
    positivity
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
  clear hge
  induction d generalizing s with
  | zero =>
    by_cases h0 : (0 : ℝ) ∈ s
    · rw [← add_zero (k + 2), ← hd, mNorm_card, Multiset.prod_eq_zero h0, mul_zero]
      positivity
    obtain ⟨h0', h1, h2⟩ := mNorm_eq_mul_prod_of_card_eq hd h0
    rw [h0', h1, h2]
    nlinarith [mNorm_two_le (s.map (·⁻¹)), sq_nonneg s.prod]
  | succ d ih =>
    obtain ⟨r, hr, hsr⟩ := exists_mNorm_eq s (m := k + 2 + d) (by omega)
    rw [hsr k (by omega), hsr (k + 1) (by omega), hsr (k + 2) (by omega)]
    exact ih r hr

/-- The equality case of Newton's inequality for a multiset with `S_{k+2} ≠ 0`. -/
private theorem eq_of_mNorm_mul_eq_sq (s : Multiset ℝ) (k : ℕ) (hne : mNorm s (k + 2) ≠ 0)
    (heq : mNorm s k * mNorm s (k + 2) = mNorm s (k + 1) ^ 2) :
    ∀ x ∈ s, ∀ y ∈ s, x = y := by
  have hge : k + 2 ≤ card s := by
    by_contra h
    exact hne (mNorm_of_card_lt (by omega))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
  clear hge
  induction d generalizing s with
  | zero =>
    have hcard : card s = k + 2 := hd
    have h0 : (0 : ℝ) ∉ s := fun h0 ↦ hne (by rw [← hcard, mNorm_card, Multiset.prod_eq_zero h0])
    have hP : s.prod ≠ 0 := Multiset.prod_ne_zero h0
    obtain ⟨h0', h1, h2⟩ := mNorm_eq_mul_prod_of_card_eq hcard h0
    rw [h0', h1, h2] at heq
    have ht : mNorm (s.map (·⁻¹)) 2 = mNorm (s.map (·⁻¹)) 1 ^ 2 := by
      refine mul_right_cancel₀ (pow_ne_zero 2 hP) ?_
      linear_combination heq
    intro x hx y hy
    have := eq_of_mNorm_two_eq _ (by rw [card_map]; omega) ht _
      (Multiset.mem_map_of_mem _ hx) _ (Multiset.mem_map_of_mem _ hy)
    exact inv_inj.mp this
  | succ d ih =>
    obtain ⟨r, hr, hsr⟩ := exists_mNorm_eq s (m := k + 2 + d) (by omega)
    rw [hsr k (by omega), hsr (k + 1) (by omega), hsr (k + 2) (by omega)] at heq
    rw [hsr (k + 2) (by omega)] at hne
    have hrr := ih r hne heq hr
    obtain ⟨c, hc⟩ := card_pos_iff_exists_mem.mp (show 0 < card r by omega)
    have hrep : r = Multiset.replicate (k + 2 + d) c :=
      Multiset.eq_replicate.mpr ⟨hr, fun b hb ↦ hrr b hb c hc⟩
    obtain ⟨h1, h2⟩ := mNorm_replicate (k + 2 + d) (by omega) c
    rw [← hrep, ← hsr 1 (by omega)] at h1
    rw [← hrep, ← hsr 2 (by omega)] at h2
    exact eq_of_mNorm_two_eq s (by omega) (by rw [h1, h2])


/-- **Newton's inequalities** for a multiset `s` of real numbers: with
`S_k = e_k(s) / binom(card s, k)`, `S_k S_{k+2} ≤ S_{k+1}²` for every `k`. -/
theorem esymm_div_choose_mul_esymm_div_choose_le_sq (s : Multiset ℝ) (k : ℕ) :
    s.esymm k / (card s).choose k * (s.esymm (k + 2) / (card s).choose (k + 2)) ≤
      (s.esymm (k + 1) / (card s).choose (k + 1)) ^ 2 :=
  mNorm_mul_le_sq s k

/-- The equality case of Newton's inequalities: if `e_{k+2}(s) ≠ 0` and `S_k S_{k+2} = S_{k+1}²`
for `S_k = e_k(s) / binom(card s, k)`, then all elements of `s` are equal. -/
theorem eq_of_esymm_div_choose_mul_esymm_div_choose_eq_sq {s : Multiset ℝ} {k : ℕ}
    (hne : s.esymm (k + 2) ≠ 0)
    (h : s.esymm k / (card s).choose k * (s.esymm (k + 2) / (card s).choose (k + 2)) =
      (s.esymm (k + 1) / (card s).choose (k + 1)) ^ 2) :
    ∀ x ∈ s, ∀ y ∈ s, x = y := by
  have hk : k + 2 ≤ card s := by
    by_contra hlt
    exact hne (esymm_of_card_lt (by omega))
  exact eq_of_mNorm_mul_eq_sq s k
    (div_ne_zero hne (by exact_mod_cast (Nat.choose_pos hk).ne')) h

/-- Rolle's theorem for the normalized elementary symmetric functions: if `card s = m + 1`, there
is a multiset `r` of `m` real numbers with `e_j(s) / binom(m + 1, j) = e_j(r) / binom(m, j)` for
every `j ≤ m`. -/
theorem exists_esymm_div_choose_eq_of_card_eq_succ (s : Multiset ℝ) {m : ℕ}
    (hs : card s = m + 1) :
    ∃ r : Multiset ℝ, card r = m ∧
      ∀ j ≤ m, s.esymm j / (m + 1).choose j = r.esymm j / m.choose j := by
  obtain ⟨r, hr, h⟩ := exists_mNorm_eq s hs
  refine ⟨r, hr, fun j hj ↦ ?_⟩
  have := h j hj
  rwa [mNorm, mNorm, hs, hr] at this

end Multiset
