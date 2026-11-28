/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.LocalPrimeSum
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Large inert primes in theta jet estimates

For an inert prime, the first term of the local prime sum measures the excess of the source
weight divided by the prime over the partner weight. Cutting back the source degree before
dividing leaves room for incoming couplings. Subtracting the resulting coupling multiplicity
from the factorial valuation costs at most twice the valuation of the cutback interval, in
addition to the local prime sum.

The coupling multiplicities and the estimate follow `New.Data.padicValNat_factorial_sub_min_le`
and `New.Data.powerDegree_add_partnerDegree_le_of_k_lt` in
`grh/src/New/Derivatives/Sharpness/Cases.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open scoped Nat

namespace TauCeti.OneSidedBound

/-- At an inert prime, remove `min ((l - n) / p) l'` couplings from the factorial valuation,
where `l'` is the degree at the first partner. If the quotient fits in the cutback `n`, the
remaining valuation is bounded by the local prime sum and twice the valuation of the product
of the `n` integers following `l - n`. -/
theorem multiplicity_factorial_sub_min_le {d p n l l' κ : ℕ} [Fact d.Prime] [Fact p.Prime]
    (hinert : legendreSym d p = -1) (hcut : (l - n) / p ≤ n) (hl : l ≤ κ + n)
    {w : ℕ → ℝ} (hw : ∀ a, 0 ≤ w a) (hpartner : w p ≤ l') :
    (multiplicity p l ! : ℝ) - (min ((l - n) / p) l' : ℕ) ≤
      localPrimeSum d p (fun a ↦ max ((κ : ℝ) / a - w a) 0) +
        2 * multiplicity p ((l - n + 1).ascFactorial n) := by
  let i := (l - n) / p
  let B := (l - n + 1).ascFactorial n
  have hB : B ≠ 0 := (Nat.ascFactorial_pos _ _).ne'
  have hmono {a : ℕ} (h : a ∣ B) : multiplicity p a ≤ multiplicity p B :=
    (multiplicity_dvd_iff_le hB).mp ((pow_multiplicity_dvd p a).trans h)
  have hsplit : multiplicity p l ! ≤ i + 2 * multiplicity p B := by
    rcases le_or_gt n l with hn | hn
    · have hi : multiplicity p i ! ≤ multiplicity p B :=
        hmono ((Nat.factorial_dvd_factorial hcut).trans (Nat.factorial_dvd_ascFactorial ..))
      have heq : (l - n)! * B = l ! := by
        dsimp only [B]
        rw [Nat.factorial_mul_ascFactorial, Nat.sub_add_cancel hn]
      have hrec : multiplicity p (l - n)! = multiplicity p i ! + i :=
        (multiplicity_mul_div_factorial _).symm.trans (multiplicity_factorial_mul i)
      rw [← heq, Nat.multiplicity_mul (Nat.factorial_ne_zero _) hB, hrec]
      omega
    · have hle : l ! ∣ B :=
        (Nat.factorial_dvd_factorial hn.le).trans (Nat.factorial_dvd_ascFactorial ..)
      exact (hmono hle).trans (by
        simp only [two_mul]
        exact le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _))
  have hquot : (i : ℝ) ≤ (κ : ℝ) / p := Nat.cast_div_le.trans <|
    div_le_div_of_nonneg_right (by exact_mod_cast (Nat.sub_le_iff_le_add.mpr hl)) (by positivity)
  have hmin : (i : ℝ) - (min i l' : ℕ) ≤ max ((κ : ℝ) / p - w p) 0 := by
    rw [Nat.cast_min, ← max_sub_sub_left, sub_self]
    exact max_le (le_max_right ..) ((sub_le_sub hquot hpartner).trans (le_max_left ..))
  have hlocal := max_div_sub_le_localPrimeSum hinert (κ : ℝ) hw
  have hsplit' : (multiplicity p l ! : ℝ) ≤ i + 2 * multiplicity p B := by exact_mod_cast hsplit
  exact (sub_le_sub_right hsplit' _).trans (by linarith [hmin.trans hlocal])

/-- The simultaneous large-prime couplings fit in the original degrees. For a permutation
`σ` of places, `j i = min ((l i - n) / p) (l (σ i))` consumes `p * j i` at `i` and `j i`
at `σ i`. The condition `(l i - n) / p ≤ n` bounds the incoming degree by the amount reserved. -/
theorem mul_min_div_add_min_div_le_of_perm {ι : Type*} (l : ι → ℕ) {σ : Equiv.Perm ι}
    {p n : ℕ} (hcut : ∀ i, (l i - n) / p ≤ n) (i : ι) :
    p * min ((l i - n) / p) (l (σ i)) + min ((l (σ.symm i) - n) / p) (l i) ≤ l i := by
  have hout : p * min ((l i - n) / p) (l (σ i)) ≤ l i - n :=
    (Nat.mul_le_mul_left _ (min_le_left ..)).trans (Nat.mul_div_le ..)
  have hin : min ((l (σ.symm i) - n) / p) (l i) ≤ min n (l i) :=
    min_le_min_right _ (hcut (σ.symm i))
  omega

/-- Large-prime coupling budget at all places. Reserve `n = ⌈6b/k⌉` degrees and couple each
place to its first partner. The incoming and outgoing degrees fit at each place, and the
sum of the uncoupled factorial valuations is bounded by the total local prime sum and the
valuation cost of the cutback intervals. The partner map at exponent `1` is the permutation
`σ`, while `partner a i` is the partner of `i` at the prime power `a`. -/
theorem exists_largePrimeCouplingMultiplicities {ι : Type*} [Fintype ι] {d p k b x : ℕ}
    [Fact d.Prime] [Fact p.Prime] (hinert : legendreSym d p = -1) (hk : 0 < k) (hkp : k ≤ p)
    (hkx : k ≤ 3 * x ^ 5) (hb : x ^ 47 ≤ b) (partner : ℕ → ι → ι)
    (hbij : Function.Bijective (partner p)) (κ l : ι → ℕ) (hκ : ∀ i, κ i ≤ b)
    (hl : ∀ i, κ i ≤ l i ∧ l i ≤ κ i + x ^ 42) :
    let n : ℕ := ⌈6 * (b : ℝ) / k⌉₊
    let σ := Equiv.ofBijective (partner p) hbij
    ∃ j : ι → ℕ, (∀ i, j i = min ((l i - n) / p) (l (σ i))) ∧
      (∀ i, p * j i + j (σ.symm i) ≤ l i) ∧
      (∑ i, ((multiplicity p (l i)! : ℝ) - (j i : ℝ))) ≤
        (∑ i, localPrimeSum d p (fun a ↦ max ((κ i : ℝ) / a - κ (partner a i)) 0)) +
          2 * ∑ i, (multiplicity p ((l i - n + 1).ascFactorial n) : ℝ) := by
  intro n σ
  have hkn : 6 * b ≤ k * n := by
    have h : 6 * (b : ℝ) ≤ (n : ℝ) * k :=
      (div_le_iff₀ (Nat.cast_pos.mpr hk)).mp (Nat.le_ceil _)
    rw [mul_comm (n : ℝ)] at h
    exact_mod_cast h
  have hxn : x ^ 42 ≤ n := by
    apply Nat.le_of_mul_le_mul_left _ hk
    calc
      k * x ^ 42 ≤ (3 * x ^ 5) * x ^ 42 := Nat.mul_le_mul_right _ hkx
      _ = 3 * x ^ 47 := by rw [mul_assoc, ← pow_add]
      _ ≤ 6 * b := by omega
      _ ≤ k * n := hkn
  have hx : 1 ≤ x := by
    by_contra! hx
    have hzero : x = 0 := by omega
    simp [hzero] at hkx
    omega
  have hxb : x ^ 42 ≤ b := (Nat.pow_le_pow_right hx (by decide)).trans hb
  have hcut (i : ι) : (l i - n) / p ≤ n := by
    have hli : l i ≤ 2 * b := by linarith [(hl i).2, hκ i]
    apply Nat.div_le_of_le_mul
    calc l i - n ≤ l i := Nat.sub_le ..
      _ ≤ 2 * b := hli
      _ ≤ 6 * b := by omega
      _ ≤ k * n := hkn
      _ ≤ p * n := Nat.mul_le_mul_right n hkp
  refine ⟨fun i ↦ min ((l i - n) / p) (l (σ i)), fun _ ↦ rfl, ?_, ?_⟩
  · intro i
    simpa only [σ.apply_symm_apply] using mul_min_div_add_min_div_le_of_perm l (σ := σ) hcut i
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ multiplicity_factorial_sub_min_le hinert (hcut i)
      ((hl i).2.trans (Nat.add_le_add_left hxn _)) (fun _ ↦ Nat.cast_nonneg _) ?_
    simpa only [σ, Equiv.ofBijective_apply, Nat.cast_le] using (hl (σ i)).1

end TauCeti.OneSidedBound
