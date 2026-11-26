/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.CosetLaw
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Weighted character sums with prescribed fibre counts

When weights on a finite set are close to constants, its weighted character sums can be
approximated by the Fourier coefficients of a prescribed distribution of the fibres. For a real
lower bound one can keep this approximation for selected characters and pay only a norm bound
for the rest. This separates the variation in the weights from the error in the fibre counts.

The application to Riesz remainders at nearby scales is the thick-place comparison in Levent
Alpöge's `Deduction.CharacterBalanceMoves.core` and `Deduction.CharacterBalanceMoves.one_char`
(`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean`).
-/

public section

open Finset

namespace MonoidHom

/-- Compare a weighted character sum with the prescribed fibre profile and a constant weight.
The two costs are the sum of the weight deviations and the total count discrepancy times the
norm of the constant weight. The profile need not be a probability distribution. -/
theorem norm_sum_comp_mul_sub_card_mul_sum_le {α Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]
    (χ : Q →* ℂ) (S : Finset α) (p : α → Q) (ν : Q → ℝ) (f : α → ℂ) (z : ℂ) :
    ‖(∑ a ∈ S, χ (p a) * f a) - (S.card : ℂ) * (∑ q, (ν q : ℂ) * χ q) * z‖ ≤
      (∑ a ∈ S, ‖f a - z‖) +
        (∑ q, |((S.filter fun a ↦ p a = q).card : ℝ) - ν q * S.card|) * ‖z‖ := by
  have hnorm (a : α) : ‖χ (p a)‖ = 1 :=
    (χ.isOfFinOrder (isOfFinOrder_of_finite (p a))).norm_eq_one
  have hvar : ‖(∑ a ∈ S, χ (p a) * f a) - (∑ a ∈ S, χ (p a)) * z‖ ≤
      ∑ a ∈ S, ‖f a - z‖ := by
    rw [sum_mul, ← sum_sub_distrib]
    simpa only [← mul_sub, norm_mul, hnorm, one_mul] using
      (norm_sum_le S (fun a ↦ χ (p a) * (f a - z)))
  have hcount := mul_le_mul_of_nonneg_right (χ.norm_sum_comp_sub_card_mul_sum_le S p ν)
    (norm_nonneg z)
  refine (norm_sub_le_norm_sub_add_norm_sub _ ((∑ a ∈ S, χ (p a)) * z) _).trans ?_
  rw [← sub_mul, norm_mul]
  exact add_le_add hvar hcount

end MonoidHom

namespace Finset

/-- Lower-bound the real part of a sum of weighted character sums. For the selected indices `K`,
keep the Fourier coefficient of the prescribed profile at the constant weight `z`. For the other
indices, subtract the norms of their constant weights. Every index pays its weight variation
`D`; only the selected indices pay the fibre-count discrepancy. The factors `c` allow phases
such as character values at a translating element. -/
theorem card_mul_le_sum_re_weighted_characters_of_fiber_counts
    {α Q ι : Type*} [Group Q] [Fintype Q] [DecidableEq Q] [DecidableEq ι]
    (S : Finset α) (p : α → Q) (ν : Q → ℝ) (I K : Finset ι) (hKI : K ⊆ I)
    (χ : ι → Q →* ℂ) (c z : ι → ℂ) (f : ι → α → ℂ) (D : ι → ℝ) (η : ℝ)
    (hν : ∀ q, |((S.filter fun a ↦ p a = q).card : ℝ) - ν q * S.card| ≤ η * S.card)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ 1) (hf : ∀ i ∈ I, ∀ a ∈ S, ‖f i a - z i‖ ≤ D i) :
    (S.card : ℝ) * ((∑ i ∈ K, (c i * (∑ q, (ν q : ℂ) * χ i q) * z i).re) -
      (∑ i ∈ I \ K, ‖z i‖) - (∑ i ∈ I, D i) -
      (Fintype.card Q : ℝ) * η * (∑ i ∈ K, ‖z i‖)) ≤
      ∑ i ∈ I, (c i * ∑ a ∈ S, χ i (p a) * f i a).re := by
  let W (i : ι) := ∑ a ∈ S, χ i (p a) * f i a
  let C (i : ι) := c i * (∑ q, (ν q : ℂ) * χ i q) * z i
  let e : ℝ := Fintype.card Q * η
  have hcount : (∑ q, |((S.filter fun a ↦ p a = q).card : ℝ) - ν q * S.card|) ≤
      S.card * e := by
    calc
      _ ≤ ∑ _q : Q, η * (S.card : ℝ) := sum_le_sum fun q _ ↦ hν q
      _ = S.card * e := by simp [e, nsmul_eq_mul]; ring
  have hkept (i : ι) (hi : i ∈ I) :
      (S.card : ℝ) * ((C i).re - D i - e * ‖z i‖) ≤ (c i * W i).re := by
    have hvar := (χ i).norm_sum_comp_mul_sub_card_mul_sum_le S p ν (f i) (z i)
    have hD : (∑ a ∈ S, ‖f i a - z i‖) ≤ S.card * D i := by
      simpa only [sum_const, nsmul_eq_mul] using sum_le_sum (hf i hi)
    have h := hvar.trans (add_le_add hD (mul_le_mul_of_nonneg_right hcount (norm_nonneg _)))
    have hphase : ‖(S.card : ℂ) * C i - c i * W i‖ ≤
        S.card * D i + (S.card * e) * ‖z i‖ := by
      have hsub : (S.card : ℂ) * C i - c i * W i =
          c i * ((S.card : ℂ) * (∑ q, (ν q : ℂ) * χ i q) * z i - W i) := by
        dsimp only [C]
        ring
      rw [hsub, norm_mul, norm_sub_rev]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hc i hi)).trans h
    have hre := (Complex.re_le_norm _).trans hphase
    rw [Complex.sub_re, ← Complex.ofReal_natCast, Complex.re_ofReal_mul] at hre
    linarith only [hre]
  have hdiscard (i : ι) (hi : i ∈ I) :
      (S.card : ℝ) * (-‖z i‖ - D i) ≤ (c i * W i).re := by
    have hW : ‖W i‖ ≤ (S.card : ℝ) * (‖z i‖ + D i) := by
      rw [← nsmul_eq_mul, ← sum_const]
      refine norm_sum_le_of_le _ fun a ha ↦ ?_
      rw [norm_mul, ((χ i).isOfFinOrder (isOfFinOrder_of_finite (p a))).norm_eq_one, one_mul]
      exact (norm_le_norm_add_norm_sub' (f i a) (z i)).trans (add_le_add_right (hf i hi a ha) _)
    have hre := (neg_le_abs (c i * W i).re).trans (Complex.abs_re_le_norm _)
    rw [norm_mul] at hre
    have h := (mul_le_of_le_one_left (norm_nonneg (W i)) (hc i hi)).trans hW
    linarith only [hre, h]
  calc
    _ = (∑ i ∈ K, (S.card : ℝ) * ((C i).re - D i - e * ‖z i‖)) +
        ∑ i ∈ I \ K, (S.card : ℝ) * (-‖z i‖ - D i) := by
      simp only [mul_sub, mul_neg, sum_sub_distrib, sum_neg_distrib, ← mul_sum,
        ← sum_sdiff hKI, C, e]
      ring
    _ ≤ (∑ i ∈ K, (c i * W i).re) + ∑ i ∈ I \ K, (c i * W i).re :=
      add_le_add (sum_le_sum fun i hi ↦ hkept i (hKI hi))
        (sum_le_sum fun i hi ↦ hdiscard i (mem_sdiff.mp hi).1)
    _ = _ := by rw [add_comm, sum_sdiff hKI]

end Finset
