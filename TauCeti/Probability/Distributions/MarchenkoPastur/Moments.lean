/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Narayana
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Combinatorics.NoncrossingPartition.PowerSeries
import TauCeti.Probability.Distributions.MarchenkoPastur.ResolventTransform

/-!
# Moments of the Marchenko–Pastur law

For an aspect ratio `y ≥ 0` and `k : ℕ`, the `k`-th moment of `marchenkoPastur y` is the sum over
all noncrossing partitions of `k` ordered positions, weighting a partition `π` by `y ^ (k - |π|)`:

`∫ x ^ k d(marchenkoPastur y)(x) = ∑_{π ∈ NC(k)} y ^ (k - |π|)`.

Equivalently, each block `B ∈ π` receives the free cumulant weight `y ^ (|B| - 1)`. Grouping by the
number of blocks via the Narayana numbers gives the explicit polynomial formula for `k + 1 ≥ 1`:

`∫ x ^ (k + 1) d(marchenkoPastur y)(x) = ∑_{i = 0}^k (C(k + 1, i + 1) C(k + 1, i) / (k + 1)) y ^ i`.

At `y = 1` every noncrossing partition has weight `1`, so the `k`-th moment of `marchenkoPastur 1`
is the Catalan number `catalan k`.

## Main results

* `TauCeti.Probability.integral_pow_succ_marchenkoPastur_eq_add`: the quadratic convolution
  recurrence `m_{n + 1} = y ∑_{i + j = n} m_i m_j + (1 - y) m_n` for the moments of `MP_y`.
* `TauCeti.Probability.integral_pow_card_marchenkoPastur_eq_sum_prod`: for any finite set `s` in a
  linear order, `∫ x ^ |s| dMP_y = ∑_{π ∈ NC(s)} ∏_{B ∈ π} y ^ (|B| - 1)`.
* `TauCeti.Probability.integral_pow_card_marchenkoPastur`: for any finite set `s` in a linear
  order, `∫ x ^ |s| dMP_y = ∑_{π ∈ NC(s)} y ^ (|s| - |π|)`.
* `TauCeti.Probability.integral_pow_marchenkoPastur`: for `k : ℕ`,
  `∫ x ^ k dMP_y = ∑_{π ∈ NC(Fin k)} y ^ (k - |π|)`.
* `TauCeti.Probability.integral_pow_succ_marchenkoPastur_eq_sum_range`: the explicit Narayana
  polynomial formula in ascending powers of `y`.
* `TauCeti.Probability.integral_pow_marchenkoPastur_one`: `∫ x ^ k dMP_1 = catalan k`.
* `TauCeti.Probability.integral_pow_three_marchenkoPastur`: the third moment `1 + 3 y + y²`.

## Implementation notes

We deduce the formal quadratic equation
`y X M(X)² + ((1 - y) X - 1) M(X) + 1 = 0`
for the moment generating series `M(X) = ∑_{k ≥ 0} m_k X^k` by comparing its polynomial truncations
along the imaginary axis `z = i t` (`t → +∞`) with the quadratic equation of the resolvent
transform (`resolventTransform_marchenkoPastur_quadratic_eq_zero`) using the sharp asymptotic
expansion `tendsto_mul_I_pow_mul_resolventTransform_add_sum`. Rewriting this quadratic equation as
`M(X) = C(X M(X))` for the geometric cumulant series `C(X) = 1 + ∑_{k ≥ 1} y^(k - 1) X^k` and
applying `TauCeti.NoncrossingPartition.sum_prod_coeff_eq_coeff_of_subst_eq` yields the noncrossing
partition formula directly, without binomial manipulations of shifted semicircle moments.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press, 2006, Proposition 12.11 and Lecture 16.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.1 and Exercise 2.1.18.
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, Lemma 3.1.
-/

public section

noncomputable section

open MeasureTheory Complex Filter Finset
open scoped NNReal Topology PowerSeries Polynomial

namespace TauCeti.Probability

/-- The ordinary moment generating series `∑_{k ≥ 0} (∫ x ^ k dMP_y) X ^ k` of `marchenkoPastur y`.
-/
private def momentSeries (y : ℝ≥0) : ℝ⟦X⟧ :=
  PowerSeries.mk fun k ↦ ∫ x, x ^ k ∂marchenkoPastur y

/-- The cumulant series `1 + ∑_{k ≥ 1} y ^ (k - 1) X ^ k` of `marchenkoPastur y`. -/
private def cumulantSeries (y : ℝ≥0) : ℝ⟦X⟧ :=
  PowerSeries.mk fun k ↦ if k = 0 then 1 else (y : ℝ) ^ (k - 1)

/-- Along the imaginary axis `z = i t` (`t → +∞`), the `(n + 1)`-truncation of `momentSeries y`
evaluated at `(i t)⁻¹` agrees with `-i t m(i t)` to order `o(t⁻ⁿ)`. -/
private lemma tendsto_mul_I_pow_mul_aeval_trunc_momentSeries (y : ℝ≥0) (n : ℕ) :
    Tendsto (fun t : ℝ ↦ ((t : ℂ) * I) ^ n *
      (Polynomial.aeval ((t : ℂ) * I)⁻¹ (PowerSeries.trunc (n + 1) (momentSeries y)) -
        -((t : ℂ) * I * resolventTransform (marchenkoPastur y) ((t : ℂ) * I))))
      atTop (𝓝 0) := by
  let w : ℝ → ℂ := fun t ↦ ((t : ℂ) * I)⁻¹
  let S : ℝ → ℂ := fun t ↦ Polynomial.aeval (w t) (PowerSeries.trunc (n + 1) (momentSeries y))
  have hw0 : Tendsto w atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ ↦ (t : ℂ)⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [w] using hinv.const_mul I⁻¹
  have hsharp := hw0.mul <| tendsto_mul_I_pow_mul_resolventTransform_add_sum
    (integrable_pow_marchenkoPastur y (n + 1))
  rw [zero_mul] at hsharp
  refine hsharp.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  have hti : (t : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 ht) I_ne_zero
  have hwt : w t * ((t : ℂ) * I) = 1 := inv_mul_cancel₀ hti
  have hSeval : S t = ∑ k ∈ range (n + 1),
      ((∫ x, x ^ k ∂marchenkoPastur y : ℝ) : ℂ) * ((t : ℂ) * I)⁻¹ ^ k := by
    simpa [S, momentSeries, w, Polynomial.aeval_def] using
      PowerSeries.eval₂_trunc_eq_sum_range (((t : ℂ) * I)⁻¹) (algebraMap ℝ ℂ) (n + 1)
        (momentSeries y)
  have hsum : (∑ k ∈ range (n + 1),
      ((∫ x, x ^ k ∂marchenkoPastur y : ℝ) : ℂ) * ((t : ℂ) * I)⁻¹ ^ (k + 1)) =
      S t * w t := by
    rw [hSeval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    dsimp only [w]
    rw [pow_succ, mul_assoc]
  rw [hsum]
  dsimp only [S]
  rw [pow_succ' _ (n + 1), pow_succ _ n]
  linear_combination (((t : ℂ) * I) ^ n * ((t : ℂ) * I) *
      resolventTransform (marchenkoPastur y) ((t : ℂ) * I) +
    ((t : ℂ) * I) ^ n * S t * (w t * ((t : ℂ) * I))) * hwt +
    ((t : ℂ) * I) ^ n * S t * hwt

/-- The moment generating series `M` of `marchenkoPastur y` satisfies the formal quadratic equation
`y X M² + ((1 - y) X - 1) M + 1 = 0`. -/
private theorem momentSeries_quadratic_eq_zero (y : ℝ≥0) :
    PowerSeries.C (y : ℝ) * PowerSeries.X * momentSeries y ^ 2 +
      (PowerSeries.C (1 - (y : ℝ)) * PowerSeries.X - 1) * momentSeries y + 1 = 0 := by
  set M := momentSeries y
  set E : ℝ⟦X⟧ := PowerSeries.C (y : ℝ) * PowerSeries.X * M ^ 2 +
    (PowerSeries.C (1 - (y : ℝ)) * PowerSeries.X - 1) * M + 1
  suffices ∀ n, PowerSeries.coeff n E = 0 from PowerSeries.ext this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  set P : ℝ[X] := PowerSeries.trunc (n + 1) M
  set F : ℝ[X] := Polynomial.C (y : ℝ) * Polynomial.X * P ^ 2 +
    (Polynomial.C (1 - (y : ℝ)) * Polynomial.X - 1) * P + 1
  have htrunc : PowerSeries.trunc (n + 1) (F : ℝ⟦X⟧) = PowerSeries.trunc (n + 1) E := by
    have hcoe : (F : ℝ⟦X⟧) = PowerSeries.C (y : ℝ) * PowerSeries.X * (P : ℝ⟦X⟧) ^ 2 +
        (PowerSeries.C (1 - (y : ℝ)) * PowerSeries.X - 1) * (P : ℝ⟦X⟧) + 1 := by
      simp [F]
    rw [hcoe]
    simp only [E, map_add, map_sub]
    congr 2
    · rw [mul_assoc, PowerSeries.trunc_C_mul, mul_assoc, PowerSeries.trunc_C_mul]
      congr 1
      rw [← PowerSeries.trunc_mul_trunc, PowerSeries.trunc_trunc_pow, PowerSeries.trunc_mul_trunc]
    · exact PowerSeries.trunc_mul_trunc _ _
  have hFd {d : ℕ} (hd : d < n + 1) : F.coeff d = PowerSeries.coeff d E := by
    rw [← Polynomial.coeff_coe, ← PowerSeries.coeff_coe_trunc_of_lt hd, htrunc,
      PowerSeries.coeff_coe_trunc_of_lt hd]
  obtain ⟨G, hFG⟩ := Polynomial.X_pow_dvd_iff.2 fun d hd ↦
    (hFd (Nat.lt_succ_of_lt hd)).trans (ih d hd)
  have hEG : PowerSeries.coeff n E = G.coeff 0 := by
    rw [← hFd n.lt_succ_self, hFG]
    simpa using Polynomial.coeff_X_pow_mul G n 0
  let w : ℝ → ℂ := fun t ↦ ((t : ℂ) * I)⁻¹
  let Q : ℝ → ℂ := fun t ↦ -((t : ℂ) * I * resolventTransform (marchenkoPastur y) ((t : ℂ) * I))
  let S : ℝ → ℂ := fun t ↦ Polynomial.aeval (w t) P
  have hw0 : Tendsto w atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ ↦ (t : ℂ)⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [w] using hinv.const_mul I⁻¹
  have hG_lim : Tendsto (fun t : ℝ ↦ Polynomial.aeval (w t) G) atTop (𝓝 ((G.coeff 0 : ℝ) : ℂ)) := by
    simpa [Function.comp_def, Polynomial.aeval_def, Polynomial.eval₂_at_zero] using
      (G.continuous_aeval.tendsto (0 : ℂ)).comp hw0
  have hQ_lim : Tendsto Q atTop (𝓝 1) := by
    simpa [Q] using (tendsto_mul_I_mul_resolventTransform (μ := marchenkoPastur y)).neg
  have hS_lim : Tendsto S atTop (𝓝 (Polynomial.aeval (0 : ℂ) P)) :=
    (P.continuous_aeval.tendsto (0 : ℂ)).comp hw0
  have hrem : Tendsto (fun t : ℝ ↦ ((t : ℂ) * I) ^ n * (S t - Q t)) atTop (𝓝 0) :=
    tendsto_mul_I_pow_mul_aeval_trunc_momentSeries y n
  have hG_zero : Tendsto (fun t : ℝ ↦ Polynomial.aeval (w t) G) atTop (𝓝 0) := by
    have hprod : Tendsto (fun t : ℝ ↦ (((t : ℂ) * I) ^ n * (S t - Q t)) *
        ((y : ℂ) * w t * (S t + Q t) + ((1 - (y : ℂ)) * w t - 1))) atTop (𝓝 0) := by
      simpa using hrem.mul (((tendsto_const_nhds.mul hw0).mul (hS_lim.add hQ_lim)).add
        ((tendsto_const_nhds.mul hw0).sub tendsto_const_nhds))
    refine hprod.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    have hti : (t : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 ht) I_ne_zero
    have hz_supp : (t : ℂ) * I ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support := by
      rintro ⟨x, -, hx⟩
      exact ht (by simpa using (congrArg Complex.im hx).symm)
    have hq := resolventTransform_marchenkoPastur_quadratic_eq_zero hz_supp
    have hwt : w t * ((t : ℂ) * I) = 1 := inv_mul_cancel₀ hti
    have hmQ : resolventTransform (marchenkoPastur y) ((t : ℂ) * I) = -(w t * Q t) := by
      dsimp only [Q]
      linear_combination -resolventTransform (marchenkoPastur y) ((t : ℂ) * I) * hwt
    have hQeq : (y : ℂ) * w t * Q t ^ 2 + ((1 - (y : ℂ)) * w t - 1) * Q t + 1 = 0 := by
      rw [hmQ] at hq
      linear_combination hq + (-(y : ℂ) * w t * Q t ^ 2 + Q t) * hwt
    have hFeval : Polynomial.aeval (w t) F =
        (y : ℂ) * w t * S t ^ 2 + ((1 - (y : ℂ)) * w t - 1) * S t + 1 := by
      simp [F, S]
    have hFG_eval : Polynomial.aeval (w t) F = w t ^ n * Polynomial.aeval (w t) G := by
      rw [hFG, map_mul, map_pow, Polynomial.aeval_X]
    have hwn : ((t : ℂ) * I) ^ n * w t ^ n = 1 := by
      rw [← mul_pow, mul_comm, hwt, one_pow]
    linear_combination -((t : ℂ) * I) ^ n * hFeval + ((t : ℂ) * I) ^ n * hFG_eval -
      ((t : ℂ) * I) ^ n * hQeq + Polynomial.aeval (w t) G * hwn
  rw [hEG]
  exact ofReal_eq_zero.1 (tendsto_nhds_unique hG_lim hG_zero)

/-- The quadratic convolution recurrence for the moments of `marchenkoPastur y`:
`m_{n + 1} = y ∑_{i + j = n} m_i m_j + (1 - y) m_n`. -/
theorem integral_pow_succ_marchenkoPastur_eq_add (y : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ (n + 1) ∂marchenkoPastur y =
      (y : ℝ) * (∑ ij ∈ antidiagonal n,
        (∫ x, x ^ ij.1 ∂marchenkoPastur y) * ∫ x, x ^ ij.2 ∂marchenkoPastur y) +
      (1 - (y : ℝ)) * ∫ x, x ^ n ∂marchenkoPastur y := by
  have h' : PowerSeries.C (y : ℝ) * (PowerSeries.X * momentSeries y ^ 2) +
      PowerSeries.C (1 - (y : ℝ)) * (PowerSeries.X * momentSeries y) + 1 = momentSeries y := by
    linear_combination momentSeries_quadratic_eq_zero y
  have h := congrArg (PowerSeries.coeff (n + 1)) h'
  simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, add_zero,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at h
  rw [sq, PowerSeries.coeff_mul] at h
  simp only [momentSeries, PowerSeries.coeff_mk] at h
  exact h.symm

/-- The moment generating series `M` satisfies `C(X * M) = M` for the cumulant series `C`. -/
private theorem subst_cumulantSeries_eq_momentSeries (y : ℝ≥0) :
    (cumulantSeries y).subst (PowerSeries.X * momentSeries y) = momentSeries y := by
  have hlin : (1 - (y : ℝ) • PowerSeries.X) * cumulantSeries y =
      1 + (1 - (y : ℝ)) • PowerSeries.X := by
    ext n
    rcases n with _ | (_ | n)
    · simp [cumulantSeries]
    · simp [cumulantSeries, sub_mul]
    · simp [cumulantSeries, sub_mul, pow_succ', PowerSeries.coeff_X]
  have hS : PowerSeries.HasSubst (PowerSeries.X * momentSeries y) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hsub := congrArg (PowerSeries.substAlgHom hS) hlin
  simp only [map_mul, map_sub, map_add, map_one, map_smul, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom] at hsub
  simp only [PowerSeries.smul_eq_C_mul] at hsub
  have hM : (1 - PowerSeries.C (y : ℝ) * (PowerSeries.X * momentSeries y)) * momentSeries y =
      1 + PowerSeries.C (1 - (y : ℝ)) * (PowerSeries.X * momentSeries y) := by
    linear_combination -momentSeries_quadratic_eq_zero y
  have hunit : IsUnit (1 - PowerSeries.C (y : ℝ) * (PowerSeries.X * momentSeries y)) :=
    PowerSeries.isUnit_iff_constantCoeff.2 (by simp)
  exact hunit.mul_left_cancel (hsub.trans hM.symm)

/-- **Moment–cumulant formula for the Marchenko–Pastur law.** For any finite set `s` in a linear
order, `∫ x ^ |s| d(marchenkoPastur y)` equals the sum over noncrossing partitions `π` of `s` of
`∏_{B ∈ π} y ^ (|B| - 1)`. -/
theorem integral_pow_card_marchenkoPastur_eq_sum_prod {α : Type*} [LinearOrder α]
    (y : ℝ≥0) (s : Finset α) :
    ∫ x, x ^ #s ∂marchenkoPastur y =
      ∑ π : NoncrossingPartition s, ∏ B ∈ π.1.parts, (y : ℝ) ^ (#B - 1) := by
  have h := TauCeti.NoncrossingPartition.sum_prod_coeff_eq_coeff_of_subst_eq
    (by simp [cumulantSeries]) (subst_cumulantSeries_eq_momentSeries y) s
  rw [momentSeries, PowerSeries.coeff_mk] at h
  rw [← h]
  refine sum_congr rfl fun π _ ↦ prod_congr rfl fun B hB ↦ ?_
  have hne : #B ≠ 0 := (π.1.nonempty_of_mem_parts hB).card_pos.ne'
  simp [cumulantSeries, hne]

/-- For any finite set `s` in a linear order, `∫ x ^ |s| d(marchenkoPastur y)` is the sum over
noncrossing partitions `π` of `s` of `y ^ (|s| - |π|)`. -/
theorem integral_pow_card_marchenkoPastur {α : Type*} [LinearOrder α] (y : ℝ≥0) (s : Finset α) :
    ∫ x, x ^ #s ∂marchenkoPastur y =
      ∑ π : NoncrossingPartition s, (y : ℝ) ^ (#s - #π.1.parts) := by
  rw [integral_pow_card_marchenkoPastur_eq_sum_prod]
  refine sum_congr rfl fun π _ ↦ ?_
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have hadd : (∑ B ∈ π.1.parts, (#B - 1)) + #π.1.parts = #s :=
    calc (∑ B ∈ π.1.parts, (#B - 1)) + #π.1.parts
        = (∑ B ∈ π.1.parts, (#B - 1)) + ∑ _ ∈ π.1.parts, 1 := by
            rw [sum_const, smul_eq_mul, mul_one]
      _ = ∑ B ∈ π.1.parts, (#B - 1 + 1) := sum_add_distrib.symm
      _ = #s := (sum_congr rfl fun B hB ↦
            Nat.sub_add_cancel (π.1.nonempty_of_mem_parts hB).card_pos).trans π.1.sum_card_parts
  omega

/-- **Noncrossing-partition moment formula for the Marchenko–Pastur law.** For every `k : ℕ`,
`∫ x ^ k d(marchenkoPastur y) = ∑_{π ∈ NC(Fin k)} y ^ (k - |π|)`. -/
theorem integral_pow_marchenkoPastur (y : ℝ≥0) (k : ℕ) :
    ∫ x, x ^ k ∂marchenkoPastur y =
      ∑ π : NoncrossingPartition (univ : Finset (Fin k)), (y : ℝ) ^ (k - #π.1.parts) := by
  simpa using integral_pow_card_marchenkoPastur y (univ : Finset (Fin k))

/-- **Narayana polynomial formula for the Marchenko–Pastur moments.** For `k : ℕ`, the `(k + 1)`-th
moment of `marchenkoPastur y` is
`∑_{i = 0}^k (C(k + 1, i + 1) C(k + 1, i) / (k + 1)) y ^ i`. -/
theorem integral_pow_succ_marchenkoPastur_eq_sum_range (y : ℝ≥0) (k : ℕ) :
    ∫ x, x ^ (k + 1) ∂marchenkoPastur y =
      ∑ i ∈ range (k + 1),
        (((k + 1).choose (i + 1) * (k + 1).choose i / (k + 1) : ℕ) : ℝ) * (y : ℝ) ^ i := by
  set s : Finset (Fin (k + 1)) := univ
  have hs : #s = k + 1 := by simp [s]
  rw [integral_pow_marchenkoPastur]
  have hpos (π : NoncrossingPartition s) : 1 ≤ #π.1.parts := by
    refine Finset.card_pos.2 (nonempty_iff_ne_empty.2 fun h ↦ ?_)
    have := Finpartition.parts_eq_empty_iff.1 h
    exact (univ_nonempty (α := Fin (k + 1))).ne_empty this
  have hle (π : NoncrossingPartition s) : #π.1.parts ≤ k + 1 :=
    π.1.card_parts_le_card.trans_eq hs
  rw [← sum_fiberwise_of_maps_to (g := fun π : NoncrossingPartition s ↦ k + 1 - #π.1.parts)
    (t := range (k + 1)) fun π _ ↦ mem_range.2 (by have := hpos π; omega)]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mem_range] at hi
  have hfib : (univ.filter fun π : NoncrossingPartition s ↦ k + 1 - #π.1.parts = i) =
      (univ.filter fun π : NoncrossingPartition s ↦ #π.1.parts = k - i + 1) := by
    ext π
    simp only [mem_filter, mem_univ, true_and]
    have := hpos π
    have := hle π
    omega
  calc ∑ π ∈ univ.filter (fun π : NoncrossingPartition s ↦ k + 1 - #π.1.parts = i),
          (y : ℝ) ^ (k + 1 - #π.1.parts)
      = ∑ _ ∈ univ.filter (fun π : NoncrossingPartition s ↦ k + 1 - #π.1.parts = i), (y : ℝ) ^ i :=
        sum_congr rfl fun π hπ ↦ by rw [(mem_filter.1 hπ).2]
    _ = (#(univ.filter fun π : NoncrossingPartition s ↦ #π.1.parts = k - i + 1) : ℝ) *
          (y : ℝ) ^ i := by
        rw [hfib, sum_const, nsmul_eq_mul]
    _ = _ := by
        rw [TauCeti.NoncrossingPartition.card_parts_eq_div, hs]
        congr 2
        have hc1 : (k + 1).choose (k - i + 1) = (k + 1).choose i := by
          have hsub : k - i + 1 = k + 1 - i := by omega
          rw [hsub]
          exact Nat.choose_symm (by omega)
        have hc2 : (k + 1).choose (k - i) = (k + 1).choose (i + 1) := by
          have hsub : k - i = k + 1 - (i + 1) := by omega
          rw [hsub]
          exact Nat.choose_symm (by omega)
        rw [hc1, hc2, mul_comm]

/-- The `k`-th moment of `marchenkoPastur 1` is the Catalan number `catalan k`. -/
theorem integral_pow_marchenkoPastur_one (k : ℕ) :
    ∫ x, x ^ k ∂marchenkoPastur 1 = catalan k := by
  simp [integral_pow_marchenkoPastur, TauCeti.NoncrossingPartition.card_fin_eq_catalan]

/-- The third moment of `marchenkoPastur y` is `1 + 3 y + y²`. -/
theorem integral_pow_three_marchenkoPastur (y : ℝ≥0) :
    ∫ x, x ^ 3 ∂marchenkoPastur y = 1 + 3 * (y : ℝ) + (y : ℝ) ^ 2 := by
  rw [integral_pow_succ_marchenkoPastur_eq_sum_range y 2]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add]
  norm_num

end TauCeti.Probability
