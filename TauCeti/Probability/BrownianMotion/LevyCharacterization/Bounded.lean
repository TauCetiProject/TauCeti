/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.Probability.Martingale.Basic

/-!
# Complex exponential martingales for bounded continuous martingales

Let `X` be a bounded, almost-surely continuous real martingale on a raw filtration `ℱ` under a
finite measure `P`, and let `A` be a strongly adapted nondecreasing Lipschitz process starting at
`0` such that `X ^ 2 - A` is a martingale. This file proves that for every real frequency `α`, the
compensated complex exponential

`t ↦ exp (I * α * X t + α ^ 2 / 2 * A t)`

is a martingale on `ℱ`.

The proof avoids stochastic integration and filtration usual conditions by telescoping along uniform
partitions of `[s, t]`. Martingale increment orthogonality annihilates the first- and second-order
Taylor terms, while the cubic remainder is controlled via Cauchy–Schwarz between the uniform modulus
of continuity of `X` on `[s, t]` and a uniform `L²` bound on discrete quadratic sums.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 3.3.16.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 3.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped NNReal Topology

namespace MeasureTheory.Martingale

section PureHelpers

private def expProc {Ω : Type*} (X A : ℝ≥0 → Ω → ℝ) (α : ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  exp (I * α * X t ω + ((α ^ 2 / 2 * A t ω : ℝ) : ℂ))

private def expRem (α x a : ℝ) : ℂ :=
  exp (I * α * x + ((α ^ 2 / 2 * a : ℝ) : ℂ)) - 1 -
    (I * α * x + ((α ^ 2 / 2 : ℝ) : ℂ) * ((a - x ^ 2 : ℝ) : ℂ))

/-- Uniform partition of `[s, t]` into `m + 1` equal subintervals. -/
private def uniformGrid (s t : ℝ≥0) (m : ℕ) (k : Fin (m + 2)) : ℝ≥0 :=
  s + ((k : ℝ≥0) / (m + 1 : ℝ≥0)) * (t - s)

private def maxInc {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k : Fin (m + 1) ↦
    |X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω|

private lemma norm_exp_I_mul_add_ofReal (x y : ℝ) :
    ‖exp (I * (x : ℂ) + (y : ℂ))‖ = Real.exp y := by
  rw [Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

private lemma stronglyMeasurable_finsetSup' {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {s : Finset ι} (hs : s.Nonempty) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun ω ↦ s.sup' hs (f · ω)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i (Finset.mem_singleton_self i)
  | cons i t hi ht ih =>
    convert (hf i (Finset.mem_cons_self i t)).sup
      (ih fun j hj ↦ hf j (Finset.mem_cons_of_mem hj)) using 1
    ext ω
    exact Finset.sup'_cons ..

private lemma ae_abs_increment_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (u v : ℝ≥0) :
    ∀ᵐ ω ∂P, |X v ω - X u ω| ≤ 2 * R := by
  filter_upwards [hXR v, hXR u] with ω hv hu
  exact (abs_sub _ _).trans (by linarith)

/-- Symmetric double sum over `Fin n` decomposes into diagonal plus twice the upper triangle. -/
private lemma sum_sq_symm_eq_diag_add_two_mul_lt {n : ℕ} {f : Fin n → Fin n → ℝ}
    (hsym : ∀ j k, f j k = f k j) :
    ∑ j : Fin n, ∑ k : Fin n, f j k =
      ∑ j : Fin n, f j j + 2 * ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (j < ·), f j k := by
  have hsplit (j : Fin n) : ∑ k : Fin n, f j k =
      f j j + ∑ k ∈ Finset.univ.filter (j < ·), f j k +
        ∑ k ∈ Finset.univ.filter (· < j), f j k := by
    have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun k ↦ k = j) (f j)).symm
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton] at h1
    rw [h1, add_assoc]
    congr 1
    have h2 := (Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun k ↦ ¬k = j))
      (fun k ↦ j < k) (f j)).symm
    rw [h2]
    congr 1 <;> refine Finset.sum_congr ?_ fun _ _ ↦ rfl <;> ext k <;> simp <;> omega
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hswap : ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (· < j), f j k =
      ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (j < ·), f j k := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by
      split_ifs <;> [exact hsym k j; rfl]
  rw [hswap]; ring

private lemma uniformGrid_zero (s t : ℝ≥0) (m : ℕ) : uniformGrid s t m 0 = s := by
  simp [uniformGrid]

private lemma uniformGrid_last {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    uniformGrid s t m (Fin.last (m + 1)) = t := by
  simp [uniformGrid, add_tsub_cancel_of_le hst]

private lemma uniformGrid_mono (s t : ℝ≥0) (m : ℕ) : Monotone (uniformGrid s t m) := by
  intro i j hij
  dsimp only [uniformGrid]
  gcongr
  exact_mod_cast hij

private lemma uniformGrid_step {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) (k : Fin (m + 1)) :
    (uniformGrid s t m k.succ : ℝ) - uniformGrid s t m k.castSucc =
      ((t : ℝ) - s) / (m + 1) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp only [uniformGrid, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_one, NNReal.coe_sub hst, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  field_simp [hm]
  ring

private lemma uniformGrid_mem_Icc {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) (k : Fin (m + 2)) :
    uniformGrid s t m k ∈ Set.Icc s t :=
  ⟨by simpa only [uniformGrid_zero] using uniformGrid_mono s t m (Fin.zero_le k),
    by simpa only [uniformGrid_last hst] using uniformGrid_mono s t m (Fin.le_last k)⟩

/-- Elementary cubic Taylor remainder bound for `expRem α x a`. -/
private lemma norm_expRem_le (α x a : ℝ) (ha : 0 ≤ a) :
    ‖expRem α x a‖ ≤ (|α| ^ 3 / 2) * |x| * a + (α ^ 4 / 8) * a ^ 2 +
      4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) *
        Real.exp (|α| * |x| + α ^ 2 / 2 * a) := by
  let w : ℂ := I * α * x + ((α ^ 2 / 2 * a : ℝ) : ℂ)
  have hw_norm : ‖w‖ ≤ |α| * |x| + α ^ 2 / 2 * a := by
    calc ‖w‖
        ≤ ‖I * (α : ℂ) * (x : ℂ)‖ + ‖((α ^ 2 / 2 * a : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |α| * |x| + α ^ 2 / 2 * a := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (show 0 ≤ α ^ 2 / 2 * a by positivity)]
  have hsum3 : ∑ j ∈ Finset.range 3, w ^ j / j.factorial = 1 + w + w ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have halg : expRem α x a = (exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial) +
      (I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)) := by
    rw [hsum3]; dsimp only [expRem, w]; push_cast; ring_nf; simp [I_sq]; ring
  have hrem : ‖exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial‖ ≤
      4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) *
        Real.exp (|α| * |x| + α ^ 2 / 2 * a) := by
    have hcube : (|α| * |x| + α ^ 2 / 2 * a) ^ 3 ≤
        4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) := by
      have hu : 0 ≤ |α| * |x| := by positivity
      have hv : 0 ≤ α ^ 2 / 2 * a := by positivity
      have h3 : (|α| * |x| + α ^ 2 / 2 * a) ^ 3 ≤ 4 * ((|α| * |x|) ^ 3 + (α ^ 2 / 2 * a) ^ 3) := by
        nlinarith [sq_nonneg (|α| * |x| - α ^ 2 / 2 * a)]
      simpa only [mul_pow] using h3
    calc ‖exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial‖
        ≤ ‖w‖ ^ 3 * Real.exp ‖w‖ := Complex.norm_exp_sub_sum_le_norm_mul_exp w 3
      _ ≤ (|α| * |x| + α ^ 2 / 2 * a) ^ 3 * Real.exp (|α| * |x| + α ^ 2 / 2 * a) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw_norm 3)
            (Real.exp_le_exp.2 hw_norm) (Real.exp_pos _).le (by positivity)
      _ ≤ 4 * (|α| ^ 3 * |x| ^ 3 + (α ^ 2 / 2) ^ 3 * a ^ 3) *
            Real.exp (|α| * |x| + α ^ 2 / 2 * a) :=
          mul_le_mul_of_nonneg_right hcube (Real.exp_pos _).le
  have hmid : ‖I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)‖ ≤
      (|α| ^ 3 / 2) * |x| * a + (α ^ 4 / 8) * a ^ 2 := by
    calc ‖I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)‖
        ≤ ‖I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ)‖ + ‖((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = (|α| ^ 3 / 2) * |x| * a + (α ^ 4 / 8) * a ^ 2 := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg ha,
            abs_of_nonneg (show 0 ≤ α ^ 4 / 8 * a ^ 2 by positivity)]
  rw [halg]
  linarith [norm_add_le (exp w - ∑ j ∈ Finset.range 3, w ^ j / j.factorial)
    (I * ((α ^ 3 / 2 * x * a : ℝ) : ℂ) + ((α ^ 4 / 8 * a ^ 2 : ℝ) : ℂ))]

/-- Single-step cubic remainder bound in terms of mesh modulus `D` and step size `L / (m + 1)`. -/
private lemma norm_mul_expRem_step_le {α R L Mz D dx da : ℝ} {m : ℕ} (hL : 0 ≤ L) (hMz : 0 ≤ Mz)
    {z : ℂ} (hz : ‖z‖ ≤ Mz) (hdx : |dx| ≤ 2 * R) (hDx : |dx| ≤ D)
    (hda0 : 0 ≤ da) (hdaL : da ≤ L / (m + 1 : ℝ)) :
    let Ke : ℝ := Real.exp (2 * |α| * R + α ^ 2 / 2 * L)
    ‖z * expRem α dx da‖ ≤ Mz *
      ((|α| ^ 3 / 2) * (D * (L / (m + 1 : ℝ))) + (α ^ 4 / 8) * (L / (m + 1 : ℝ)) ^ 2 +
        4 * |α| ^ 3 * Ke * (D * dx ^ 2) + 4 * (α ^ 2 / 2) ^ 3 * Ke * (L / (m + 1 : ℝ)) ^ 3) := by
  intro Ke
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hDx
  have hda_le : da ≤ L := hdaL.trans (div_le_self hL (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  have hexp : Real.exp (|α| * |dx| + α ^ 2 / 2 * da) ≤ Ke := by
    refine Real.exp_le_exp.2 ?_
    have h1 : |α| * |dx| ≤ 2 * |α| * R :=
      (mul_le_mul_of_nonneg_left hdx (abs_nonneg _)).trans_eq (by ring)
    have h2 : α ^ 2 / 2 * da ≤ α ^ 2 / 2 * L := mul_le_mul_of_nonneg_left hda_le (by positivity)
    linarith
  have hcube : |dx| ^ 3 ≤ D * dx ^ 2 := by
    calc |dx| ^ 3 = |dx| * |dx| ^ 2 := by ring
      _ = |dx| * dx ^ 2 := by rw [sq_abs]
      _ ≤ D * dx ^ 2 := mul_le_mul_of_nonneg_right hDx (sq_nonneg _)
  have hstep := norm_expRem_le α dx da hda0
  rw [norm_mul]
  refine mul_le_mul hz ?_ (norm_nonneg _) hMz
  have hp1 : (|α| ^ 3 / 2) * |dx| * da ≤ (|α| ^ 3 / 2) * (D * (L / (m + 1 : ℝ))) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hDx hdaL hda0 hD0) (by positivity)
  have hp2 : (α ^ 4 / 8) * da ^ 2 ≤ (α ^ 4 / 8) * (L / (m + 1 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hda0 hdaL 2) (by positivity)
  have hp3 : 4 * (|α| ^ 3 * |dx| ^ 3 + (α ^ 2 / 2) ^ 3 * da ^ 3) *
      Real.exp (|α| * |dx| + α ^ 2 / 2 * da) ≤
      4 * |α| ^ 3 * Ke * (D * dx ^ 2) + 4 * (α ^ 2 / 2) ^ 3 * Ke * (L / (m + 1 : ℝ)) ^ 3 := by
    have hinner : |α| ^ 3 * |dx| ^ 3 + (α ^ 2 / 2) ^ 3 * da ^ 3 ≤
        |α| ^ 3 * (D * dx ^ 2) + (α ^ 2 / 2) ^ 3 * (L / (m + 1 : ℝ)) ^ 3 := by
      gcongr
    calc 4 * (|α| ^ 3 * |dx| ^ 3 + (α ^ 2 / 2) ^ 3 * da ^ 3) *
          Real.exp (|α| * |dx| + α ^ 2 / 2 * da)
        ≤ 4 * (|α| ^ 3 * (D * dx ^ 2) + (α ^ 2 / 2) ^ 3 * (L / (m + 1 : ℝ)) ^ 3) * Ke :=
          mul_le_mul (mul_le_mul_of_nonneg_left hinner (by norm_num))
            hexp (Real.exp_pos _).le (by positivity)
      _ = 4 * |α| ^ 3 * Ke * (D * dx ^ 2) + 4 * (α ^ 2 / 2) ^ 3 * Ke * (L / (m + 1 : ℝ)) ^ 3 := by
          ring
  linarith

/-- Summed pointwise bound on the cubic remainder along the `m`-th uniform grid. -/
private lemma norm_sum_expRem_le {α R L Mz : ℝ} {m : ℕ} (hL : 0 ≤ L) (hMz : 0 ≤ Mz)
    {z : Fin (m + 1) → ℂ} {dx da : Fin (m + 1) → ℝ}
    (hz : ∀ k, ‖z k‖ ≤ Mz) (hdx : ∀ k, |dx k| ≤ 2 * R)
    (hda : ∀ k, 0 ≤ da k ∧ da k ≤ L / (m + 1 : ℝ)) :
    let D : ℝ := Finset.univ.sup' Finset.univ_nonempty fun k : Fin (m + 1) ↦ |dx k|
    let S : ℝ := ∑ k : Fin (m + 1), dx k ^ 2
    let Ke : ℝ := Real.exp (2 * |α| * R + α ^ 2 / 2 * L)
    ‖∑ k : Fin (m + 1), z k * expRem α (dx k) (da k)‖ ≤
      Mz * ((|α| ^ 3 / 2 * L) * D + (α ^ 4 / 8 * L ^ 2) / (m + 1 : ℝ) +
        4 * |α| ^ 3 * Ke * (D * S) + 4 * (α ^ 2 / 2) ^ 3 * Ke * L ^ 3 / (m + 1 : ℝ) ^ 2) := by
  intro D S Ke
  have hmne : (m : ℝ) + 1 ≠ 0 := by positivity
  calc ‖∑ k : Fin (m + 1), z k * expRem α (dx k) (da k)‖
      ≤ ∑ k : Fin (m + 1), ‖z k * expRem α (dx k) (da k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin (m + 1), Mz *
          ((|α| ^ 3 / 2) * (D * (L / (m + 1 : ℝ))) + (α ^ 4 / 8) * (L / (m + 1 : ℝ)) ^ 2 +
            4 * |α| ^ 3 * Ke * (D * dx k ^ 2) +
            4 * (α ^ 2 / 2) ^ 3 * Ke * (L / (m + 1 : ℝ)) ^ 3) :=
        Finset.sum_le_sum fun k _ ↦ norm_mul_expRem_step_le hL hMz (hz k) (hdx k)
          (Finset.le_sup' (f := fun j : Fin (m + 1) ↦ |dx j|) (Finset.mem_univ k))
          (hda k).1 (hda k).2
    _ = Mz * ((|α| ^ 3 / 2 * L) * D + (α ^ 4 / 8 * L ^ 2) / (m + 1 : ℝ) +
          4 * |α| ^ 3 * Ke * (D * S) + 4 * (α ^ 2 / 2) ^ 3 * Ke * L ^ 3 / (m + 1 : ℝ) ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        push_cast; field_simp [hmne]; ring

private lemma tendsto_partition_err {α L Mz Ke B C : ℝ} {d1 d2 : ℕ → ℝ}
    (hd1 : Tendsto d1 atTop (𝓝 0)) (hd2 : Tendsto d2 atTop (𝓝 0)) :
    Tendsto (fun m : ℕ ↦
      Mz * ((|α| ^ 3 / 2 * L) * d1 m + (α ^ 4 / 8 * L ^ 2 * C) / (m + 1 : ℝ) +
        4 * |α| ^ 3 * Ke * Real.sqrt (d2 m * B) +
        4 * (α ^ 2 / 2) ^ 3 * Ke * (L ^ 3 * C) / (m + 1 : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun m : ℕ ↦ (1 : ℝ) / (m + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht1 : Tendsto (fun m ↦ (|α| ^ 3 / 2 * L) * d1 m) atTop (𝓝 0) := by
    simpa using hd1.const_mul (|α| ^ 3 / 2 * L)
  have ht2 : Tendsto (fun m : ℕ ↦ (α ^ 4 / 8 * L ^ 2 * C) / (m + 1 : ℝ)) atTop (𝓝 0) := by
    have h := hinv.const_mul (α ^ 4 / 8 * L ^ 2 * C)
    rw [mul_zero] at h
    exact h.congr fun m ↦ by ring
  have ht3 : Tendsto (fun m ↦ 4 * |α| ^ 3 * Ke * Real.sqrt (d2 m * B)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun m ↦ d2 m * B) atTop (𝓝 0) := by simpa using hd2.mul_const B
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hmul).const_mul (4 * |α| ^ 3 * Ke)
  have ht4 : Tendsto (fun m : ℕ ↦
      4 * (α ^ 2 / 2) ^ 3 * Ke * (L ^ 3 * C) / (m + 1 : ℝ) ^ 2) atTop (𝓝 0) := by
    have h := (hinv.pow 2).const_mul (4 * (α ^ 2 / 2) ^ 3 * Ke * (L ^ 3 * C))
    rw [zero_pow two_ne_zero, mul_zero] at h
    exact h.congr fun m ↦ by rw [one_div, inv_pow, ← div_eq_mul_inv]
  simpa using (((ht1.add ht2).add ht3).add ht4).const_mul Mz

private lemma ae_norm_expProc_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X A : ℝ≥0 → Ω → ℝ} {c : ℝ} (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) (u : ℝ≥0) :
    ∀ᵐ ω ∂P, ‖expProc X A α u ω‖ ≤ Real.exp (α ^ 2 / 2 * (c * (u : ℝ))) := by
  filter_upwards [hA0, hA_step 0 u bot_le] with ω h0 hA
  have hAr : A u ω ≤ c * (u : ℝ) := by simpa [h0] using hA.2
  have heq : expProc X A α u ω =
      exp (I * ((α * X u ω : ℝ) : ℂ) + ((α ^ 2 / 2 * A u ω : ℝ) : ℂ)) := by
    dsimp only [expProc]; congr 1; push_cast; ring
  rw [heq, norm_exp_I_mul_add_ofReal]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hAr (by positivity))

private lemma ae_norm_sum_expRem_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ} (hc : 0 ≤ c) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    ∀ᵐ ω ∂P, ‖∑ k : Fin (m + 1), expProc X A α (uniformGrid s t m k.castSucc) ω *
        expRem α (X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω)
          (A (uniformGrid s t m k.succ) ω - A (uniformGrid s t m k.castSucc) ω)‖ ≤
      Real.exp (α ^ 2 / 2 * (c * (t : ℝ))) *
        ((|α| ^ 3 / 2 * (c * ((t : ℝ) - s))) * maxInc X s t m ω +
          (α ^ 4 / 8 * (c * ((t : ℝ) - s)) ^ 2) / (m + 1 : ℝ) +
          4 * |α| ^ 3 * Real.exp (2 * |α| * R + α ^ 2 / 2 * (c * ((t : ℝ) - s))) *
            (maxInc X s t m ω *
              ∑ k : Fin (m + 1),
                (X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω) ^ 2) +
          4 * (α ^ 2 / 2) ^ 3 * Real.exp (2 * |α| * R + α ^ 2 / 2 * (c * ((t : ℝ) - s))) *
            (c * ((t : ℝ) - s)) ^ 3 / (m + 1 : ℝ) ^ 2) := by
  have hL : 0 ≤ c * ((t : ℝ) - s) := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  have hallX := ae_all_iff.2 fun k : Fin (m + 1) ↦
    ae_abs_increment_le hXR (uniformGrid s t m k.castSucc) (uniformGrid s t m k.succ)
  have hallA : ∀ᵐ ω ∂P, ∀ k : Fin (m + 1),
      0 ≤ A (uniformGrid s t m k.succ) ω - A (uniformGrid s t m k.castSucc) ω ∧
        A (uniformGrid s t m k.succ) ω - A (uniformGrid s t m k.castSucc) ω ≤
          c * ((t : ℝ) - s) / (m + 1 : ℝ) :=
    ae_all_iff.2 fun k ↦ (hA_step _ _ (uniformGrid_mono s t m (Fin.castSucc_le_succ k))).mono
      fun ω hω ↦ by
        rw [uniformGrid_step hst m k] at hω
        exact ⟨hω.1, by simpa only [mul_div_assoc] using hω.2⟩
  have hallZ : ∀ᵐ ω ∂P, ∀ k : Fin (m + 1),
      ‖expProc X A α (uniformGrid s t m k.castSucc) ω‖ ≤ Real.exp (α ^ 2 / 2 * (c * (t : ℝ))) :=
    ae_all_iff.2 fun k ↦ (ae_norm_expProc_le (X := X) hA0 hA_step α _).mono fun ω hω ↦
      hω.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (NNReal.coe_le_coe.2 (uniformGrid_mem_Icc hst m k.castSucc).2) hc) (by positivity)))
  filter_upwards [hallX, hallA, hallZ] with ω hXω hAω hZω
  exact norm_sum_expRem_le hL (Real.exp_pos _).le hZω hXω hAω

end PureHelpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ}

section Orthogonality

/-- A bounded `ℱ s`-measurable real weight is orthogonal to any later martingale increment. -/
private lemma integral_mul_sub_eq_zero_real {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    {s t : ℝ≥0} (hst : s ≤ t) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ s] g) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    ∫ ω, g ω * (M t ω - M s ω) ∂P = 0 := by
  have hsub_int : Integrable (fun ω ↦ M t ω - M s ω) P := (hM.integrable t).sub (hM.integrable s)
  have hmul : Integrable (g * (M t - M s)) P :=
    hsub_int.bdd_mul (hg.mono (ℱ.le s)).aestronglyMeasurable
      (hb.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])
  have hcond : P[g * (M t - M s) | ℱ s] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    have hpull := condExp_mul_of_stronglyMeasurable_left hg hmul hsub_int
    have hdiff := condExp_sub (m := ℱ s) (hM.integrable t) (hM.integrable s)
    filter_upwards [hpull, hdiff, hM.condExp_ae_eq hst] with ω hp hd hm
    simp only [Pi.mul_apply, Pi.sub_apply] at hp hd
    rw [hp, hd, hm, condExp_of_stronglyMeasurable (ℱ.le s) (hM.stronglyAdapted s)
      (hM.integrable s)]
    simp
  have hzero : ∫ ω, (g * (M t - M s)) ω ∂P = 0 := by
    rw [← integral_condExp (ℱ.le s), integral_congr_ae hcond, integral_zero]
  simpa only [Pi.mul_apply, Pi.sub_apply] using hzero

/-- Complex-valued set-integral version of martingale increment orthogonality. -/
private lemma setIntegral_mul_sub_eq_zero_complex {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    {s t : ℝ≥0} (hst : s ≤ t) {E : Set Ω} (hE : MeasurableSet[ℱ s] E)
    {Z : Ω → ℂ} (hZ : StronglyMeasurable[ℱ s] Z) {C : ℝ} (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ∫ ω in E, Z ω * ((M t ω - M s ω : ℝ) : ℂ) ∂P = 0 := by
  have hre : StronglyMeasurable[ℱ s] (E.indicator fun ω ↦ (Z ω).re) :=
    (Complex.continuous_re.comp_stronglyMeasurable hZ).indicator hE
  have him : StronglyMeasurable[ℱ s] (E.indicator fun ω ↦ (Z ω).im) :=
    (Complex.continuous_im.comp_stronglyMeasurable hZ).indicator hE
  have hbre : ∀ᵐ ω ∂P, |E.indicator (fun ω ↦ (Z ω).re) ω| ≤ max C 0 := by
    filter_upwards [hb] with ω hω
    by_cases hωE : ω ∈ E
    · simpa only [Set.indicator_of_mem hωE] using
        (Complex.abs_re_le_norm (Z ω)).trans (hω.trans (le_max_left C 0))
    · simp [Set.indicator_of_notMem hωE]
  have hbim : ∀ᵐ ω ∂P, |E.indicator (fun ω ↦ (Z ω).im) ω| ≤ max C 0 := by
    filter_upwards [hb] with ω hω
    by_cases hωE : ω ∈ E
    · simpa only [Set.indicator_of_mem hωE] using
        (Complex.abs_im_le_norm (Z ω)).trans (hω.trans (le_max_left C 0))
    · simp [Set.indicator_of_notMem hωE]
  have hsub : Integrable (fun ω ↦ M t ω - M s ω) P := (hM.integrable t).sub (hM.integrable s)
  have hint_re : Integrable (fun ω ↦ E.indicator (fun ω ↦ (Z ω).re) ω * (M t ω - M s ω)) P :=
    hsub.bdd_mul (hre.mono (ℱ.le s)).aestronglyMeasurable
      (hbre.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])
  have hint_im : Integrable (fun ω ↦ E.indicator (fun ω ↦ (Z ω).im) ω * (M t ω - M s ω)) P :=
    hsub.bdd_mul (him.mono (ℱ.le s)).aestronglyMeasurable
      (hbim.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])
  have hsplit : ∀ ω, E.indicator (fun ω ↦ Z ω * ((M t ω - M s ω : ℝ) : ℂ)) ω =
      ((E.indicator (fun ω ↦ (Z ω).re) ω * (M t ω - M s ω) : ℝ) : ℂ) +
        I * ((E.indicator (fun ω ↦ (Z ω).im) ω * (M t ω - M s ω) : ℝ) : ℂ) := fun ω ↦ by
    by_cases hωE : ω ∈ E
    · simp only [Set.indicator_of_mem hωE]; apply Complex.ext <;> simp
    · simp [Set.indicator_of_notMem hωE]
  rw [← integral_indicator (ℱ.le s E hE)]
  simp_rw [hsplit, ← Complex.ofRealCLM_apply]
  rw [integral_add (Complex.ofRealCLM.integrable_comp hint_re)
      ((Complex.ofRealCLM.integrable_comp hint_im).const_mul I),
    integral_const_mul,
    Complex.ofRealCLM.integral_comp_comm hint_re,
    Complex.ofRealCLM.integral_comp_comm hint_im,
    integral_mul_sub_eq_zero_real hM hst hre hbre,
    integral_mul_sub_eq_zero_real hM hst him hbim]
  simp

/-- If `X` is a bounded martingale and `X ^ 2 - A` is a martingale, then any bounded
`ℱ s`-measurable real weight is orthogonal to `(X t - X s) ^ 2 - (A t - A s)`. -/
private lemma integral_mul_sq_sub_eq_zero_real {X A : ℝ≥0 → Ω → ℝ} {R : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) {s t : ℝ≥0} (hst : s ≤ t)
    {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ s] g) {C : ℝ} (hb : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    ∫ ω, g ω * ((X t ω - X s ω) ^ 2 - (A t ω - A s ω)) ∂P = 0 := by
  have h2 : StronglyMeasurable[ℱ s] (fun ω ↦ 2 * g ω * X s ω) :=
    (stronglyMeasurable_const.mul hg).mul (hX.stronglyAdapted s)
  have hb2 : ∀ᵐ ω ∂P, |2 * g ω * X s ω| ≤ 2 * max C 0 * max R 0 := by
    filter_upwards [hb, hXR s] with ω hC hR
    have hC' : |g ω| ≤ max C 0 := hC.trans (le_max_left C 0)
    have hR' : |X s ω| ≤ max R 0 := hR.trans (le_max_left R 0)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
  have hint1 : Integrable (fun ω ↦ g ω * ((X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω))) P :=
    ((hQ.integrable t).sub (hQ.integrable s)).bdd_mul (hg.mono (ℱ.le s)).aestronglyMeasurable
      (hb.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])
  have hint2 : Integrable (fun ω ↦ (2 * g ω * X s ω) * (X t ω - X s ω)) P :=
    ((hX.integrable t).sub (hX.integrable s)).bdd_mul (h2.mono (ℱ.le s)).aestronglyMeasurable
      (hb2.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])
  have halg : ∀ ω, g ω * ((X t ω - X s ω) ^ 2 - (A t ω - A s ω)) =
      g ω * ((X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω)) -
        (2 * g ω * X s ω) * (X t ω - X s ω) := fun ω ↦ by ring
  simp_rw [halg]
  rw [integral_sub hint1 hint2, integral_mul_sub_eq_zero_real hQ hst hg hb,
    integral_mul_sub_eq_zero_real hX hst h2 hb2, sub_self]

/-- Complex-valued set-integral orthogonality for `(A t - A s) - (X t - X s) ^ 2`. -/
private lemma setIntegral_mul_sq_sub_eq_zero_complex {X A : ℝ≥0 → Ω → ℝ} {R : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) {s t : ℝ≥0} (hst : s ≤ t)
    {E : Set Ω} (hE : MeasurableSet[ℱ s] E) {Z : Ω → ℂ} (hZ : StronglyMeasurable[ℱ s] Z)
    {C : ℝ} (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ∫ ω in E, Z ω * (((A t ω - A s ω) - (X t ω - X s ω) ^ 2 : ℝ) : ℂ) ∂P = 0 := by
  have halg : ∀ ω, Z ω * (((A t ω - A s ω) - (X t ω - X s ω) ^ 2 : ℝ) : ℂ) =
      -(Z ω * ((((X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω) : ℝ) : ℂ))) +
        (2 * Z ω * (X s ω : ℂ)) * ((X t ω - X s ω : ℝ) : ℂ) := fun ω ↦ by push_cast; ring
  have h2Z : StronglyMeasurable[ℱ s] (fun ω ↦ 2 * Z ω * (X s ω : ℂ)) :=
    (stronglyMeasurable_const.mul hZ).mul
      (Complex.continuous_ofReal.comp_stronglyMeasurable (hX.stronglyAdapted s))
  have hb2Z : ∀ᵐ ω ∂P, ‖2 * Z ω * (X s ω : ℂ)‖ ≤ 2 * max C 0 * max R 0 := by
    filter_upwards [hb, hXR s] with ω hC hR
    have hC' : ‖Z ω‖ ≤ max C 0 := hC.trans (le_max_left C 0)
    have hR' : |X s ω| ≤ max R 0 := hR.trans (le_max_left R 0)
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have hint1 : IntegrableOn
      (fun ω ↦ -(Z ω * ((((X t ω ^ 2 - A t ω) - (X s ω ^ 2 - A s ω) : ℝ) : ℂ)))) E P :=
    ((Complex.ofRealCLM.integrable_comp ((hQ.integrable t).sub (hQ.integrable s))).bdd_mul
      (hZ.mono (ℱ.le s)).aestronglyMeasurable hb).neg.integrableOn
  have hint2 : IntegrableOn
      (fun ω ↦ (2 * Z ω * (X s ω : ℂ)) * ((X t ω - X s ω : ℝ) : ℂ)) E P :=
    ((Complex.ofRealCLM.integrable_comp ((hX.integrable t).sub (hX.integrable s))).bdd_mul
      (h2Z.mono (ℱ.le s)).aestronglyMeasurable hb2Z).integrableOn
  simp_rw [halg]
  rw [integral_add hint1 hint2, integral_neg,
    setIntegral_mul_sub_eq_zero_complex hQ hst hE hZ hb,
    setIntegral_mul_sub_eq_zero_complex hX hst hE h2Z hb2Z]
  simp

end Orthogonality

section QuadraticSumBound

private lemma memLp_increment_sq {X : ℝ≥0 → Ω → ℝ} {R : ℝ}
    (hX : StronglyAdapted ℱ X) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (u v : ℝ≥0) :
    MemLp (fun ω ↦ (X v ω - X u ω) ^ 2) 2 P := by
  have hsm : AEStronglyMeasurable (fun ω ↦ (X v ω - X u ω) ^ 2) P :=
    (((hX v).mono (ℱ.le v)).sub ((hX u).mono (ℱ.le u))).aestronglyMeasurable.pow 2
  refine MemLp.of_bound hsm ((2 * R) ^ 2) ?_
  filter_upwards [ae_abs_increment_le hXR u v] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hω 2

private lemma integrable_increment_bracket {X A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) :
    Integrable (fun ω ↦ A v ω - A u ω) P := by
  have hA_sm (w : ℝ≥0) : AEStronglyMeasurable (A w) P := by
    have h1 : AEStronglyMeasurable (fun ω ↦ X w ω ^ 2) P :=
      ((hX.stronglyAdapted w).mono (ℱ.le w)).aestronglyMeasurable.pow 2
    have h2 : AEStronglyMeasurable (fun ω ↦ X w ω ^ 2 - A w ω) P :=
      ((hQ.stronglyAdapted w).mono (ℱ.le w)).aestronglyMeasurable
    have heq : A w = (fun ω ↦ X w ω ^ 2) - fun ω ↦ X w ω ^ 2 - A w ω := by ext ω; simp
    rw [heq]
    exact h1.sub h2
  refine (integrable_const (c * ((v : ℝ) - u))).mono' ((hA_sm v).sub (hA_sm u)) ?_
  filter_upwards [hA_step u v huv] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
  exact hω.2

/-- First-moment bound for discrete quadratic sums along a partition `g` of `[s, t]`. -/
private lemma integral_sum_sq_le {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) {s t : ℝ≥0} (hs : g 0 = s)
    (ht : g (Fin.last n) = t) :
    ∫ ω, (∑ k : Fin n, (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2) ∂P ≤
      c * ((t : ℝ) - s) * P.real Set.univ := by
  have hsq_int (k : Fin n) : Integrable (fun ω ↦ (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2) P :=
    (memLp_increment_sq hX.stronglyAdapted hXR (g k.castSucc) (g k.succ)).integrable one_le_two
  have hterm (k : Fin n) :
      ∫ ω, (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2 ∂P ≤
        c * ((g k.succ : ℝ) - g k.castSucc) * P.real Set.univ := by
    have hstep := hg (Fin.castSucc_le_succ k)
    have hA_int := integrable_increment_bracket hX hQ hA_step hstep
    have h0 := integral_mul_sq_sub_eq_zero_real hX hQ hXR hstep
      (g := fun _ ↦ (1 : ℝ)) stronglyMeasurable_const (C := 1) (ae_of_all P fun _ ↦ by norm_num)
    simp only [one_mul] at h0
    rw [integral_sub (hsq_int k) hA_int, sub_eq_zero] at h0
    rw [h0]
    calc ∫ ω, (A (g k.succ) ω - A (g k.castSucc) ω) ∂P
        ≤ ∫ _, c * ((g k.succ : ℝ) - g k.castSucc) ∂P :=
          integral_mono_ae hA_int (integrable_const _) ((hA_step _ _ hstep).mono fun _ hω ↦ hω.2)
      _ = c * ((g k.succ : ℝ) - g k.castSucc) * P.real Set.univ := by
          rw [integral_const, smul_eq_mul, mul_comm]
  calc ∫ ω, (∑ k : Fin n, (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2) ∂P
      = ∑ k : Fin n, ∫ ω, (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2 ∂P :=
        integral_finsetSum Finset.univ fun k _ ↦ hsq_int k
    _ ≤ ∑ k : Fin n, c * ((g k.succ : ℝ) - g k.castSucc) * P.real Set.univ :=
        Finset.sum_le_sum fun k _ ↦ hterm k
    _ = c * (∑ k : Fin n, ((g k.succ : ℝ) - g k.castSucc)) * P.real Set.univ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = c * ((t : ℝ) - s) * P.real Set.univ := by
        rw [Fin.sum_univ_succ_sub_castSucc (fun i ↦ (g i : ℝ)), hs, ht]

/-- For non-overlapping intervals `u₁ ≤ v₁ ≤ u₂ ≤ v₂`, the cross-product of squared martingale
increments has the same expectation as pairing with the later bracket increment. -/
private lemma integral_sq_mul_sq_eq_mul_bracket {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u₁ v₁ u₂ v₂ : ℝ≥0} (h1 : u₁ ≤ v₁) (h12 : v₁ ≤ u₂) (h2 : u₂ ≤ v₂) :
    ∫ ω, (X v₁ ω - X u₁ ω) ^ 2 * (X v₂ ω - X u₂ ω) ^ 2 ∂P =
      ∫ ω, (X v₁ ω - X u₁ ω) ^ 2 * (A v₂ ω - A u₂ ω) ∂P := by
  have hsm : StronglyMeasurable[ℱ u₂] (fun ω ↦ (X v₁ ω - X u₁ ω) ^ 2) :=
    (((hX.stronglyAdapted v₁).mono (ℱ.mono h12)).sub
      ((hX.stronglyAdapted u₁).mono (ℱ.mono (h1.trans h12)))).pow 2
  have hbd : ∀ᵐ ω ∂P, |(X v₁ ω - X u₁ ω) ^ 2| ≤ (2 * R) ^ 2 := by
    filter_upwards [ae_abs_increment_le hXR u₁ v₁] with ω hω
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have h0 := integral_mul_sq_sub_eq_zero_real hX hQ hXR h2 hsm hbd
  have hsq2 : Integrable (fun ω ↦ (X v₂ ω - X u₂ ω) ^ 2) P :=
    (memLp_increment_sq hX.stronglyAdapted hXR u₂ v₂).integrable one_le_two
  have hA2 := integrable_increment_bracket hX hQ hA_step h2
  have hbd' : ∀ᵐ ω ∂P, ‖(X v₁ ω - X u₁ ω) ^ 2‖ ≤ (2 * R) ^ 2 :=
    hbd.mono fun _ h ↦ by rwa [Real.norm_eq_abs]
  have halg : ∀ ω, (X v₁ ω - X u₁ ω) ^ 2 * ((X v₂ ω - X u₂ ω) ^ 2 - (A v₂ ω - A u₂ ω)) =
      (X v₁ ω - X u₁ ω) ^ 2 * (X v₂ ω - X u₂ ω) ^ 2 -
        (X v₁ ω - X u₁ ω) ^ 2 * (A v₂ ω - A u₂ ω) := fun ω ↦ by ring
  simp_rw [halg] at h0
  rwa [integral_sub (hsq2.bdd_mul (hsm.mono (ℱ.le u₂)).aestronglyMeasurable hbd')
    (hA2.bdd_mul (hsm.mono (ℱ.le u₂)).aestronglyMeasurable hbd'), sub_eq_zero] at h0

/-- Off-diagonal contribution to the second moment of discrete quadratic sums. -/
private lemma sum_lt_integral_sq_mul_sq_le {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ} (hc : 0 ≤ c)
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) {s t : ℝ≥0} (hs : g 0 = s)
    (ht : g (Fin.last n) = t) :
    let ΔX : Fin n → Ω → ℝ := fun k ω ↦ X (g k.succ) ω - X (g k.castSucc) ω
    ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (j < ·),
      ∫ ω, ΔX j ω ^ 2 * ΔX k ω ^ 2 ∂P ≤ (c * ((t : ℝ) - s)) ^ 2 * P.real Set.univ := by
  intro ΔX
  let ΔA : Fin n → Ω → ℝ := fun k ω ↦ A (g k.succ) ω - A (g k.castSucc) ω
  have hsq_int (k : Fin n) : Integrable (fun ω ↦ ΔX k ω ^ 2) P :=
    (memLp_increment_sq hX.stronglyAdapted hXR (g k.castSucc) (g k.succ)).integrable one_le_two
  have hsq_bd (k : Fin n) : ∀ᵐ ω ∂P, ‖ΔX k ω ^ 2‖ ≤ (2 * R) ^ 2 := by
    filter_upwards [ae_abs_increment_le hXR (g k.castSucc) (g k.succ)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hΔA_int (k : Fin n) : Integrable (ΔA k) P :=
    integrable_increment_bracket hX hQ hA_step (hg (Fin.castSucc_le_succ k))
  have hrow (j : Fin n) : ∑ k ∈ Finset.univ.filter (j < ·), ∫ ω, ΔX j ω ^ 2 * ΔX k ω ^ 2 ∂P ≤
      c * ((t : ℝ) - s) * ∫ ω, ΔX j ω ^ 2 ∂P := by
    have hsum_eq : ∑ k ∈ Finset.univ.filter (j < ·), ∫ ω, ΔX j ω ^ 2 * ΔX k ω ^ 2 ∂P =
        ∫ ω, ΔX j ω ^ 2 * (∑ k ∈ Finset.univ.filter (j < ·), ΔA k ω) ∂P := by
      rw [Finset.sum_congr rfl fun k hk ↦ integral_sq_mul_sq_eq_mul_bracket hX hQ hXR hA_step
            (hg (Fin.castSucc_le_succ j))
            (hg (Fin.succ_le_castSucc_iff.2 (Finset.mem_filter.1 hk).2))
            (hg (Fin.castSucc_le_succ k)),
        ← integral_finsetSum _ fun k _ ↦
            (hΔA_int k).bdd_mul (hsq_int j).aestronglyMeasurable (hsq_bd j)]
      exact integral_congr_ae (ae_of_all P fun ω ↦ (Finset.mul_sum ..).symm)
    rw [hsum_eq, ← integral_const_mul]
    refine integral_mono_ae ((integrable_finsetSum _ fun k _ ↦ hΔA_int k).bdd_mul
        (hsq_int j).aestronglyMeasurable (hsq_bd j)) ((hsq_int j).const_mul _) ?_
    have hall := ae_all_iff.2 fun k : Fin n ↦ hA_step _ _ (hg (Fin.castSucc_le_succ k))
    filter_upwards [hall] with ω hω
    have hle_sum : ∑ k ∈ Finset.univ.filter (j < ·), ΔA k ω ≤ c * ((t : ℝ) - s) :=
      calc ∑ k ∈ Finset.univ.filter (j < ·), ΔA k ω
          ≤ ∑ k : Fin n, ΔA k ω := Finset.sum_le_univ_sum_of_nonneg fun k ↦ (hω k).1
        _ ≤ ∑ k : Fin n, c * ((g k.succ : ℝ) - g k.castSucc) :=
            Finset.sum_le_sum fun k _ ↦ (hω k).2
        _ = c * ((t : ℝ) - s) := by
            rw [← Finset.mul_sum, Fin.sum_univ_succ_sub_castSucc (fun i ↦ (g i : ℝ)), hs, ht]
    rw [mul_comm (c * ((t : ℝ) - s))]
    exact mul_le_mul_of_nonneg_left hle_sum (sq_nonneg _)
  have hst : (s : ℝ) ≤ t := by exact_mod_cast (hs ▸ ht ▸ hg (Fin.zero_le (Fin.last n)))
  calc ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (j < ·), ∫ ω, ΔX j ω ^ 2 * ΔX k ω ^ 2 ∂P
      ≤ ∑ j : Fin n, c * ((t : ℝ) - s) * ∫ ω, ΔX j ω ^ 2 ∂P := Finset.sum_le_sum fun j _ ↦ hrow j
    _ = c * ((t : ℝ) - s) * ∫ ω, (∑ k : Fin n, ΔX k ω ^ 2) ∂P := by
        rw [← Finset.mul_sum, ← integral_finsetSum Finset.univ fun k _ ↦ hsq_int k]
    _ ≤ c * ((t : ℝ) - s) * (c * ((t : ℝ) - s) * P.real Set.univ) :=
        mul_le_mul_of_nonneg_left (integral_sum_sq_le hX hQ hXR hA_step hg hs ht)
          (mul_nonneg hc (sub_nonneg.2 hst))
    _ = (c * ((t : ℝ) - s)) ^ 2 * P.real Set.univ := by ring

/-- Uniform `L²` bound on discrete quadratic sums of a bounded martingale with Lipschitz bracket. -/
private lemma integral_sq_sum_sq_le {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ} (hc : 0 ≤ c)
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) {s t : ℝ≥0} (hs : g 0 = s)
    (ht : g (Fin.last n) = t) :
    let S : Ω → ℝ := fun ω ↦ ∑ k : Fin n, (X (g k.succ) ω - X (g k.castSucc) ω) ^ 2
    ∫ ω, S ω ^ 2 ∂P ≤
      (4 * R ^ 2 * (c * ((t : ℝ) - s)) + 2 * (c * ((t : ℝ) - s)) ^ 2) * P.real Set.univ := by
  intro S
  let ΔX : Fin n → Ω → ℝ := fun k ω ↦ X (g k.succ) ω - X (g k.castSucc) ω
  have hsq_int (k : Fin n) : Integrable (fun ω ↦ ΔX k ω ^ 2) P :=
    (memLp_increment_sq hX.stronglyAdapted hXR (g k.castSucc) (g k.succ)).integrable one_le_two
  have hsq_bd (k : Fin n) : ∀ᵐ ω ∂P, ‖ΔX k ω ^ 2‖ ≤ (2 * R) ^ 2 := by
    filter_upwards [ae_abs_increment_le hXR (g k.castSucc) (g k.succ)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hmul_int (j k : Fin n) : Integrable (fun ω ↦ ΔX j ω ^ 2 * ΔX k ω ^ 2) P :=
    (hsq_int k).bdd_mul (hsq_int j).aestronglyMeasurable (hsq_bd j)
  have hdiag : ∑ j : Fin n, ∫ ω, ΔX j ω ^ 2 * ΔX j ω ^ 2 ∂P ≤
      4 * R ^ 2 * (c * ((t : ℝ) - s)) * P.real Set.univ := by
    have hstep (j : Fin n) : ∫ ω, ΔX j ω ^ 2 * ΔX j ω ^ 2 ∂P ≤
        4 * R ^ 2 * ∫ ω, ΔX j ω ^ 2 ∂P := by
      rw [← integral_const_mul]
      refine integral_mono_ae (hmul_int j j) ((hsq_int j).const_mul _) ?_
      filter_upwards [hsq_bd j] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hω
      exact mul_le_mul_of_nonneg_right (hω.trans_eq (by ring)) (sq_nonneg _)
    calc ∑ j : Fin n, ∫ ω, ΔX j ω ^ 2 * ΔX j ω ^ 2 ∂P
        ≤ ∑ j : Fin n, 4 * R ^ 2 * ∫ ω, ΔX j ω ^ 2 ∂P := Finset.sum_le_sum fun j _ ↦ hstep j
      _ = 4 * R ^ 2 * ∫ ω, S ω ∂P := by
          rw [← Finset.mul_sum, ← integral_finsetSum Finset.univ fun k _ ↦ hsq_int k]
      _ ≤ 4 * R ^ 2 * (c * ((t : ℝ) - s) * P.real Set.univ) :=
          mul_le_mul_of_nonneg_left (integral_sum_sq_le hX hQ hXR hA_step hg hs ht) (by positivity)
      _ = 4 * R ^ 2 * (c * ((t : ℝ) - s)) * P.real Set.univ := by ring
  have hsq : ∀ ω, S ω ^ 2 = ∑ j : Fin n, ∑ k : Fin n, ΔX j ω ^ 2 * ΔX k ω ^ 2 := fun ω ↦ by
    rw [sq, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ ↦ Finset.mul_sum ..
  have hdecomp : ∫ ω, S ω ^ 2 ∂P =
      ∑ j : Fin n, ∫ ω, ΔX j ω ^ 2 * ΔX j ω ^ 2 ∂P +
        2 * ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (j < ·),
          ∫ ω, ΔX j ω ^ 2 * ΔX k ω ^ 2 ∂P := by
    simp_rw [hsq]
    rw [integral_finsetSum Finset.univ fun j _ ↦
      integrable_finsetSum Finset.univ fun k _ ↦ hmul_int j k]
    simp_rw [integral_finsetSum Finset.univ fun k _ ↦ hmul_int _ k]
    exact sum_sq_symm_eq_diag_add_two_mul_lt fun j k ↦ by simp_rw [mul_comm (ΔX j _ ^ 2)]
  have hoff := sum_lt_integral_sq_mul_sq_le hc hX hQ hXR hA_step hg hs ht
  rw [hdecomp]; linarith

end QuadraticSumBound

section ModulusAndPartition

/-- Maximum increment of a bounded process on a uniform grid lies in `L²`. -/
private lemma memLp_maxInc {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (hX : StronglyAdapted ℱ X)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (s t : ℝ≥0) (m : ℕ) :
    MemLp (maxInc X s t m) 2 P := by
  have hcomp (k : Fin (m + 1)) : StronglyMeasurable (fun ω ↦
      |X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω|) :=
    (((hX (uniformGrid s t m k.succ)).mono (ℱ.le _)).sub
      ((hX (uniformGrid s t m k.castSucc)).mono (ℱ.le _))).norm
  refine MemLp.of_bound
    (stronglyMeasurable_finsetSup' Finset.univ_nonempty fun k _ ↦ hcomp k).aestronglyMeasurable
    (2 * R) ?_
  filter_upwards [ae_all_iff.2 fun k : Fin (m + 1) ↦
    ae_abs_increment_le hXR (uniformGrid s t m k.castSucc) (uniformGrid s t m k.succ)] with ω hω
  dsimp only [maxInc]
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (abs_nonneg _)
    (Finset.le_sup' (f := fun k : Fin (m + 1) ↦
      |X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω|) (Finset.mem_univ 0)))]
  exact Finset.sup'_le _ _ fun k _ ↦ hω k

/-- Maximum increment of a continuous bounded process on uniform partitions of `[s, t]` tends to
zero in `L¹` and `L²`. -/
private lemma tendsto_integral_maxInc_and_sq {X : ℝ≥0 → Ω → ℝ} {R : ℝ}
    (hX : StronglyAdapted ℱ X) (hcont : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun m ↦ ∫ ω, maxInc X s t m ω ∂P) atTop (𝓝 0) ∧
      Tendsto (fun m ↦ ∫ ω, maxInc X s t m ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hD_sm (m : ℕ) : AEStronglyMeasurable (maxInc X s t m) P :=
    (memLp_maxInc hX hXR s t m).aestronglyMeasurable
  have hD_bd (m : ℕ) : ∀ᵐ ω ∂P, 0 ≤ maxInc X s t m ω ∧ maxInc X s t m ω ≤ 2 * R := by
    filter_upwards [ae_all_iff.2 fun k : Fin (m + 1) ↦
      ae_abs_increment_le hXR (uniformGrid s t m k.castSucc) (uniformGrid s t m k.succ)] with ω hω
    exact ⟨le_trans (abs_nonneg _) (Finset.le_sup' (f := fun k : Fin (m + 1) ↦
        |X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω|) (Finset.mem_univ 0)),
      Finset.sup'_le _ _ fun k _ ↦ hω k⟩
  have hD_lim : ∀ᵐ ω ∂P, Tendsto (fun m ↦ maxInc X s t m ω) atTop (𝓝 0) := by
    filter_upwards [hcont] with ω hω
    have huc := (isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous hω.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδ_prop⟩ := huc ε hε
    have hstep : Tendsto (fun m : ℕ ↦ ((t : ℝ) - s) / (m + 1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((t : ℝ) - s)
      rw [mul_zero] at h
      exact h.congr fun m ↦ by ring
    obtain ⟨N, hN⟩ := (hstep.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
    refine ⟨N, fun m hm ↦ ?_⟩
    have hD_nonneg : 0 ≤ maxInc X s t m ω := le_trans (abs_nonneg _)
      (Finset.le_sup' (f := fun k : Fin (m + 1) ↦
        |X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω|) (Finset.mem_univ 0))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hD_nonneg]
    refine (Finset.sup'_lt_iff Finset.univ_nonempty).2 fun k _ ↦ ?_
    have hdist : dist (uniformGrid s t m k.succ) (uniformGrid s t m k.castSucc) < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2
        (NNReal.coe_le_coe.2 (uniformGrid_mono s t m (Fin.castSucc_le_succ k)))),
        uniformGrid_step hst m k]
      exact hN m hm
    simpa [Real.dist_eq] using hδ_prop _ (uniformGrid_mem_Icc hst m k.succ)
      _ (uniformGrid_mem_Icc hst m k.castSucc) hdist
  constructor
  · simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * R) hD_sm
      (integrable_const (2 * R))
      (fun m ↦ (hD_bd m).mono fun ω hω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2)
      hD_lim
  · have h2 := tendsto_integral_of_dominated_convergence (fun _ ↦ (2 * R) ^ 2)
      (fun m ↦ (hD_sm m).pow 2) (integrable_const ((2 * R) ^ 2))
      (fun m ↦ (hD_bd m).mono fun ω hω ↦ by
        rw [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ hω.1 hω.2 2)
      (hD_lim.mono fun ω hω ↦ by simpa only [Pi.pow_apply, zero_pow two_ne_zero] using hω.pow 2)
    simpa only [Pi.pow_apply, integral_zero] using h2

private lemma stronglyMeasurable_expProc {X A : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted ℱ X) (hA : StronglyAdapted ℱ A) (α : ℝ) (u : ℝ≥0) :
    StronglyMeasurable[ℱ u] (expProc X A α u) :=
  Complex.continuous_exp.comp_stronglyMeasurable
    ((stronglyMeasurable_const.mul (Complex.continuous_ofReal.comp_stronglyMeasurable (hX u))).add
      (Complex.continuous_ofReal.comp_stronglyMeasurable (stronglyMeasurable_const.mul (hA u))))

private lemma integrable_expProc {X A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hX : StronglyAdapted ℱ X) (hA : StronglyAdapted ℱ A) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) (u : ℝ≥0) :
    Integrable (expProc X A α u) P :=
  (integrable_const _).mono'
    ((stronglyMeasurable_expProc hX hA α u).mono (ℱ.le u)).aestronglyMeasurable
    (ae_norm_expProc_le (X := X) hA0 hA_step α u)

/-- On each subinterval `[u, v]`, martingale orthogonality replaces `expProc v - expProc u` by
`expProc u * expRem`, and both integrands are integrable on `E`. -/
private lemma setIntegral_exp_step_eq_rem {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (hA_adapt : StronglyAdapted ℱ A)
    (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) {u v : ℝ≥0} (huv : u ≤ v) {E : Set Ω} (hE : MeasurableSet[ℱ u] E) :
    IntegrableOn (fun ω ↦ expProc X A α u ω * expRem α (X v ω - X u ω) (A v ω - A u ω)) E P ∧
      ∫ ω in E, (expProc X A α v ω - expProc X A α u ω) ∂P =
        ∫ ω in E, expProc X A α u ω * expRem α (X v ω - X u ω) (A v ω - A u ω) ∂P := by
  have hZ_adapt := stronglyMeasurable_expProc hX.stronglyAdapted hA_adapt α u
  have hZ_bd := ae_norm_expProc_le (X := X) hA0 hA_step α u
  have hZ_sub : IntegrableOn (fun ω ↦ expProc X A α v ω - expProc X A α u ω) E P :=
    ((integrable_expProc hX.stronglyAdapted hA_adapt hA0 hA_step α v).sub
      (integrable_expProc hX.stronglyAdapted hA_adapt hA0 hA_step α u)).integrableOn
  have hlin1 : IntegrableOn
      (fun ω ↦ (I * (α : ℂ)) * (expProc X A α u ω * ((X v ω - X u ω : ℝ) : ℂ))) E P :=
    (((Complex.ofRealCLM.integrable_comp ((hX.integrable v).sub (hX.integrable u))).bdd_mul
      (hZ_adapt.mono (ℱ.le u)).aestronglyMeasurable hZ_bd).const_mul _).integrableOn
  have hlin2 : IntegrableOn (fun ω ↦ ((α ^ 2 / 2 : ℝ) : ℂ) *
      (expProc X A α u ω * (((A v ω - A u ω) - (X v ω - X u ω) ^ 2 : ℝ) : ℂ))) E P :=
    (((Complex.ofRealCLM.integrable_comp ((integrable_increment_bracket hX hQ hA_step huv).sub
        ((memLp_increment_sq hX.stronglyAdapted hXR u v).integrable one_le_two))).bdd_mul
      (hZ_adapt.mono (ℱ.le u)).aestronglyMeasurable hZ_bd).const_mul _).integrableOn
  have hdecomp : ∀ ω, expProc X A α u ω * expRem α (X v ω - X u ω) (A v ω - A u ω) =
      (expProc X A α v ω - expProc X A α u ω) -
        (I * (α : ℂ)) * (expProc X A α u ω * ((X v ω - X u ω : ℝ) : ℂ)) -
        ((α ^ 2 / 2 : ℝ) : ℂ) *
          (expProc X A α u ω * (((A v ω - A u ω) - (X v ω - X u ω) ^ 2 : ℝ) : ℂ)) := fun ω ↦ by
    have hstep_eq : expProc X A α u ω *
        (exp (I * α * ((X v ω - X u ω : ℝ) : ℂ) + ((α ^ 2 / 2 * (A v ω - A u ω) : ℝ) : ℂ)) - 1) =
        expProc X A α v ω - expProc X A α u ω := by
      dsimp only [expProc]
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [← hstep_eq]; dsimp only [expRem]; ring
  have hsub1 : IntegrableOn (fun ω ↦ (expProc X A α v ω - expProc X A α u ω) -
      (I * (α : ℂ)) * (expProc X A α u ω * ((X v ω - X u ω : ℝ) : ℂ))) E P := hZ_sub.sub hlin1
  refine ⟨by simp_rw [hdecomp]; exact hsub1.sub hlin2, ?_⟩
  simp_rw [hdecomp]
  rw [integral_sub hsub1 hlin2, integral_sub hZ_sub hlin1,
    integral_const_mul, integral_const_mul,
    setIntegral_mul_sub_eq_zero_complex hX huv hE hZ_adapt hZ_bd,
    setIntegral_mul_sq_sub_eq_zero_complex hX hQ hXR huv hE hZ_adapt hZ_bd]
  simp

/-- Telescoping identity expressing the set integral of `expProc t - expProc s` as the sum of
the third-order remainder terms along the uniform grid of `[s, t]`. -/
private lemma setIntegral_exp_sub_eq_sum_expRem {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (hA_adapt : StronglyAdapted ℱ A)
    (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {E : Set Ω} (hE : MeasurableSet[ℱ s] E) (m : ℕ) :
    IntegrableOn (fun ω ↦ ∑ k : Fin (m + 1), expProc X A α (uniformGrid s t m k.castSucc) ω *
        expRem α (X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω)
          (A (uniformGrid s t m k.succ) ω - A (uniformGrid s t m k.castSucc) ω)) E P ∧
      ∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P =
        ∫ ω in E, (∑ k : Fin (m + 1), expProc X A α (uniformGrid s t m k.castSucc) ω *
          expRem α (X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω)
            (A (uniformGrid s t m k.succ) ω - A (uniformGrid s t m k.castSucc) ω)) ∂P := by
  have hstep (k : Fin (m + 1)) := setIntegral_exp_step_eq_rem hX hQ hXR hA_adapt hA0 hA_step α
    (uniformGrid_mono s t m (Fin.castSucc_le_succ k))
    (ℱ.mono (uniformGrid_mem_Icc hst m k.castSucc).1 _ hE)
  have hZ_diff (k : Fin (m + 1)) : IntegrableOn
      (fun ω ↦ expProc X A α (uniformGrid s t m k.succ) ω -
        expProc X A α (uniformGrid s t m k.castSucc) ω) E P :=
    ((integrable_expProc hX.stronglyAdapted hA_adapt hA0 hA_step α _).sub
      (integrable_expProc hX.stronglyAdapted hA_adapt hA0 hA_step α _)).integrableOn
  refine ⟨integrable_finsetSum Finset.univ fun k _ ↦ (hstep k).1, ?_⟩
  have htele : ∀ ω, expProc X A α t ω - expProc X A α s ω =
      ∑ k : Fin (m + 1), (expProc X A α (uniformGrid s t m k.succ) ω -
        expProc X A α (uniformGrid s t m k.castSucc) ω) := fun ω ↦ by
    rw [Fin.sum_univ_succ_sub_castSucc (fun k ↦ expProc X A α (uniformGrid s t m k) ω),
      uniformGrid_zero, uniformGrid_last hst]
  simp_rw [htele]
  rw [integral_finsetSum Finset.univ fun k _ ↦ hZ_diff k,
    integral_finsetSum Finset.univ fun k _ ↦ (hstep k).1]
  exact Finset.sum_congr rfl fun k _ ↦ (hstep k).2

/-- Partition error estimate on `[s, t]` for a fixed uniform mesh size `m`. -/
private lemma norm_setIntegral_exp_sub_le {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ} (hc : 0 ≤ c)
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R) (hA_adapt : StronglyAdapted ℱ A)
    (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {E : Set Ω} (hE : MeasurableSet[ℱ s] E) (m : ℕ) :
    let L : ℝ := c * ((t : ℝ) - s)
    let Mz : ℝ := Real.exp (α ^ 2 / 2 * (c * (t : ℝ)))
    let Ke : ℝ := Real.exp (2 * |α| * R + α ^ 2 / 2 * L)
    let B : ℝ := (4 * R ^ 2 * L + 2 * L ^ 2) * P.real Set.univ
    ‖∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P‖ ≤
      Mz * ((|α| ^ 3 / 2 * L) * ∫ ω, maxInc X s t m ω ∂P +
        (α ^ 4 / 8 * L ^ 2 * P.real Set.univ) / (m + 1 : ℝ) +
        4 * |α| ^ 3 * Ke * Real.sqrt ((∫ ω, maxInc X s t m ω ^ 2 ∂P) * B) +
        4 * (α ^ 2 / 2) ^ 3 * Ke * (L ^ 3 * P.real Set.univ) / (m + 1 : ℝ) ^ 2) := by
  intro L Mz Ke B
  let S : Ω → ℝ := fun ω ↦ ∑ k : Fin (m + 1),
    (X (uniformGrid s t m k.succ) ω - X (uniformGrid s t m k.castSucc) ω) ^ 2
  obtain ⟨hrem_int, hsum_eq⟩ :=
    setIntegral_exp_sub_eq_sum_expRem hX hQ hXR hA_adapt hA0 hA_step α hst hE m
  have hD_memLp : MemLp (maxInc X s t m) 2 P := memLp_maxInc hX.stronglyAdapted hXR s t m
  have hS_memLp : MemLp S 2 P := memLp_finsetSum Finset.univ fun k _ ↦
    memLp_increment_sq hX.stronglyAdapted hXR _ _
  have hCS : ∫ ω, maxInc X s t m ω * S ω ∂P ≤ Real.sqrt ((∫ ω, maxInc X s t m ω ^ 2 ∂P) * B) := by
    have hS2 : ∫ ω, S ω ^ 2 ∂P ≤ B := by
      simpa only [S, B, L] using integral_sq_sum_sq_le hc hX hQ hXR hA_step
        (uniformGrid_mono s t m) (uniformGrid_zero s t m) (uniformGrid_last hst m)
    exact Real.le_sqrt_of_sq_le
      ((TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq hD_memLp hS_memLp).trans
        (mul_le_mul_of_nonneg_left hS2 (integral_nonneg fun _ ↦ sq_nonneg _)))
  let f1 (ω : Ω) := |α| ^ 3 / 2 * L * maxInc X s t m ω
  let f2 : Ω → ℝ := fun _ ↦ α ^ 4 / 8 * L ^ 2 / (m + 1 : ℝ)
  let f3 (ω : Ω) := 4 * |α| ^ 3 * Ke * (maxInc X s t m ω * S ω)
  let f4 : Ω → ℝ := fun _ ↦ 4 * (α ^ 2 / 2) ^ 3 * Ke * L ^ 3 / (m + 1 : ℝ) ^ 2
  have ht1 : Integrable f1 P := (hD_memLp.integrable one_le_two).const_mul _
  have ht3 : Integrable f3 P := (memLp_one_iff_integrable.1 (hD_memLp.mul hS_memLp)).const_mul _
  have ht12 : Integrable (fun ω ↦ f1 ω + f2 ω) P := ht1.add (integrable_const _)
  have ht123 : Integrable (fun ω ↦ f1 ω + f2 ω + f3 ω) P := ht12.add ht3
  have hrhs_int : Integrable (fun ω ↦ Mz * (f1 ω + f2 ω + f3 ω + f4 ω)) P :=
    (ht123.add (integrable_const _)).const_mul Mz
  have hnorm_le : ‖∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P‖ ≤
      ∫ ω, Mz * (f1 ω + f2 ω + f3 ω + f4 ω) ∂P := by
    rw [hsum_eq]
    refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae hrem_int.norm
      hrhs_int.integrableOn
      (ae_restrict_of_ae (ae_norm_sum_expRem_le hc hXR hA0 hA_step α hst m))).trans
      (setIntegral_le_integral hrhs_int (ae_of_all P fun ω ↦ ?_)))
    have hL : 0 ≤ L := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
    have hD0 : 0 ≤ maxInc X s t m ω := le_trans (abs_nonneg _) (Finset.le_sup'
      (f := fun k : Fin (m + 1) ↦ |X (uniformGrid s t m k.succ) ω -
        X (uniformGrid s t m k.castSucc) ω|) (Finset.mem_univ 0))
    have hS0 : 0 ≤ S ω := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    dsimp only [f1, f2, f3, f4]; positivity
  refine hnorm_le.trans ?_
  rw [integral_const_mul, integral_add ht123 (integrable_const _), integral_add ht12 ht3,
    integral_add ht1 (integrable_const _)]
  simp only [f1, f3, integral_const_mul, integral_const, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hterm := mul_le_mul_of_nonneg_left hCS (by positivity : 0 ≤ 4 * |α| ^ 3 * Ke)
  linarith [show P.real Set.univ * (α ^ 4 / 8 * L ^ 2 / (m + 1 : ℝ)) =
      α ^ 4 / 8 * L ^ 2 * P.real Set.univ / (m + 1 : ℝ) by ring,
    show P.real Set.univ * (4 * (α ^ 2 / 2) ^ 3 * Ke * L ^ 3 / (m + 1 : ℝ) ^ 2) =
      4 * (α ^ 2 / 2) ^ 3 * Ke * (L ^ 3 * P.real Set.univ) / (m + 1 : ℝ) ^ 2 by ring]

end ModulusAndPartition

/-- **Complex exponential martingale for a bounded continuous martingale with Lipschitz bracket.**
If `X` is a bounded, almost-surely continuous real martingale, `A` is a strongly adapted
nondecreasing Lipschitz process starting at `0`, and `X ^ 2 - A` is a martingale, then
`t ↦ exp (I * α * X t + α ^ 2 / 2 * A t)` is a martingale for every `α : ℝ`. -/
theorem exp_I_mul_add_of_bounded {X A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hX : Martingale X ℱ P) (hQ : Martingale (fun u ω ↦ X u ω ^ 2 - A u ω) ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (X · ω)) (hXR : ∀ u, ∀ᵐ ω ∂P, |X u ω| ≤ R)
    (hA_adapt : StronglyAdapted ℱ A) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (α : ℝ) :
    Martingale (fun t ω ↦ exp (I * α * X t ω + ((α ^ 2 / 2 * A t ω : ℝ) : ℂ))) ℱ P := by
  let c' : ℝ := max c 0
  have hc' : 0 ≤ c' := le_max_right c 0
  have hA_step' (u v : ℝ≥0) (huv : u ≤ v) :
      ∀ᵐ ω ∂P, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c' * ((v : ℝ) - u) :=
    (hA_step u v huv).mono fun _ hω ↦
      ⟨hω.1, hω.2.trans (mul_le_mul_of_nonneg_right (le_max_left c 0)
        (sub_nonneg.2 (NNReal.coe_le_coe.2 huv)))⟩
  have hZ_adapt : StronglyAdapted ℱ (expProc X A α) :=
    stronglyMeasurable_expProc hX.stronglyAdapted hA_adapt α
  have hZ_int (u : ℝ≥0) : Integrable (expProc X A α u) P :=
    integrable_expProc hX.stronglyAdapted hA_adapt hA0 hA_step' α u
  change Martingale (expProc X A α) ℱ P
  rw [hZ_adapt.martingale_iff_setIntegral_eq hZ_int]
  intro s t hst E hE
  suffices hzero : ‖∫ ω in E, (expProc X A α t ω - expProc X A α s ω) ∂P‖ = 0 by
    have hsub := norm_eq_zero.1 hzero
    rw [integral_sub (hZ_int t).integrableOn (hZ_int s).integrableOn, sub_eq_zero] at hsub
    exact hsub.symm
  obtain ⟨hD1, hD2⟩ := tendsto_integral_maxInc_and_sq hX.stronglyAdapted hcont hXR hst
  exact le_antisymm
    (ge_of_tendsto' (tendsto_partition_err hD1 hD2) fun m ↦
      norm_setIntegral_exp_sub_le hc' hX hQ hXR hA_adapt hA0 hA_step' α hst hE m)
    (norm_nonneg _)

end MeasureTheory.Martingale
