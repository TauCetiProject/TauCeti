/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord.Analytic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Slice
import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# Cycle-word generating products for countable atomic models

This file lifts the finite cycle-word results to countable alphabets: signed power sum evaluation
at `Q = 1` (`countableAtomicTrace_cycleWord_of_sq_eq_one`), norm bound
(`norm_countableAtomicTrace_cycleWord_le`), the infinite generating product
(`countableAtomicTrace_cycleWord_hasProd`), and its left-slice specialization
(`hasProd_ofReal_cycleWord`).
-/

public section

open Filter
open scoped Topology

namespace TauCeti.TypeAHeckeAlgebra

/-- Absolute summability of the signed `(m + 1)`-th powers
`(if pos a then 1 else -1) ^ m * p a ^ (m + 1)` for an absolutely summable family `p : ι → R`. -/
theorem summable_signed_pow_mul_pow {R ι : Type*} [SeminormedRing R] (pos : ι → Prop)
    [DecidablePred pos] {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    Summable fun a ↦ ‖(if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)‖ := by
  refine (hp.mul_left (‖(1 : R)‖ * (∑' b, ‖p b‖) ^ m)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun a ↦ (norm_mul_le _ _).trans ?_
  rw [show ‖(if pos a then (1 : R) else -1) ^ m‖ = ‖(1 : R)‖ by split_ifs <;> simp, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((norm_pow_le' (p a) (Nat.succ_pos m)).trans
    (by rw [pow_succ]; gcongr; exact hp.le_tsum a fun _ _ ↦ norm_nonneg _)) (norm_nonneg _)

/-- **Cycle-word countable atomic trace at `Q = 1`** equals the signed `(m + 1)`-th power sum. -/
theorem countableAtomicTrace_cycleWord_of_sq_eq_one {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ)
    (hq : (q : R) ^ 2 = 1) (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) =
      ∑' a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  refine tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1)))
    <| (summable_signed_pow_mul_pow pos hp m).of_norm.hasSum.congr fun s ↦ by
      rw [← Finset.sum_attach s (fun a ↦ (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)),
        ← Finset.univ_eq_attach, ← atomicTrace_cycleWord_of_sq_eq_one (fun a : s ↦ pos a) q hq]

private theorem sum_subtype_norm_le_tsum {E ι : Type*} [SeminormedAddCommGroup E] {p : ι → E}
    (hp : Summable fun a ↦ ‖p a‖) (s : Finset ι) : ∑ a : s, ‖p a‖ ≤ ∑' a, ‖p a‖ := by
  rw [Finset.univ_eq_attach, s.sum_attach fun a ↦ ‖p a‖]; exact hp.sum_le_tsum s fun _ _ ↦
    norm_nonneg _

/-- Norm bound on the countable atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_countableAtomicTrace_cycleWord_le {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m * (∑' a, ‖p a‖) ^ (m + 1) := by
  refine le_of_tendsto (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))).norm
    (Eventually.of_forall fun s ↦ (norm_atomicTrace_cycleWord_le (fun a : s ↦ pos a) q _ m).trans
      ?_)
  have hs := sum_subtype_norm_le_tsum hp s; gcongr; exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Absolute summability of the countable cycle-trace generating series on the convergence disk. -/
theorem summable_norm_countableAtomicTrace_cycleWord_mul_pow {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1) :
    Summable fun m : ℕ ↦
      ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ :=
  summable_norm_mul_pow_succ_of_le (by positivity) (tsum_nonneg fun _ ↦ norm_nonneg _) hx
    fun m ↦ by
      simpa only [norm_one, one_mul] using norm_countableAtomicTrace_cycleWord_le pos q p hp m

/-- **Countable cycle-trace generating product** over any complete normed field `K` on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1`. -/
theorem countableAtomicTrace_cycleWord_hasProd {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦
        ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      HasProd (fun a : ι ↦ if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x)) (1 + ((q : K) ^ 2 - 1) * ∑' m : ℕ,
        countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) := by
  refine ⟨summable_norm_countableAtomicTrace_cycleWord_mul_pow pos q p hp hx, ?_⟩
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖); set S : ℝ := ∑' a, ‖p a‖
  have _ : 0 ≤ S := tsum_nonneg fun _ ↦ norm_nonneg _
  refine (tendsto_const_nhds.add ((tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (by positivity) hx).mul_left (S * ‖x‖))
    (fun m ↦ (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))).mul_const _)
    (Eventually.of_forall fun s m ↦ norm_mul_pow_succ_le (M := M) (S := S) <|
      (norm_atomicTrace_cycleWord_le _ q _ m).trans (by
        simp only [norm_one, one_mul]; have hs := sum_subtype_norm_le_tsum hp s
        have h0 : 0 ≤ ∑ a : s, ‖p a‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
        gcongr))).const_mul _)).congr fun s ↦ ?_
  rw [(atomicTrace_cycleWord_generating_eval (fun a : s ↦ pos a) q (fun a : s ↦ p a)
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sum_subtype_norm_le_tsum hp s)
        (by positivity)) (norm_nonneg x)).trans_lt hx)).2, Finset.univ_eq_attach, s.prod_attach
    fun a ↦ if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
      else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x)]

/-- **Rational evaluation of the cycle-trace product for real-weighted left-slice Markov
models.** -/
theorem hasProd_ofReal_cycleWord {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
    [DecidablePred pos] {q : ℂˣ} {Q : ℝ} (hqQ : (q : ℂ) ^ 2 = Q) {w : ι → ℝ}
    (hw : Summable fun a ↦ ‖w a‖) (hw0 : ∀ a, 0 ≤ w a) (hsum : (∑' a, w a) = 1)
    (η : ℝ) (hslice : ∀ b, (if pos b then Q else -1) * w b +
      (Q - 1) * (∑' a, if a < b then w a else 0) = (1 + Q) * η - 1)
    {x : ℂ} (hxM : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ‖x‖ < 1)
    (hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1) :
    HasProd (fun a : ι ↦ if pos a then (1 - (w a : ℂ) * x) / (1 - (q : ℂ) ^ 2 * (w a : ℂ) * x)
        else (1 + (q : ℂ) ^ 2 * (w a : ℂ) * x) / (1 + (w a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) / (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hp : Summable fun a ↦ ‖(w a : ℂ)‖ := hw.congr fun _ ↦ (Complex.norm_real _).symm
  have hnorm_sum : (∑' a, ‖(w a : ℂ)‖) = 1 := by simpa [Real.norm_of_nonneg (hw0 _)] using hsum
  have hprod := (countableAtomicTrace_cycleWord_hasProd pos q _ hp (by rwa [hnorm_sum, mul_one])).2
  set s : ℝ := (1 + Q) * η - 1
  have htr (m : ℕ) : countableAtomicTrace pos q (fun a ↦ (w a : ℂ))
      hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1) = x * ((s : ℂ) * x) ^ m := by
    rw [countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice pos hqQ hw η hsum hslice,
      toInfinite_cycleWord, (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace _).map_cycleWord,
      Nat.add_sub_cancel, mul_markovParam_proj_eq hqQ η]; ring
  have hne : 1 - (s : ℂ) * x ≠ 0 := sub_ne_zero.mpr fun h ↦ by
    linarith [norm_one (α := ℂ) ▸ congrArg (‖·‖) h]
  convert hprod using 1; simp_rw [htr]
  rw [(summable_geometric_of_norm_lt_one hsx).tsum_mul_left, tsum_geometric_of_norm_lt_one hsx, hqQ,
    show (((1 + Q) * η - 1 : ℝ) : ℂ) = s from rfl, eq_comm, eq_div_iff hne, add_mul,
    mul_assoc (_ - 1), mul_assoc x, inv_mul_cancel₀ hne]; dsimp only [s]; push_cast; ring

end TauCeti.TypeAHeckeAlgebra
