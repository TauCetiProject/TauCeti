/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord.Analytic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Cycle-word generating products for countable atomic models

This file lifts the finite cycle-word results to countable alphabets with absolutely summable
weights: the signed power sum evaluation at `Q = 1`
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_of_sq_eq_one`), the exponential norm
bound (`TauCeti.TypeAHeckeAlgebra.norm_countableAtomicTrace_cycleWord_le`) obtained from finite
exhaustion and `TauCeti.TypeAHeckeAlgebra.norm_atomicTrace_cycleWord_le`, and the infinite
cycle-trace generating product (`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_hasProd`)
over any complete normed field `K`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.summable_signed_pow_mul_pow`: absolute summability of signed power
  sums `(if pos a then 1 else -1) ^ m * p a ^ (m + 1)`.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_of_sq_eq_one`: countable cycle-word
  trace at `Q = 1`.
* `TauCeti.TypeAHeckeAlgebra.norm_countableAtomicTrace_cycleWord_le`: norm bound on countable
  cycle-word traces.
* `TauCeti.TypeAHeckeAlgebra.summable_norm_countableAtomicTrace_cycleWord_mul_pow` and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_cycleWord_hasProd`: convergence and infinite
  product formula for the countable cycle-trace generating function.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.TypeAHeckeAlgebra

/-- Absolute summability of the signed `(m + 1)`-th powers `(if pos a then 1 else -1) ^ m *
p a ^ (m + 1)` for an absolutely summable family `p : ι → R`. -/
theorem summable_signed_pow_mul_pow {R ι : Type*} [NormedCommRing R] (pos : ι → Prop)
    [DecidablePred pos] {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    Summable fun a ↦ ‖(if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)‖ := by
  have hsign (a : ι) : ‖(if pos a then (1 : R) else -1) ^ m‖ = ‖(1 : R)‖ := by
    split_ifs <;> simp
  refine (hp.mul_left (‖(1 : R)‖ * (∑' b, ‖p b‖) ^ m)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun a ↦ (norm_mul_le _ _).trans ?_
  rw [hsign a, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((norm_pow_le' (p a) (Nat.succ_pos m)).trans ?_)
    (norm_nonneg _)
  rw [pow_succ]
  gcongr
  exact hp.le_tsum a fun _ _ ↦ norm_nonneg _

/-- **Cycle-word countable atomic trace at `Q = 1`** equals the signed `(m + 1)`-th power sum. -/
theorem countableAtomicTrace_cycleWord_of_sq_eq_one {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ)
    (hq : (q : R) ^ 2 = 1) (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) =
      ∑' a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  refine tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))) <|
    (summable_signed_pow_mul_pow pos hp m).of_norm.hasSum.congr fun s ↦ ?_
  rw [← Finset.sum_attach s (fun a ↦ (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)),
    ← Finset.univ_eq_attach, ← atomicTrace_cycleWord_of_sq_eq_one (fun a : s ↦ pos a) q hq]

/-- Norm bound on the countable atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_countableAtomicTrace_cycleWord_le {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m *
        (∑' a, ‖p a‖) ^ (m + 1) := by
  refine le_of_tendsto (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))).norm
    (Eventually.of_forall fun s ↦ ?_)
  refine (norm_atomicTrace_cycleWord_le (fun a : s ↦ pos a) q (fun a : s ↦ p a) m).trans ?_
  have hs : ∑ a : s, ‖p a‖ ≤ ∑' a, ‖p a‖ := by
    rw [Finset.univ_eq_attach, s.sum_attach fun a ↦ ‖p a‖]
    exact hp.sum_le_tsum s fun _ _ ↦ norm_nonneg _
  gcongr; exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Absolute summability of the countable cycle-trace generating series on the convergence disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem summable_norm_countableAtomicTrace_cycleWord_mul_pow {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1) :
    Summable fun m : ℕ ↦
      ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ :=
  summable_norm_mul_pow_of_le (by positivity) (tsum_nonneg fun _ ↦ norm_nonneg _) hx
    (norm_countableAtomicTrace_cycleWord_le pos q p hp)

/-- **Countable cycle-trace generating product** over any complete normed field `K` on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem countableAtomicTrace_cycleWord_hasProd {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦
        ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      HasProd (fun a : ι ↦
          if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))
        (1 + ((q : K) ^ 2 - 1) * ∑' m : ℕ,
          countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) := by
  refine ⟨summable_norm_countableAtomicTrace_cycleWord_mul_pow pos q p hp hx, ?_⟩
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  set S : ℝ := ∑' a, ‖p a‖
  have hS0 : 0 ≤ S := tsum_nonneg fun _ ↦ norm_nonneg _
  have hs_le (s : Finset ι) : ∑ a : s, ‖p a‖ ≤ S := by
    rw [Finset.univ_eq_attach, s.sum_attach fun a ↦ ‖p a‖]
    exact hp.sum_le_tsum s fun _ _ ↦ norm_nonneg _
  have hdom : Tendsto (fun s : Finset ι ↦ ∑' m : ℕ,
      atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1)) atTop
      (𝓝 (∑' m : ℕ, countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1))) :=
    tendsto_tsum_of_dominated_convergence (summable_cycleWordMajorant (by positivity) hS0 hx)
      (fun m ↦ (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))).mul_const _)
      (Eventually.of_forall fun s m ↦ norm_mul_pow_le_cycleWordMajorant
        ((norm_atomicTrace_cycleWord_le _ q _ m).trans
          (by have := hs_le s; gcongr; exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)))
  refine (tendsto_const_nhds.add (hdom.const_mul _)).congr fun s ↦ ?_
  have hxs : M * (∑ a : s, ‖p a‖) * ‖x‖ < 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs_le s) (by positivity))
      (norm_nonneg x)).trans_lt hx
  rw [(atomicTrace_cycleWord_generating_eval (fun a : s ↦ pos a) q (fun a : s ↦ p a) hxs).2,
    Finset.univ_eq_attach, s.prod_attach (fun a ↦
      if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
      else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))]

end TauCeti.TypeAHeckeAlgebra
