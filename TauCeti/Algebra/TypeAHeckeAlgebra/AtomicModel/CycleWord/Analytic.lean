/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord.NormBounds
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.RingTheory.PowerSeries.EvalAt

/-!
# Analytic evaluation of finite cycle-trace generating functions

For a finite linearly ordered alphabet `ι` and weights `p : ι → R` over a normed commutative ring,
`TauCeti.TypeAHeckeAlgebra.norm_atomicTrace_cycleWord_le` bounds the finite atomic trace of the
cycle word `cycleWord q (m + 1)` directly by summing the diagonal word bounds. Over a complete
normed field `K`, `TauCeti.TypeAHeckeAlgebra.atomicTrace_cycleWord_generating_eval` evaluates the
formal generating identity `TauCeti.TypeAHeckeAlgebra.atomicTrace_cycleWord_generating_function` on
the disk `max 1 (max ‖q ^ 2‖ ‖q ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1`, without depending on
countable trace positivity or GNS constructions.

## Main results

* `TauCeti.TypeAHeckeAlgebra.norm_atomicTrace_cycleWord_le`: norm bound on finite cycle-word atomic
  traces.
* `TauCeti.TypeAHeckeAlgebra.norm_mul_pow_le_cycleWordMajorant`,
  `TauCeti.TypeAHeckeAlgebra.summable_cycleWordMajorant`, and
  `TauCeti.TypeAHeckeAlgebra.summable_norm_mul_pow_of_le`: shared geometric majorant and
  summability helpers for cycle-trace generating series.
* `TauCeti.TypeAHeckeAlgebra.summable_norm_atomicTrace_cycleWord_mul_pow`: absolute summability of
  the finite cycle-trace generating series on the convergence disk.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_cycleWord_generating_eval`: analytic evaluation of the
  finite cycle-trace generating function.
-/

public section

open Finsupp

namespace TauCeti.TypeAHeckeAlgebra

/-- Norm bound on the finite atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_atomicTrace_cycleWord_le {R : Type*} [NormedCommRing R] {ι : Type*}
    [LinearOrder ι] [Fintype ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) (p : ι → R)
    (m : ℕ) :
    ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m *
        (∑ a, ‖p a‖) ^ (m + 1) := by
  rw [atomicTrace_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ w : Fin (m + 1) → ι, ‖signedChecked pos q (cycleWord q (m + 1)) (single w 1) w * ∏ i, p (w i)‖
      ≤ ∑ w : Fin (m + 1) → ι,
          (‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m) * ∏ i, ‖p (w i)‖ :=
        Finset.sum_le_sum fun w _ ↦ (norm_mul_le _ _).trans <|
          mul_le_mul (norm_signedChecked_cycleWord_single_apply_le pos q w)
            (Finset.norm_prod_le' _ Finset.univ_nonempty _) (norm_nonneg _) (by positivity)
    _ = ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m *
          ∑ w : Fin (m + 1) → ι, ∏ i, ‖p (w i)‖ := (Finset.mul_sum ..).symm
    _ = ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m * (∑ a, ‖p a‖) ^ (m + 1) := by
        rw [← Fintype.prod_sum (fun (_ : Fin (m + 1)) a ↦ ‖p a‖), Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]

/-- Shared geometric majorant bound for cycle-trace generating series: if
`‖t‖ ≤ ‖(1 : K)‖ * M ^ m * S ^ (m + 1)`, then
`‖t * x ^ (m + 1)‖ ≤ (S * ‖x‖) * (M * S * ‖x‖) ^ m`. -/
theorem norm_mul_pow_le_cycleWordMajorant {K : Type*} [NormedField K] {t : K} {M S : ℝ}
    {x : K} {m : ℕ} (ht : ‖t‖ ≤ ‖(1 : K)‖ * M ^ m * S ^ (m + 1)) :
    ‖t * x ^ (m + 1)‖ ≤ (S * ‖x‖) * (M * S * ‖x‖) ^ m := by
  rw [norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_right ht (pow_nonneg (norm_nonneg x) _)).trans ?_
  rw [norm_one, one_mul]
  exact le_of_eq (by ring)

/-- Summability of the geometric majorant `(S * ‖x‖) * (M * S * ‖x‖) ^ m` when `M * S * ‖x‖ < 1`. -/
theorem summable_cycleWordMajorant {K : Type*} [NormedField K] {M S : ℝ} (hM : 0 ≤ M)
    (hS : 0 ≤ S) {x : K} (hx : M * S * ‖x‖ < 1) :
    Summable fun m : ℕ ↦ (S * ‖x‖) * (M * S * ‖x‖) ^ m :=
  (summable_geometric_of_lt_one (by positivity) hx).mul_left (S * ‖x‖)

/-- Shared geometric summability criterion for cycle-trace generating series. -/
theorem summable_norm_mul_pow_of_le {K : Type*} [NormedField K] {f : ℕ → K} {M S : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) {x : K} (hx : M * S * ‖x‖ < 1)
    (hf : ∀ m, ‖f m‖ ≤ ‖(1 : K)‖ * M ^ m * S ^ (m + 1)) :
    Summable fun m : ℕ ↦ ‖f m * x ^ (m + 1)‖ :=
  (summable_cycleWordMajorant hM hS hx).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun m ↦ norm_mul_pow_le_cycleWordMajorant (hf m)

/-- Absolute summability of the finite cycle-trace generating series on the convergence disk. -/
theorem summable_norm_atomicTrace_cycleWord_mul_pow {K : Type*} [NormedField K] {ι : Type*}
    [LinearOrder ι] [Fintype ι] (pos : ι → Prop) [DecidablePred pos] (q : Kˣ) (p : ι → K)
    {x : K} (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) :
    Summable fun m : ℕ ↦ ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ :=
  summable_norm_mul_pow_of_le (by positivity) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hx
    (norm_atomicTrace_cycleWord_le pos q p)

private theorem eval_denom_ne_zero {K : Type*} [NormedField K] {ι : Type*} [Fintype ι]
    (pos : ι → Prop) [DecidablePred pos] (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) (a : ι) :
    (if pos a then 1 - (q : K) ^ 2 * p a * x else 1 + p a * x) ≠ 0 := by
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  have hpa : ‖p a‖ ≤ ∑ b, ‖p b‖ :=
    Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)
  have h1M : 1 ≤ M := le_max_left _ _
  have hQM : ‖(q : K) ^ 2‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  split_ifs <;> intro h0
  · have : ‖(q : K) ^ 2 * p a * x‖ = 1 := by simpa [sub_eq_zero.mp h0] using norm_one (α := K)
    have : ‖(q : K) ^ 2 * p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ := by simp only [norm_mul]; gcongr
    linarith
  · have : ‖p a * x‖ = 1 := by rw [eq_neg_of_add_eq_zero_right h0, norm_neg, norm_one]
    have : ‖p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ := by rw [norm_mul, ← one_mul ‖p a‖]; gcongr
    linarith

/-- **Analytic evaluation of the cycle-trace generating function on a finite alphabet** on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem atomicTrace_cycleWord_generating_eval {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] [Fintype ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦ ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      1 + ((q : K) ^ 2 - 1) *
          (∑' m : ℕ, atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) =
        ∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x)) := by
  have hsum := summable_norm_atomicTrace_cycleWord_mul_pow pos q p hx
  refine ⟨hsum, ?_⟩
  let F : PowerSeries K := PowerSeries.mk fun m ↦
    if m = 0 then 1 else ((q : K) ^ 2 - 1) * atomicTrace pos q p m (cycleWord q m)
  let P : Polynomial K := ∏ a, if pos a then 1 - Polynomial.C ((q : K) ^ 2 * p a) * Polynomial.X
    else 1 + Polynomial.C (p a) * Polynomial.X
  let Qp : Polynomial K := ∏ a, if pos a then 1 - Polynomial.C (p a) * Polynomial.X
    else 1 + Polynomial.C ((q : K) ^ 2 * p a) * Polynomial.X
  have hF_sum : Summable fun m : ℕ ↦ ‖PowerSeries.coeff m F • x ^ m‖ := by
    rw [← summable_nat_add_iff 1]
    exact (hsum.mul_left ‖(q : K) ^ 2 - 1‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun m ↦ by
      simp only [F, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte, smul_eq_mul, mul_assoc]
      exact norm_mul_le _ _
  have hFP : F * (P : PowerSeries K) = (Qp : PowerSeries K) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply (φ := P),
      ← Polynomial.coeToPowerSeries.ringHom_apply (φ := Qp)]
    simpa only [F, P, Qp, map_prod, Polynomial.coeToPowerSeries.ringHom_apply,
      apply_ite ((↑) : Polynomial K → PowerSeries K), Polynomial.coe_sub, Polynomial.coe_add,
      Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X] using
      atomicTrace_cycleWord_generating_function pos q p
  have heval := PowerSeries.evalAt_mul_coe_of_summable_norm P hF_sum
  rw [hFP, PowerSeries.evalAt_coe, PowerSeries.evalAt_def, hF_sum.of_norm.tsum_eq_zero_add]
    at heval
  simp only [F, P, Qp, PowerSeries.coeff_mk, ↓reduceIte, smul_eq_mul, pow_zero, mul_one,
    Nat.succ_ne_zero, mul_assoc, hsum.of_norm.tsum_mul_left, Polynomial.coe_aeval_eq_eval,
    Polynomial.eval_prod, apply_ite (Polynomial.eval x), Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at heval
  let num : ι → K := fun a ↦ if pos a then 1 - p a * x else 1 + (q : K) ^ 2 * (p a * x)
  let den : ι → K := fun a ↦ if pos a then 1 - (q : K) ^ 2 * (p a * x) else 1 + p a * x
  calc
    1 + ((q : K) ^ 2 - 1) *
        ∑' m : ℕ, atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)
      = (∏ a, num a) / ∏ a, den a :=
        (eq_div_iff (Finset.prod_ne_zero_iff.mpr fun a _ ↦ by
          simpa only [den, mul_assoc] using eval_denom_ne_zero pos q p hx a)).mpr heval.symm
    _ = ∏ a, num a / den a := by rw [← Finset.prod_div_distrib]
    _ = ∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x)) :=
        Finset.prod_congr rfl fun a _ ↦ by
          dsimp only [num, den]; split_ifs <;> simp only [mul_assoc]

end TauCeti.TypeAHeckeAlgebra
