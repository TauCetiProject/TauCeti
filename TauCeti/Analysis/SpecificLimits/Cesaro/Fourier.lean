/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.ZMod.Defs
import TauCeti.Analysis.Fourier.ZMod

/-!
# Cesàro averages via discrete Fourier transforms

* `TauCeti.tendsto_cesaro_ite_mod_of_fourier`: vanishing of rational Fourier twists modulo `q`
  implies vanishing of the masked Cesàro average on a residue class `r < q`.
-/

public section

open Filter Finset

namespace TauCeti

/-- Vanishing of rational Fourier twists modulo `q` implies vanishing on the residue class `r < q`
for any complex sequence `b : ℕ → ℂ`. -/
theorem tendsto_cesaro_ite_mod_of_fourier {b : ℕ → ℂ} {q r : ℕ} [NeZero q] (hr : r < q)
    (h : ∀ a : ZMod q, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
      ∑ i ∈ range (n + 1), b i * fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), if i % q = r then b i else 0)
      atTop (nhds (0 : ℂ)) := by
  have hsum : Tendsto (fun n : ℕ ↦ (q : ℂ)⁻¹ * ∑ a : ZMod q, ZMod.stdAddChar (-((r : ZMod q) * a)) *
      (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1),
        b i * fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle))) atTop (nhds 0) := by
    have hsum' := (tendsto_const_nhds (x := (q : ℂ)⁻¹)).mul (tendsto_finsetSum univ fun a _ ↦
      by simpa only [mul_zero] using
        (tendsto_const_nhds (x := ZMod.stdAddChar (-((r : ZMod q) * a)))).mul (h a))
    rwa [sum_const_zero, mul_zero] at hsum'
  refine hsum.congr fun n ↦ ?_
  have hterm (i : ℕ) : (if i % q = r then b i else 0) = (q : ℂ)⁻¹ * ∑ a : ZMod q,
      ZMod.stdAddChar (-((r : ZMod q) * a)) *
        (b i * fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle)) := by
    rw [(by split_ifs <;> simp :
        (if i % q = r then b i else 0) = (if i % q = r then (1 : ℂ) else 0) * b i),
      ZMod.ite_mod_eq_sum_fourier hr i, mul_assoc, sum_mul]
    exact congrArg ((q : ℂ)⁻¹ * ·) (sum_congr rfl fun _ _ ↦ by ring)
  simp_rw [hterm, Complex.real_smul, ← mul_sum]
  rw [sum_comm (s := range (n + 1)) (t := univ), mul_left_comm _ (q : ℂ)⁻¹]
  simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]
  congr 1; rw [mul_sum]; exact sum_congr rfl fun a _ ↦ by rw [← mul_sum, mul_left_comm]

end TauCeti
