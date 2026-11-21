/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Group
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Summable real and complex powers

A nonnegative family `f` with a summable positive power `f ^ p` tends to `0` along the cofinite
filter, since its terms are the `p`-th roots of a summable family.

For `1 < s.re` and any complex shift `c : ℂ`, the shifted principal-power series
`∑' n : ℕ, ((n : ℂ) + c) ^ (-s)` converges absolutely. At a nonpositive integer shift `c = -n`
(`n : ℕ`), the base `(n : ℂ) + c` vanishes and the principal-power summand `0 ^ (-s)` is `0` for
`1 < s.re` by Lean's totalized `Complex.cpow`; genuine non-totalized shifts require `c ∉ -ℕ`.

## Main results

* `TauCeti.tendsto_cofinite_zero_of_summable_rpow` — a nonnegative family with a summable positive
  power tends to `0`.
* `TauCeti.summable_norm_natCast_add_cpow_neg` and `TauCeti.summable_natCast_add_cpow_neg` —
  absolute convergence of `∑' n : ℕ, ((n : ℂ) + c) ^ (-s)` for `1 < s.re` and any `c : ℂ`.
-/

public section

open Complex

namespace TauCeti

/-- A nonnegative family `f` with `f ^ p` summable for some `0 < p` tends to `0` along the
cofinite filter. -/
theorem tendsto_cofinite_zero_of_summable_rpow {ι : Type*} {f : ι → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (h : Summable fun i ↦ f i ^ p) :
    Filter.Tendsto f Filter.cofinite (nhds 0) := by
  have h' := h.tendsto_cofinite_zero.rpow_const (p := p⁻¹) (Or.inr (inv_nonneg.2 hp.le))
  rw [Real.zero_rpow (inv_ne_zero hp.ne')] at h'
  exact h'.congr fun i ↦ Real.rpow_rpow_inv (hf i) hp.ne'

private theorem re_natCast_add_floor_add_one_pos (c : ℂ) (n : ℕ) :
    0 < (((n + (⌊1 - c.re⌋₊ + 1) : ℕ) : ℂ) + c).re := by
  have hlt : 1 - c.re < (⌊1 - c.re⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  simp only [add_re, natCast_re, Nat.cast_add, Nat.cast_one, one_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- For `1 < s.re` and any `c : ℂ`, the principal-power series `∑' n : ℕ, ‖(n + c) ^ (-s)‖` is
summable (for `c = -n` with `n : ℕ`, the `n`-th summand uses the totalized principal power
`0 ^ (-s) = 0`). -/
theorem summable_norm_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖((n : ℂ) + c) ^ (-s)‖) := by
  set N : ℕ := ⌊1 - c.re⌋₊ + 1
  have hN : (N : ℂ) + c ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (by simpa [N] using re_natCast_add_floor_add_one_pos c 0))
  obtain ⟨U, hU, -, C, -, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hN (-s)
  have hp : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-s.re)) :=
    ((summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow (p := -s.re)).mpr (by linarith))).congr
      fun n => by push_cast; rw [add_comm]
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hp.mul_left C)
  have h := hbound ((N : ℂ) + c) (mem_of_mem_nhds hU) (n : ℝ) (Nat.cast_nonneg n)
  simpa only [ofReal_natCast, neg_re, Nat.cast_add, add_assoc] using h

/-- For `1 < s.re` and any `c : ℂ`, `n ↦ (n + c) ^ (-s)` is summable (with totalized `0 ^ (-s) = 0`
at index `n` when `c = -n`). -/
theorem summable_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) :=
  (summable_norm_natCast_add_cpow_neg hs c).of_norm

end TauCeti
