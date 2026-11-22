/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Topology and strict bounds in `ℝ≥0`

A strict bound `c < a` persists for `c * C ^ n` when `C` is slightly greater than one. This
absorbs a small multiplicative loss in estimates with a fixed natural power.

For `0 < c`, the maps `t ↦ (c + t)⁻¹` and `t ↦ t * (c + t)⁻¹` are continuous on `ℝ≥0`
(`NNReal.continuous_inv_add`, `NNReal.continuous_mul_inv_add`).

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter
open scoped NNReal Topology

namespace NNReal

/-- A strict coefficient bound persists after multiplication by a fixed natural power of some
factor greater than one. -/
theorem exists_one_lt_mul_pow_lt (c : ℝ≥0) {a : ℝ≥0} (hca : c < a) (n : ℕ) :
    ∃ C : ℝ≥0, 1 < C ∧ c * C ^ n < a := by
  have hcont : ContinuousAt (fun C : ℝ≥0 ↦ c * C ^ n) 1 := by fun_prop
  have hnear : ∀ᶠ C in 𝓝 (1 : ℝ≥0), c * C ^ n < a :=
    hcont.eventually_lt_const (by simpa only [one_pow, mul_one] using hca)
  obtain ⟨C, hCa, hC⟩ :=
    ((hnear.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists
      (f := 𝓝[>] (1 : ℝ≥0))
  exact ⟨C, hC, hCa⟩

/-- For a positive `c : ℝ≥0`, the shifted reciprocal `t ↦ (c + t)⁻¹` is continuous on `ℝ≥0`. -/
@[fun_prop]
theorem continuous_inv_add {c : ℝ≥0} (hc : 0 < c) :
    Continuous (fun t : ℝ≥0 ↦ (c + t)⁻¹) :=
  (continuous_const.add continuous_id).inv₀ fun t ↦ (add_pos_of_pos_of_nonneg hc t.property).ne'

/-- For a positive `c : ℝ≥0`, the bounded rational map `t ↦ t * (c + t)⁻¹` is continuous on
`ℝ≥0`. -/
@[fun_prop]
theorem continuous_mul_inv_add {c : ℝ≥0} (hc : 0 < c) :
    Continuous (fun t : ℝ≥0 ↦ t * (c + t)⁻¹) :=
  continuous_id.mul (continuous_inv_add hc)

end NNReal
